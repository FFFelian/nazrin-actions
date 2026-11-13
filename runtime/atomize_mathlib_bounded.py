#!/usr/bin/env python3
"""Resume a pinned theorem inventory with isolated workers and hard deadlines."""
from __future__ import annotations

import argparse
from collections import OrderedDict
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import selectors
import signal
import subprocess
import sys
import time
import uuid

PROTOCOL = b"NAZRIN_WORKER "
TERMINAL = {"success", "failure", "timeout", "crash", "import_failure", "invalid_symbol"}
TAIL_LIMIT = 16384
LINE_LIMIT = 65536


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value: dict) -> None:
    staging = path.with_name(path.name + ".tmp")
    with staging.open("w", encoding="utf-8") as handle:
        handle.write(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(staging, path)
    directory_fd = os.open(path.parent, os.O_DIRECTORY)
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)


def append_ledger(path: Path, record: dict) -> None:
    # A killed writer may leave one partial row. Keep it separate from the next row.
    with path.open("a+b") as handle:
        handle.seek(0, os.SEEK_END)
        if handle.tell():
            handle.seek(-1, os.SEEK_END)
            if handle.read(1) != b"\n":
                handle.write(b"\n")
        handle.write(json.dumps(record, ensure_ascii=False, separators=(",", ":")).encode() + b"\n")
        handle.flush()
        os.fsync(handle.fileno())


def load_latest(path: Path, inventory_keys: set[tuple[int, str, str]]) -> dict[tuple[int, str, str], str]:
    latest = {}
    if path.is_symlink():
        raise SystemExit("bounded ledger must not be a symlink")
    if not path.exists():
        return latest

    valid_lines, rejected_lines = [], []
    for raw_line in path.read_bytes().splitlines(keepends=True):
        try:
            row = json.loads(raw_line)
            if not isinstance(row, dict):
                raise ValueError("ledger row is not an object")
            index, theorem, module = row.get("index"), row.get("theorem"), row.get("module")
            if type(index) is not int or not isinstance(theorem, str) or not isinstance(module, str):
                raise ValueError("ledger identity has invalid types")
            key = (index, theorem, module)
            if key not in inventory_keys:
                raise ValueError("ledger identity is outside the inventory")
            status = row.get("status")
            if status not in TERMINAL | {"unknown"}:
                raise ValueError("ledger status is invalid")
            if status in TERMINAL | {"unknown"}:
                latest[key] = status
            valid_lines.append(raw_line if raw_line.endswith(b"\n") else raw_line + b"\n")
        except (json.JSONDecodeError, KeyError, TypeError, AttributeError, ValueError):
            rejected_lines.append(raw_line if raw_line.endswith(b"\n") else raw_line + b"\n")

    if rejected_lines:
        rejected_path = path.with_name(".bounded-rejected-results.jsonl")
        if rejected_path.is_symlink():
            raise SystemExit("rejected ledger archive must not be a symlink")
        existing = rejected_path.read_bytes() if rejected_path.is_file() else b""
        combined = existing
        if combined and not combined.endswith(b"\n"):
            combined += b"\n"
        staged = rejected_path.with_name(rejected_path.name + ".tmp")
        with staged.open("wb") as handle:
            handle.write(combined + b"".join(rejected_lines))
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(staged, rejected_path)
        staged = path.with_name(path.name + ".tmp")
        with staged.open("wb") as handle:
            handle.write(b"".join(valid_lines))
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(staged, path)
    return latest


def regular_file(path: Path) -> bool:
    try:
        return not path.is_symlink() and path.is_file()
    except OSError:
        return False


class Worker:
    """Own exactly one subprocess session; never signal any pre-existing task."""
    def __init__(self, executable: Path, env: dict, cwd: Path, module: str, args):
        self.command = [str(executable), module, str(args.max_heartbeats)]
        self.env, self.cwd = env, cwd
        self.memory_bytes = int(args.memory_gib * 1024**3)
        self.proc = None
        self.selector = selectors.DefaultSelector()
        self.pending = bytearray()
        self.dropping_line = False
        self.tail = bytearray()

    def limits(self):
        if self.memory_bytes:
            resource.setrlimit(resource.RLIMIT_AS, (self.memory_bytes, self.memory_bytes))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    def start(self, timeout: float):
        self.proc = subprocess.Popen(
            self.command, cwd=self.cwd, env=self.env, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0,
            start_new_session=True, preexec_fn=self.limits,
        )
        for stream, label in ((self.proc.stdout, "stdout"), (self.proc.stderr, "stderr")):
            os.set_blocking(stream.fileno(), False)
            self.selector.register(stream, selectors.EVENT_READ, label)
        message = self.read_message(timeout)
        if message.get("status") != "ready" or message.get("module") != self.command[1]:
            raise RuntimeError(f"unexpected worker startup reply: {message}")

    def diagnostic(self, data: bytes):
        self.tail.extend(data)
        if len(self.tail) > TAIL_LIMIT:
            del self.tail[:-TAIL_LIMIT]

    def read_message(self, timeout: float) -> dict:
        deadline = time.monotonic() + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("worker deadline exceeded")
            events = self.selector.select(remaining)
            if not events:
                raise TimeoutError("worker deadline exceeded")
            for key, _ in events:
                chunk = os.read(key.fd, 65536)
                if not chunk:
                    self.selector.unregister(key.fileobj)
                    continue
                if key.data == "stderr":
                    self.diagnostic(chunk)
                    continue
                pieces = chunk.split(b"\n")
                for i, piece in enumerate(pieces):
                    complete = i < len(pieces) - 1
                    if not self.dropping_line:
                        self.pending.extend(piece)
                        if len(self.pending) > LINE_LIMIT:
                            self.diagnostic(self.pending[-TAIL_LIMIT:])
                            self.pending.clear()
                            self.dropping_line = True
                    if complete:
                        line = bytes(self.pending)
                        self.pending.clear()
                        if not self.dropping_line and line.startswith(PROTOCOL):
                            message = json.loads(line[len(PROTOCOL):])
                            if not isinstance(message, dict):
                                raise ValueError("worker reply is not an object")
                            return message
                        self.diagnostic(line + b"\n")
                        self.dropping_line = False
            if not self.selector.get_map():
                code = self.proc.poll()
                raise EOFError(f"worker exited/closed output (exit={code})")

    def run(self, theorem: str, path: Path, timeout: float) -> dict:
        self.tail.clear()
        request = json.dumps({"theorem": theorem, "path": str(path)}, ensure_ascii=False).encode() + b"\n"
        self.proc.stdin.write(request)
        self.proc.stdin.flush()
        result = self.read_message(timeout)
        if result.get("theorem") != theorem:
            raise ValueError("worker response theorem does not match request")
        if result.get("status") not in {"success", "failure", "invalid_symbol"}:
            raise ValueError(f"unexpected worker status: {result.get('status')!r}")
        return result

    def stop(self):
        if self.proc is not None:
            # Session ID is created by this class, and is never a caller-supplied PID.
            try:
                os.killpg(self.proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                self.proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(self.proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                self.proc.wait()
            for stream in (self.proc.stdin, self.proc.stdout, self.proc.stderr):
                if stream is not None:
                    stream.close()
        self.selector.close()
        self.proc = None


def execute(args) -> int:
    inventory, output, project = args.inventory.resolve(), args.output.resolve(), args.project.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # Hold the lock for the whole run, without affecting legacy Atomizer processes.
    lock = (output / ".bounded.lock").open("a")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit("another bounded supervisor is already writing this output directory")
    worker_bin = (args.worker or Path(__file__).resolve().parents[1] / ".lake/build/bin/AtomizerWorker").resolve()
    if not worker_bin.is_file():
        raise SystemExit(f"worker binary does not exist: {worker_bin}")
    if args.timeout_seconds <= 0 or args.startup_timeout_seconds <= 0 or args.max_heartbeats < 0 or args.memory_gib < 0 or args.lean_workers < 1 or args.recycle_every < 1:
        raise SystemExit("deadlines, worker count, and recycle interval must be positive; memory/heartbeat limits must be nonnegative")
    env = dict(os.environ)
    env["LEAN_PATH"] = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True, timeout=60,
    ).strip()
    env["LEAN_TASK_MANAGER_WORKERS"] = str(args.lean_workers)
    runtime_report_path = Path(__file__).resolve().parents[1] / ".nazrin-actions-runtime.json"
    if not regular_file(runtime_report_path):
        raise SystemExit("assembled runtime provenance is missing; refusing to resume")
    runtime_report = json.loads(runtime_report_path.read_text(encoding="utf-8"))
    if (not isinstance(runtime_report, dict)
            or not isinstance(runtime_report.get("source_commit"), str)
            or not isinstance(runtime_report.get("mathlib_commit"), str)
            or not isinstance(runtime_report.get("runtime_manifest_sha256"), str)
            or len(runtime_report["runtime_manifest_sha256"]) != 64):
        raise SystemExit("assembled runtime provenance is invalid; refusing to resume")
    manifest = {
        "schema": 1, "inventory_sha256": sha256(inventory),
        "worker_sha256": sha256(worker_bin),
        "project_manifest_sha256": sha256(project / "lake-manifest.json"),
        "toolchain": (project / "lean-toolchain").read_text().strip(),
        "runtime_provenance_sha256": sha256(runtime_report_path),
        "runtime_manifest_sha256": runtime_report.get("runtime_manifest_sha256"),
        "supervisor_sha256": sha256(Path(__file__).resolve()),
        "source_commit": runtime_report.get("source_commit"),
        "mathlib_commit": runtime_report.get("mathlib_commit"),
        "timeout_seconds": args.timeout_seconds, "startup_timeout_seconds": args.startup_timeout_seconds,
        "max_heartbeats": args.max_heartbeats, "memory_gib": args.memory_gib,
        "lean_workers": args.lean_workers, "import_module": args.import_module,
    }
    manifest_path = output / ".bounded-manifest.json"
    ledger = output / ".bounded-results.jsonl"
    if manifest_path.exists():
        if json.loads(manifest_path.read_text()) != manifest:
            raise SystemExit("run manifest differs from this inventory, worker, project, runtime, or limits; use a new output directory")
    elif any(path.name not in {".bounded.lock", "runtime-provenance.json", "shard-input.tsv",
                               "fixture-inventory.tsv", "supervisor.log"}
             for path in output.iterdir()):
        raise SystemExit("existing bounded state has no version manifest; use a new output directory")
    else:
        write_json(manifest_path, manifest)
    excluded = {int(v) for v in args.exclude_indices.split(",") if v.strip()}
    modules = OrderedDict()
    inventory_keys = set()
    inventory_rows = []
    with inventory.open(encoding="utf-8") as handle:
        if next(handle, "").rstrip("\r\n") != "index\ttheorem\tmodule":
            raise SystemExit("invalid theorem inventory header")
        for line in handle:
            index_text, theorem, module = line.rstrip("\r\n").split("\t")
            index = int(index_text)
            key = (index, theorem, module)
            inventory_keys.add(key)
            inventory_rows.append((index, theorem, module))
    latest = load_latest(ledger, inventory_keys)
    reused = 0
    for index, theorem, module in inventory_rows:
        if index < args.start_index or index in excluded:
            continue
        if args.mathlib_only and module != "Mathlib" and not module.startswith("Mathlib."):
            continue
        status = latest.get((index, theorem, module))
        artifact = output / (hashlib.sha256(theorem.encode()).hexdigest() + ".txt")
        if status == "success" and regular_file(artifact) and artifact.stat().st_size > 0:
            continue
        if status in TERMINAL - {"success", "import_failure"} and not args.retry_failures:
            continue
        if args.reuse_legacy:
            legacy = output / (theorem + ".txt")
            if legacy.parent == output and (regular_file(legacy) or (not args.retry_failures and regular_file(Path(str(legacy) + ".log")))):
                reused += 1
                continue
        modules.setdefault(args.import_module or module, []).append((index, theorem, module))
    if args.limit is not None:
        keep = max(0, args.limit)
        selected = OrderedDict()
        for module, rows in modules.items():
            if not keep:
                break
            selected[module] = rows[:keep]
            keep -= len(selected[module])
        modules = selected
    total = sum(map(len, modules.values()))
    print(f"queued {total} declarations in {len(modules)} imported modules; reused {reused} historical artifacts; ledger={ledger}", flush=True)
    state_path = output / ".bounded-state.json"
    attempted = 0
    worker = None
    worker_count = 0
    try:
        for import_module, rows in modules.items():
            import_error = None
            for index, theorem, owner in rows:
                digest = hashlib.sha256(theorem.encode()).hexdigest()
                basename = digest + ".txt"
                final = output / basename
                # Staging names never look like committed trace artifacts.
                staging = output / (".pending-" + uuid.uuid4().hex)
                started = time.monotonic()
                write_json(state_path, {"status": "running", "pid": os.getpid(), "index": index,
                    "theorem": theorem, "module": owner, "import_module": import_module,
                    "attempted_this_run": attempted, "queued_this_run": total})
                diagnostic = b""
                result = None
                if import_error is not None:
                    status, error = "import_failure", import_error
                else:
                    if worker is None:
                        worker = Worker(worker_bin, env, project, import_module, args)
                        try:
                            worker.start(args.startup_timeout_seconds)
                            worker_count = 0
                        except Exception as exc:
                            diagnostic = bytes(worker.tail)
                            worker.stop()
                            worker = None
                            import_error = f"Could not import {import_module}: {str(exc)[:512]}"
                    if worker is None:
                        status, error = "import_failure", import_error
                    else:
                        try:
                            result = worker.run(theorem, staging, args.timeout_seconds)
                            status, error = result["status"], ""
                            source = staging if status == "success" else Path(str(staging) + ".log")
                            if status in {"success", "failure"}:
                                if not regular_file(source):
                                    raise ValueError("worker reported an outcome without a regular artifact")
                                destination = final if status == "success" else Path(str(final) + ".log")
                                os.replace(source, destination)
                                with destination.open("rb") as artifact_handle:
                                    os.fsync(artifact_handle.fileno())
                                directory_fd = os.open(output, os.O_DIRECTORY)
                                try:
                                    os.fsync(directory_fd)
                                finally:
                                    os.close(directory_fd)
                            worker_count += 1
                        except TimeoutError:
                            status, error = "timeout", f"Hard timeout after {args.timeout_seconds:g} seconds"
                        except (OSError, EOFError, ValueError) as exc:
                            status, error = "crash", f"Worker error: {str(exc)[:1024]}"
                        diagnostic = bytes(worker.tail)
                        if status in {"timeout", "crash"} or worker_count >= args.recycle_every:
                            worker.stop()
                            worker = None
                elapsed = time.monotonic() - started
                record = {"index": index, "theorem": theorem, "module": owner, "status": status,
                    "filename": basename if status == "success" else basename + ".log",
                    "elapsed_seconds": round(elapsed, 6)}
                if error:
                    record["error"] = error
                if status not in {"success", "failure"}:
                    Path(str(final) + ".log").write_text((error or status) + "\n" + diagnostic.decode("utf-8", errors="replace"), encoding="utf-8")
                append_ledger(ledger, record)
                if status == "import_failure":
                    write_json(state_path, {"status": "import_failure", "pid": os.getpid(),
                        "theorem": theorem, "module": owner, "import_module": import_module,
                        "attempted_this_run": attempted, "queued_this_run": total})
                    raise SystemExit("worker import failed; remaining declarations were left unattempted (resume retries import failures)")
                # Only remove this attempt's validated staging names, after its result is durable.
                for stale in (staging, Path(str(staging) + ".log")):
                    if stale.parent == output and stale.name.startswith(".pending-") and regular_file(stale):
                        stale.unlink()
                attempted += 1
                if attempted % 25 == 0 or status in {"timeout", "crash", "import_failure"}:
                    print(f"{status} {attempted}/{total} {theorem}", flush=True)
            if worker is not None:
                worker.stop()
                worker = None
        write_json(state_path, {"status": "finished", "pid": os.getpid(), "attempted_this_run": attempted, "queued_this_run": total})
    finally:
        if worker is not None:
            worker.stop()
        lock.close()
    print(f"finished {attempted} declarations", flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--worker", type=Path)
    parser.add_argument("--timeout-seconds", type=float, default=90.0)
    parser.add_argument("--startup-timeout-seconds", type=float, default=600.0)
    parser.add_argument("--max-heartbeats", type=int, default=200_000)
    parser.add_argument("--memory-gib", type=float, default=8.0, help="per-worker virtual-address-space limit; 0 disables")
    parser.add_argument("--lean-workers", type=int, default=2)
    parser.add_argument("--recycle-every", type=int, default=500, help="reimport after this many requests to release accumulated caches")
    parser.add_argument("--import-module", help="import this umbrella module instead of each declaration's owner")
    parser.add_argument("--mathlib-only", action="store_true")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--exclude-indices", default="")
    parser.add_argument("--reuse-legacy", action="store_true", help="skip original Atomizer artifacts in this output directory")
    parser.add_argument("--retry-failures", action="store_true")
    args = parser.parse_args()
    def stop_on_signal(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, stop_on_signal)
    try:
        return execute(args)
    except KeyboardInterrupt:
        print("interrupted; recorded outcomes can be resumed", file=sys.stderr)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
