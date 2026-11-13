#!/usr/bin/env python3
"""Run one immutable theorem shard and record terminal versus pending rows."""
from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import time
from typing import Any

try:
    from plan_shards import parse_inventory, stable_shard
except ModuleNotFoundError:
    from scripts.plan_shards import parse_inventory, stable_shard

HEADER = "index\ttheorem\tmodule"
OUTCOME_STATUSES = {"success", "failure", "timeout", "crash", "invalid_symbol"}


def read_inventory(path: Path) -> list[dict[str, Any]]:
    return parse_inventory(path)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _safe_artifact(output: Path, filename: object) -> Path | None:
    if not isinstance(filename, str) or not filename or Path(filename).name != filename:
        return None
    candidate = output / filename
    if candidate.is_symlink() or not candidate.is_file():
        return None
    return candidate


def terminal_coverage(
    inventory: list[dict[str, Any]], output: Path
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Subtract only validated theorem outcomes, never import failures or cursor state."""
    ledger = output / ".bounded-results.jsonl"
    by_key = {(row["index"], row["theorem"], row["module"]): row for row in inventory}
    latest: dict[tuple[int, str, str], dict[str, Any]] = {}
    invalid_rows = 0
    unknown_rows = 0
    if ledger.is_symlink():
        invalid_rows += 1
    elif ledger.exists():
        with ledger.open(encoding="utf-8", errors="replace") as handle:
            for line in handle:
                if not line.strip():
                    continue
                try:
                    record = json.loads(line)
                    key = (record["index"], record["theorem"], record["module"])
                    if not isinstance(record, dict) or key not in by_key:
                        unknown_rows += 1
                        continue
                    if record.get("status") not in OUTCOME_STATUSES | {"import_failure", "unknown"}:
                        invalid_rows += 1
                        continue
                    latest[key] = record
                except (json.JSONDecodeError, KeyError, TypeError):
                    invalid_rows += 1

    terminal: set[tuple[int, str, str]] = set()
    status_counts: dict[str, int] = {}
    missing_artifacts = 0
    for key, record in latest.items():
        status = record.get("status")
        if status not in OUTCOME_STATUSES:
            continue
        artifact = _safe_artifact(output, record.get("filename"))
        valid_artifact = artifact is not None
        if valid_artifact and status in {"success", "failure"}:
            valid_artifact = artifact.stat().st_size > 0
        if not valid_artifact:
            missing_artifacts += 1
            continue
        terminal.add(key)
        status_counts[status] = status_counts.get(status, 0) + 1

    pending = [row for row in inventory if (row["index"], row["theorem"], row["module"]) not in terminal]
    stats = {
        "inventory_rows": len(inventory),
        "terminal_rows": len(terminal),
        "pending_rows": len(pending),
        "terminal_status_counts": status_counts,
        "invalid_ledger_rows": invalid_rows,
        "unknown_ledger_rows": unknown_rows,
        "missing_terminal_artifacts": missing_artifacts,
    }
    return pending, stats


def _atomic_json(path: Path, value: dict[str, Any]) -> None:
    temp = path.with_name(path.name + ".tmp")
    temp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(temp, path)


def _enable_child_subreaper() -> bool:
    if not sys.platform.startswith("linux"):
        return False
    try:
        return ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) == 0
    except (AttributeError, OSError):
        return False


def _process_identity(pid: int) -> tuple[int, int, int, str] | None:
    try:
        raw = Path(f"/proc/{pid}/stat").read_text()
        fields = raw[raw.rfind(")") + 2:].split()
        return int(fields[1]), int(fields[2]), int(fields[3]), fields[19]
    except (OSError, ValueError, IndexError):
        return None


WorkerSessions = dict[int, dict[int, str]]


def _process_snapshot() -> dict[int, tuple[int, int, int, str, str]]:
    processes = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            raw = (entry / "stat").read_text()
            fields = raw[raw.rfind(")") + 2:].split()
            processes[int(entry.name)] = (
                int(fields[1]), int(fields[2]), int(fields[3]), fields[19], fields[0]
            )
        except (OSError, ValueError, IndexError):
            continue
    return processes


def _session_has_live_members(session_id: int) -> bool:
    return any(info[2] == session_id and info[4] not in {"Z", "X"}
               for info in _process_snapshot().values())


def _merge_worker_sessions(target: WorkerSessions, new: WorkerSessions) -> None:
    for session_id, members in new.items():
        target.setdefault(session_id, {}).update(members)


def _worker_sessions(supervisor_pid: int) -> WorkerSessions:
    """Track isolated child sessions using member PIDs and their start times."""
    children_path = Path(f"/proc/{supervisor_pid}/task/{supervisor_pid}/children")
    try:
        child_pids = [int(value) for value in children_path.read_text().split()]
    except (OSError, ValueError):
        return {}
    supervisor_identity = _process_identity(supervisor_pid)
    supervisor_session = supervisor_identity[2] if supervisor_identity else supervisor_pid
    sessions: WorkerSessions = {}
    for pid in child_pids:
        identity = _process_identity(pid)
        if identity is not None and identity[2] != supervisor_session:
            sessions.setdefault(identity[2], {})[pid] = identity[3]
    return sessions


def _adopted_worker_sessions() -> WorkerSessions:
    sessions: WorkerSessions = {}
    own_session = os.getsid(0)
    for pid, info in _process_snapshot().items():
        if info[0] == os.getpid() and info[2] != own_session:
            sessions.setdefault(info[2], {})[pid] = info[3]
    return sessions


def _live_worker_members(sessions: WorkerSessions) -> dict[int, str]:
    snapshot = _process_snapshot()
    live = {}
    for session_id, remembered in sessions.items():
        # A matching member anchors ownership even after the session leader exits.
        if not any(pid in snapshot and snapshot[pid][2:4] == (session_id, start)
                   for pid, start in remembered.items()):
            continue
        for pid, info in snapshot.items():
            if info[2] == session_id:
                remembered[pid] = info[3]
                if info[4] not in {"Z", "X"}:
                    live[pid] = info[3]
    return live


def _signal_worker_sessions(sessions: WorkerSessions, sig: int) -> None:
    for pid, start_ticks in _live_worker_members(sessions).items():
        descriptor = None
        try:
            if hasattr(os, "pidfd_open") and hasattr(signal, "pidfd_send_signal"):
                descriptor = os.pidfd_open(pid)
            identity = _process_identity(pid)
            if identity is None or identity[3] != start_ticks:
                continue
            if descriptor is not None:
                signal.pidfd_send_signal(descriptor, sig)
            else:
                os.kill(pid, sig)
        except ProcessLookupError:
            pass
        finally:
            if descriptor is not None:
                os.close(descriptor)


def _reap_worker_sessions(sessions: WorkerSessions, grace_seconds: float) -> None:
    _merge_worker_sessions(sessions, _adopted_worker_sessions())
    _signal_worker_sessions(sessions, signal.SIGTERM)
    deadline = time.monotonic() + grace_seconds
    while _live_worker_members(sessions) and time.monotonic() < deadline:
        time.sleep(0.05)
    # Wait briefly after KILL: sending it alone does not mean the child has exited.
    deadline = time.monotonic() + 2.0
    while True:
        _merge_worker_sessions(sessions, _adopted_worker_sessions())
        _signal_worker_sessions(sessions, signal.SIGKILL)
        live = _live_worker_members(sessions)
        for pid, info in _process_snapshot().items():
            if info[0] == os.getpid() and info[2] in sessions:
                try:
                    os.waitpid(pid, os.WNOHANG)
                except (ChildProcessError, OSError):
                    pass
        if not live:
            return
        if time.monotonic() >= deadline:
            raise RuntimeError(f"worker processes did not exit after SIGKILL: {sorted(live)}")
        time.sleep(0.05)


def run(args: argparse.Namespace) -> int:
    inventory_path = args.inventory.resolve()
    output = args.output.resolve()
    source = args.source.resolve()
    project = args.project.resolve()
    supervisor = args.supervisor.resolve()
    worker = (source / ".lake/build/bin/AtomizerWorker").resolve()
    for path, label in ((inventory_path, "inventory"), (supervisor, "supervisor"), (worker, "AtomizerWorker")):
        if not path.is_file():
            raise FileNotFoundError(f"missing {label}: {path}")
    if args.timeout_seconds != 30:
        raise ValueError("per-theorem timeout is fixed at 30 seconds")
    if args.shard_count < 1 or not 0 <= args.shard_id < args.shard_count:
        raise ValueError("shard ID must be in range 0..shard-count-1")
    if args.internal_workers < 1 or args.max_runtime_seconds <= 0 or args.grace_seconds < 0:
        raise ValueError("worker count/runtime must be positive and grace period nonnegative")
    rows = read_inventory(inventory_path)
    for row in rows:
        expected_shard = stable_shard(row["module"], row["theorem"], args.shard_count)
        if expected_shard != args.shard_id:
            raise ValueError(
                f"theorem {row['theorem']!r} is assigned to shard {expected_shard}, "
                f"not requested shard {args.shard_id}"
            )
    output.mkdir(parents=True, exist_ok=True)
    runtime_path = source / ".nazrin-actions-runtime.json"
    runtime_manifest_sha256 = None
    if runtime_path.is_file():
        runtime_bytes = runtime_path.read_bytes()
        runtime = json.loads(runtime_bytes)
        if runtime.get("source_commit") != args.source_commit.lower():
            raise ValueError("assembled runtime source identity mismatch")
        runtime_manifest_sha256 = runtime["runtime_manifest_sha256"]
        runtime_copy = output / "runtime-provenance.json"
        if runtime_copy.exists() and runtime_copy.read_bytes() != runtime_bytes:
            raise ValueError("existing shard belongs to a different assembled runtime")
        runtime_copy.write_bytes(runtime_bytes)
    input_copy = output / "shard-input.tsv"
    digest = sha256(inventory_path)
    if input_copy.exists():
        if sha256(input_copy) != digest:
            raise ValueError("existing shard output belongs to a different inventory")
    else:
        input_copy.write_bytes(inventory_path.read_bytes())

    output.mkdir(parents=True, exist_ok=True)
    project_env = os.environ.copy()
    project_env["LEAN_TASK_MANAGER_WORKERS"] = str(args.internal_workers)
    lake_bin = shutil.which("lake", path=project_env.get("PATH"))
    if not lake_bin:
        raise FileNotFoundError("lake executable is not on PATH")
    lean_path = subprocess.check_output(
        [lake_bin, "env", "printenv", "LEAN_PATH"], cwd=project,
        env=project_env, text=True, timeout=60,
    ).strip()
    separator = os.pathsep if os.name == "nt" else ":"
    source_libraries = [source / ".lake/build/lib/lean"]
    source_libraries.extend(
        package / ".lake/build/lib/lean"
        for package in sorted((source / ".lake/packages").glob("*"))
        if (package / ".lake/build/lib/lean").is_dir()
    )
    project_env["LEAN_PATH"] = separator.join([str(p) for p in source_libraries] + ([lean_path] if lean_path else []))

    # Lake retains incoming LEAN_PATH after its workspace paths. The supervisor
    # uses the real Lake executable and inherits these source dependency paths.

    command = [
        sys.executable, str(supervisor), str(inventory_path), str(output),
        "--project", str(project), "--worker", str(worker),
        "--timeout-seconds", str(args.timeout_seconds),
        "--startup-timeout-seconds", str(args.startup_timeout_seconds),
        "--max-heartbeats", str(args.max_heartbeats),
        "--memory-gib", str(args.memory_gib),
        "--lean-workers", str(args.internal_workers),
        "--recycle-every", str(args.recycle_every),
        "--import-module", args.import_module,
    ]
    if args.retry_failures:
        command.append("--retry-failures")

    stop_requested = False
    previous_handlers: dict[int, Any] = {}

    def request_stop(signum: int, _frame: Any) -> None:
        nonlocal stop_requested
        stop_requested = True

    for sig in (signal.SIGINT, signal.SIGTERM):
        previous_handlers[sig] = signal.signal(sig, request_stop)
    if sys.platform.startswith("linux") and not _enable_child_subreaper():
        raise OSError("could not enable Linux child-subreaper cleanup")

    started = time.monotonic()
    deadline = started + args.max_runtime_seconds
    returncode: int | None = None
    stop_reason: str | None = None
    worker_sessions: WorkerSessions = {}
    try:
        with (output / "supervisor.log").open("ab", buffering=0) as log:
            proc = subprocess.Popen(
                command,
                cwd=project,
                env=project_env,
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            while proc.poll() is None:
                _merge_worker_sessions(worker_sessions, _worker_sessions(proc.pid))
                if stop_requested:
                    stop_reason = "received_signal"
                elif time.monotonic() >= deadline:
                    stop_reason = "runtime_budget_reached"
                if stop_reason:
                    _merge_worker_sessions(worker_sessions, _worker_sessions(proc.pid))
                    _signal_worker_sessions(worker_sessions, signal.SIGTERM)
                    try:
                        os.killpg(proc.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        returncode = proc.wait(timeout=args.grace_seconds)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(proc.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        returncode = proc.wait()
                    finally:
                        _signal_worker_sessions(worker_sessions, signal.SIGKILL)
                    break
                time.sleep(min(1.0, max(0.05, deadline - time.monotonic())))
            if returncode is None:
                returncode = proc.wait()
    finally:
        if returncode is not None:
            _merge_worker_sessions(worker_sessions, _worker_sessions(proc.pid))
            if sys.platform.startswith("linux"):
                _merge_worker_sessions(worker_sessions, _adopted_worker_sessions())
            _reap_worker_sessions(worker_sessions, min(args.grace_seconds, 5.0))
        for sig, handler in previous_handlers.items():
            signal.signal(sig, handler)

    pending, stats = terminal_coverage(rows, output)
    pending_path = output / "pending-inventory.tsv"
    with pending_path.open("w", encoding="utf-8", newline="") as handle:
        handle.write(HEADER + "\n")
        for row in pending:
            handle.write(f"{row['index']}\t{row['theorem']}\t{row['module']}\n")

    state_path = output / ".bounded-state.json"
    scanner_state = None
    if state_path.is_file():
        try:
            scanner_state = json.loads(state_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            scanner_state = {"status": "invalid_json"}
    status = "finished" if returncode == 0 and stop_reason is None else "interrupted" if stop_reason else "failed"
    summary = {
        "schema": 1,
        "shard_id": args.shard_id,
        "status": status,
        "source_commit": args.source_commit.lower(),
        "runtime_manifest_sha256": runtime_manifest_sha256,
        "inventory_sha256": digest,
        "timeout_seconds_per_theorem": args.timeout_seconds,
        "lean_internal_workers": args.internal_workers,
        "supervisor_exit_code": returncode,
        "stop_reason": stop_reason,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "scanner_state": scanner_state,
        **stats,
        "pending_inventory": pending_path.name,
    }
    _atomic_json(output / "shard-summary.json", summary)
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    # Deliberately return success for a planned cutoff/interruption so workflow can upload it.
    return 0 if status in {"finished", "interrupted"} else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--supervisor", type=Path)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--shard-id", type=int, required=True)
    parser.add_argument("--shard-count", type=int, required=True)
    parser.add_argument("--timeout-seconds", type=float, default=30.0)
    parser.add_argument("--startup-timeout-seconds", type=float, default=180.0)
    parser.add_argument("--max-heartbeats", type=int, default=200_000)
    parser.add_argument("--memory-gib", type=float, default=10.0, help="RLIMIT_AS virtual address-space limit, not a RAM reservation")
    parser.add_argument("--internal-workers", type=int, default=2)
    parser.add_argument("--recycle-every", type=int, default=500)
    parser.add_argument("--import-module", default="Mathlib")
    parser.add_argument("--max-runtime-seconds", type=float, default=16_200.0, help="supervisor-only budget; reserve job time for setup and uploads")
    parser.add_argument("--grace-seconds", type=float, default=180.0)
    parser.add_argument("--retry-failures", action="store_true")
    args = parser.parse_args()
    if args.supervisor is None:
        args.supervisor = args.source / "script/atomize_mathlib_bounded.py"
    try:
        return run(args)
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
