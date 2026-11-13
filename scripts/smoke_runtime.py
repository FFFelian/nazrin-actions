#!/usr/bin/env python3
"""Smoke-test an assembled runtime after setup; retain all output for diagnosis.

Requires lake on PATH and the setup-exported Nazrin/Mathlib LEAN_PATH. Invoke
with --source SOURCE --project PROJECT --output OUTPUT (a fresh directory).
The bounded supervisor runs the real worker; no shard mapping is involved.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
from typing import Any

FIXTURE_ROWS = ((0, "Nat.le_refl", "Mathlib"), (1, "Nat.succ_pos", "Mathlib"))
FIXTURE = (
    "index\ttheorem\tmodule\n"
    "0\tNat.le_refl\tMathlib\n"
    "1\tNat.succ_pos\tMathlib\n"
).encode("utf-8")
LIMITS = {
    "timeout_seconds": 30,
    "startup_timeout_seconds": 180,
    "max_heartbeats": 200_000,
    "memory_gib": 10,
    "lean_workers": 2,
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value: dict[str, Any]) -> None:
    staging = path.with_name(path.name + ".tmp")
    with staging.open("w", encoding="utf-8") as handle:
        handle.write(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(staging, path)
    directory_fd = os.open(path.parent, os.O_DIRECTORY)
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)


def require_file(path: Path) -> None:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"missing regular file: {path}")


def read_object(path: Path) -> dict[str, Any]:
    require_file(path)
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object: {path.name}")
    return value


def expected_manifest(source: Path, project: Path, inventory: Path) -> dict[str, Any]:
    worker = source / ".lake/build/bin/AtomizerWorker"
    provenance = source / ".nazrin-actions-runtime.json"
    supervisor = source / "script/atomize_mathlib_bounded.py"
    for path in (worker, provenance, supervisor, project / "lake-manifest.json", project / "lean-toolchain"):
        require_file(path)
    # Parse the project manifest as well as binding its exact bytes to the run.
    read_object(project / "lake-manifest.json")
    toolchain = (project / "lean-toolchain").read_text(encoding="utf-8").strip()
    require_file(source / "lean-toolchain")
    if not toolchain or (source / "lean-toolchain").read_text(encoding="utf-8").strip() != toolchain:
        raise ValueError("source and project toolchains must match")
    runtime_identity = read_object(provenance)
    if (not isinstance(runtime_identity.get("source_commit"), str)
            or not isinstance(runtime_identity.get("mathlib_commit"), str)
            or not isinstance(runtime_identity.get("runtime_manifest_sha256"), str)):
        raise ValueError("assembled runtime provenance is incomplete")
    return {
        "schema": 1,
        "inventory_sha256": sha256(inventory),
        "worker_sha256": sha256(worker),
        "project_manifest_sha256": sha256(project / "lake-manifest.json"),
        "runtime_provenance_sha256": sha256(provenance),
        "runtime_manifest_sha256": runtime_identity["runtime_manifest_sha256"],
        "source_commit": runtime_identity["source_commit"],
        "mathlib_commit": runtime_identity["mathlib_commit"],
        "supervisor_sha256": sha256(supervisor),
        "toolchain": toolchain,
        **LIMITS,
        "import_module": "Mathlib",
    }


def validate_output(output: Path, manifest: dict[str, Any]) -> list[dict[str, Any]]:
    """Accept only two fresh successful outcomes and their committed traces."""
    inventory = output / "fixture-inventory.tsv"
    require_file(inventory)
    if inventory.read_bytes() != FIXTURE:
        raise ValueError("immutable fixture inventory was changed")
    if read_object(output / ".bounded-manifest.json") != manifest:
        raise ValueError("bounded manifest does not match fixture, worker, project, or limits")

    ledger = output / ".bounded-results.jsonl"
    require_file(ledger)
    data = ledger.read_bytes()
    if not data.endswith(b"\n"):
        raise ValueError("bounded ledger has an incomplete final row")
    lines = data.decode("utf-8").splitlines()
    if len(lines) != len(FIXTURE_ROWS):
        raise ValueError("bounded ledger must contain exactly one outcome per fixture row")
    traces = []
    for line, (index, theorem, module) in zip(lines, FIXTURE_ROWS):
        record = json.loads(line)
        if not isinstance(record, dict):
            raise ValueError("bounded ledger outcome must be an object")
        if (type(record.get("index")) is not int
                or (record["index"], record.get("theorem"), record.get("module")) != (index, theorem, module)):
            raise ValueError(f"bounded outcome does not match fixture row {index}")
        if record.get("status") != "success":
            raise ValueError(f"fixture {theorem} did not succeed: {record.get('status')}")
        elapsed = record.get("elapsed_seconds")
        if (type(elapsed) not in (int, float) or not math.isfinite(elapsed) or elapsed < 0):
            raise ValueError(f"invalid elapsed time for {theorem}")
        filename = hashlib.sha256(theorem.encode("utf-8")).hexdigest() + ".txt"
        if record.get("filename") != filename:
            raise ValueError(f"unexpected trace filename for {theorem}")
        trace = output / filename
        require_file(trace)
        text = trace.read_text(encoding="utf-8")
        if not text.strip():
            raise ValueError(f"empty success trace for {theorem}")
        traces.append({
            "theorem": theorem,
            "status": "success",
            "filename": filename,
            "bytes": trace.stat().st_size,
            "sha256": sha256(trace),
        })

    state = read_object(output / ".bounded-state.json")
    if (state.get("status") != "finished"
            or type(state.get("attempted_this_run")) is not int
            or type(state.get("queued_this_run")) is not int
            or state["attempted_this_run"] != len(FIXTURE_ROWS)
            or state["queued_this_run"] != len(FIXTURE_ROWS)):
        raise ValueError("bounded state must finish every fixture row in this run")
    if any(path.name.startswith(".pending-") for path in output.iterdir()):
        raise ValueError("uncommitted worker artifacts remain")
    return traces


def run(source: Path, project: Path, output: Path) -> int:
    source, project = source.resolve(), project.resolve()
    if output.is_symlink():
        raise ValueError("smoke output must be a fresh regular directory")
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("smoke output must be empty; use a new directory to exercise the worker")

    started = time.monotonic()
    supervisor = source / "script/atomize_mathlib_bounded.py"
    inventory = output / "fixture-inventory.tsv"
    command = [
        sys.executable, str(supervisor), str(inventory), str(output),
        "--project", str(project),
        "--worker", str(source / ".lake/build/bin/AtomizerWorker"),
        "--timeout-seconds", str(LIMITS["timeout_seconds"]),
        "--startup-timeout-seconds", str(LIMITS["startup_timeout_seconds"]),
        "--max-heartbeats", str(LIMITS["max_heartbeats"]),
        "--memory-gib", str(LIMITS["memory_gib"]),
        "--lean-workers", str(LIMITS["lean_workers"]),
        "--import-module", "Mathlib",
    ]
    report: dict[str, Any] = {
        "schema": 1,
        "status": "failed",
        "source": str(source),
        "project": str(project),
        "fixture_rows": len(FIXTURE_ROWS),
        "import_module": "Mathlib",
        "limits": dict(LIMITS),
        "command": command,
        "supervisor_log": "supervisor.log",
        "supervisor_exit_code": None,
        "success_rows": 0,
    }
    try:
        require_file(supervisor)
        environment = os.environ.copy()
        if not shutil.which("lake", path=environment.get("PATH")):
            raise ValueError("lake executable is not on PATH; run runtime setup first")
        if not environment.get("LEAN_PATH", "").strip():
            raise ValueError("LEAN_PATH must include the setup Nazrin and Mathlib libraries")
        environment["LEAN_TASK_MANAGER_WORKERS"] = str(LIMITS["lean_workers"])
        report["lean_path"] = environment["LEAN_PATH"]
        # Exclusive creation plus a fresh output directory prevents resume/skip.
        with inventory.open("xb") as handle:
            handle.write(FIXTURE)
            handle.flush()
            os.fsync(handle.fileno())
        manifest = expected_manifest(source, project, inventory)
        report["manifest"] = manifest
        with (output / "supervisor.log").open("wb") as log:
            completed = subprocess.run(
                command, cwd=project, env=environment,
                stdout=log, stderr=subprocess.STDOUT, check=False,
            )
        report["supervisor_exit_code"] = completed.returncode
        if completed.returncode != 0:
            raise ValueError(f"bounded supervisor exited with code {completed.returncode}")
        traces = validate_output(output, manifest)
        # Check inputs again to detect a changed worker/project during the run.
        if expected_manifest(source, project, inventory) != manifest or sha256(supervisor) != manifest["supervisor_sha256"]:
            raise ValueError("runtime inputs changed during the smoke test")
        report.update(status="passed", success_rows=len(traces), traces=traces)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        report["error"] = str(exc)
    report["elapsed_seconds"] = round(time.monotonic() - started, 3)
    report_path = output / "integration-report.json"
    write_json(report_path, report)
    print(f"runtime smoke {report['status']}: {report['success_rows']}/{len(FIXTURE_ROWS)} successes; report={report_path}")
    if "error" in report:
        print(report["error"], file=sys.stderr)
    return 0 if report["status"] == "passed" else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        return run(args.source, args.project, args.output)
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
