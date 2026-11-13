"""Standard-library client for the Nazrin NPA REPL (Standalone/NPARepl.lean).

The REPL is deliberately a separate process: Lean keeps the imported
environment and the live `GoalState`, while Python only exchanges one-line
JSON messages.  This module has no third-party dependencies.

Typical use::

    with ReplClient(module="Init") as client:
        reply = client.start_theorem("Nat.add_zero")
        reply = client.apply(reply["goals"][0]["id"], "intro n; rfl")
        assert reply["solved"]
"""

from __future__ import annotations

import json
import os
import queue
import shutil
import subprocess
import threading
import time
from collections import deque
from pathlib import Path
from typing import Any, Deque, Dict, List, Optional, Sequence

PROTOCOL_PREFIX = "NAZRIN_NPA "
REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_REPL_FILE = REPO_ROOT / "Standalone" / "NPARepl.lean"


class ReplError(RuntimeError):
    """Base class for REPL transport and protocol failures."""


class ReplTimeout(ReplError):
    """Raised when the REPL does not answer before the deadline."""


class ReplProtocolError(ReplError):
    """Raised when a protocol line is not valid JSON or has an invalid shape."""


def find_lake() -> str:
    """Locate `lake`, including the common elan installation path.

    The test environment may not put `~/.elan/bin` on PATH, so checking the
    default elan location keeps the tests runnable from a plain shell.
    """

    override = os.environ.get("LAKE")
    if override:
        return override
    found = shutil.which("lake")
    if found:
        return found
    candidates = [
        Path.home() / ".elan" / "bin" / "lake",
        Path("/home/felian/.elan/bin/lake"),
        Path("/root/.elan/bin/lake"),
    ]
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate)
    raise ReplError(
        "could not find `lake`; put it on PATH, set LAKE, or pass lean_cmd=[...]"
    )


class ReplClient:
    """Manages one `Standalone/NPARepl.lean` subprocess.

    Parameters
    ----------
    module:
        Lean module to import, usually ``"Init"`` for tests or ``"Mathlib"``
        in a project that has Mathlib available.
    max_heartbeats:
        Passed to the REPL as the optional second command-line argument.
    timeout:
        Default seconds to wait for a response (or for the initial `ready`
        line).  A timeout kills the subprocess and raises `ReplTimeout`.
    lean_cmd:
        Optional command prefix overriding the default
        ``[lake, "env", "lean", "--run", Standalone/NPARepl.lean]``.
    cwd:
        Working directory for the subprocess; defaults to the repository root.
    """

    def __init__(
        self,
        module: str = "Init",
        max_heartbeats: int = 200_000,
        timeout: float = 60.0,
        lean_cmd: Optional[Sequence[str]] = None,
        cwd: Optional[os.PathLike[str] | str] = None,
    ) -> None:
        self.module = module
        self.max_heartbeats = int(max_heartbeats)
        self.timeout = float(timeout)
        self.cwd = Path(cwd) if cwd is not None else REPO_ROOT
        if lean_cmd is None:
            self.lean_cmd: List[str] = [
                find_lake(),
                "env",
                "lean",
                "--run",
                str(DEFAULT_REPL_FILE),
            ]
        else:
            self.lean_cmd = list(lean_cmd)

        self._process: Optional[subprocess.Popen[str]] = None
        self._stdout_queue: "queue.Queue[Any]" = queue.Queue()
        self._stderr_lines: Deque[str] = deque(maxlen=200)
        self._stdout_extra: Deque[str] = deque(maxlen=100)
        self._stdout_thread: Optional[threading.Thread] = None
        self._stderr_thread: Optional[threading.Thread] = None
        self._ready_response: Optional[Dict[str, Any]] = None

    # ------------------------------------------------------------------
    # Process lifecycle
    # ------------------------------------------------------------------
    @property
    def process(self) -> Optional[subprocess.Popen[str]]:
        return self._process

    def is_running(self) -> bool:
        return self._process is not None and self._process.poll() is None

    def start(self) -> Dict[str, Any]:
        """Start Lean and wait until it has imported the requested module."""

        if self.is_running():
            raise ReplError("REPL is already running")
        if self._process is not None:
            # Clean up a process that exited on its own since the last call.
            self._terminate_process()
        command = self.lean_cmd + [self.module, str(self.max_heartbeats)]
        try:
            self._process = subprocess.Popen(
                command,
                cwd=str(self.cwd),
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding="utf-8",
                errors="replace",
                bufsize=1,
            )
        except OSError as exc:
            raise ReplError(f"could not start REPL: {exc}") from exc

        self._stdout_queue = queue.Queue()
        self._stderr_lines.clear()
        self._stdout_extra.clear()
        self._stdout_thread = threading.Thread(
            target=self._read_stdout,
            name="npa-repl-stdout",
            daemon=True,
        )
        self._stderr_thread = threading.Thread(
            target=self._read_stderr,
            name="npa-repl-stderr",
            daemon=True,
        )
        self._stdout_thread.start()
        self._stderr_thread.start()

        try:
            ready = self._wait_for_response(self.timeout)
        except Exception:
            self._terminate_process()
            raise
        if not ready.get("ready"):
            self._terminate_process()
            raise ReplProtocolError(f"REPL did not report ready: {ready!r}")
        self._ready_response = ready
        return ready

    def close(self, timeout: float = 10.0) -> None:
        """Send `close`, wait for exit, and release all process resources.

        Safe to call more than once.  A dead or missing process is treated as
        already closed.
        """

        process = self._process
        if process is None:
            return
        if process.poll() is None:
            try:
                self._send({"cmd": "close"}, timeout=min(timeout, self.timeout))
            except ReplError:
                pass
            try:
                if process.stdin is not None:
                    process.stdin.close()
            except OSError:
                pass
            try:
                process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                self._terminate_process()
        self._join_threads()
        self._close_streams(process)
        self._process = None

    def _close_streams(self, process: subprocess.Popen[str]) -> None:
        for stream in (process.stdin, process.stdout, process.stderr):
            if stream is None:
                continue
            try:
                stream.close()
            except OSError:
                pass

    def _terminate_process(self) -> None:
        process = self._process
        if process is None:
            return
        if process.poll() is None:
            process.kill()
        try:
            process.wait(timeout=5.0)
        except subprocess.TimeoutExpired:
            pass
        self._join_threads()
        self._close_streams(process)
        self._process = None

    def _join_threads(self, timeout: float = 2.0) -> None:
        for thread in (self._stdout_thread, self._stderr_thread):
            if thread is not None and thread.is_alive():
                thread.join(timeout=timeout)

    def __enter__(self) -> "ReplClient":
        self.start()
        return self

    def __exit__(self, exc_type: Any, exc: Any, tb: Any) -> None:
        self.close()

    # ------------------------------------------------------------------
    # Command API
    # ------------------------------------------------------------------
    def start_theorem(self, name: str) -> Dict[str, Any]:
        """Start a fresh proof from the type of theorem `name`."""

        response = self._send({"cmd": "start", "theorem": name})
        if response.get("status") != "ok":
            raise ReplError(
                f"start failed for {name!r}: "
                f"{response.get('kind', 'error')}: {response.get('message', response)}"
            )
        return response

    def apply(self, goal_id: int | str, tactic: str) -> Dict[str, Any]:
        """Run one string tactic on `goal_id`.

        Tactic failures are returned as ``{"status": "error", ...}`` instead of
        raising, so a caller can inspect `kind` and `message` and continue using
        the same proof state.
        """

        return self._send({"cmd": "apply", "goal": goal_id, "tactic": tactic})

    def goals(self) -> Dict[str, Any]:
        """Return the current goal list."""

        return self._send({"cmd": "goals"})

    def snapshot(self, name: str) -> Dict[str, Any]:
        """Save the current proof branch under `name`."""

        return self._send({"cmd": "snapshot", "name": name})

    def restore(self, name: str) -> Dict[str, Any]:
        """Restore a previously saved proof branch."""

        return self._send({"cmd": "restore", "name": name})

    # ------------------------------------------------------------------
    # Transport
    # ------------------------------------------------------------------
    def _send(
        self, request: Dict[str, Any], timeout: Optional[float] = None
    ) -> Dict[str, Any]:
        process = self._process
        if process is None or process.poll() is not None:
            raise ReplError(
                "REPL is not running"
                + (f"; stderr:\n{self.stderr_text()}" if self._stderr_lines else "")
            )
        if process.stdin is None:
            raise ReplError("REPL stdin is unavailable")
        line = json.dumps(request, ensure_ascii=False, separators=(",", ":"))
        try:
            process.stdin.write(line + "\n")
            process.stdin.flush()
        except (BrokenPipeError, OSError) as exc:
            raise ReplError(
                f"could not write to REPL: {exc}; stderr:\n{self.stderr_text()}"
            ) from exc
        return self._wait_for_response(self.timeout if timeout is None else timeout)

    def _wait_for_response(self, timeout: float) -> Dict[str, Any]:
        deadline = time.monotonic() + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                self._terminate_process()
                raise ReplTimeout(
                    f"REPL did not respond within {timeout:.1f}s; "
                    f"stderr:\n{self.stderr_text()}"
                )
            try:
                item = self._stdout_queue.get(timeout=remaining)
            except queue.Empty:
                self._terminate_process()
                raise ReplTimeout(
                    f"REPL did not respond within {timeout:.1f}s; "
                    f"stderr:\n{self.stderr_text()}"
                ) from None
            if item is None:
                self._terminate_process()
                raise ReplError(
                    "REPL process exited unexpectedly; "
                    f"stderr:\n{self.stderr_text()}"
                )
            kind, payload = item
            if kind == "json":
                return payload
            if kind == "protocol_error":
                raise ReplProtocolError(
                    f"invalid protocol output: {payload!r}; stderr:\n{self.stderr_text()}"
                )

    def _read_stdout(self) -> None:
        process = self._process
        assert process is not None and process.stdout is not None
        try:
            for line in process.stdout:
                line = line.rstrip("\n")
                if line.startswith(PROTOCOL_PREFIX):
                    raw = line[len(PROTOCOL_PREFIX) :]
                    try:
                        payload = json.loads(raw)
                    except json.JSONDecodeError as exc:
                        self._stdout_queue.put(("protocol_error", line))
                        continue
                    if isinstance(payload, dict):
                        self._stdout_queue.put(("json", payload))
                    else:
                        self._stdout_queue.put(("protocol_error", line))
                elif line.strip():
                    self._stdout_extra.append(line)
        finally:
            self._stdout_queue.put(None)

    def _read_stderr(self) -> None:
        process = self._process
        assert process is not None and process.stderr is not None
        for line in process.stderr:
            self._stderr_lines.append(line.rstrip("\n"))

    # ------------------------------------------------------------------
    # Diagnostics
    # ------------------------------------------------------------------
    def stderr_text(self) -> str:
        return "\n".join(self._stderr_lines)

    def stdout_text(self) -> str:
        return "\n".join(self._stdout_extra)

    def ready_response(self) -> Optional[Dict[str, Any]]:
        return self._ready_response

    def __del__(self) -> None:  # pragma: no cover - best-effort cleanup
        try:
            self.close(timeout=1.0)
        except Exception:
            pass
