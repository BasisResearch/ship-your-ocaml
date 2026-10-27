#!/usr/bin/env python3
"""Stop a failed or memory-heavy worker build without losing the worker.

Run an already capped command, e.g. scripts/lean-capped.sh lake env lean ... .
The 10 GiB early stop is enabled only inside an inherited <=12 GiB cgroup.
"""
import argparse
import os
from pathlib import Path
import re
import signal
import subprocess
import time


def worker_memory_file():
    if os.environ.get("SYO_LEAN_CAPPED") != "1":
        return None
    for line in Path("/proc/self/cgroup").read_text().splitlines():
        if line.startswith("0::"):
            group = Path("/sys/fs/cgroup") / line[3:].lstrip("/")
            try:
                limit = int((group / "memory.max").read_text())
                if limit <= 12 * 1024**3:
                    return group / "memory.current"
            except (OSError, ValueError):
                pass
    return None


def stop_group(process):
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            break
        if sig == signal.SIGTERM:
            time.sleep(1)
    process.wait()


def interrupted(_signum, _frame):
    raise KeyboardInterrupt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a capped command is required")
    memory = worker_memory_file()
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    with open(args.log, "w") as output, open(args.log, errors="replace") as reader:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        aborted = False
        try:
            pending = ""
            while process.poll() is None:
                pending += reader.read()
                lines = pending.split("\n")
                pending = lines.pop()
                failure = any(re.match(r"(?:error:|✖|.+:\d+:\d+: error:)", line)
                              for line in lines)
                pressure = memory is not None and int(memory.read_text()) >= 10 * 1024**3
                if failure or pressure:
                    aborted = True
                    reason = "reported build error" if failure else "worker cgroup reached 10 GiB"
                    print(f"guard: stopping this build: {reason}", flush=True)
                    stop_group(process)
                    return 1
                time.sleep(0.25)
            return process.returncode
        except KeyboardInterrupt:
            aborted = True
            stop_group(process)
            return 130
        finally:
            if not aborted and process.poll() is None:
                stop_group(process)


if __name__ == "__main__":
    raise SystemExit(main())
