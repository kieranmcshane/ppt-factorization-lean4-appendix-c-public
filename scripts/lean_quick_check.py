#!/usr/bin/env python3
"""Run a bounded Lean/Lake check for one targeted module.

This is intentionally small: the normal proof loop should check the module that
just changed, not the whole `PptFactorization` root target.
"""

from __future__ import annotations

import argparse
import os
import signal
import subprocess
import sys
from pathlib import Path


def run_bounded(cmd: list[str], timeout: int) -> int:
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        start_new_session=True,
    )
    try:
        out, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            out, _ = proc.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            out, _ = proc.communicate()
        print(f"Lean check timed out after {timeout}s: {' '.join(cmd)}")
        if out:
            print("\nLast output:")
            print("".join(out.splitlines(keepends=True)[-80:]), end="")
        return 124
    else:
        if proc.returncode != 0 and out:
            print("".join(out.splitlines(keepends=True)[-120:]), end="")
        return proc.returncode or 0
    finally:
        if proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
            proc.wait()


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Bounded proof-loop check for one Lean module."
    )
    parser.add_argument("module", help="Lean module target, e.g. PptFactorization.Foo")
    parser.add_argument("--timeout", type=int, default=360)
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    os.chdir(root)
    return run_bounded(["lake", "build", args.module], args.timeout)


if __name__ == "__main__":
    sys.exit(main())
