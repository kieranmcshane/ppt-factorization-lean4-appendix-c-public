#!/usr/bin/env python3
"""Report the local scientific toolchain status for U-AUB-02.

The output deliberately avoids printing secrets.  It only says whether a key is
present and whether local helpers are reachable.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ZOTERO_HELPER = (
    Path.home()
    / ".codex/plugins/cache/openai-curated/zotero/3f0def1b/skills/zotero/scripts/zotero.py"
)

CHATTER_RE = re.compile(
    r"("
    r"noisy.*?(settings?|configuration|config|tool[\s_-]*logs?)"
    r"|(settings?|configuration|config|tool[\s_-]*logs?).*?(noise|noisy|chatter)"
    r"|"
    r"(local|project|workspace|user|global)[\s_-]*(settings?|setup|configuration|config|machine|shell|workspace)"
    r"|(settings?|configuration|config)\s*(file|path|source|profile)"
    r"|(settings?|configuration|config)\s*(loaded|read|found|applied|detected)"
    r"|(loaded|loading|read|reading|found|using|applying|applied|detected).*?(settings?|configuration|config)"
    r"|runtime[\s_-]*(settings?|configuration|environment|state)"
    r"|session[\s_-]*(metadata|registry|id)"
    r"|request[\s_-]*id"
    r"|tool[\s_-]*(logs?|output|telemetry|state|settings?)"
    r"|telemetry"
    r"|machine[\s_-]*(state|profile|preferences?)"
    r"|settings\.json"
    r"|config\.toml"
    r"|\.grok"
    r"|preferences?\s*(file|loaded|read|found|applied|detected)"
    r")",
    re.IGNORECASE,
)


def clean_tool_output(text: str) -> str:
    return "\n".join(
        line.strip()
        for line in text.splitlines()
        if line.strip() and not CHATTER_RE.search(line)
    )


def run(cmd: list[str], timeout: int = 8) -> tuple[bool, str]:
    try:
        proc = subprocess.run(
            cmd,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except Exception as exc:  # noqa: BLE001 - diagnostic script
        return False, str(exc)
    output = clean_tool_output(proc.stdout + "\n" + proc.stderr)
    return proc.returncode == 0, output


def first_line(text: str) -> str:
    return text.splitlines()[0] if text else ""


def command_status(name: str, version_cmd: list[str] | None = None) -> dict[str, str]:
    path = shutil.which(name)
    if path is None:
        return {"name": name, "state": "missing", "detail": "not on PATH"}
    if version_cmd is None:
        return {"name": name, "state": "ok", "detail": path}
    ok, out = run(version_cmd)
    detail = first_line(out) if out else path
    return {"name": name, "state": "ok" if ok else "warning", "detail": detail}


def narration_access_status() -> dict[str, str]:
    private_file = ROOT / ".env.local"
    present = False
    if private_file.exists():
        for line in private_file.read_text(encoding="utf-8", errors="ignore").splitlines():
            if line.startswith("OPENAI_API_KEY=") and line.partition("=")[2].strip():
                present = True
                break
    present = present or bool(os.environ.get("OPENAI_API_KEY"))
    return {
        "name": "Narration access",
        "state": "ok" if present else "missing",
        "detail": "available" if present else "not configured",
    }


def zotero_status() -> dict[str, str]:
    if not ZOTERO_HELPER.exists():
        return {"name": "Reference bridge", "state": "missing", "detail": "helper missing"}
    ok, out = run(["python3", str(ZOTERO_HELPER), "status", "--json"])
    if not ok:
        return {"name": "Reference bridge", "state": "warning", "detail": "not ready"}
    try:
        payload = json.loads(out)
    except json.JSONDecodeError:
        return {"name": "Reference bridge", "state": "warning", "detail": "not ready"}
    if payload.get("api_running") and payload.get("connector_running"):
        return {
            "name": "Reference bridge",
            "state": "ok",
            "detail": "ready",
        }
    return {
        "name": "Reference bridge",
        "state": "warning",
        "detail": "not ready",
    }


def blueprint_status() -> dict[str, str]:
    decls = ROOT / "blueprint/lean_decls"
    content = ROOT / "blueprint/src/content.tex"
    if decls.exists() and content.exists():
        return {
            "name": "leanblueprint project files",
            "state": "ok",
            "detail": "blueprint/lean_decls and blueprint/src/content.tex present",
        }
    return {"name": "leanblueprint project files", "state": "missing", "detail": "blueprint files incomplete"}


def blueprint_plastex_status() -> dict[str, str]:
    path = Path.home() / ".local/share/uv/tools/leanblueprint/bin/plastex"
    if path.exists():
        return {
            "name": "leanblueprint plasTeX runtime",
            "state": "ok",
            "detail": "available",
        }
    return {
        "name": "leanblueprint plasTeX runtime",
        "state": "missing",
        "detail": "run: uv tool install leanblueprint",
    }


def sage_gap_status() -> dict[str, str]:
    sage = shutil.which("sage")
    gap = shutil.which("gap")
    if sage:
        ok, out = run(["sage", "--version"], timeout=15)
        return {"name": "SageMath/GAP", "state": "ok", "detail": first_line(out) if ok else sage}
    if gap:
        ok, out = run(["gap", "-q", "-c", "Display(GAPInfo.Version); QUIT;"], timeout=15)
        return {"name": "SageMath/GAP", "state": "ok", "detail": first_line(out) if ok else gap}
    return {
        "name": "SageMath/GAP",
        "state": "manual",
        "detail": "optional finite-combinatorics backend not currently available",
    }


def main() -> int:
    rows = [
        command_status("python3", ["python3", "--version"]),
        command_status("lake", ["lake", "--version"]),
        sage_gap_status(),
        command_status("dot", ["dot", "-V"]),
        command_status("pandoc", ["pandoc", "--version"]),
        command_status("latexdiff", ["latexdiff", "--version"]),
        command_status("leanblueprint", ["leanblueprint", "--help"]),
        blueprint_plastex_status(),
        command_status("grok", ["grok", "--version"]),
        command_status("uvx", ["uvx", "--version"]),
        narration_access_status(),
        zotero_status(),
        blueprint_status(),
        {
            "name": "Narrate Lean wrapper",
            "state": "ok" if (ROOT / "scripts/narratelean_with_env.sh").exists() else "missing",
            "detail": "scripts/narratelean_with_env.sh",
        },
    ]

    print("Scientific toolchain status for U-AUB-02")
    print("=" * 45)
    for row in rows:
        print(f"{row['state']:>7}  {row['name']:<30} {row['detail']}")

    hard_missing = [
        row["name"]
        for row in rows
        if row["state"] == "missing" and row["name"] not in {"SageMath/GAP"}
    ]
    if hard_missing:
        print("\nMissing required tools: " + ", ".join(hard_missing), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
