#!/usr/bin/env python3
"""Reject local execution chatter in reader-facing review/status artifacts."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


DEFAULT_PATHS = [
    Path("TICKET_LEDGER.md"),
    Path("FORMALIZATION_BOARD.md"),
    Path("tools/SCIENTIFIC_TOOLCHAIN.md"),
    Path("exposition/formalization_workflow.md"),
    Path("exposition/u_aub_02_formalization_note.md"),
    Path("exposition/u_aub_02_grok_workflow_review.md"),
    Path("article/publishable_pure_math_2026_06_08/grok_formalization_workflow_review.md"),
    Path("article/publishable_pure_math_2026_06_08/grok_referee_report.md"),
    Path("article/publishable_pure_math_2026_06_08/grok_referee_response.md"),
    Path("article/from_scratch_u_aub_02/grok_referee_report.md"),
    Path("article/from_scratch_u_aub_02/grok_referee_response.md"),
    Path("build/grok_u_aub_02_review.md"),
]


CHATTER_RE = re.compile(
    r"("
    r"noisy.*?(settings?|configuration|config|tool[\s_-]*logs?)"
    r"|(settings?|configuration|config|tool[\s_-]*logs?).*?(noise|noisy|chatter)"
    r"|"
    r"local[\s_-]*(settings?|setup|machine|shell|runtime|environment|installation|paths?|tooling)"
    r"|(settings?|configuration|config)\s*(file|path|source|profile)"
    r"|(settings?|configuration|config)\s*(loaded|read|found|applied|detected)"
    r"|(loaded|loading|read|reading|found|using|applying|applied|detected).*?(settings?|configuration|config)"
    r"|(cannot|can.?t|unable to|no access to).*?(inspect|access|read|see).*?(settings?|configuration|config|tool[\s_-]*logs?|stderr|stdout|runtime|environment)"
    r"|(inspect|access|read|see).*?(settings?|configuration|config|tool[\s_-]*logs?|stderr|stdout|runtime|environment).*?(cannot|can.?t|unable to|no access to)"
    r"|tool[\s_-]*(logs?|telemetry|settings?)"
    r"|session[\s_-]*(metadata|registry|id)"
    r"|request[\s_-]*id"
    r"|telemetry"
    r"|machine[\s_-]*(state|profile|preferences?)"
    r"|credentials?"
    r"|api[\s_-]*keys?"
    r"|openai_api_key"
    r"|gcloud"
    r"|application[\s_-]*default[\s_-]*credentials?"
    r"|settings\.json"
    r"|config\.toml"
    r"|(?<![A-Za-z0-9_])\.env(?![A-Za-z0-9_])"
    r"|\.grok"
    r"|preferences?\s*(file|loaded|read|found|applied|detected)"
    r"|cli[\s_-]*run"
    r"|diagnostic[\s_-]*field"
    r"|bounded[\s_-]*turn[\s_-]*cap"
    r"|no[\s_-]*repo[\s_-]*access[\s_-]*wrapper"
    r"|quarantine"
    r"|temporary[\s_-]*review[\s_-]*inputs?"
    r"|raw[\s_-]*review"
    r"|scratch[\s_-]*files?"
    r"|private[\s_-]*diagnostic"
    r"|runner[\s_-]*(notes?|chatter|metadata)"
    r"|review[\s_-]*(runner|wrapper)"
    r"|stderr"
    r"|stdout"
    r"|how\s+(this|the)\s+review\s+was\s+(run|sent|transmitted|configured|logged)"
    r")",
    re.IGNORECASE,
)


def line_hits(path: Path) -> list[tuple[int, str]]:
    text = path.read_text(encoding="utf-8", errors="ignore")
    hits: list[tuple[int, str]] = []
    for idx, line in enumerate(text.splitlines(), start=1):
        if CHATTER_RE.search(line):
            hits.append((idx, line.strip()))
    return hits


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help="reader-facing files to check; defaults to the U-AUB review/status set",
    )
    args = parser.parse_args()

    paths = args.paths or DEFAULT_PATHS
    failures: list[str] = []
    for path in paths:
        if not path.exists():
            continue
        for line_no, line in line_hits(path):
            failures.append(f"{path}:{line_no}: {line}")

    if failures:
        print("reader-facing artifacts contain local execution chatter:")
        for failure in failures:
            print(failure)
        return 1
    print("reader-facing review/status artifacts are clean")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
