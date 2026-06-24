#!/usr/bin/env python3
"""Keep reviewer artifacts mathematical and reader-facing.

This filter is intentionally conservative: any paragraph that talks about the
review runner, settings, credentials, session metadata, or transport details is
removed before the review is kept as a project artifact.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


NOISE_RE = re.compile(
    r"("
    r"noisy.*?(settings?|configuration|config|tool[\s_-]*logs?)"
    r"|(settings?|configuration|config|tool[\s_-]*logs?).*?(noise|noisy|chatter)"
    r"|"
    r"(local|project|workspace|user|global)[\s_-]*(settings?|setup|configuration|config|machine|shell|workspace)"
    r"|(settings?|configuration|config)\s*(file|path|source|profile)"
    r"|(settings?|configuration|config)\s*(loaded|read|found|applied|detected)"
    r"|(loaded|loading|read|reading|found|using|applying|applied|detected).*?(settings?|configuration|config)"
    r"|(cannot|can.?t|unable to|no access to).*?(inspect|access|read|see).*?(settings?|configuration|config|tool[\s_-]*logs?|stderr|stdout|runtime|environment)"
    r"|(inspect|access|read|see).*?(settings?|configuration|config|tool[\s_-]*logs?|stderr|stdout|runtime|environment).*?(cannot|can.?t|unable to|no access to)"
    r"|local[\s_-]*(runtime|environment|installation|paths?|tooling)"
    r"|runtime[\s_-]*(settings?|configuration|state|details?)"
    r"|session[\s_-]*(metadata|registry|id)"
    r"|request[\s_-]*id"
    r"|stop[\s_-]*reason"
    r"|hidden[\s_-]*tools?"
    r"|tool[\s_-]*(logs?|output|telemetry|state|settings?)"
    r"|reviewer[\s_-]*(tool|transport|settings?|logs?)"
    r"|execution[\s_-]*(settings?|logs?|transport)"
    r"|transport[\s_-]*(layer|logs?|metadata|envelope|object)"
    r"|telemetry"
    r"|machine[\s_-]*specific"
    r"|machine[\s_-]*(state|profile|preferences?)"
    r"|credentials?"
    r"|api[\s_-]*keys?"
    r"|openai_api_key"
    r"|insufficient_quota"
    r"|quota"
    r"|gcloud"
    r"|zotero[\s_-]*local[\s_-]*api"
    r"|grok[\s_-]*cli"
    r"|xai[\s_-]*cli"
    r"|settings\.json"
    r"|config\.toml"
    r"|(?<![A-Za-z0-9_])\.env(?![A-Za-z0-9_])"
    r"|\.grok"
    r"|preferences?\s*(file|loaded|read|found|applied|detected)"
    r"|cli[\s_-]*run"
    r"|diagnostic[\s_-]*field"
    r"|bounded[\s_-]*turn[\s_-]*cap"
    r"|no[\s_-]*repo[\s_-]*access[\s_-]*wrapper"
    r"|temporary[\s_-]*review[\s_-]*inputs?"
    r"|raw[\s_-]*review"
    r"|scratch[\s_-]*files?"
    r"|private[\s_-]*diagnostic"
    r"|runner[\s_-]*(notes?|chatter|metadata)"
    r"|review[\s_-]*(runner|wrapper)"
    r"|stderr"
    r"|stdout"
    r"|how\s+(this|the)\s+review\s+was\s+(run|sent|transmitted|configured|logged)"
    r"|project[\s_-]*instructions?"
    r"|user[\s_-]*instructions?"
    r"|personal[\s_-]*memory"
    r"|shared[\s_-]*memory"
    r"|mcp[\s_-]*(server|tool|tools)"
    r"|permission[\s_-]*mode"
    r"|sandbox[\s_-]*(profile|mode)"
    r")",
    re.IGNORECASE,
)


def split_blocks(text: str) -> list[str]:
    return re.split(r"\n{2,}", text.strip())


def sanitize(text: str) -> str:
    kept: list[str] = []
    for block in split_blocks(text):
        if not block.strip():
            continue
        if NOISE_RE.search(block):
            continue
        kept.append(block.strip())
    return "\n\n".join(kept).strip() + ("\n" if kept else "")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path, nargs="?")
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="fail if the input is not already reader-facing",
    )
    args = parser.parse_args()

    raw = args.input.read_text(encoding="utf-8", errors="ignore")
    if args.check_only:
        if NOISE_RE.search(raw):
            raise SystemExit(f"{args.input} contains non-mathematical reviewer chatter")
        return 0

    if args.output is None:
        raise SystemExit("output path is required unless --check-only is used")

    clean = sanitize(raw)
    if not clean:
        raise SystemExit("reviewer output contained no reader-facing mathematical content")
    if NOISE_RE.search(clean):
        raise SystemExit("sanitized reviewer output still contains runner chatter")
    args.output.write_text(clean, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
