#!/usr/bin/env python3
"""Summarize fixed-bridge hit-count CSV files."""

from __future__ import annotations

import argparse
import csv
import statistics
from collections import defaultdict
from pathlib import Path


def summarize(path: Path) -> list[dict[str, object]]:
    rows = list(csv.DictReader(path.open(newline="")))
    by_target: dict[tuple[str, str, str, str], list[int]] = defaultdict(list)
    for row in rows:
        target = row["target_t"], row["target_g"], row["target_p"], row["target_q"]
        by_target[target].append(int(row["hit_count"]))
    out: list[dict[str, object]] = []
    for target, hits in sorted(by_target.items()):
        positive = [hit for hit in hits if hit > 0]
        out.append(
            {
                "file": path.name,
                "target_t": target[0],
                "target_g": target[1],
                "target_p": target[2],
                "target_q": target[3],
                "source_rows": len(hits),
                "positive_source_rows": len(positive),
                "total_hits": sum(hits),
                "min_hits": min(hits),
                "median_hits": statistics.median(hits),
                "max_hits": max(hits),
                "hit_counts": ";".join(str(hit) for hit in hits),
            }
        )
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("hit_count_csv", type=Path, nargs="+")
    args = parser.parse_args()

    fieldnames = [
        "file",
        "target_t",
        "target_g",
        "target_p",
        "target_q",
        "source_rows",
        "positive_source_rows",
        "total_hits",
        "min_hits",
        "median_hits",
        "max_hits",
        "hit_counts",
    ]
    writer = csv.DictWriter(__import__("sys").stdout, fieldnames=fieldnames, lineterminator="\n")
    writer.writeheader()
    for path in args.hit_count_csv:
        for row in summarize(path):
            writer.writerow(row)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
