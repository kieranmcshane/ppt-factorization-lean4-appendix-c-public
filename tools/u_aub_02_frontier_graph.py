#!/usr/bin/env python3
"""Generate a Graphviz picture of the active U-AUB-02 frontier."""

from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "build" / "u_aub_02_frontier"


NODES = {
    "U-AUB-02": ("U-AUB-02\npublic Aubrun count closure", "open"),
    "U-AUB-154": ("U-AUB-154\none-sided plus-defect route", "open"),
    "endpoint": (
        "Current honest endpoint\nBiane + child internal branch + Chapuy",
        "checked",
    ),
    "large_left": ("Left large-gap Biane\n2 < c-a, c-a != 3", "open"),
    "large_right": ("Right large-gap Biane\noutside checked d-b=3 slice", "open"),
    "frontier": (
        "Residual branch frontiers\nfive side leaves + one child internal",
        "open",
    ),
    "confinement": (
        "Off-cycle block confinement\nstrictly inside return interval",
        "checked",
    ),
    "smaller_contour": (
        "Off-cycle smaller interval\nwith contour-repeat packet",
        "checked",
    ),
    "side_residual": (
        "Off-cycle smaller residual\nwith side data preserved",
        "checked",
    ),
    "child_split": (
        "Child residual split\nprimitive vs internal subinterval",
        "checked",
    ),
    "child_primitive_split": (
        "Child primitive split\nfive local branches",
        "checked",
    ),
    "child_primitive_absorb": (
        "Child primitive absorption\nstrict child primitive => parent primitive",
        "checked",
    ),
    "chapuy": ("Chapuy/trisection recurrence", "open"),
    "gap_two": ("Gap-two Biane links", "checked"),
    "gap_three": ("Finite gap-three slices", "checked"),
    "scalar": ("Shifted-base scalar absorption", "checked"),
    "rank": ("Aubrun rank/defect budget", "done"),
    "ncpart": ("NCPart cardinality/genus-zero base", "checked"),
}

EDGES = [
    ("rank", "endpoint"),
    ("scalar", "endpoint"),
    ("ncpart", "endpoint"),
    ("gap_two", "endpoint"),
    ("gap_three", "endpoint"),
    ("large_left", "endpoint"),
    ("large_right", "endpoint"),
    ("confinement", "smaller_contour"),
    ("smaller_contour", "side_residual"),
    ("side_residual", "child_split"),
    ("child_split", "child_primitive_split"),
    ("child_primitive_split", "child_primitive_absorb"),
    ("child_primitive_absorb", "frontier"),
    ("frontier", "endpoint"),
    ("chapuy", "endpoint"),
    ("endpoint", "U-AUB-154"),
    ("U-AUB-154", "U-AUB-02"),
]

COLORS = {
    "done": "#d7f5df",
    "checked": "#e8f0ff",
    "open": "#ffe6e6",
}


def dot_text() -> str:
    lines = [
        "digraph U_AUB_02 {",
        '  graph [rankdir=BT, bgcolor="white", pad="0.2"];',
        '  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=10];',
        '  edge [fontname="Helvetica", fontsize=9, color="#555555"];',
    ]
    for node, (label, status) in NODES.items():
        lines.append(
            f'  "{node}" [label="{label}", fillcolor="{COLORS[status]}", color="#666666"];'
        )
    for source, target in EDGES:
        lines.append(f'  "{source}" -> "{target}";')
    lines.append("}")
    return "\n".join(lines) + "\n"


def main() -> int:
    OUT.parent.mkdir(parents=True, exist_ok=True)
    dot_path = OUT.with_suffix(".dot")
    svg_path = OUT.with_suffix(".svg")
    png_path = OUT.with_suffix(".png")
    dot_path.write_text(dot_text(), encoding="utf-8")
    subprocess.run(["dot", "-Tsvg", str(dot_path), "-o", str(svg_path)], check=True)
    subprocess.run(["dot", "-Tpng", str(dot_path), "-o", str(png_path)], check=True)
    print(f"wrote {dot_path}")
    print(f"wrote {svg_path}")
    print(f"wrote {png_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
