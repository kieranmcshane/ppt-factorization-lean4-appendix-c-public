#!/usr/bin/env python3

from __future__ import annotations

import json
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
OUTPUT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else TOOLS / "appendix_b_progress.json"
CACHE = TOOLS / "appendix_b_progress_cache.json"

HIGH_PROB = ROOT / "PptFactorization" / "HighProbabilityBounds.lean"
CONCRETE_BRIDGE = ROOT / "PptFactorization" / "AppendixBConcreteBridge.lean"
LEVY_BRIDGE = ROOT / "PptFactorization" / "AppendixBLevyPolarBridge.lean"
RADIAL = ROOT / "PptFactorization" / "AppendixBRadialSpherical.lean"
AUBRUN = ROOT / "PptFactorization" / "AppendixBAubrunGraduate.lean"
FINAL = ROOT / "PptFactorization" / "AppendixBFinal.lean"

TRACKED_FILES = sorted((ROOT / "PptFactorization").glob("AppendixB*.lean")) + [HIGH_PROB]
TEXTS = {path: path.read_text(encoding="utf-8").splitlines() for path in {HIGH_PROB, CONCRETE_BRIDGE, LEVY_BRIDGE, RADIAL, AUBRUN}}


def first_match(path: Path, pattern: str) -> tuple[int, str] | None:
    regex = re.compile(pattern)
    for line_no, line in enumerate(TEXTS[path], start=1):
        if regex.search(line):
            return line_no, line.strip()
    return None


def evidence(path: Path, match: tuple[int, str] | None, *, missing: str) -> str:
    if match is None:
        return missing
    line_no, line = match
    return f"{path.name}:{line_no} - {line}"


def theorem_item(path: Path, name: str, label: str) -> dict[str, object]:
    match = first_match(path, rf"^\s*theorem\s+{re.escape(name)}\b")
    return {
        "label": label,
        "checked": match is not None,
        "evidence": evidence(path, match, missing=f"{path.name} has no theorem named {name}."),
    }


def def_item(path: Path, name: str, label: str) -> dict[str, object]:
    match = first_match(path, rf"^\s*(?:noncomputable\s+)?def\s+{re.escape(name)}\b")
    return {
        "label": label,
        "checked": match is not None,
        "evidence": evidence(path, match, missing=f"{path.name} has no definition named {name}."),
    }


def blocked_by_definition(path: Path, pattern: str, label: str, cleared_note: str) -> dict[str, object]:
    match = first_match(path, pattern)
    return {
        "label": label,
        "checked": match is None,
        "evidence": cleared_note if match is None else evidence(path, match, missing=cleared_note),
    }


def no_placeholder_item() -> dict[str, object]:
    for path in TRACKED_FILES:
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            stripped = line.strip()
            if "axiom-free" in stripped:
                continue
            if re.search(r"\bsorry\b", line):
                return {
                    "label": "No `sorry`, `admit`, or standalone `axiom` remains in Appendix B or HighProbabilityBounds.",
                    "checked": False,
                    "evidence": f"{path.name}:{line_no} - {stripped}",
                }
            if re.search(r"\badmit\b", line):
                return {
                    "label": "No `sorry`, `admit`, or standalone `axiom` remains in Appendix B or HighProbabilityBounds.",
                    "checked": False,
                    "evidence": f"{path.name}:{line_no} - {stripped}",
                }
            if re.match(r"^\s*axiom\b", line):
                return {
                    "label": "No `sorry`, `admit`, or standalone `axiom` remains in Appendix B or HighProbabilityBounds.",
                    "checked": False,
                    "evidence": f"{path.name}:{line_no} - {stripped}",
                }
    return {
        "label": "No `sorry`, `admit`, or standalone `axiom` remains in Appendix B or HighProbabilityBounds.",
        "checked": True,
        "evidence": f"Scanned {len(TRACKED_FILES)} tracked Lean files with no placeholders found.",
    }


def load_cache() -> dict[str, object]:
    if not CACHE.exists():
        return {}
    try:
        return json.loads(CACHE.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def save_cache(payload: dict[str, object]) -> None:
    CACHE.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def compile_item() -> dict[str, object]:
    build_stamp = max(path.stat().st_mtime_ns for path in TRACKED_FILES)
    cache = load_cache()
    cached = cache.get("appendix_b_final_compile")
    if cache.get("build_stamp") == build_stamp and isinstance(cached, dict):
        return cached

    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "PptFactorization/AppendixBFinal.lean"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=900,
            check=False,
        )
        output = "\n".join(
            line.strip()
            for line in (proc.stdout + "\n" + proc.stderr).splitlines()
            if line.strip()
        )
        if proc.returncode == 0:
            result = {
                "label": "`PptFactorization/AppendixBFinal.lean` compiles.",
                "checked": True,
                "evidence": f"Direct build check passed for AppendixBFinal.lean at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}.",
            }
        else:
            snippet = output.splitlines()[0] if output else "build failed with no diagnostic text"
            result = {
                "label": "`PptFactorization/AppendixBFinal.lean` compiles.",
                "checked": False,
                "evidence": f"Build failed: {snippet}",
            }
    except subprocess.TimeoutExpired:
        result = {
            "label": "`PptFactorization/AppendixBFinal.lean` compiles.",
            "checked": False,
            "evidence": "Build check timed out after 900 seconds.",
        }

    save_cache({"build_stamp": build_stamp, "appendix_b_final_compile": result})
    return result


sections = [
    {
        "name": "Build Health",
        "items": [
            no_placeholder_item(),
            compile_item(),
        ],
    },
    {
        "name": "Closed Packages",
        "items": [
            theorem_item(
                HIGH_PROB,
                "GaussianQuadraticFormBernsteinStatement_of_estimate",
                "`GaussianQuadraticFormBernsteinStatement_of_estimate` is a theorem.",
            ),
            theorem_item(
                HIGH_PROB,
                "ConcreteHighProbabilityBoundsStatement",
                "`ConcreteHighProbabilityBoundsStatement` is a theorem.",
            ),
            theorem_item(
                HIGH_PROB,
                "ConcreteHighProbabilityBoundsExplicit",
                "`ConcreteHighProbabilityBoundsExplicit` is a theorem.",
            ),
            def_item(
                CONCRETE_BRIDGE,
                "concreteRemainingExpectationInputs",
                "`concreteRemainingExpectationInputs` exists as the concrete no-input package.",
            ),
            theorem_item(
                CONCRETE_BRIDGE,
                "concreteRemainingExpectationInputs_to_normalized_bounds",
                "`concreteRemainingExpectationInputs_to_normalized_bounds` is a theorem.",
            ),
            theorem_item(
                AUBRUN,
                "aubrunLemma36_card_le_k_pow_three_mul",
                "`aubrunLemma36_card_le_k_pow_three_mul` is a theorem.",
            ),
            theorem_item(
                AUBRUN,
                "aubrunLemma74_fixedDefectClassCount_le",
                "`aubrunLemma74_fixedDefectClassCount_le` is a theorem.",
            ),
            theorem_item(
                AUBRUN,
                "aubrunLemma75_relationCounting_of_profileCountSumBound",
                "`aubrunLemma75_relationCounting_of_profileCountSumBound` is a theorem.",
            ),
        ],
    },
    {
        "name": "Remaining Blockers",
        "items": [
            blocked_by_definition(
                AUBRUN,
                r"^\s*def\s+AubrunGraduateRelationCounting\b",
                "`AubrunGraduateRelationCounting` is no longer a `def ... : Prop` placeholder.",
                "The old `def AubrunGraduateRelationCounting ... : Prop` line is gone.",
            ),
            theorem_item(
                LEVY_BRIDGE,
                "polarLaw",
                "A top-level theorem `polarLaw` exists in `AppendixBLevyPolarBridge.lean`.",
            ),
            theorem_item(
                LEVY_BRIDGE,
                "gaussianRadius_indep_gaussianDirection",
                "A concrete radius-direction independence theorem exists.",
            ),
            blocked_by_definition(
                LEVY_BRIDGE,
                r"^\s*def\s+StrongGlobalSurfaceSubtypeLevy\b",
                "`StrongGlobalSurfaceSubtypeLevy` is no longer just a `def ... : Prop` input.",
                "The old `def StrongGlobalSurfaceSubtypeLevy ... : Prop` line is gone.",
            ),
        ],
    },
]

completed = sum(1 for section in sections for item in section["items"] if item["checked"])
total = sum(len(section["items"]) for section in sections)
open_items = [item["label"] for section in sections for item in section["items"] if not item["checked"]]

payload = {
    "title": "Appendix B Checklist",
    "subtitle": "Objective criteria only: theorem names, remaining input wrappers, and a direct build check.",
    "updated": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    "completed": completed,
    "total": total,
    "sections": sections,
    "openItems": open_items,
}

OUTPUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
