#!/usr/bin/env python3
from __future__ import annotations

import json
import re
from collections import defaultdict
from pathlib import Path


DECL_RE = re.compile(r"^(theorem|lemma|def|structure|abbrev|class|instance)\s+([A-Za-z0-9_'.]+)", re.M)
TEX_BLOCK_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|definition|corollary|remark|example)\}"
)


def load_manifest(root: Path) -> dict:
    manifest_path = root / "tools" / "appendix_b_textbook_audit_manifest.json"
    return json.loads(manifest_path.read_text())


def file_stem(relpath: str) -> str:
    return Path(relpath).stem


def find_anchor(scope_texts: dict[str, str], anchor: str) -> list[str]:
    hits = []
    pat = re.compile(rf"^(theorem|lemma|def|structure|abbrev|class|instance)\s+{re.escape(anchor)}\b", re.M)
    for relpath, text in scope_texts.items():
        if pat.search(text):
            hits.append(relpath)
    return hits


def count_declarations(scope_texts: dict[str, str]) -> tuple[int, dict[str, int]]:
    per_file = {}
    total = 0
    for relpath, text in scope_texts.items():
        n = len(DECL_RE.findall(text))
        per_file[relpath] = n
        total += n
    return total, per_file


def build_report(root: Path) -> dict:
    manifest = load_manifest(root)
    tex_path = root / manifest["textbook_tex"]
    pdf_path = root / manifest["textbook_pdf"]
    tex = tex_path.read_text()

    scope_files = manifest["scope_files"]
    scope_texts = {relpath: (root / relpath).read_text() for relpath in scope_files}

    total_formal_decls, per_file_decls = count_declarations(scope_texts)
    textbook_statement_blocks = len(TEX_BLOCK_RE.findall(tex))
    textbook_chapters = re.findall(r"\\chapter\{([^}]+)\}", tex)

    chapter_results = []
    covered_files = set()
    for chapter in manifest["chapters"]:
        missing_files = [rel for rel in chapter["files"] if rel not in scope_texts]
        covered_files.update(chapter["files"])
        anchor_hits = {}
        missing_anchors = []
        for anchor in chapter["anchors"]:
            hits = find_anchor(scope_texts, anchor)
            anchor_hits[anchor] = hits
            if not hits:
                missing_anchors.append(anchor)
        chapter_results.append(
            {
                "title": chapter["title"],
                "chapter_present_in_textbook": chapter["title"] in textbook_chapters,
                "missing_files": missing_files,
                "missing_anchors": missing_anchors,
                "anchor_hits": anchor_hits,
            }
        )

    module_mentions = {}
    missing_module_mentions = []
    for relpath in scope_files:
        stem = file_stem(relpath)
        token = f"\\leanfile{{{stem}}}"
        present = token in tex
        module_mentions[stem] = present
        if not present:
            missing_module_mentions.append(stem)

    unmapped_scope_files = sorted(set(scope_files) - covered_files)

    family_level_pass = (
        tex_path.exists()
        and pdf_path.exists()
        and not missing_module_mentions
        and not unmapped_scope_files
        and all(
            r["chapter_present_in_textbook"]
            and not r["missing_files"]
            and not r["missing_anchors"]
            for r in chapter_results
        )
    )

    strict_decl_level_status = "not_established"
    strict_decl_reason = (
        "The current textbook provides chapter/family-level correspondence, "
        "but it does not contain a declaration-level index for all formal items."
    )
    if total_formal_decls <= textbook_statement_blocks:
        strict_decl_level_status = "plausible"
        strict_decl_reason = (
            "The textbook has at least as many explicit statement blocks as the formal declaration count."
        )

    return {
        "artifacts": {
            "textbook_tex_exists": tex_path.exists(),
            "textbook_pdf_exists": pdf_path.exists(),
            "textbook_tex": str(tex_path),
            "textbook_pdf": str(pdf_path),
        },
        "counts": {
            "scope_file_count": len(scope_files),
            "covered_scope_file_count": len(covered_files),
            "formal_declaration_count": total_formal_decls,
            "textbook_statement_block_count": textbook_statement_blocks,
            "textbook_chapter_count": len(textbook_chapters),
        },
        "per_file_declaration_count": per_file_decls,
        "module_mentions": module_mentions,
        "missing_module_mentions": missing_module_mentions,
        "unmapped_scope_files": unmapped_scope_files,
        "chapter_results": chapter_results,
        "verdict": {
            "family_level_correspondence": "pass" if family_level_pass else "fail",
            "strict_declaration_level_correspondence": strict_decl_level_status,
            "strict_declaration_level_reason": strict_decl_reason,
        },
    }


def write_reports(root: Path, report: dict) -> None:
    outdir = root / "build" / "appendix_b_textbook"
    outdir.mkdir(parents=True, exist_ok=True)
    json_path = outdir / "AppendixB_textbook_audit_report.json"
    md_path = outdir / "AppendixB_textbook_audit_report.md"
    json_path.write_text(json.dumps(report, indent=2, sort_keys=True))

    lines = []
    lines.append("# Appendix B Textbook Audit Report")
    lines.append("")
    lines.append(f"- Family-level correspondence: `{report['verdict']['family_level_correspondence']}`")
    lines.append(
        f"- Strict declaration-level correspondence: `{report['verdict']['strict_declaration_level_correspondence']}`"
    )
    lines.append(f"- Scope files: `{report['counts']['scope_file_count']}`")
    lines.append(f"- Formal declarations in audited scope: `{report['counts']['formal_declaration_count']}`")
    lines.append(
        f"- Explicit textbook statement blocks: `{report['counts']['textbook_statement_block_count']}`"
    )
    lines.append("")
    lines.append("## Checks")
    lines.append("")
    lines.append(
        f"- Textbook source exists: `{report['artifacts']['textbook_tex_exists']}`"
    )
    lines.append(
        f"- Textbook PDF exists: `{report['artifacts']['textbook_pdf_exists']}`"
    )
    lines.append(
        f"- Missing module mentions in concordance: `{len(report['missing_module_mentions'])}`"
    )
    lines.append(
        f"- Unmapped scope files: `{len(report['unmapped_scope_files'])}`"
    )
    lines.append("")
    lines.append("## Chapter Results")
    lines.append("")
    for chapter in report["chapter_results"]:
        status = (
            "pass"
            if chapter["chapter_present_in_textbook"]
            and not chapter["missing_files"]
            and not chapter["missing_anchors"]
            else "fail"
        )
        lines.append(f"- `{chapter['title']}`: `{status}`")
        if chapter["missing_files"]:
            lines.append(f"  Missing files: {', '.join(chapter['missing_files'])}")
        if chapter["missing_anchors"]:
            lines.append(f"  Missing anchors: {', '.join(chapter['missing_anchors'])}")
    lines.append("")
    lines.append("## Strict Declaration-Level Note")
    lines.append("")
    lines.append(report["verdict"]["strict_declaration_level_reason"])
    md_path.write_text("\n".join(lines) + "\n")


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    report = build_report(root)
    write_reports(root, report)
    print(json.dumps(report["verdict"], indent=2, sort_keys=True))
    print(
        json.dumps(
            {
                "scope_file_count": report["counts"]["scope_file_count"],
                "formal_declaration_count": report["counts"]["formal_declaration_count"],
                "textbook_statement_block_count": report["counts"]["textbook_statement_block_count"],
                "missing_module_mentions": report["missing_module_mentions"],
                "unmapped_scope_files": report["unmapped_scope_files"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
