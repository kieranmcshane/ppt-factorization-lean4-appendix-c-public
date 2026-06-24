# Appendix B Textbook Audit Protocol

This protocol is the objective test for the claimed correspondence between the
formal Appendix B development and the pure-math textbook
[`AppendixB_textbook.tex`](./AppendixB_textbook.tex).

## 1. Audit Levels

We use two levels, because "1-to-1 correspondence" can mean two different
things.

- `Family level`: every mathematically substantive proof family in the formal
  development has a unique textbook locus, every audited Lean file is in scope,
  every scope file is assigned to at least one textbook chapter, and every
  critical closure theorem is present and accounted for.

- `Declaration level`: every formal declaration (`theorem`, `lemma`, `def`,
  `structure`, `abbrev`, `class`, `instance`) has its own explicit textbook
  index entry. This is strictly stronger than the family-level claim.

The current textbook is designed to satisfy the family-level claim. It is not
yet designed as a declaration-by-declaration encyclopedia.

## 2. Acceptance Criteria

Family-level correspondence passes if and only if all of the following hold.

1. The audited scope is frozen and explicit.
2. Every scope file is mentioned in the concordance appendix of the textbook.
3. Every scope file is assigned to at least one textbook chapter in the audit
   manifest.
4. Every chapter in the audit manifest exists in the textbook.
5. Every chapter has all of its critical theorem anchors present in the Lean
   sources.
6. The textbook source exists.
7. The textbook PDF exists and compiles.

Declaration-level correspondence passes only if, in addition, there is an
explicit declaration-level index or equivalent artifact that maps every formal
declaration to a unique textbook locus.

## 3. Audit Artifacts

- Manifest:
  [`tools/appendix_b_textbook_audit_manifest.json`](./tools/appendix_b_textbook_audit_manifest.json)

- Audit script:
  [`tools/audit_appendix_b_textbook.py`](./tools/audit_appendix_b_textbook.py)

- Generated JSON report:
  [`build/appendix_b_textbook/AppendixB_textbook_audit_report.json`](./build/appendix_b_textbook/AppendixB_textbook_audit_report.json)

- Generated Markdown report:
  [`build/appendix_b_textbook/AppendixB_textbook_audit_report.md`](./build/appendix_b_textbook/AppendixB_textbook_audit_report.md)

## 4. Current Interpretation

If the audit reports:

- `family_level_correspondence = pass`

then the book is faithful at the mathematically substantive family/chapter
level.

If the audit reports:

- `strict_declaration_level_correspondence = not_established`

then the book is still honest and well-audited, but it is not yet a literal
declaration-by-declaration translation artifact.

That distinction is intentional. It prevents us from claiming more than the
current artifact actually supports.
