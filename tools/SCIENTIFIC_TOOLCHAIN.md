# Scientific Toolchain For U-AUB-02

This repository now has one local entry point for the tool stack:

```bash
python3 tools/scientific_tool_status.py
```

The status output is intentionally reader-facing: raw version probes are
filtered so operational prose is not shown as project evidence.

The intended roles are:

- `scripts/u_aub_02_perm_explorer.py`: finite permutation and bidefect sanity
  checks.  This is conjecture-finding only, never proof evidence.
- `scripts/aubrun_branch_sanity.py`: active frontier sanity profiles.  It
  reports the empty finite gap-three branch list, the live large-gap Biane
  profile, the nested predecessor-skip profile behind the side-tied
  subinterval-descended residual frontier, and, with `--wrap-position`, the
  four position-refined wrap internal-subinterval leaves currently exposed by
  the sharp endpoint.  These profiles are conjecture-finding only, never proof
  evidence.
- `tools/u_aub_02_frontier_graph.py`: Graphviz rendering of the active
  U-AUB-02 frontier.
- `leanblueprint`: maintained declaration inventory and dependency graph in
  `blueprint/`.
- `scripts/narratelean_with_env.sh`: optional narration wrapper.  Narration is
  exposition support only, never proof evidence.
- `tools/grok_review_u_aub_02.sh`: adversarial Grok review for the
  article-style exposition and workflow.  Its saved Markdown is kept to
  scientific reviewer text; if no such text is produced, no public review is
  retained.
- `tools/zotero_project_refs.sh`: reference-library search/import/export
  wrapper.  The publishable article keeps stable citation keys in
  `article/publishable_pure_math_2026_06_08/references.bib`; Zotero export is
  useful for library management, but should not overwrite that file unless the
  TeX citation keys are changed at the same time.
- `tools/build_formalization_artifacts.sh`: rebuilds the tool status graph,
  blueprint, and exposition PDFs.

Sage/GAP note: Sage/GAP is optional.  Use it for larger finite-combinatorics
experiments if it is available:

```bash
brew install --cask sage
```

Until Sage is installed, the pure Python explorer gives the small-`m`
permutation tables needed for proof-route sanity checks.
