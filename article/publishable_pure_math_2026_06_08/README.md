# Publishable Pure-Math Article

This directory is a fresh LaTeX article project, written as a pure
mathematics manuscript rather than as a Lean report.

- Main source: `main.tex`
- Build command: `make pdf`
- Output: `main.pdf`
- Formal sync note: `lean_sync_status.md`
- External referee pass: `grok_referee_report.md`
- Zotero provenance export: `references.zotero.bib`

The manuscript body intentionally avoids Lean theorem names and ticket labels.
Those belong in the sync note and formalization board.

The build uses `references.bib`, whose stable citation keys are TeX-safe.  The
Zotero export records the source items:

- `R9XTV2VV` -> `Aubrun2012`
- `D9ZQUM4F` -> `AubrunSzarekYe2014`
- `WQVQ7TD7` -> `Biane1997`
- `GA76Q7V7` -> `Chapuy2011`
