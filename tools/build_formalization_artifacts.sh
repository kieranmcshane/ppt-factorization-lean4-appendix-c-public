#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

export PATH="$HOME/.local/share/uv/tools/leanblueprint/bin:$HOME/.local/bin:$PATH"

python3 tools/scientific_tool_status.py
python3 tools/u_aub_02_frontier_graph.py

leanblueprint pdf
leanblueprint web
leanblueprint checkdecls

pandoc exposition/u_aub_02_formalization_note.md \
  --from markdown \
  --to latex \
  --standalone \
  --output exposition/u_aub_02_formalization_note.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=exposition exposition/u_aub_02_formalization_note.tex

pandoc exposition/formalization_workflow.md \
  --from markdown \
  --to latex \
  --standalone \
  --output exposition/formalization_workflow.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=exposition exposition/formalization_workflow.tex

python3 tools/check_public_review_chatter.py
