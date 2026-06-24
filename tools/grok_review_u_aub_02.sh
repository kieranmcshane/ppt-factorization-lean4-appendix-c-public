#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

mkdir -p build
scratch_dir="build/private/grok_u_aub_02_review"
mkdir -p "$scratch_dir"

prompt_file="$scratch_dir/prompt.txt"
raw_file="$scratch_dir/raw.md"
text_file="build/grok_u_aub_02_review.md"
stderr_file="$scratch_dir/stderr.txt"
rejected_file="$scratch_dir/rejected.md"
grok_review_bin="${GROK_REVIEW_BIN:-$HOME/.codex/skills/grok-build/scripts/grok_review.py}"

rm -f \
  build/grok_u_aub_02_review_prompt.txt \
  build/grok_u_aub_02_review.raw.md \
  build/grok_u_aub_02_review.stderr \
  "$raw_file" \
  "$rejected_file"

if [[ ! -x "$grok_review_bin" ]]; then
  if command -v grok-review >/dev/null 2>&1; then
    grok_review_bin="$(command -v grok-review)"
  else
    echo "grok-review helper not found; expected $grok_review_bin" >&2
    exit 127
  fi
fi

cat > "$prompt_file" <<'EOF'
You are reviewing a Lean 4 formalization workflow for ticket U-AUB-02.

Current status:
- U-AUB-02 is not done.
- The current checked endpoint is:
  PptFactorization.AppendixB.AubrunBiDefectCountBound_of_bianeAdjacentLinkHalves_left_gap_three_start_impossible_frontiers_nestedStrictReturnIntervalOpenNonwrapOffCycleSmallerInternalOnly_and_chapuy
- The remaining theorem-strength leaves are:
  1. left large-gap Biane adjacent-link theorem;
  2. right large-gap Biane adjacent-link theorem;
  3. the side-specific residual branch return-interval common-cycle
     collision theorems for non-fixed predecessor skips: primitive-residual
     branches for nonwrapping first return, wrap-below last return, and
     wrap-above first return; internal-subinterval branches for wrap-below and
     wrap-above; and the strict side-aware nonwrapping smaller child
     internal-subinterval branch;
  4. Chapuy/trisection recurrence.
- Checked components include rank/defect budget, scalar shifted-base absorption,
  NCPart cardinality/genus-zero base, gap-two Biane links, finite gap-three
  slices, the direct-hit predecessor-skip branch, the branch-normalized nested
  return-interval extractor, the strict/residual frontier split, internal-right
  subinterval descent, the side-case split of the nested residual leaf, the
  primitive/internal-subinterval branch split inside each side case, the
  nonwrapping open-internal and off-cycle refinements of the
  internal-subinterval branch, the strict noncrossing confinement of the
  off-cycle witness block, the strictly smaller contour-repeat interval
  extracted from that witness, the smaller side-aware residual split that
  preserves the no-x-cycle and block-off-x data, the descended branch split of
  that child residual, the five-way branch split of the child primitive
  residual, the strict branch split of the smaller contour-repeat packet, the
  adjacent-or-shorter split of the raw internal-T child branch, the parent
  primitive absorption theorem that removes the five child primitive leaves
  from the endpoint surface, and a Lean no-go theorem showing that the loose
  primitive residual route is false without the nested side data.

You have no repository access for this review.  Treat the context above as the
complete input.  Do not use tools.  Do not browse.

Please give adversarial feedback on:
1. whether this project workflow prevents confusing checked adapters with done tickets;
2. whether the article-style exposition should foreground the four remaining leaf groups differently;
3. which branch collision leaf or other proof leaf looks most promising to attack next and why;
4. any hidden risk in using finite permutation enumeration as conjecture-finding only.

Do not invent Lean theorem names. Flag uncertainty explicitly. Keep the answer
about the mathematics and formalization workflow only. Do not discuss how this
review was run, transmitted, configured, or logged.
EOF

if "$grok_review_bin" \
  --cwd "$repo_root" \
  --max-turns "${GROK_REVIEW_MAX_TURNS:-8}" \
  --timeout "${GROK_REVIEW_TIMEOUT:-300}" \
  --prompt-file "$prompt_file" > "$raw_file" 2> "$stderr_file"; then
  rm -f "$stderr_file"
else
  rc=$?
  echo "external review failed before returning scientific feedback" >&2
  exit "$rc"
fi

python3 tools/sanitize_reviewer_output.py "$raw_file" "$text_file"
rm -f "$raw_file"

if ! python3 tools/sanitize_reviewer_output.py --check-only "$text_file"; then
  mv "$text_file" "$rejected_file"
  echo "external review returned non-mathematical material and was rejected" >&2
  exit 2
fi

echo "wrote $text_file"
