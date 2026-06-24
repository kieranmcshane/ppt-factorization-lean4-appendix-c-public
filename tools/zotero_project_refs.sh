#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
helper="$HOME/.codex/plugins/cache/openai-curated/zotero/3f0def1b/skills/zotero/scripts/zotero.py"
article_dir="$repo_root/article/publishable_pure_math_2026_06_08"
zotero_bib="$article_dir/references.zotero.bib"
seed_bib="$article_dir/references.bib"

case "${1:-status}" in
  status)
    python3 "$helper" status --json
    ;;
  search)
    shift
    python3 "$helper" search "$*" --json
    ;;
  export-all)
    inventory="$(python3 "$helper" inventory --json)"
    if [[ "$inventory" =~ ^[[:space:]]*\[\][[:space:]]*$ ]]; then
      echo "Zotero library has 0 top-level items; leaving $zotero_bib unchanged." >&2
      exit 3
    fi
    tmp="$(mktemp "${TMPDIR:-/tmp}/zotero-project-refs.XXXXXX")"
    trap 'rm -f "$tmp"' EXIT
    python3 "$helper" export-bibtex --out "$tmp" >/dev/null
    entries="$(grep -c '^[[:space:]]*@' "$tmp" || true)"
    if [[ "$entries" -eq 0 ]]; then
      echo "Zotero export produced 0 BibTeX entries; leaving $zotero_bib unchanged." >&2
      exit 3
    fi
    mv "$tmp" "$zotero_bib"
    trap - EXIT
    echo "Exported $entries BibTeX entries to $zotero_bib"
    ;;
  export-check)
    tmp="$(mktemp "${TMPDIR:-/tmp}/zotero-project-refs.XXXXXX")"
    trap 'rm -f "$tmp"' EXIT
    python3 "$helper" export-bibtex --out "$tmp" >/dev/null
    entries="$(grep -c '^[[:space:]]*@' "$tmp" || true)"
    echo "Zotero export produced $entries BibTeX entries."
    echo "$tmp"
    sed -n '1,120p' "$tmp"
    ;;
  article-seed)
    entries="$(grep -c '^[[:space:]]*@' "$seed_bib" || true)"
    echo "$seed_bib"
    echo "$entries BibTeX entries"
    ;;
  import-article-seed)
    python3 "$helper" import-bibtex --file "$seed_bib" --yes
    ;;
  *)
    echo "usage: $0 {status|search <query>|export-all|export-check|article-seed|import-article-seed}" >&2
    exit 2
    ;;
esac
