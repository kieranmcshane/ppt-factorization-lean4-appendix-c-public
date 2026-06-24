#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
env_file="$repo_root/.env.local"

if [[ -f "$env_file" ]]; then
  set -a
  # shellcheck disable=SC1090
  source "$env_file"
  set +a
fi

if [[ -z "${OPENAI_API_KEY:-}" && -z "${LITELLM_API_KEY:-}" ]]; then
  echo "No OPENAI_API_KEY or LITELLM_API_KEY is available. Put OPENAI_API_KEY in $env_file." >&2
  exit 2
fi

exec uvx narratelean "$@"
