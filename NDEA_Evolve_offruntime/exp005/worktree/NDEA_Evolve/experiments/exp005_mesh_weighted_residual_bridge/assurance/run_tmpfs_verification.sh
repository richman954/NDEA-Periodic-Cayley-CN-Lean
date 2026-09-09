#!/usr/bin/env bash
# Compatibility entry point. Default cache is /tmp; pass --cache-root for tmpfs.
set -euo pipefail
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$script_dir/run_verification.py" "$@"
