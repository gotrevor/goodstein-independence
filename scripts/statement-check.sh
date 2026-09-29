#!/usr/bin/env bash
# Statement-fingerprint gate: every GoodsteinPA declaration's type (and definition value), with the
# Compat shim delta-expanded, must match the committed baseline scripts/statement-snapshot.txt.
#   scripts/statement-check.sh            compare (exit 1 on any difference, printing the diff)
#   scripts/statement-check.sh --update   rewrite the baseline (only with a reviewed reason)
set -euo pipefail
cd "$(dirname "$0")/.."
cur=$(mktemp)
lake env lean scripts/StatementSnapshot.lean 2>&1 | sed -E 's/^scripts\/StatementSnapshot\.lean:[0-9]+:[0-9]+: info: //' | grep -E '^[^ ]+ [0-9]+$' > "$cur"
if [ "${1:-}" = "--update" ]; then cp "$cur" scripts/statement-snapshot.txt; echo "statement-check: baseline updated ($(wc -l < "$cur") decls)"; exit 0; fi
if diff -u scripts/statement-snapshot.txt "$cur"; then echo "statement-check: OK ($(wc -l < "$cur") decls)"; else echo "statement-check: FAILED"; exit 1; fi
