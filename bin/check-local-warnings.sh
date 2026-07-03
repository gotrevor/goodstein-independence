#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Local warning-audit sketch. This is intentionally not wired into CI and
# intentionally does not fail on warnings.
#
# Dependencies are built leniently because Foundation/mathlib can replay warning
# noise that is outside this repository's control. The source-file pass below is
# useful for finding local warnings, but the exact strict policy is unfinished.
lake build @Foundation @checkdecls --log-level=error

if [[ $# -gt 0 ]]; then
  root_targets=("$@")
else
  root_targets=("@/GoodsteinPA" "@/GoodsteinPABlueprint" "@/blueprint_audit")
fi

lake build "${root_targets[@]}" --log-level=error

status=0
while IFS= read -r file; do
  echo "audit: ${file}"
  if ! lake env lean -R src "${file}"; then
    status=1
  fi
done < <(find src -name '*.lean' | sort)

exit "${status}"
