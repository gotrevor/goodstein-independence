#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

lake build GoodsteinPA.BlueprintAttr >&2

{
  cat wip/PathBProbe.lean
  printf '\n'
  printf '#eval show Lean.CoreM Unit from do\n'
  printf '  IO.println (← GoodsteinPA.Blueprint.renderMarkdown "Path B Blueprint: Open Capstones")\n'
} | lake env lean --stdin > PATHB-BLUEPRINT.md
