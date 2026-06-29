#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

lake build GoodsteinPABlueprint >&2

{
  printf 'import GoodsteinPABlueprint\n\n'
  printf '#eval show Lean.CoreM Unit from do\n'
  printf '  IO.println (← GoodsteinPA.Blueprint.renderMarkdown "Path B Blueprint: Open Capstones")\n'
} | lake env lean --stdin > PATHB-BLUEPRINT.md
