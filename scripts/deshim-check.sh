#!/usr/bin/env bash
# De-shim gate: the Foundation compat shim is gone and nothing re-creates it elsewhere.
#   1. GoodsteinPA/ToFoundation/Compat.lean does not exist and nothing imports it;
#   2. no module-level notation commands beyond the 3 that predate this work
#      (a moved shim would show up as new `notation`/`prefix`/... lines);
#   3. the old shim spellings are gone from the sources.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
if [ -e GoodsteinPA/ToFoundation/Compat.lean ]; then echo "FAIL: Compat.lean still exists"; fail=1; fi
if grep -rn 'ToFoundation\.Compat' GoodsteinPA GoodsteinPA.lean --include=*.lean; then echo "FAIL: something still imports Compat"; fail=1; fi
n=$(grep -rnE '^\s*(prefix|infix|infixl|infixr|postfix|notation|macro)\b' GoodsteinPA --include=*.lean | wc -l | tr -d ' ')
if [ "$n" -gt 3 ]; then echo "FAIL: $n module-level notation commands (baseline 3):"; grep -rnE '^\s*(prefix|infix|infixl|infixr|postfix|notation|macro)\b' GoodsteinPA --include=*.lean; fail=1; fi
if grep -rnE '∀⁰|∃⁰|⊧ₘ|\bgValm?\b|\bgEvalm?\b|[^𝗜]𝚺₀|[^𝗜]𝚷₀|𝚫₀|[^𝗜]𝚺₁|𝚷₁|𝚫₁' GoodsteinPA --include=*.lean | head -20 | grep .; then echo "FAIL: old shim spellings remain (first 20 shown)"; fail=1; fi
[ $fail = 0 ] && echo "deshim-check: OK"
exit $fail
