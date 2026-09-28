/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import PAComparator.Goodstein.Support.InternalPow

/-!
# Comparator challenge support — arithmetization brick 3 (`ilog`)

Verbatim re-declaration of the base-`b` logarithm `𝚺₁`-graph from `src/GoodsteinPA/InternalLog.lean`.
Kept in its own module to mirror the source-file boundary (see `Support/InternalPow.lean` for why
that matters for byte-identity under comparator).
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace GoodsteinPA.InternalPow

/-- `𝚺₁`-graph of the base-`b` logarithm `ilog b n` (top exponent of `n` in base `b`): for
`2 ≤ b ∧ 0 < n`, `b^e ≤ n < b^(e+1)`, else `e = 0`. Verbatim from `src/GoodsteinPA/InternalLog.lean:116`. -/
def _root_.FFL.FirstOrder.Arithmetic.ilogDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “e b n. (2 ≤ b ∧ 0 < n → (∃ pe, !ipowDef pe b e ∧ pe ≤ n) ∧ (∃ pf, !ipowDef pf b (e + 1) ∧ n < pf))
        ∧ (¬(2 ≤ b ∧ 0 < n) → e = 0)”

end GoodsteinPA.InternalPow
