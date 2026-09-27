/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import PAComparator.Goodstein.Support.InternalBump

/-!
# Comparator challenge support — arithmetization brick 5 (the internal Goodstein run)

Verbatim re-declaration of the internal Goodstein-sequence `𝚺₁`-objects from
`src/GoodsteinPA/InternalGoodstein.lean`. Kept in its own module to mirror the source-file boundary:
this is where `goodstein.blueprint` (the third of the three `PR.Blueprint 1` objects) must live so
its auto-generated arity-1 proof gets its own `goodstein.blueprint._proof_N` — matching the solution,
where `pow.blueprint`/`bumpTable.blueprint` sit in imported modules (see `Support/InternalPow.lean`).
`igoodsteinDef` is the sentence's arithmetization entry point: `!igoodsteinDef 0 m N` says
`igoodstein m N = 0`.
-/

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol

namespace GoodsteinPA.InternalPow

/-- Blueprint for the Goodstein run: `zero ↦ m₀`, `succ : (k, v) ↦ ibump (k+2) v - 1`.
Verbatim from `src/GoodsteinPA/InternalGoodstein.lean:24` (namespace `GoodsteinPA.InternalPow`). -/
def goodstein.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. ∃ w, !ibumpDef w (n + 2) ih ∧ !subDef y w 1”

/-- `𝚺₁`-definition of the internal Goodstein sequence `igoodstein m₀ k = mₖ` (over base `k+2`).
Verbatim from `src/GoodsteinPA/InternalGoodstein.lean:47`. -/
def _root_.LO.FirstOrder.Arithmetic.igoodsteinDef : 𝚺₁.Semisentence 3 :=
  goodstein.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

end GoodsteinPA.InternalPow
