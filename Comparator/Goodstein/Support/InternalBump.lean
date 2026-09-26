/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Comparator.Goodstein.Support.InternalLog

/-!
# Comparator challenge support — arithmetization brick 4 (the hereditary base-change `bump`)

Verbatim re-declaration of the `bumpNext`/`bumpTable`/`ibump` `𝚺₁`-objects from
`src/GoodsteinPA/InternalBump.lean`. Kept in its own module to mirror the source-file boundary: this
is where `bumpTable.blueprint` (the second of the three `PR.Blueprint 1` objects) must live so its
auto-generated arity-1 proof gets its own `bumpTable.blueprint._proof_N` — the same as in the
solution, where `pow.blueprint` sits in the imported `InternalPow.lean` (see `Support/InternalPow.lean`).
-/

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol

namespace GoodsteinPA.InternalPow

/-- The `𝚺₁` graph-definition of `bumpNext` (the table step of the hereditary base-change),
composing `ilog`, `ipow`, `znth`, `div`, `rem`. Verbatim from `src/GoodsteinPA/InternalBump.lean:31`. -/
def _root_.LO.FirstOrder.Arithmetic.bumpNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b M s.
    ∃ e, !ilogDef e b M ∧ ∃ pe, !ipowDef pe b e ∧ ∃ te, !znthDef te s e ∧
      ∃ pte, !ipowDef pte (b + 1) te ∧ ∃ q, !divDef q M pe ∧ ∃ r, !remDef r M pe ∧
        ∃ tr, !znthDef tr s r ∧ y = q * pte + tr”

/-- Blueprint for the `bump` table: `bumpTable b 0 = ⟨0⟩`, `bumpTable b (n+1)` appends
`bumpNext b (n+1) (bumpTable b n)`. Verbatim from `src/GoodsteinPA/InternalBump.lean:47` (its file
opens `namespace GoodsteinPA.InternalPow`, so the real name is
`GoodsteinPA.InternalPow.bumpTable.blueprint`). -/
def bumpTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n x. ∃ v, !bumpNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

/-- `𝚺₁`-definition of the `bump` table `ibumpTable b n = ⟨bump b 0,…,bump b n⟩`.
Verbatim from `src/GoodsteinPA/InternalBump.lean:74`. -/
def _root_.LO.FirstOrder.Arithmetic.ibumpTableDef : 𝚺₁.Semisentence 3 :=
  bumpTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

/-- `𝚺₁`-definition of the internalized hereditary base-change `ibump b n` (the `n`-th table entry).
Verbatim from `src/GoodsteinPA/InternalBump.lean:85`. -/
def _root_.LO.FirstOrder.Arithmetic.ibumpDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y b n. ∃ t, !ibumpTableDef t b n ∧ !znthDef y t n”

end GoodsteinPA.InternalPow
