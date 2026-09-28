/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import Foundation.FirstOrder.Arithmetic.HFS

@[expose] public section

/-!
# Comparator challenge support — the Foundation-DSL arithmetization

Verbatim re-declaration of the `𝚺₁`-objects the Goodstein sentence's closure reaches, from
`src/GoodsteinPA/Internal.lean` (the consolidated `InternalPow → InternalLog → InternalBump →
InternalGoodstein` chain).

**Why one module, in this exact declaration order.**  Lean lifts the auto-generated
well-formedness / `NeZero` proofs of a `.mkSigma` or `PR.Blueprint` field into auxiliary
`…_proof_N` declarations and *deduplicates* identical ones against earlier declarations **in the
same module**.  So the challenge copy only elaborates to the same `ConstantInfo`s as the solution
if it mirrors the development's module boundary and order exactly: one module (`Internal.lean`),
`module`-mode (the module system also affects the numbering), declarations in the order
`pow.blueprint, ipowDef, ilogDef, bumpNextDef, bumpTable.blueprint, ibumpTableDef, ibumpDef,
goodstein.blueprint, igoodsteinDef`.  The development's model-side `…construction`s and the
`𝚺₁-Function` instances in between own no auxiliary proof that these defs would dedup onto, so
they need not be reproduced.

`Challenge.lean` is still the audit surface; this module just reproduces the development's own
module structure so the arithmetization objects elaborate byte-identically.  Every
un-re-declared `!…Def` splice (`znthDef`, `divDef`, `remDef`, `subDef`, `seqConsDef`,
`mkSeq₁Def`) resolves to the shared Foundation constant.
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace GoodsteinPA.InternalPow

/-! ### `ipow` — variable-base power -/

/-- Primitive-recursion blueprint for variable-base power: one parameter (the base `x = b`),
`zero ↦ 1`, `succ : ih ↦ ih * b`.  Verbatim from `Internal.lean:51`. -/
def pow.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = 1”
  succ := .mkSigma “y ih n x. y = ih * x”

/-- `𝚺₁`-definition of `ipow` (variable-base power `b ^ x` inside a model of `IΣ₁`), with the
argument order `(output, b, x)`.  Verbatim from `Internal.lean:73`. -/
def _root_.FFL.FirstOrder.Arithmetic.ipowDef : 𝚺ᴬ₁.Semisentence 3 :=
  pow.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

/-! ### `ilog` — base-`b` logarithm -/

/-- `𝚺₁`-graph of the base-`b` logarithm `ilog b n` (top exponent of `n` in base `b`): for
`2 ≤ b` and `0 < n` it is the `e` with `b^e ≤ n < b^(e+1)`, else `0`.  Verbatim from
`Internal.lean:314`. -/
def _root_.FFL.FirstOrder.Arithmetic.ilogDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “e b n. (2 ≤ b ∧ 0 < n → (∃ pe, !ipowDef pe b e ∧ pe ≤ n) ∧ (∃ pf, !ipowDef pf b (e + 1) ∧ n < pf))
        ∧ (¬(2 ≤ b ∧ 0 < n) → e = 0)”

/-! ### `ibump` — the hereditary base-change -/

/-- The `𝚺₁` graph-definition of `bumpNext` (the table step of the hereditary base-change),
composing `ilog`, `ipow`, `znth`, `div`, `rem`.  Verbatim from `Internal.lean:360`. -/
def _root_.FFL.FirstOrder.Arithmetic.bumpNextDef : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y b M s.
    ∃ e, !ilogDef e b M ∧ ∃ pe, !ipowDef pe b e ∧ ∃ te, !znthDef te s e ∧
      ∃ pte, !ipowDef pte (b + 1) te ∧ ∃ q, !divDef q M pe ∧ ∃ r, !remDef r M pe ∧
        ∃ tr, !znthDef tr s r ∧ y = q * pte + tr”

/-- Blueprint for the `bump` table: `bumpTable b 0 = ⟨0⟩`, `bumpTable b (n+1)` appends
`bumpNext b (n+1) (bumpTable b n)`.  Verbatim from `Internal.lean:376`. -/
def bumpTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n x. ∃ v, !bumpNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

/-- `𝚺₁`-definition of the `bump` table `ibumpTable b n = ⟨bump b 0,…,bump b n⟩`.
Verbatim from `Internal.lean:403`. -/
def _root_.FFL.FirstOrder.Arithmetic.ibumpTableDef : 𝚺ᴬ₁.Semisentence 3 :=
  bumpTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

/-- `𝚺₁`-definition of the internalized hereditary base-change `ibump b n` (the `n`-th table
entry).  Verbatim from `Internal.lean:414`. -/
def _root_.FFL.FirstOrder.Arithmetic.ibumpDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y b n. ∃ t, !ibumpTableDef t b n ∧ !znthDef y t n”

/-! ### `igoodstein` — the internal Goodstein run -/

/-- Blueprint for the Goodstein run: `zero ↦ m₀`, `succ : (k, v) ↦ ibump (k+2) v - 1`.
Verbatim from `Internal.lean:815`. -/
def goodstein.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. ∃ w, !ibumpDef w (n + 2) ih ∧ !subDef y w 1”

/-- `𝚺₁`-definition of the internal Goodstein sequence `igoodstein m₀ k = mₖ` (over base `k+2`).
Verbatim from `Internal.lean:838`. -/
def _root_.FFL.FirstOrder.Arithmetic.igoodsteinDef : 𝚺ᴬ₁.Semisentence 3 :=
  goodstein.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

end GoodsteinPA.InternalPow
