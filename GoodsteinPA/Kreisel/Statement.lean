module

public import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Incompleteness.Second

@[expose] public section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Kreisel's unnatural well-ordering: the statements

Kreisel's example behind the "natural well-ordering" problem.  We build a `Δ₁` (hence
primitive-recursively decidable) binary relation `kreiselLT` on the naturals which, **in the
standard model, is literally the usual `<`** — order type `ω` — and yet `𝗣𝗔` does not prove
transfinite induction along it, not even for the single formula `good`.  By contrast `𝗣𝗔` proves
transfinite induction along the *syntactic* `<` for every formula.  So the proof-theoretic strength
of "transfinite induction up to `α`" depends on the *notation*, not on the order type: exactly
Kreisel's point.

## The construction

* `prfBotΔ z` — "`z` codes a `𝗣𝗔`-proof of `⊥`", i.e. Foundation's `Δ₁` proof predicate
  `proof 𝗣𝗔` with its formula slot fixed to `⌜(⊥ : Sentence ℒₒᵣ)⌝`.
* `goodΔ x` — `∀ z ≤ x, ¬ prfBotΔ z`: no contradiction proof is coded at or below `x`.
* `kreiselLTΔ x y` — `<` restricted to the good part, then everything good before everything bad,
  then the bad part in **reverse** order.  If `𝗣𝗔` were inconsistent with least contradiction
  proof `p`, the tail from `p` on would be an infinite descending chain; since `𝗣𝗔` is in fact
  consistent, no `x` is bad and the relation collapses to `<` (headline 1).

## The four headlines

1. `kreiselLT_iff_lt` — in `ℕ`, `kreiselLT` *is* `<`.
2. `pa_not_proves_TI_kreisel` — `𝗣𝗔 ⊬ TI kreiselLT good`.
3. `pa_proves_TI_lt` — `𝗣𝗔 ⊢ TI ltRel φ` for every `φ`.
4. `kreiselLT_delta1` — `kreiselLTΔ` is `Δ₁`: its `Σ₁` and `Π₁` halves are provably equivalent
   over `𝗣𝗔` (`ProvablyProperOn`, Foundation's notion of `Δ₁`-ness), the two halves being in
   `Hierarchy 𝚺 1` / `Hierarchy 𝚷 1` by construction.

Phase 1 (this file) states these and leaves the proofs `sorry`; see `KREISEL.md`.
-/

namespace GoodsteinPA.Kreisel

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.HierarchySymbol

/-! ## The relation -/

/-- `prfBotΔ z` : "`z` codes a `𝗣𝗔`-proof of `⊥`".  Foundation's `Δ₁` proof predicate
`proof 𝗣𝗔 d φ` with the formula slot fixed to `⌜⊥⌝`. -/
noncomputable def prfBotΔ : 𝚫₁.Semisentence 1 :=
  (proof 𝗣𝗔).rew (Rew.subst ![#0, ⌜(⊥ : Sentence ℒₒᵣ)⌝])

/-- `prfBotΔ` as a plain formula. -/
noncomputable abbrev prfBot : Semisentence ℒₒᵣ 1 := prfBotΔ.val

/-- `goodΔ x` : `∀ z ≤ x, ¬ prfBot z` — no `𝗣𝗔`-proof of `⊥` is coded at or below `x`.
Bounded, hence still `Δ₁`. -/
noncomputable def goodΔ : 𝚫₁.Semisentence 1 :=
  HierarchySymbol.Semiformula.ball ‘x. x + 1’ (∼ prfBotΔ.rew (Rew.subst ![#0]))

/-- `goodΔ` as a plain formula; this is the `φ` of headline 2. -/
noncomputable abbrev good : Semisentence ℒₒᵣ 1 := goodΔ.val

/-- The `Δ₁` order relation `x < y` (a `Δ₀` matrix packaged as `Δ₁`). -/
noncomputable def ltΔ : 𝚫₁.Semisentence 2 :=
  .mkDelta (.mkSigma “x y. x < y”) (.mkPi “x y. x < y”)

/-- The `Δ₁` relation `y < x`. -/
noncomputable def gtΔ : 𝚫₁.Semisentence 2 :=
  .mkDelta (.mkSigma “x y. y < x”) (.mkPi “x y. y < x”)

/-- `goodΔ` at the first argument of a binary formula. -/
noncomputable abbrev goodΔ₀ : 𝚫₁.Semisentence 2 := goodΔ.rew (Rew.subst ![#0])

/-- `goodΔ` at the second argument of a binary formula. -/
noncomputable abbrev goodΔ₁ : 𝚫₁.Semisentence 2 := goodΔ.rew (Rew.subst ![#1])

/-- **Kreisel's relation.**  `x ≺ y` iff
`(good x ∧ good y ∧ x < y) ∨ (good x ∧ ¬ good y) ∨ (¬ good x ∧ ¬ good y ∧ y < x)`. -/
noncomputable def kreiselLTΔ : 𝚫₁.Semisentence 2 :=
  (goodΔ₀ ⋏ goodΔ₁ ⋏ ltΔ) ⋎ (goodΔ₀ ⋏ ∼goodΔ₁) ⋎ (∼goodΔ₀ ⋏ ∼goodΔ₁ ⋏ gtΔ)

/-- Kreisel's relation as a plain formula. -/
noncomputable abbrev kreiselLT : Semisentence ℒₒᵣ 2 := kreiselLTΔ.val

/-- The ordinary `<`, as a binary semisentence. -/
def ltRel : Semisentence ℒₒᵣ 2 := “x y. x < y”

/-! ## Transfinite induction, internalized -/

/-- `TI r φ` : the sentence "`φ` is progressive along `r` implies `φ` holds everywhere",
i.e. `(∀ x, (∀ y, y ≺ x → φ y) → φ x) → ∀ x, φ x`. -/
def TI (r : Semisentence ℒₒᵣ 2) (φ : Semisentence ℒₒᵣ 1) : Sentence ℒₒᵣ :=
  “(∀ x, (∀ y, !r y x → !φ y) → !φ x) → ∀ x, !φ x”

/-! ## Headlines -/

/-- **Headline 1.**  In the standard model Kreisel's relation *is* the usual `<`: it has order
type `ω`.  (Uses that `𝗣𝗔` is sound, so no `z` codes a proof of `⊥`, so every `x` is `good`.) -/
theorem kreiselLT_iff_lt : ∀ x y : ℕ, (ℕ ⊧/![x, y] kreiselLT) ↔ x < y := by
  sorry

/-- **Headline 2.**  `𝗣𝗔` does not prove transfinite induction along `kreiselLT`, already for the
single instance `φ := good`.  Sketch: inside `𝗣𝗔`, `good` is progressive along `kreiselLT`
(if `¬ good x` then `y := x + 1` satisfies `¬ good y` and `y ≺ x`), so `TI kreiselLT good` yields
`∀ x, good x`, which `𝗣𝗔` proves equivalent to `𝗣𝗔.consistent`; Gödel II
(`consistent_unprovable`) finishes. -/
theorem pa_not_proves_TI_kreisel : 𝗣𝗔 ⊬ ↑(TI kreiselLT good) := by
  sorry

/-- **Headline 3.**  `𝗣𝗔` proves transfinite induction along the ordinary `<` for *every* formula:
this is just strong induction, available in `𝗣𝗔`.  Same relation in `ℕ` as headline 1's, opposite
provability status. -/
theorem pa_proves_TI_lt : ∀ φ : Semisentence ℒₒᵣ 1, 𝗣𝗔 ⊢ ↑(TI ltRel φ) := by
  sorry

/-- **Headline 4a.**  The two halves of `kreiselLTΔ` sit in `𝚺₁` resp. `𝚷₁` (by construction). -/
theorem kreiselLT_hierarchy :
    Arithmetic.Hierarchy 𝚺 1 kreiselLTΔ.sigma.val ∧
      Arithmetic.Hierarchy 𝚷 1 kreiselLTΔ.pi.val := ⟨by simp, by simp⟩

/-- **Headline 4b.**  `kreiselLTΔ` is `Δ₁` in Foundation's sense: `𝗣𝗔` proves its `𝚺₁` and `𝚷₁`
halves equivalent.  Together with `kreiselLT_hierarchy` this is the precise content of "the
relation is primitive recursive". -/
theorem kreiselLT_delta1 : kreiselLTΔ.ProvablyProperOn 𝗣𝗔 := by
  sorry

/-! ## Known-answer sanity checks -/

example : ∀ x y : ℕ, (ℕ ⊧/![x, y] ltRel) ↔ x < y := by intro x y; simp [ltRel]

example (z : ℕ) : (ℕ ⊧/![z] prfBot) ↔ Proof 𝗣𝗔 z (⌜(⊥ : Sentence ℒₒᵣ)⌝ : ℕ) := by
  simp [prfBot, prfBotΔ]

/-- Faithfulness of `good`: it really says "no `𝗣𝗔`-proof of `⊥` is coded at or below `x`".
Not free from `simp`, because the `∼` of a `𝚫₁` formula evaluates through its `𝚷₁` half; it needs
the properness of `prfBotΔ` (which comes from Foundation's `Proof.defined`).  Phase 2. -/
theorem good_iff (x : ℕ) :
    (ℕ ⊧/![x] good) ↔ ∀ z ≤ x, ¬ Proof 𝗣𝗔 z (⌜(⊥ : Sentence ℒₒᵣ)⌝ : ℕ) := by
  sorry

end GoodsteinPA.Kreisel

end
