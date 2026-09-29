/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA.WainerGeneral
import OrdinalAnalysis.Gentzen.UpperBound

/-!
# Wainer's classification, lower half

Every function `ONote.fastGrowing o` with `o` in normal form (so `o < ε₀`) is provably total in PA:
some Σ₁ definition of its graph has `∀x ∃y` provable in `𝗣𝗔`.  The route goes through KT. Wu's
Gentzen upper bound (`OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound`: PA proves
transfinite induction up to every notation below ε₀).

With g-i's upper half (`GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing`)
this gives Wainer's classification of the PA-provably total functions.

See `WAINER-LOWER.md` for the plan.
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace GoodsteinWu

/-- **Wainer, lower half.**  For every normal-form `o : ONote`, the function `fastGrowing o` has a
Σ₁-definable graph `φ(y, n) ↔ y = fastGrowing o n` whose totality `∀n ∃y φ` PA proves. -/
theorem fastGrowing_provably_total (o : ONote) (ho : o.NF) :
    ∃ φ : Semisentence ℒₒᵣ 2, Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ ∧
      (∀ n y : ℕ, ℕ ⊧/![y, n] φ ↔ y = ONote.fastGrowing o n) ∧
      𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) := by
  sorry

/-- **Wainer's classification** of PA's provably total functions: every PA-provable Π₂ sentence
has witnesses eventually below some `fastGrowing o` with `o < ε₀` (upper half), and every such
`fastGrowing o` is itself PA-provably total (lower half). -/
theorem wainer_classification :
    (∀ (φ : Semisentence ℒₒᵣ 2), Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ →
        𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) →
        ∃ o : ONote, o.NF ∧ ∃ M : ℕ, ∀ m, M ≤ m →
          ∃ N ≤ ONote.fastGrowing o m, ℕ ⊧/![N, m] φ) ∧
    (∀ o : ONote, o.NF →
        ∃ φ : Semisentence ℒₒᵣ 2, Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ ∧
          (∀ n y : ℕ, ℕ ⊧/![y, n] φ ↔ y = ONote.fastGrowing o n) ∧
          𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ)) :=
  ⟨fun φ hφ h => GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing φ hφ h,
   fastGrowing_provably_total⟩

end GoodsteinWu
