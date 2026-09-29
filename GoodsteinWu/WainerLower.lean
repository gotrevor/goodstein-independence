/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA.WainerGeneral
import GoodsteinWu.FgFormula

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
      𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) :=
  ⟨FgFormula.fgFormula o, FgFormula.hierarchy_fgFormula o,
    FgFormula.eval_fgFormula_nat o ho, FgFormula.peano_fgFormula o ho⟩

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

/-! ### Anti-vacuity anchors

The frozen `↔` is only as meaningful as `ONote.fastGrowing`, so pin two of its low values through
the formula actually produced above.  These would break immediately if `fgFormula` ever came
detached from the hierarchy it is supposed to compute. -/

/-- At `o = 0` the produced formula reads as the successor function. -/
example (n y : ℕ) : ℕ ⊧/![y, n] (FgFormula.fgFormula 0) ↔ y = n + 1 := by
  rw [FgFormula.eval_fgFormula_nat 0 ONote.NF.zero, ONote.fastGrowing_zero]

/-- At `o = 1` it reads as doubling. -/
example (n y : ℕ) : ℕ ⊧/![y, n] (FgFormula.fgFormula 1) ↔ y = 2 * n := by
  rw [FgFormula.eval_fgFormula_nat 1 (by infer_instance), ONote.fastGrowing_one]

end GoodsteinWu
