import GoodsteinPA.OperatorZef2

/-!
# Route-(c) value gate — the hereditary `Gated` predicate (lap 206, step (2))

Mandated by the DIRECTION lap-206 block, step (2), after the step-(1) gadget probe PASSED
(`wip/ReadoffValueGadgetProbe.lean`).  Design (PENDING_WORK lap-206 top): instead of threading a
SYNTACTIC subformula-closure through the read-off's derivation induction, the invariant tracks a
SEMANTIC hereditary predicate `Gated P V ψ` —

* at a false `∀⁰ χ` member the trap descent needs a **value-gated false branch**
  `∃ k ≤ P V, ¬ atomTrue (χ/[nm k])` (E–W's rule-side branch gate, reconstructed semantically);
* every quantifier instance stays `Gated` at the bumped budget `max V k` (so the invariant
  survives `allω`/vacuous-`exI` insertions), and connective constituents stay `Gated` at the
  same budget (`andI`/`orI` insertions).

The syntactic work (φ's `Hierarchy 𝚺` ball-shapes + the subterm value bound `P_φ`) then
discharges `Gated` ONCE, at the pipeline root, for the concrete `goodsteinBodyE` instances —
NOT inside the derivation induction.  This file defines `Gated` and banks its two derivation-side
laws: budget monotonicity (`Gated_mono`) and the accessor lemmas the induction's cases consume.

Wip-only ruling input; `Gated` is internal proof machinery (no ratified-statement contact).
-/

namespace GoodsteinPA.ReadoffValueGate

open LO LO.FirstOrder
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-- **The hereditary value gate.**  `Gated P V ψ` says: along any refutation descent through
`ψ`'s quantifier/connective structure, false `∀⁰`-heads admit a false branch of index `≤ P` of
the running budget, where the budget starts at `V` and absorbs every instantiation index.
Atoms/⊤/⊥ are vacuously gated (the read-off's leaf cases never descend). -/
def Gated (P : ℕ → ℕ) : ℕ → Form → Prop
  | _, Semiformula.rel _ _ => True
  | _, Semiformula.nrel _ _ => True
  | _, Semiformula.verum => True
  | _, Semiformula.falsum => True
  | V, Semiformula.and χ₁ χ₂ => Gated P V χ₁ ∧ Gated P V χ₂
  | V, Semiformula.or χ₁ χ₂ => Gated P V χ₁ ∧ Gated P V χ₂
  | V, Semiformula.all χ =>
      (¬ atomTrue (Semiformula.all χ) → ∃ k, k ≤ P V ∧ ¬ atomTrue (χ/[nm k])) ∧
      ∀ k, Gated P (max V k) (χ/[nm k])
  | V, Semiformula.exs χ => ∀ n, Gated P (max V n) (χ/[nm n])
termination_by _ φ => φ.complexity
decreasing_by
  all_goals simp [Semiformula.complexity_rew]

/-! ## Accessors — the shapes the read-off induction's cases consume -/

theorem Gated_and_iff {P : ℕ → ℕ} {V : ℕ} {χ₁ χ₂ : Form} :
    Gated P V (χ₁ ⋏ χ₂) ↔ Gated P V χ₁ ∧ Gated P V χ₂ := by
  rw [show (χ₁ ⋏ χ₂) = Semiformula.and χ₁ χ₂ from rfl, Gated]

theorem Gated_or_iff {P : ℕ → ℕ} {V : ℕ} {χ₁ χ₂ : Form} :
    Gated P V (χ₁ ⋎ χ₂) ↔ Gated P V χ₁ ∧ Gated P V χ₂ := by
  rw [show (χ₁ ⋎ χ₂) = Semiformula.or χ₁ χ₂ from rfl, Gated]

theorem Gated_all_iff {P : ℕ → ℕ} {V : ℕ} {χ : SyntacticSemiformula ℒₒᵣ 1} :
    Gated P V (∀⁰ χ) ↔
      ((¬ atomTrue (∀⁰ χ) → ∃ k, k ≤ P V ∧ ¬ atomTrue (χ/[nm k])) ∧
        ∀ k, Gated P (max V k) (χ/[nm k])) := by
  rw [show (∀⁰ χ) = Semiformula.all χ from rfl, Gated]

theorem Gated_exs_iff {P : ℕ → ℕ} {V : ℕ} {χ : SyntacticSemiformula ℒₒᵣ 1} :
    Gated P V (∃⁰ χ) ↔ ∀ n, Gated P (max V n) (χ/[nm n]) := by
  rw [show (∃⁰ χ) = Semiformula.exs χ from rfl, Gated]

/-! ## Budget monotonicity — old members stay gated when the budget bumps -/

theorem Gated_mono {P : ℕ → ℕ} (hP : Monotone P) :
    ∀ (φ : Form) (V V' : ℕ), V ≤ V' → Gated P V φ → Gated P V' φ
  | Semiformula.rel _ _, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.nrel _ _, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.verum, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.falsum, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.and χ₁ χ₂, V, V', h, hg => by
      rw [Gated] at hg ⊢
      exact ⟨Gated_mono hP χ₁ V V' h hg.1, Gated_mono hP χ₂ V V' h hg.2⟩
  | Semiformula.or χ₁ χ₂, V, V', h, hg => by
      rw [Gated] at hg ⊢
      exact ⟨Gated_mono hP χ₁ V V' h hg.1, Gated_mono hP χ₂ V V' h hg.2⟩
  | Semiformula.all χ, V, V', h, hg => by
      rw [Gated] at hg ⊢
      refine ⟨fun hf => ?_, fun k => ?_⟩
      · obtain ⟨k, hk, hkf⟩ := hg.1 hf
        exact ⟨k, le_trans hk (hP h), hkf⟩
      · exact Gated_mono hP (χ/[nm k]) (max V k) (max V' k)
          (max_le_max h le_rfl) (hg.2 k)
  | Semiformula.exs χ, V, V', h, hg => by
      rw [Gated] at hg ⊢
      intro n
      exact Gated_mono hP (χ/[nm n]) (max V n) (max V' n)
        (max_le_max h le_rfl) (hg n)
termination_by φ _ _ _ _ => φ.complexity
decreasing_by
  all_goals simp [Semiformula.complexity_rew]

end GoodsteinPA.ReadoffValueGate
