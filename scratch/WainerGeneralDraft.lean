import GoodsteinPA.WainerBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic ONote

namespace GoodsteinPA.Wainer

/-- DRAFT for ratification.  **Wainer's bound (upper half of the classification).**  If PA proves a
Π₂ sentence `∀ m, ∃ N, φ(m, N)` with `φ` a Σ₁ formula, then some single `f_o`, `o < ε₀` (as a
normal-form `ONote`), eventually bounds a witness: for all large `m` there is `N ≤ f_o(m)` with
`φ(m, N)` true in ℕ.  Bound variables: `#0 = N`, `#1 = m`. -/
theorem pa_provable_pi2_eventually_witnessed_below_fastGrowing
    (φ : Semisentence ℒₒᵣ 2) (hφ : Hierarchy 𝚺 1 φ)
    (h : 𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ)) :
    ∃ o : ONote, o.NF ∧ ∃ M : ℕ, ∀ m, M ≤ m →
      ∃ N ≤ fastGrowing o m, ℕ ⊧/![N, m] φ := by
  sorry

end GoodsteinPA.Wainer
