import GoodsteinPA.WainerGeneral

/-!
DRAFT (stage 3, for ratification) — the Paris–Harrington principle.

`PH e r k N`: every `r`-colouring of the `e`-element subsets of `{1, …, N}` has a homogeneous
`H ⊆ {1, …, N}` with `|H| ≥ k` that is *relatively large*: `|H| ≥ min H`.
(Paris–Harrington 1977; Wikipedia's formulation, with `S = {1, 2, …, N}`.)
-/

set_option linter.dupNamespace false

namespace GoodsteinPA.PH

open Finset

/-- **Relatively large**: the least element is at most the cardinality. -/
def RelLarge (H : Finset ℕ) : Prop := ∀ a ∈ H, (∀ b ∈ H, a ≤ b) → a ≤ H.card

/-- `H` is homogeneous for `c` on `e`-subsets: all `e`-subsets of `H` get one colour. -/
def Homog {N e r : ℕ} (c : (Icc 1 N).powersetCard e → Fin r) (H : Finset ℕ) : Prop :=
  ∃ i : Fin r, ∀ (s : Finset ℕ) (hs : s ∈ (Icc 1 N).powersetCard e), s ⊆ H → c ⟨s, hs⟩ = i

/-- **The Paris–Harrington property at `N`.** -/
def PH (e r k N : ℕ) : Prop :=
  ∀ c : (Icc 1 N).powersetCard e → Fin r,
    ∃ H ∈ (Icc 1 N).powerset, k ≤ H.card ∧ RelLarge H ∧ Homog c H

instance (e r k N : ℕ) : Decidable (PH e r k N) := by
  unfold PH RelLarge Homog; infer_instance

/-- The three parameters, packed into one input `x = ⟪e, ⟪r, k⟫⟫`. -/
def PHx (x N : ℕ) : Prop := PH x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2 N

-- Known-answer anchors (hand-computed): points (e = 1), two colours, a pair.
-- N = 2: colour 1 and 2 differently — no monochromatic pair.  N = 3: two of {1,2,3} share a
-- colour; any such pair {a,b} has min ≤ 2 = card.
example : ¬ PH 1 2 2 2 := by decide
example : PH 1 2 2 3 := by decide

section Headline
open LO LO.FirstOrder

/-- DRAFT headline: for every Σ₁ `φ` defining `PHx` pointwise in ℕ, PA does not prove
`∀ x, ∃ N, φ(x, N)`. -/
theorem pa_not_proves_ph
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (hdef : ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N) :
    𝗣𝗔 ⊬ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) := sorry

/-- DRAFT anti-vacuity: such a `φ` exists. -/
theorem exists_sigma1_ph_def :
    ∃ φ : Semisentence ℒₒᵣ 2, Arithmetic.Hierarchy 𝚺 1 φ ∧
      ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N := sorry

end Headline

/-- DRAFT truth (the positive theorem PA cannot prove), via infinite Ramsey + compactness. -/
theorem ph_true (e r k : ℕ) : ∃ N, PH e r k N := sorry

end GoodsteinPA.PH
