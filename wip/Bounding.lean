/-
# M7 — the bounding bridge + assembly (Route B)

Joins M4 (embedding `embedC`, DONE), M5 (ε₀ cut-elimination `Provable.cutElim`, DONE) and M6
(Hardy lower bound `lowerBound_hardy_selfcontained`, DONE) into the headline
`𝗣𝗔 ⊬ ↑goodsteinSentence`.

## The shape of the argument (Towsner Route B)
`↑goodsteinSentence = ↑(∀⁰ code)` is a TRUE closed Π₂ sentence (`∀m ∃N, code(m,N)`), so it *does*
have a cut-free `Z∞` derivation (ω-completeness `provable_true`) — the contradiction is **not**
"no cut-free proof", it is the **ordinal bound**:
- A finite `𝗣𝗔` proof embeds (`embedC`) to a `Z∞` derivation of ordinal `< ε₀`  ⟦**B1**, sorry⟧.
- Cut-elimination keeps it `< ε₀` (`Provable.cutElim` + `omegaTower_lt_epsilon0`).
- A cut-free derivation of `{∀m ∃N code}` of ordinal `α < ε₀` bounds the witness `N` by a Hardy
  function `H_α` (∀-inversion `allInv` per numeral `m`, then the cut-free ∃-witness bound) — but the
  true witness is the Goodstein length `G(m)`, and `H_α(m) < G(m)` eventually for `α < ε₀`
  (M6 `hardy_lt_goodsteinLength`). Contradiction.  ⟦**B2–B5**, packaged as `cutfree_lt_eps0_absurd`⟧.

## Decomposition of the remaining obligations (see PENDING_WORK)
- **B1** `embed_lt_eps0` — `embedC` with the ordinal bounded by `ε₀` (track the ordinal through the
  structural induction; `provable_true` of each PA axiom has small ordinal; the `allω` sups stay
  `< ε₀`).
- **B2** cut-free ∀/∃ witness bound on the real `Deriv` (Towsner's boundedness lemma).
- **B3** arithmetization: the Σ₁ `codeOfREPred` matrix ↔ `atomTrue`/Goodstein (M7a).
- **B4** ordinal seam: mathlib `Ordinal < ε₀` ↔ `ONote` NF.
- **B5** final assembly vs `lowerBound_hardy_selfcontained`.
-/
import GoodsteinPA.Embedding
import GoodsteinPA.LowerBound
import GoodsteinPA.Encoding

namespace GoodsteinPA.Bounding

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open GoodsteinPA.ZinftyF GoodsteinPA.ZinftyF.Deriv GoodsteinPA.Embedding

open scoped Ordinal

/-- The encoded Goodstein sentence is closed, so any closing substitution `asg e` fixes it. -/
lemma asg_goodsteinSentence (e : ℕ → ℕ) :
    asg e ▹ (↑goodsteinSentence : SyntacticFormula ℒₒᵣ)
      = (↑goodsteinSentence : SyntacticFormula ℒₒᵣ) := by
  apply Semiformula.rew_eq_self_of
  · exact fun x => x.elim0
  · intro x hx; simp [Semiformula.FVar?] at hx

/-- **B1 (disclosed).** The embedding of a finite `𝗣𝗔` proof lands at a `Z∞` ordinal `< ε₀`. -/
theorem embed_lt_eps0 {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) :
    ∃ c : ℕ, ∀ e : ℕ → ℕ, ∃ α, α < ε₀ ∧ Provable α c (Γ.image (fun φ => asg e ▹ φ)) := by
  sorry

/-- **The bridge (B2–B5, disclosed).** No cut-free `Z∞` derivation of the encoded Goodstein
sentence has ordinal `< ε₀`: such a bound would dominate the Goodstein length, contradicting
`lowerBound_hardy_selfcontained` (M6). -/
theorem cutfree_lt_eps0_absurd :
    ¬ ∃ α, α < ε₀ ∧ Provable α 0 {(↑goodsteinSentence : SyntacticFormula ℒₒᵣ)} := by
  sorry

/-- **Assembly (Route B).** The headline reduces to `embed_lt_eps0` (B1) + `cutfree_lt_eps0_absurd`
(the bridge) via `Provable.cutElim` + `omegaTower_lt_epsilon0`. This proof is COMPLETE modulo those
two disclosed obligations — it isolates exactly the remaining gap. -/
theorem peano_not_proves_goodstein_routeB : 𝗣𝗔 ⊬ ↑goodsteinSentence := by
  intro h
  have h2 : (↑(𝗣𝗔 : ArithmeticTheory) : Schema ℒₒᵣ) ⊢ (↑goodsteinSentence : SyntacticFormula ℒₒᵣ) :=
    provable_def.mp h
  have h3 : (↑(𝗣𝗔 : ArithmeticTheory) : Schema ℒₒᵣ) ⊢!₂! (↑goodsteinSentence : SyntacticFormula ℒₒᵣ) :=
    (@provable_iff_derivable2 ℒₒᵣ _ _ _).mp h2
  obtain ⟨d2⟩ := h3
  obtain ⟨c, hc⟩ := embed_lt_eps0 d2
  obtain ⟨α, hαlt, hα⟩ := hc (fun _ => 0)
  rw [show ({(↑goodsteinSentence : SyntacticFormula ℒₒᵣ)} : Finset _).image
        (fun φ => asg (fun _ => 0) ▹ φ) = {(↑goodsteinSentence : SyntacticFormula ℒₒᵣ)} by
      simp [asg_goodsteinSentence]] at hα
  exact cutfree_lt_eps0_absurd
    ⟨omegaTower c α, omegaTower_lt_epsilon0 c hαlt, Provable.cutElim hα⟩

end GoodsteinPA.Bounding
