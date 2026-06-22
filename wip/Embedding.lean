/-
# M4 — the embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` (Towsner §16 / Buchholz §5.5)

**The universal bottleneck of the whole expedition** (required on every route to the headline;
see `REFLECTION-2026-06-22.md`). This file is the lap-9 feasibility scaffold: it sets the embedding
up over Foundation's **`Derivation2`** (the Finset-sequent variant, `Calculus2.lean`), which lives
over the *same* `Finset (SyntacticFormula ℒₒᵣ)` substrate as M5's `ZinftyF.Seq` — so the embedding is
a pure rule-by-rule map with **no language translation**.

## API anchors (verified lap 9)
- `Schema ℒₒᵣ := Set (SyntacticFormula ℒₒᵣ)`; `(𝗣𝗔 : Theory) ↦ (𝗣𝗔 : Schema) = Rewriting.emb '' 𝗣𝗔`.
- `provable_def : T ⊢ σ ↔ (T : Schema) ⊢ ↑σ` (rfl) · `provable_iff_derivable2 : 𝓢 ⊢ φ ↔ 𝓢 ⊢!₂! φ`.
  ⟹ `𝗣𝗔 ⊢ goodsteinSentence` unfolds to `Nonempty (Derivation2 (𝗣𝗔:Schema) {↑goodsteinSentence})`.
- M5 target: `GoodsteinPA.ZinftyF.Deriv.Provable α c Γ` with constructors `axL/verumR/andI/orI/exI/
  allω/cut/weakening/mono/cast` (`src/Zinfty.lean:116–208`).

## Status of the cases (lap 9 — scaffold compiles, `lake env lean wip/Embedding.lean`)
- **DONE (structural, 5/10):** `verum`, `wk`, `or`, `and`, `cut` — pure rule map + cut-rank alignment,
  all typecheck against the real Foundation `Derivation2` + M5 `Provable` APIs (the rule-map is
  VALIDATED end-to-end). Only `embed` carries `sorry` (the 5 deep cases); no `axiom` declarations.
- **DISCLOSED `sorry` (the real content), hardest-first:**
  - `axm` — each PA axiom Z∞-derivable. `𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`: PeanoMinus is a
    finite set of true ∀-sentences (finite ordinal); `univCl (succInd ψ)` is derived **via the ω-rule**
    (`allω`) — THE deep case (Buchholz §5.5).
  - `all` — finitary `∀` (`free φ :: Γ.image shift`) → M5 ω-rule `allω`: substitute the free var by each
    numeral via Foundation's `Derivation.rewrite` (`Calculus.lean:255`), embed each premise.
  - `exs` — witness term `t` → numeral (term-model evaluation), then `exI`.
  - `closed` — general identity `φ, ∼φ ∈ Γ`: M5 `em` lemma, by induction on `φ.complexity` (finite).
  - `shift` — `Provable` invariance under `Rewriting.shift` (free-variable renaming).
-/
import GoodsteinPA.Zinfty
import Foundation.FirstOrder.Basic.Calculus2
import Foundation.FirstOrder.Arithmetic.Schemata

namespace GoodsteinPA.Embedding

open LO LO.FirstOrder GoodsteinPA.ZinftyF GoodsteinPA.ZinftyF.Deriv

/-- A `Z_∞`-derivable sequent, existentially quantified over the ordinal bound and cut rank
(Towsner states the whole embedding/cut-elim chain existentially in `(α, c)` — see
`ANALYSIS-…-cutelim-k-threading.md`). -/
def ZProvable (Γ : ZinftyF.Seq) : Prop := ∃ α c, Provable α c Γ

namespace ZProvable

theorem mono {Γ : ZinftyF.Seq} : ZProvable Γ → ZProvable Γ := id

/-- Weaken the sequent (Foundation `wk`). -/
theorem weakening {Γ Δ : ZinftyF.Seq} (h : Γ ⊆ Δ) : ZProvable Γ → ZProvable Δ := by
  rintro ⟨α, c, hd⟩; exact ⟨α, c, hd.weakening h⟩

/-- Drop a sequent element that already occurs (`insert X Γ = Γ` when `X ∈ Γ`). -/
theorem of_insert_mem {Γ : ZinftyF.Seq} {X : ZinftyF.Form} (h : X ∈ Γ) :
    ZProvable (insert X Γ) → ZProvable Γ := by
  rw [Finset.insert_eq_self.mpr h]; exact id

end ZProvable

/-- **The embedding (M4), Finset form.** Every Foundation `Derivation2` from the `𝗣𝗔` schema embeds
into the infinitary `Z_∞` calculus. Structural rules are mapped; the five non-structural cases
(`axm`/`all`/`exs`/`closed`/`shift`) are the disclosed deep obligations (see header). -/
theorem embed {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) : ZProvable Γ := by
  induction d with
  | closed Γ φ hp hn =>
    -- M5 `em`: derive `{φ, ∼φ}` by induction on `φ.complexity` (finite ordinal). DEEP (finite).
    sorry
  | axm φ hφ hΓ =>
    -- `φ ∈ (𝗣𝗔 : Schema)`, i.e. `φ = ↑σ`, `σ ∈ 𝗣𝗔⁻ + InductionScheme`. Each Z∞-derivable:
    --   PeanoMinus = finite true ∀-sentences; `univCl (succInd ψ)` via the ω-rule. THE deep case.
    sorry
  | verum hΓ =>
    exact ⟨0, 0, Provable.verumR hΓ⟩
  | @and Γ φ ψ h _dp _dq ihp ihq =>
    obtain ⟨a1, c1, h1⟩ := ihp
    obtain ⟨a2, c2, h2⟩ := ihq
    refine ⟨max a1 a2 + 1, max c1 c2, ?_⟩
    have h1' := h1.mono (le_refl a1) (le_max_left c1 c2)
    have h2' := h2.mono (le_refl a2) (le_max_right c1 c2)
    have hand := Provable.andI φ ψ h1' h2'
    rwa [Finset.insert_eq_self.mpr h] at hand
  | @or Γ φ ψ h _d ih =>
    obtain ⟨a, c, hd⟩ := ih
    refine ⟨a + 1, c, ?_⟩
    have hor := Provable.orI φ ψ hd
    rwa [Finset.insert_eq_self.mpr h] at hor
  | @all Γ φ h _d _ih =>
    -- finitary ∀ (`free φ :: Γ.image shift`) → M5 ω-rule `allω` via `Derivation.rewrite`. DEEP.
    sorry
  | @exs Γ φ h t _d _ih =>
    -- witness term `t` → numeral (term-model eval), then `exI`. DEEP.
    sorry
  | @wk Δ Γ _d h ih =>
    exact ih.weakening h
  | @shift Γ _d ih =>
    -- `Provable` invariance under `Rewriting.shift` (free-variable renaming). DEEP.
    sorry
  | @cut Γ φ _d _dn ihd ihdn =>
    obtain ⟨a1, c1, h1⟩ := ihd
    obtain ⟨a2, c2, h2⟩ := ihdn
    refine ⟨max a1 a2 + 1, max (φ.complexity + 1) (max c1 c2), ?_⟩
    have h1' := h1.mono (le_refl a1)
      (show c1 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_left c1 c2) (le_max_right _ _))
    have h2' := h2.mono (le_refl a2)
      (show c2 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_right c1 c2) (le_max_right _ _))
    have hc : ((φ.complexity + 1 : ℕ) : ℕ∞) ≤ ((max (φ.complexity + 1) (max c1 c2) : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.le_max_left _ _
    exact Provable.cut φ hc h1' h2'

end GoodsteinPA.Embedding
