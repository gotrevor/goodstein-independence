/-
# Path C — the arithmetized one-sided Tait Z∞ derivation (`ZInf`)

The lap-106 architectural finding (`NEXT_STEPS.md`): the inversion / cut-elimination META template
`Zinfty.{allInvAux,andInvAux,orInvAux,cutElim}` (`src/Zinfty.lean`) is **one-sided Tait** (`Deriv : Seq →
Type`, `Seq = Finset Form`, negation via `∼φ`), with mathlib `Ordinal` heights. To run that proof
structure V-internally — so the cut-elimination descent rides crux-1's PRWO(ε₀) — we arithmetize the
DERIVATION STRUCTURE here as `ZInf : V → Prop`, the one-sided Tait derivation over Finset-codes (a
sequence-code `Γ` of formula-codes, set semantics via `inAnt`/`seqCons`). The 9 constructors mirror
`Zinfty.Deriv` exactly. The `allω` ω-rule is strictly positive (the recursive `ZInf` sits only under
`∀ t, IsSemiterm … → ·`), so Lean accepts the inductive and gives a STRUCTURAL recursor including an IH
for the whole ω-premise family — the recursion vehicle the ported `allInvAux`/`cutElim` need.

This is the proof-STRUCTURE carrier; the ORDINAL carriers remain the two-sided engine codes
(`sord`/`iord`/`zCutOmega …` in `wip/PathCOmega.lean`). The leaf-blocker (`ZcDer.leaf` wraps an arbitrary
engine `ZDerivation`, not structurally invertible) is dissolved: `ZInf`'s leaves are genuinely atomic
(`axL`/`verumR`), every compound inference explicit (`andI`/`orI`/`exI`/`cut`/`allω`).

NOT imported by `GoodsteinPA.lean` — a `wip/` brick; verify with `lake env lean wip/PathCInf.lean`.
-/
import GoodsteinPA.InternalZ

namespace GoodsteinPA.InternalZ.PathCInf

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalZ

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Arithmetized one-sided Tait Z∞ derivation** (port of `Zinfty.Deriv`). The argument `Γ` is the Tait
sequent-code: a sequence-code of formula-codes, with membership `inAnt A Γ` (set semantics; multiplicity
absorbed by `weak`). The 9 constructors mirror `Zinfty.Deriv`'s `axL/axTrue/verumR/weak/andI/orI/allω/
exI/cut` (here `axL` covers the literal+negation axiom; `axTrue`/`verumR` the true-literal/⊤ axioms). The
ω-rule `allω` ranges over all closed terms `t` (the standard-model instances), strictly positive ⟹ Lean
accepts it with a full structural recursor. -/
inductive ZInf : V → Prop where
  | axL {Γ k r v : V} (hΓ : Seq Γ) (hp : inAnt (qqRel k r v) Γ) (hn : inAnt (qqNRel k r v) Γ) : ZInf Γ
  | verumR {Γ : V} (hΓ : Seq Γ) (h : inAnt (qqVerum : V) Γ) : ZInf Γ
  | weak {Δ Γ : V} (hΓ : Seq Γ) (d : ZInf Δ) (h : ∀ A, inAnt A Δ → inAnt A Γ) : ZInf Γ
  | andI {Γ φ ψ : V} (hΓ : Seq Γ) (dφ : ZInf (seqCons Γ φ)) (dψ : ZInf (seqCons Γ ψ)) :
      ZInf (seqCons Γ (qqAnd φ ψ))
  | orI {Γ φ ψ : V} (hΓ : Seq Γ) (d : ZInf (seqCons (seqCons Γ ψ) φ)) : ZInf (seqCons Γ (qqOr φ ψ))
  | allω {Γ φ : V} (hΓ : Seq Γ)
      (d : ∀ t, IsSemiterm ℒₒᵣ 0 t → ZInf (seqCons Γ (substs1 ℒₒᵣ t φ))) :
      ZInf (seqCons Γ (qqAll φ))
  | exI {Γ φ t : V} (hΓ : Seq Γ) (ht : IsSemiterm ℒₒᵣ 0 t)
      (d : ZInf (seqCons Γ (substs1 ℒₒᵣ t φ))) :
      ZInf (seqCons Γ (qqExs φ))
  | cut {Γ φ : V} (hΓ : Seq Γ) (d₁ : ZInf (seqCons Γ φ)) (d₂ : ZInf (seqCons Γ (neg ℒₒᵣ φ))) :
      ZInf Γ

/-- **Every `ZInf`-derivable conclusion is a well-formed `Seq`** (carried by each constructor; the
seqCons-conclusion nodes via `Seq.seqCons`). The membership bookkeeping (`inAnt_seqCons`) needs it. -/
theorem ZInf.seq {Γ : V} (d : ZInf Γ) : Seq Γ := by
  cases d with
  | axL hΓ => exact hΓ
  | verumR hΓ => exact hΓ
  | weak hΓ => exact hΓ
  | andI hΓ => exact hΓ.seqCons _
  | orI hΓ => exact hΓ.seqCons _
  | allω hΓ => exact hΓ.seqCons _
  | exI hΓ => exact hΓ.seqCons _
  | cut hΓ => exact hΓ

/-- **Weakening is admissible at the membership level** (the `weak` constructor, repackaged): if `Γ` is a
`Seq` and every formula of `Δ` occurs in `Γ`, a `ZInf Δ` lifts to `ZInf Γ`. The reusable monotonicity the
inversion recursion leans on (cf. `Zinfty`'s `Provable.weakening`). -/
theorem ZInf.weakening {Δ Γ : V} (hΓ : Seq Γ) (d : ZInf Δ) (h : ∀ A, inAnt A Δ → inAnt A Γ) : ZInf Γ :=
  .weak hΓ d h

/-! ### Membership bookkeeping for the inversion recursion -/

/-- `A` is in `Γ ⌢ A`. -/
theorem inAnt_seqCons_self {Γ A : V} (hΓ : Seq Γ) : inAnt A (seqCons Γ A) :=
  (inAnt_seqCons hΓ).mpr (Or.inl rfl)

/-- Membership is preserved by `seqCons`. -/
theorem inAnt_seqCons_of {Γ A B : V} (hΓ : Seq Γ) (h : inAnt A Γ) : inAnt A (seqCons Γ B) :=
  (inAnt_seqCons hΓ).mpr (Or.inr h)

/-- **`seqCons` commutes up to membership**: `Γ⌢A⌢B` and `Γ⌢B⌢A` have the same members. The reorder the
commuting inversion cases need (cf. `Zinfty.invPush1`/`invPull1`). -/
theorem inAnt_seqCons_comm {Γ A B C : V} (hΓ : Seq Γ) :
    inAnt C (seqCons (seqCons Γ A) B) ↔ inAnt C (seqCons (seqCons Γ B) A) := by
  rw [inAnt_seqCons (hΓ.seqCons A), inAnt_seqCons (hΓ.seqCons B),
    inAnt_seqCons hΓ, inAnt_seqCons hΓ]
  tauto

/-- A formula in `Γ ⌢ A` other than `A` itself is in `Γ`. -/
theorem inAnt_of_seqCons_ne {Γ A B : V} (hΓ : Seq Γ) (h : inAnt B (seqCons Γ A)) (hne : B ≠ A) :
    inAnt B Γ := ((inAnt_seqCons hΓ).mp h).resolve_left hne

/-! ### Structural weakening helpers (the reorder/insert moves of `allInvAux`) -/

/-- Add a formula at the top: `ZInf Γ → ZInf (Γ ⌢ A)`. -/
theorem ZInf.weaken_top {Γ A : V} (hΓ : Seq Γ) (d : ZInf Γ) : ZInf (seqCons Γ A) :=
  d.weakening (hΓ.seqCons A) (fun _ hC => inAnt_seqCons_of hΓ hC)

/-- Swap the top two formulas: `ZInf (Γ⌢A⌢B) → ZInf (Γ⌢B⌢A)`. -/
theorem ZInf.seqCons_comm {Γ A B : V} (hΓ : Seq Γ) (d : ZInf (seqCons (seqCons Γ A) B)) :
    ZInf (seqCons (seqCons Γ B) A) :=
  d.weakening ((hΓ.seqCons B).seqCons A) (fun _ hC => (inAnt_seqCons_comm hΓ).mp hC)

/-- Insert a formula `Y` just below the top: `ZInf (Γ⌢X) → ZInf (Γ⌢Y⌢X)`. -/
theorem ZInf.weaken_under {Γ X Y : V} (hΓ : Seq Γ) (d : ZInf (seqCons Γ X)) :
    ZInf (seqCons (seqCons Γ Y) X) :=
  d.weakening ((hΓ.seqCons Y).seqCons X) (fun C hC => by
    rcases (inAnt_seqCons hΓ).mp hC with rfl | hCΓ
    · exact inAnt_seqCons_self (hΓ.seqCons Y)
    · exact inAnt_seqCons_of (hΓ.seqCons Y) (inAnt_seqCons_of hΓ hCΓ))

/-! ### ∀-inversion (the port of `Zinfty.allInvAux` — the structural cut-elimination recursion)

The genuinely-deep core. From a `ZInf`-derivation of any sequent containing `^∀ φ`, for every closed
term `t` we extract a derivation of the SAME sequent with the instance `φ(t)` added. The recursion is
STRUCTURAL on `ZInf` (Lean's recursor, including the infinitary `allω` IH) — the V-internal port of the
mathlib `Zinfty.allInvAux`. Principal case (`allω` introducing exactly `^∀ φ`) = premise selection at `t`;
every other rule COMMUTES (recurse into premises, re-apply, reorder via the weakening helpers). This is the
re-principalization the lap-104 orbit-stall needs, now a closed structural recursion.

**STATUS (lap 106):** the recursion STRUCTURE is in place and the principal `allω` selection + the
atomic base cases are proven; the COMMUTING cases (`weak`/`andI`/`orI`/`exI`/`cut`/`allω`-side) carry a
disclosed `sorry` — their membership/permutation bookkeeping over `seqCons`-towers triggers pathological
HFS `whnf` under `induction` (timeout even at 1.6M heartbeats). The fix (next lap) is a cheap permutation
API: a single `ZInf.permCongr : (∀ A, inAnt A Γ ↔ inAnt A Δ) → ZInf Γ → ZInf Δ` proven ONCE standalone
(outside `induction`, where the helpers compile fast), so each commuting case is one `permCongr` call
with a `tauto`-closed membership `↔`. The math is the verbatim `allInvAux` port; only the term-mode
bookkeeping cost is open. -/
theorem ZInf.allInv {φ t : V} (ht : IsSemiterm ℒₒᵣ 0 t) :
    ∀ {Γ : V}, ZInf Γ → inAnt (qqAll φ) Γ → ZInf (seqCons Γ (substs1 ℒₒᵣ t φ)) := by
  intro Γ d
  induction d with
  | @axL Γ k r v hΓ hp hn =>
    intro _
    exact .axL (hΓ.seqCons _) (inAnt_seqCons_of hΓ hp) (inAnt_seqCons_of hΓ hn)
  | @verumR Γ hΓ h =>
    intro _
    exact .verumR (hΓ.seqCons _) (inAnt_seqCons_of hΓ h)
  | @weak Δ Γ hΓ d' h ih =>
    -- COMMUTING: weakening; split on whether `^∀ φ ∈ Δ`. (bookkeeping `sorry`, see status note)
    intro _; sorry
  | @andI Γ₀ φ' ψ' hΓ dφ dψ ihφ ihψ =>
    -- COMMUTING ∧: recurse into both conjunct premises, re-apply `andI`, reorder. (bookkeeping `sorry`)
    intro hmem
    have hne : (qqAll φ : V) ≠ qqAnd φ' ψ' := by intro H; simp [qqAll, qqAnd] at H
    have hmem0 : inAnt (qqAll φ) Γ₀ := inAnt_of_seqCons_ne hΓ hmem hne
    sorry
  | @orI Γ₀ φ' ψ' hΓ d' ih =>
    -- COMMUTING ∨: recurse into the premise, re-apply `orI`, reorder. (bookkeeping `sorry`)
    intro hmem
    have hne : (qqAll φ : V) ≠ qqOr φ' ψ' := by intro H; simp [qqAll, qqOr] at H
    have hmem0 : inAnt (qqAll φ) Γ₀ := inAnt_of_seqCons_ne hΓ hmem hne
    sorry
  | @allω Γ₀ φ' hΓ dprem ih =>
    intro hmem
    by_cases hφ : φ' = φ
    · -- PRINCIPAL: the last rule introduces exactly `^∀ φ`; select the premise at the inversion
      -- witness `t` (it derives the instance `φ(t)`) and re-insert `^∀ φ` below. PROVEN.
      subst hφ
      exact (dprem t ht).weaken_under hΓ
    · -- COMMUTING ∀ (a different matrix `φ' ≠ φ`): invert each ω-premise, re-apply `allω`. (`sorry`)
      have hne : (qqAll φ : V) ≠ qqAll φ' := fun H => hφ ((qqAll_inj _ _).mp H.symm)
      have hmem0 : inAnt (qqAll φ) Γ₀ := inAnt_of_seqCons_ne hΓ hmem hne
      sorry
  | @exI Γ₀ φ' t' hΓ ht' dprem ih =>
    -- COMMUTING ∃: invert the premise, re-apply `exI` at the same witness, reorder. (bookkeeping `sorry`)
    intro hmem
    have hne : (qqAll φ : V) ≠ qqExs φ' := by intro H; simp [qqAll, qqExs] at H
    have hmem0 : inAnt (qqAll φ) Γ₀ := inAnt_of_seqCons_ne hΓ hmem hne
    sorry
  | @cut Γ₀ φc hΓ d₁ d₂ ih₁ ih₂ =>
    -- COMMUTING cut: invert both cut premises, re-apply `cut`. (bookkeeping `sorry`)
    intro hmem; sorry

end GoodsteinPA.InternalZ.PathCInf

