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

/-! ### ∀-inversion — and the lap-107 finding that THIS statement is VACUOUS

⚠️ **LAP-107 COURSE-CORRECTION (kernel-verified).** The statement below — `ZInf Γ → inAnt (^∀φ) Γ →
ZInf (seqCons Γ (φ(t)))` — is **VACUOUS**: it is provable by a SINGLE weakening (`ZInf.weaken_top d.seq d`),
using neither `ht` (that `t` is a closed term) NOR the `^∀φ ∈ Γ` hypothesis. Verified in-kernel by
replacing the whole 40-line `induction` with `exact ZInf.weaken_top d.seq d` (lean accepts; only an
"`ht` unused" linter warning fires). So the lap-106 "principal case proven" + the six commuting `sorry`s
were elaborate work on a content-free lemma, and the planned `permCongr` perf fix would polish nothing.

**Why vacuous — the two missing pieces of `Zinfty.allInvAux`.** The META `allInvAux` (`src/Zinfty.lean:429`)
concludes `Provable (o d) c (insert (χ/[nm n]) (Γ.erase (∀⁰χ)))`. Its ENTIRE content is (1) **ordinal
preservation** — same bound `o d`, same cut rank `c`; and (2) **erasure** — `∀⁰χ` is REMOVED, `χ(t)` added.
`ZInf : V → Prop` carries **no ordinal index**, and this statement **keeps `^∀φ`** (output `seqCons Γ φ(t)`
⊇ `Γ`). With `^∀φ` retained and no ordinal to preserve, the conclusion is just a weakening of `Γ` — trivial.

**Consequence (see `NEXT_STEPS.md` lap-107).** Cut-elimination IS an argument about ORDINALS; a carrier
with no ordinal cannot express it. `ZInf` is therefore a DEAD carrier for crux-2. More fundamentally, every
EXTERNAL Lean inductive (`ZInf`/`ZcOK`/`ZcDer`) is non-load-bearing for the headline: the headline needs
`IΣ₁ ⊢ Con(PA)`, i.e. the descent must hold in EVERY `V ⊧ IΣ₁`, including non-standard models whose coded
⊥-proof `z` is non-standard — and no external (well-founded) inductive tree exists for a non-standard `z`,
so `foundation_bot_to_Z_empty` is unprovable for such `z`. The load-bearing carrier is the Σ₁ CODE engine
`red`/`iord` (`InternalZ.lean`), which is already arithmetized and works on non-standard codes. The real
obstruction is that engine `red` (= `iRNextG`) dispatches ONLY on the conclusion's top `zTag`, so after one
K/cut reduction the reduct's top is no longer a cut and `red` stalls (lap-104) — `iord_descent_red` is
therefore unprovable for the current `red`. FIX = redesign `red` to locate the relevant redex anywhere in
the derivation (Gentzen's reduction), with a provable `iord` descent. `ZInf` stays only as a combinatorial
sketch of the inversion cases. -/
theorem ZInf.allInv_vacuous {φ t : V} (ht : IsSemiterm ℒₒᵣ 0 t) :
    ∀ {Γ : V}, ZInf Γ → inAnt (qqAll φ) Γ → ZInf (seqCons Γ (substs1 ℒₒᵣ t φ)) := by
  -- VACUOUS: pure weakening — adds `φ(t)` without erasing `^∀φ`, and `ZInf` tracks no ordinal.
  intro Γ d _; exact ZInf.weaken_top d.seq d

end GoodsteinPA.InternalZ.PathCInf

