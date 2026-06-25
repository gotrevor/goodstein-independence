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
  | axL {Γ k r v : V} (hp : inAnt (qqRel k r v) Γ) (hn : inAnt (qqNRel k r v) Γ) : ZInf Γ
  | verumR {Γ : V} (h : inAnt (qqVerum : V) Γ) : ZInf Γ
  | weak {Δ Γ : V} (d : ZInf Δ) (h : ∀ A, inAnt A Δ → inAnt A Γ) : ZInf Γ
  | andI {Γ φ ψ : V} (dφ : ZInf (seqCons Γ φ)) (dψ : ZInf (seqCons Γ ψ)) :
      ZInf (seqCons Γ (qqAnd φ ψ))
  | orI {Γ φ ψ : V} (d : ZInf (seqCons (seqCons Γ ψ) φ)) : ZInf (seqCons Γ (qqOr φ ψ))
  | allω {Γ φ : V} (d : ∀ t, IsSemiterm ℒₒᵣ 0 t → ZInf (seqCons Γ (substs1 ℒₒᵣ t φ))) :
      ZInf (seqCons Γ (qqAll φ))
  | exI {Γ φ t : V} (ht : IsSemiterm ℒₒᵣ 0 t) (d : ZInf (seqCons Γ (substs1 ℒₒᵣ t φ))) :
      ZInf (seqCons Γ (qqExs φ))
  | cut {Γ φ : V} (d₁ : ZInf (seqCons Γ φ)) (d₂ : ZInf (seqCons Γ (neg ℒₒᵣ φ))) : ZInf Γ

/-- **Weakening is admissible at the membership level** (the `weak` constructor, repackaged): if every
formula of `Δ` occurs in `Γ`, a `ZInf Δ` lifts to `ZInf Γ`. The reusable monotonicity the inversion
recursion leans on (cf. `Zinfty`'s `Provable.weakening`). -/
theorem ZInf.weakening {Δ Γ : V} (d : ZInf Δ) (h : ∀ A, inAnt A Δ → inAnt A Γ) : ZInf Γ :=
  .weak d h

end GoodsteinPA.InternalZ.PathCInf
