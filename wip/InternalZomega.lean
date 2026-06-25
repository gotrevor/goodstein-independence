/-
# wip/InternalZomega.lean — the ω-rule de-risk SPIKE (lap 101 reflection PRIORITY 1)

**Purpose (see `REFLECTION-2026-06-25-lap101.md`, `NEXT_STEPS.md`).** Settle the finitary-vs-ω-rule
sub-route fork with EVIDENCE, not conviction. The lap-92 reflection recommended pivoting crux-2's
internalized cut-elimination from Buchholz's *finitary eigenvariable* system to the *infinitary ω-rule*
system (`Z^∞`), arguing it dissolves O1 (freshness), O2 (eigen-subst), AND the route-B `tpReduce`
conclusion-tracking motive (`redZKReady`) at once, because a critical ∀-cut SELECTS the premise `dₜ`
(already deriving `Γ→F(t)`) rather than substituting. Lap-95 overruled to the finitary Path X **without
running the spike lap-92 said to run first.** This file runs it.

NOT imported by `GoodsteinPA.lean` — a self-contained probe; it cannot affect the green gate. Verify with
`lake env lean wip/InternalZomega.lean`.

## What this spike DEMONSTRATES (in-kernel, axiom-clean)

The decisive dissolution claim, made concrete on the EXISTING machinery: **the ω-rule premise family is
already materializable from a finitary I∀ node, and its validity is discharged purely by the
construction-time freshness bound `maxEigen d0 < a` (= `ZRegular`, which `red` already maintains) — with NO
criticality / conclusion-tracking motive.** A critical ∀-cut's reduct is the SELECTION `zOmegaPrem d0 a t`,
whose validity is `zOmegaPrem_valid` (a hypothesis-level fact about a well-formed ∀-node), NOT an obligation
discharged inside the cut-elimination recursion. Contrast the finitary K-case, whose validity needs the
`redZKReady` hereditary-all-Rep motive (`Crux2Blueprint.redSoundGen`'s open `sorry`).

**Where the substitution-validity work goes under the ω-rule view:** to NODE-CONSTRUCTION time (proving the
premise family `∀ t, ZDerivation (zsubst d0 a t)` once, with the clean freshness bound), NOT into the
cut-elimination recursion. That decoupling is exactly why the conclusion-tracking motive evaporates: the
selected premise's conclusion `Γ→F(t)` is COMPUTED (`zOmegaPrem_concl`), never threaded.

## The arithmetization-risk probe (the genuine unknown — see the sorried statements at the bottom)

The remaining Path-C question is whether the ω-rule *cut-elimination* — recursion on the ordinal height
`iord`, selecting premises from infinite families — arithmetizes in IΣ₁ without its own wall. The premise
family here is materialized on demand by `zsubst` (Buchholz §6 `Z*`: `h[t] = h₀(x/t)`), so premise access
is Σ₁; the open question is `iord` assignment to an ω-node + the cut-reduction recursion. Stated below as
the next obligations.
-/
import GoodsteinPA.Zsubst

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## The ω-rule premise family, materialized from a finitary I∀ node

The finitary I∀ node `zIall s a p d0` packages a single eigenvariable premise `d0 ⊢ Γ→F(a)`. Its ω-rule
view is the premise family indexed by closed terms `t`: premise-`t` = `zsubst d0 a t ⊢ Γ→F(t)`. This is
exactly Buchholz §6 `Z*` (`h[t] = h₀(x/t)`): a finite code (`d0`) with premise-`t` computed on demand. -/

/-- **The `t`-th ω-rule premise** generated from the I∀ premise `d0` with eigenvariable `a`: substitute the
closed term `t` for `a`. The whole ω-rule premise family is `t ↦ zOmegaPrem d0 a t`. -/
noncomputable def zOmegaPrem (d0 a t : V) : V := zsubst d0 a t

/-- **The ω-rule ∀-cut reduct is VALIDITY-FREE (the Path-C dissolution, concrete).** Every premise of the
ω-rule family generated from a valid I∀ node is a `ZDerivation`, discharged PURELY by the construction-time
freshness bound `maxEigen d0 < a` — NO criticality, NO conclusion-tracking motive. A critical ∀-cut on
`∀x F` SELECTS `zOmegaPrem d0 a t` (the premise for the cut witness `t`); its validity is THIS lemma, a
hypothesis-level fact about the well-formed ∀-node — not an obligation inside the cut-elimination recursion.
This is the in-kernel evidence that the ω-rule presentation retires the `redZKReady` wall. -/
theorem zOmegaPrem_valid {s a p d0 t : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hZ : ZDerivation (zIall s a p d0)) (hfresh : maxEigen d0 < a) :
    ZDerivation (zOmegaPrem d0 a t) :=
  ZDerivation_zsubst_zIall_premise ht hZ hfresh

/-- **The selected premise's conclusion is COMPUTED, never threaded (conclusion-tracking automatic).**
`zOmegaPrem d0 a t` derives exactly `Γ→F(t)` (`= seqSetSucc s (substs1 t p)`), given the eigenvariable `a`
is fresh in the matrix `p` (`hpfresh`) and the antecedent `Γ = seqAnt s` (`hΓfresh`) — Buchholz's
eigenvariable side condition, supplied at the I∀ node, NOT re-discharged per cut. The finitary route's
`tpReduce` conclusion-reduction + the `redZKReady` hereditary-Rep motive exist only to recover THIS
equation through the chain machinery; under the ω-rule view it is a direct computation. Generalizes
`red_zIall_tpReduce` (its `t = 0` instance) to the whole premise family. -/
theorem zOmegaPrem_concl {s a p d0 t : V} (hZ : ZDerivation (zIall s a p d0))
    (hpfresh : fvSubst ℒₒᵣ a t p = p)
    (hΓfresh : fvSubstSeq a t (seqAnt s) = seqAnt s)
    (ht : IsSemiterm ℒₒᵣ 0 t) :
    fstIdx (zOmegaPrem d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p) := by
  obtain ⟨hd0, _, hwff⟩ := zDerivation_zIall_inv hZ
  have hfa : IsSemiterm ℒₒᵣ 0 (^&a : V) := by simp
  rw [zOmegaPrem, fstIdx_zsubst _ _ hd0]
  simp only [fvSubstSeqt, seqSetSucc, hwff.1, hwff.2.1, hΓfresh,
    fvSubst_substs1 ht hfa hwff.2.2, termFvSubst_fvar_self, hpfresh]

/-! ## The remaining Path-C obligations (the genuine arithmetization-risk probe — OPEN)

These are the next-lap targets if the spike's evidence justifies the pivot. They are the questions the
finitary route never had to answer (it has no ω-node) and the ω-route must:

1. **`iord` assignment to an ω-node.** The ω-rule ∀-node's ordinal height is `sup_t (iord (premise t)) + 1`
   (a sup over the infinite family). Does the repo's `iord`/ω-tower engine assign an ordinal to an ω-node
   from its premise-family code? (The engine has `sup`/successor; the open question is the sup over a
   `zsubst`-generated family.) This is the SHARPEST arithmetization-risk probe — if `iord` is not
   assignable, that is the Path-C wall and justifies committing to Path X.

2. **The ω-rule cut-elimination step, substitution-free.** A cut with R-premise an ω-node `∀x F` and
   L-premise its dual reduces to a cut on `F(t)` against `zOmegaPrem d0 a t` (premise selection) — the
   Schütte/Tait reduction, as `Zinfty.lean` does it at the META level. The arithmetized version recurses on
   `iord`; the validity of the selected premise is `zOmegaPrem_valid` (already discharged above), so the
   reduction itself introduces NO new substitution-validity obligation.

**NEXT-LAP TARGET (Probe 1, the sharpest arithmetization-risk question):** build an `iord`-height
assignment for the ω-rule ∀-node, `iord(zAllω) = sup_t (iord (zOmegaPrem d0 a t)) + 1`, from the
premise-family code `d0`. The repo's `iord`/ω-tower engine has `sup`/successor; the open question is the
sup over a `zsubst`-generated family. If unbuildable → Path X is the forced route (commit with that
evidence). If buildable → the pivot is justified; proceed to the ω-rule cut-elimination step (Probe 2,
recursion on `iord`, premise selection à la `Zinfty.lean`).
-/

end GoodsteinPA.InternalZ
