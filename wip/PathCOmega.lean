/-
# wip/PathCOmega.lean — Path C, brick 1: the stored-ordinal ω-∀-node (lap 102→)

**Purpose (see `HANDOFF-2026-06-25-lap102.md`, `NEXT_STEPS.md` PRIORITY 1).** Probe 2 (lap 102,
`wip/InternalZomega.lean`) settled the crux-2 sub-route fork in favour of **Path C** (the ω-rule), with the
refinement that the ordinal layer must be REPLACED by **stored** ordinals (Buchholz operator-controlled
derivations), not the computed `iord` — because the induction ω-node's ordinal is a genuine limit
(`iotil_zK_iIndReduct_strictMono`) the finite-`#`-fold `iord` cannot assign.

This file begins the arithmetized stored-ordinal datatype. **Brick 1 = the ω-∀-node**, the cleanest case
(its premises are eigensubsts, ordinal-PRESERVING), where the stored ordinal can be taken to be the
existing finitary `zIall` node's own `iord` and the descent side-condition is the banked
`iord_descent_zIall`. This pins the Path-C node design in-kernel and shows the existing I∀ embedding
realizes it wholesale — the ∀-cut half of the `Zinfty.cutElimStep` analogue, on the existing engine.

NOT imported by `GoodsteinPA.lean` — a `wip/` brick; verify with `lake env lean wip/PathCOmega.lean`.

## Design (Buchholz §6 `Z*` / Towsner `ZinftyF.Deriv`, arithmetized)

An ω-∀-node is `zAllOmega s d0 a α` = `⟪s, 7, d0, a, α⟫ + 1` (tag 7): conclusion sequent `s = Γ→∀x F`,
premise generator `d0` (the eigenvariable premise deriving `Γ→F(a)`), eigenvariable `a`, **stored ordinal**
`α` (a CNF code). The premise family is `t ↦ zsubst d0 a t` (Buchholz `Z*`: `h[t] = h₀(x/t)`), materialized
on demand — never stored, so no `Fixpoint.StrongFinite` issue. **Validity** (`zAllOmegaValid`) asserts: the
premise family is uniformly valid AND every premise ordinal is `≺ α` (the stored side-condition — fully Σ₁,
NO sup/limit operation, the whole point of the stored design). A critical ∀-cut SELECTS premise `t` and the
reduction drops the ordinal below `α` for free (second validity conjunct). -/
import GoodsteinPA.Zsubst

namespace GoodsteinPA.InternalZ.PathC

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote
open GoodsteinPA.InternalZ

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **The Path-C stored-ordinal ω-∀-node** (tag 7). `s` conclusion `Γ→∀x F`, `d0` eigenvariable premise,
`a` eigenvariable, `α` the STORED ordinal. Premise-`t` = `zsubst d0 a t` (computed on demand). -/
noncomputable def zAllOmega (s d0 a α : V) : V := ⟪s, 7, d0, a, α⟫ + 1

/-- **Stored-ordinal ω-∀-node validity.** The premise family is uniformly valid (`ZDerivation` for every
closed `t`), and every premise ordinal is strictly below the stored ordinal `α`. The second conjunct is the
Buchholz operator-control side-condition — a bounded Σ₁ statement over the family, with NO ordinal-sup.
(The conclusion `_s` is carried for API/definability uniformity; the conclusion-TRACKING conjunct
`fstIdx (zsubst d0 a t) = seqSetSucc s (F t)` is the spike's `zOmegaPrem_concl`, added in a later brick
once the O3 freshness data is threaded — deferred here to keep brick 1 minimal.) -/
def zAllOmegaValid (_s d0 a α : V) : Prop :=
  (∀ t, IsSemiterm ℒₒᵣ 0 t → ZDerivation (zsubst d0 a t)) ∧
  (∀ t, IsSemiterm ℒₒᵣ 0 t → icmp (iord (zsubst d0 a t)) α = 0)

/-- **Brick 1 — a regular finitary `zIall` REALIZES the stored-ordinal ω-∀-node**, with the stored ordinal
taken to be the finitary node's own `iord`. The premise family is valid (`ZDerivation_zsubst_zIall_premise`,
freshness bound only), and each premise's ordinal `= iord d0 ≺ iord (zIall …)` (the banked
`iord_descent_zIall`, via `iord_zsubst`). So the existing I∀ embedding produces a valid Path-C ω-node for
free — the stored side-condition is exactly the banked descent, no new infrastructure. This is the ∀-cut
case of the `Zinfty.cutElimStep` ordinal drop, arithmetized on the existing engine. -/
theorem zIall_realizes_zAllOmegaValid {s a p d0 : V}
    (hZ : ZDerivation (zIall s a p d0)) (hreg : maxEigen d0 < a) :
    zAllOmegaValid s d0 a (iord (zIall s a p d0)) := by
  refine ⟨fun t ht => ZDerivation_zsubst_zIall_premise ht hZ hreg, fun t ht => ?_⟩
  rw [iord_zsubst ht.isUTerm (zDerivation_zIall_inv hZ).1 a]
  exact iord_descent_zIall s a p d0

/-- **The ω-∀-cut reduct descends below the stored ordinal — UNIFORMLY in the witness.** A critical ∀-cut
on `∀x F` with the ω-node on the R-side selects premise `zsubst d0 a t` (no new substitution); its ordinal
is `≺ α` directly from validity. This is the Path-C ∀-cut termination measure — the stored-ordinal analogue
of the spike's `iord_descent_zOmegaPrem`, now reading the side-condition off the node data rather than
recomputing. The full `cutElimStep` (all cut shapes) is brick 2 (`sorry` below). -/
theorem zAllOmega_cut_descends {s d0 a α t : V}
    (hvalid : zAllOmegaValid s d0 a α) (ht : IsSemiterm ℒₒᵣ 0 t) :
    icmp (iord (zsubst d0 a t)) α = 0 :=
  hvalid.2 t ht

/-- **The selected premise of an ω-∀-cut is a `ZDerivation` — for every witness.** The reduct-validity
half, read off the node data (no cut-elimination recursion). With `zAllOmega_cut_descends` this is the full
∀-cut invariant for Path C: validity-preserving AND ordinal-decreasing below the stored `α`. -/
theorem zAllOmega_cut_valid {s d0 a α t : V}
    (hvalid : zAllOmegaValid s d0 a α) (ht : IsSemiterm ℒₒᵣ 0 t) :
    ZDerivation (zsubst d0 a t) :=
  hvalid.1 t ht

/-! ## NEXT BRICKS (Path C, `sorry`-disclosed milestones — PENDING_WORK lap 102)

Brick 1 above pins the ω-∀-node design + its cut invariant on the existing engine. The remaining Path-C
datatype (each a `wip/` milestone, ported from `ZinftyF.Deriv`/`o`/`cr`):

- **Brick 2 — `cutElimStep` (the single rank drop).** The full Schütte/Tait reduction over all node shapes
  (`Zinfty.cutElimStep`/`cutElimPrincipal`, Towsner §19.7): a rank-`c+1` derivation reduces to rank-`c` with
  stored ordinal `α ↦ ω^α`. The ∀-cut case = brick 1; the ∧/∨/atom cases are the other `cutReduce*`.
- **Brick 3 — the induction ω-node.** Tag-7-style node whose premise family is the iterated step
  (`F(0),F(1),…`); its stored ordinal is the limit `ω^{õ d1 + 1} # ω^{õ d0}` (Probe 2), assigned as DATA
  with `∀k, o(premise k) ≺ stored`. The non-constant-ordinal case the computed `iord` can't do.
- **Brick 4 — `false_of_ZDerivesEmpty` (Path C).** `red` = one `cutElimStep`; the ∅→⊥ sequent has no
  cut-free proof, so `red` never terminates ⟹ the stored ordinal strictly descends forever ⟹ infinite
  ε₀-descent ⟹ contradicts PRWO(ε₀) (crux-1). No chain, no `redZKReady`.
- **Σ₁-definability** of `zAllOmega`/`zAllOmegaValid` (the `⟪…⟫`/`icmp`/`iord` pieces are all already
  `𝚺₁`/`𝚫₁`; this is bookkeeping, deferred until the datatype shape stabilizes). -/

end GoodsteinPA.InternalZ.PathC
