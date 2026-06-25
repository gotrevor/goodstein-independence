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

/-! ### Brick 1, completed — conclusion-TRACKING (the deferred `zAllOmegaValid` conjunct)

The minimal `zAllOmegaValid` dropped conclusion-tracking. Here it is, with the eigenvariable side-condition
O3 supplied explicitly (the embedding's fresh-eigenvariable choice gives it). The full validity predicate
`zAllOmegaValidFull` is the complete Path-C ω-∀-node datum: premise family valid + conclusion-tracked +
ordinal-bounded by the stored `α` — and a regular finitary `zIall` realizes ALL THREE. -/

/-- **Conclusion-tracking for the ω-∀-node premise.** Premise-`t` derives exactly `Γ→F(t)`
(`= seqSetSucc s (substs1 t p)`), given the O3 eigenvariable side-condition (`a` substitution-invariant in
the matrix `p` and antecedent `Γ`) — Buchholz's condition supplied at the I∀ node, NOT re-discharged per
cut. The reduct's conclusion is COMPUTED, never threaded through a motive (the contrast with the finitary
`tpReduce`/`redZKReady` machinery). -/
theorem zAllOmega_concl {s a p d0 t : V} (hZ : ZDerivation (zIall s a p d0))
    (hpfresh : fvSubst ℒₒᵣ a t p = p)
    (hΓfresh : fvSubstSeq a t (seqAnt s) = seqAnt s)
    (ht : IsSemiterm ℒₒᵣ 0 t) :
    fstIdx (zsubst d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p) := by
  obtain ⟨hd0, _, hwff⟩ := zDerivation_zIall_inv hZ
  have hfa : IsSemiterm ℒₒᵣ 0 (^&a : V) := by simp
  rw [fstIdx_zsubst _ _ hd0]
  simp only [fvSubstSeqt, seqSetSucc, hwff.1, hwff.2.1, hΓfresh,
    fvSubst_substs1 ht hfa hwff.2.2, termFvSubst_fvar_self, hpfresh]

/-- **Full Path-C ω-∀-node validity** — the complete node datum: premise family uniformly valid AND
conclusion-tracked (`Γ→F(t)`) AND every premise ordinal `≺ α`. -/
def zAllOmegaValidFull (s p d0 a α : V) : Prop :=
  (∀ t, IsSemiterm ℒₒᵣ 0 t → ZDerivation (zsubst d0 a t)) ∧
  (∀ t, IsSemiterm ℒₒᵣ 0 t → fstIdx (zsubst d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p)) ∧
  (∀ t, IsSemiterm ℒₒᵣ 0 t → icmp (iord (zsubst d0 a t)) α = 0)

/-- **Brick 1 capstone — a regular finitary `zIall` realizes the FULL Path-C ω-∀-node** (all three
conjuncts), with stored ordinal = the node's own `iord`. The existing I∀ embedding produces a complete,
valid Path-C ω-node — validity (`ZDerivation_zsubst_zIall_premise`), conclusion (`zAllOmega_concl`), and the
stored-ordinal side-condition (`iord_descent_zIall`), all from banked lemmas + the embedding's O3 data. -/
theorem zIall_realizes_zAllOmegaValidFull {s a p d0 : V}
    (hZ : ZDerivation (zIall s a p d0)) (hreg : maxEigen d0 < a)
    (hO3p : ∀ t, IsSemiterm ℒₒᵣ 0 t → fvSubst ℒₒᵣ a t p = p)
    (hO3Γ : ∀ t, IsSemiterm ℒₒᵣ 0 t → fvSubstSeq a t (seqAnt s) = seqAnt s) :
    zAllOmegaValidFull s p d0 a (iord (zIall s a p d0)) := by
  refine ⟨fun t ht => ZDerivation_zsubst_zIall_premise ht hZ hreg,
    fun t ht => zAllOmega_concl hZ (hO3p t ht) (hO3Γ t ht) ht,
    fun t ht => ?_⟩
  rw [iord_zsubst ht.isUTerm (zDerivation_zIall_inv hZ).1 a]
  exact iord_descent_zIall s a p d0

/-! ## Brick 3 kernel — the INDUCTION ω-node's stored ordinal (the limit case)

Probe 2 (`wip/InternalZomega.lean`) showed the induction ω-node's premise ordinals strictly increase in
the unfolding depth, so its ordinal is a genuine LIMIT the computed `iord` cannot reach. The stored design
sidesteps this: assign the node a FIXED ordinal `α` that provably dominates the whole premise family, and
require `∀k, o(premise k) ≺ α` as data. Here we DISCHARGE that side-condition in-kernel — the limit is
assignable as a fixed code and dominates every finite unfolding. -/

/-- **The induction ω-node's stored ordinal** = `ω_{dg}(ω^{õ d1 + 1} # ω^{õ d0})`, where `dg = idg (zInd s
at' p d0 d1)` is the unfolding's (k-independent) degree. The õ-part is the `k→∞` limit of the depth-`k`
unfolding's õ `ω^{õ d1}·k # ω^{õ d0}` (Probe 2) — the smallest CNF code dominating the whole family. -/
noncomputable def indOmegaStoredOrd (s at' p d0 d1 : V) : V :=
  iotower (inadd (ocOadd (iadd (iotil d1) (ocOadd 0 1 0)) 1 0) (ocOadd (iotil d0) 1 0))
    (idg (zInd s at' p d0 d1))

/-- **Brick 3 kernel — the stored ordinal BOUNDS every induction premise (iord level), uniformly in `k`.**
For NF premise õs, the depth-`k` unfolding's ordinal `iord (zK s' (irk p) (iIndReductSeq d0 d1 k)) ≺
indOmegaStoredOrd …` for ALL `k > 0`. Proof: the degree is constant (`idg_zK_iIndReduct`), so the
comparison lifts (`icmp_iotower_mono`) from the õ-bound `ω^{õ d1}·k # ω^{õ d0} ≺ ω^{õ d1 + 1} # ω^{õ d0}`,
which is `inadd_right_mono` applied to the banked `icmp_term_lt_omega_succ` (`ω^β·k ≺ ω^{β+1}`, all finite
`k`). This is the Buchholz operator-control side-condition for the induction ω-node, DISCHARGED — the limit
Probe 2 showed `iord` can't compute, assigned as a fixed code that provably dominates the family.

**Carrier note (design honesty).** The premise here is the FINITARY unfolding `zK … (iIndReductSeq …)`,
which under the true ω-rule (Towsner `ZinftyF.Deriv`) would be a cut-TREE deriving `F(k)`, not a Buchholz
K-chain. So this exact node is NOT the final Path-C induction node — but the ORDINAL fact IS path-portable:
Buchholz combines cut-premise ordinals by the same `#`-natural-sum, so a cut-tree unfolding of depth `k`
carries the same õ `ω^{õd1}·k # ω^{õd0}`, dominated by the same limit. This lemma stands as (i) Probe-2
evidence that the limit is the right stored ordinal, and (ii) a reusable ordinal bound for the eventual
cut-tree node. -/
theorem iord_iIndReduct_lt_storedBound {s s' at' p d0 d1 k : V} (hk : 0 < k)
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    icmp (iord (zK s' (irk p) (iIndReductSeq d0 d1 k)))
      (indOmegaStoredOrd s at' p d0 d1) = 0 := by
  rw [indOmegaStoredOrd, iord, iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 k),
      iseqNaddIdg_iIndReductSeq hk, idg_zK_iIndReduct (s := s) (s' := s') (at' := at') hk]
  exact icmp_iotower_mono
    (inadd_right_mono
      ((isNF_ocOadd _ _ _).mpr ⟨hk.ne', hd1, isNF_zero, Or.inl rfl⟩)
      ((isNF_ocOadd _ _ _).mpr ⟨(by simp), isNF_iadd_one_right hd1, isNF_zero, Or.inl rfl⟩)
      (icmp_term_lt_omega_succ (iotil d1) k)
      (ocOadd (iotil d0) 1 0) (isNF_omega_pow hd0))
    (idg (zInd s at' p d0 d1))

/-! ## NEXT BRICKS (Path C, `sorry`-disclosed milestones — PENDING_WORK lap 102)

Brick 1 above pins the ω-∀-node design + its cut invariant on the existing engine. The remaining Path-C
datatype (each a `wip/` milestone, ported from `ZinftyF.Deriv`/`o`/`cr`):

- **Brick 2 — `cutElimStep` (the single rank drop).** The full Schütte/Tait reduction over all node shapes
  (`Zinfty.cutElimStep`/`cutElimPrincipal`, Towsner §19.7): a rank-`c+1` derivation reduces to rank-`c` with
  stored ordinal `α ↦ ω^α`. The ∀-cut case = brick 1; the ∧/∨/atom cases are the other `cutReduce*`.
- **Brick 3 — the induction ω-node.** Kernel DONE above (`indOmegaStoredOrd` + `iord_iIndReduct_lt_storedBound`):
  the stored limit ordinal provably dominates every finite unfolding's `iord`, uniformly in `k`. Remaining:
  package it as a node + validity (premise-family `ZDerivation`s via `znth_iIndReductSeq_ZDerivation`, the
  conclusion-tracking `F(k)`, the Σ₁ side-condition), mirroring `zAllOmega`/`zAllOmegaValid`.
- **Brick 4 — `false_of_ZDerivesEmpty` (Path C).** `red` = one `cutElimStep`; the ∅→⊥ sequent has no
  cut-free proof, so `red` never terminates ⟹ the stored ordinal strictly descends forever ⟹ infinite
  ε₀-descent ⟹ contradicts PRWO(ε₀) (crux-1). No chain, no `redZKReady`.
- **Σ₁-definability** of `zAllOmega`/`zAllOmegaValid` (the `⟪…⟫`/`icmp`/`iord` pieces are all already
  `𝚺₁`/`𝚫₁`; this is bookkeeping, deferred until the datatype shape stabilizes). -/

end GoodsteinPA.InternalZ.PathC
