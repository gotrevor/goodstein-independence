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

## The arithmetization-risk probe — substantially RETIRED this lap (see Probe 1, bottom)

The lap-92 reflection named the riskiest unknown as "premise-`t` as a Σ₁ recursive notation + cut-elimination
recursion on `iord`, selecting premises from infinite families." This spike retires the two hardest pieces
in-kernel: the premise family is materialized on demand by `zsubst` (Buchholz §6 `Z*`: `h[t] = h₀(x/t)`), so
premise access is Σ₁ (`zOmegaPrem`); its validity is motive-free (`zOmegaPrem_valid`); and the premise-family
ordinal is CONSTANT `= iord d0` (`iord_zOmegaPrem_constant`), so the ω-node's `iord` is the finite `iord d0 +
1` — no sup-over-infinite-family primitive. The single remaining open piece is the ω-rule cut-elimination
STEP itself (Probe 2, bottom), which needs the ω-node datatype + Fixpoint extension (the templated rebuild).
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

/-! ## Probe 1 — `iord` for the ω-node: the premise-family ordinal is CONSTANT (risk DISSOLVED)

The lap-92 reflection named "premise-`n` as a Σ₁ recursive notation + cut-elimination recursion on `iord`"
as the riskiest unprobed assumption. For the `iord` half it dissolves cleanly: the eigensubst already
preserves the ordinal (`iord_zsubst`, proven axiom-clean), so the ω-node's premise family `t ↦ zOmegaPrem
d0 a t` has CONSTANT ordinal `iord d0`. Hence the would-be `sup_t (iord (premise t))` is the sup of a
constant family `= iord d0` — NO sup over an infinite family is needed; `iord(zAllω) := iord d0 + 1` is a
FINITE, computable ordinal assignment built with the existing `iord` engine, no new primitive. -/

/-- **Every ω-rule premise has the SAME ordinal `iord d0`.** The eigensubst `zsubst d0 a t` preserves
`iord` (`iord_zsubst`), so the premise-family ordinal is constant in the index `t`. -/
theorem iord_zOmegaPrem {d0 a t : V} (ht : IsUTerm ℒₒᵣ t) (hZ : ZDerivation d0) :
    iord (zOmegaPrem d0 a t) = iord d0 := by
  rw [zOmegaPrem]; exact iord_zsubst ht hZ a

/-- **Probe 1 RESOLVED (the arithmetization-risk de-risk).** The ω-node's ordinal is `iord d0 + 1` — a
FINITE successor of the single I∀-premise ordinal, NOT a sup over an infinite premise family. Concretely:
for any two closed terms `t₁ t₂`, the premises `zOmegaPrem d0 a t₁` and `zOmegaPrem d0 a t₂` have EQUAL
ordinal, so the family's supremum is just `iord d0`. The "sup over an infinite family" that looked like the
Path-C wall does not arise; the existing `iord`/ω-tower engine assigns the ω-node its ordinal unchanged.
This is the in-kernel evidence that the ω-rule node arithmetizes — the strongest single signal for the
pivot. -/
theorem iord_zOmegaPrem_constant {d0 a t₁ t₂ : V}
    (ht₁ : IsUTerm ℒₒᵣ t₁) (ht₂ : IsUTerm ℒₒᵣ t₂) (hZ : ZDerivation d0) :
    iord (zOmegaPrem d0 a t₁) = iord (zOmegaPrem d0 a t₂) := by
  rw [iord_zOmegaPrem ht₁ hZ, iord_zOmegaPrem ht₂ hZ]

/-- **The ω-rule ∀-cut REDUCTION strictly descends — for EVERY witness, uniformly (Probe 2's ordinal
half).** Selecting the premise `zOmegaPrem d0 a t` for cut witness `t` drops the ordinal strictly below the
∀-node: `iord (selected) = iord d0 ≺ iord (zIall …)` (the banked `iord_descent_zIall`, composed with
`iord_zOmegaPrem`). This is the heart of why ω-rule cut-elimination terminates on ∀-cuts — the reduction's
ordinal recursion is well-founded, UNIFORMLY in the witness, with NO chain machinery. Combined with
`zOmegaPrem_valid` (selected premise valid) it shows the ∀-cut reduction is both validity-preserving and
ordinal-decreasing — exactly the cut-elimination invariant, in-kernel on the existing nodes. -/
theorem iord_descent_zOmegaPrem {s a p d0 t : V} (ht : IsUTerm ℒₒᵣ t) (hZ : ZDerivation d0) :
    icmp (iord (zOmegaPrem d0 a t)) (iord (zIall s a p d0)) = 0 := by
  rw [iord_zOmegaPrem ht hZ]; exact iord_descent_zIall s a p d0

/-! ## Capstone — the ω-rule ∀-node is REALIZABLE from a regular finitary I∀ node

The decisive structural point: a (would-be) ω-node `zAllω s a p d0` carries the SAME finite data as the
existing `zIall s a p d0` — premise-`t` is computed on demand (`zsubst d0 a t`), never stored. And its full
ω-rule validity (premise family valid + conclusions correct + ordinals uniform) is DERIVED from the existing
regular `zIall` node, with no chain machinery and no conclusion-tracking motive. So a Path-C rebuild reuses
the existing I∀ embedding wholesale (PA's ∀-intro already produces a regular `zIall` with fresh
eigenvariable = O3). -/

/-- **Spike capstone — a regular `zIall` realizes the full ω-rule ∀-node.** From `ZDerivation (zIall s a p
d0)`, the freshness bound `maxEigen d0 < a`, and the eigenvariable side-condition O3 (`a` not free in the
matrix `p` or antecedent `Γ`, phrased as substitution-invariance — exactly what the embedding's fresh
eigenvariable choice supplies), EVERY closed term `t` gives: the premise `zOmegaPrem d0 a t` is a
`ZDerivation` of exactly `Γ→F(t)`, with ordinal `iord d0` (uniform across the family). This is the formal
object the ω-rule cut-elimination consumes — assembled from `zOmegaPrem_valid` (motive-free validity),
`zOmegaPrem_concl` (computed conclusion), `iord_zOmegaPrem` (finite uniform ordinal), all in-kernel. -/
theorem zIall_realizes_omega {s a p d0 : V}
    (hZ : ZDerivation (zIall s a p d0)) (hreg : maxEigen d0 < a)
    (hO3p : ∀ t, IsSemiterm ℒₒᵣ 0 t → fvSubst ℒₒᵣ a t p = p)
    (hO3Γ : ∀ t, IsSemiterm ℒₒᵣ 0 t → fvSubstSeq a t (seqAnt s) = seqAnt s) :
    ∀ t, IsSemiterm ℒₒᵣ 0 t →
      ZDerivation (zOmegaPrem d0 a t) ∧
      fstIdx (zOmegaPrem d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p) ∧
      iord (zOmegaPrem d0 a t) = iord d0 := by
  intro t ht
  exact ⟨zOmegaPrem_valid ht hZ hreg,
    zOmegaPrem_concl hZ (hO3p t ht) (hO3Γ t ht) ht,
    iord_zOmegaPrem ht.isUTerm (zDerivation_zIall_inv hZ).1⟩

/-! ## Spike verdict so far + the one remaining Path-C obligation (Probe 2 — OPEN)

**Evidence gathered (all axiom-clean, in-kernel):**
- `zOmegaPrem_valid` — premise family uniformly valid, motive-free (freshness bound only).
- `zOmegaPrem_concl` — selected premise's conclusion computed, not threaded.
- `iord_zOmegaPrem` / `iord_zOmegaPrem_constant` — premise-family ordinal is CONSTANT `= iord d0`, so the
  ω-node's `iord` is the finite `iord d0 + 1` (no sup-over-infinite-family primitive needed). Probe 1's
  arithmetization-risk concern is RETIRED.

**The ω-rule ∀-cut reduction's CORE invariant is now in-kernel.** `iord_descent_zOmegaPrem`: selecting the
premise for witness `t` strictly drops the ordinal (`iord d0 ≺ iord (zIall …)`), UNIFORMLY in `t`; with
`zOmegaPrem_valid` (selected premise valid) this is the full cut-elimination invariant for the ∀-cut —
validity-preserving AND ordinal-decreasing — proven on the existing nodes, no chain machinery.

**HONEST SCOPING — what this spike does and does NOT settle.** What it settles: the ω-rule ∀-NODE
arithmetizes cleanly (validity motive-free, ordinal finite, per-step ∀-cut descent), which was the lap-92
"riskiest assumption" — solid evidence the ω-rule infrastructure is realizable in IΣ₁ on the existing
engine. What it does NOT yet settle: the ACTUAL crux-2 wall is the **chain (`zK`) cut-elimination on the
⊥-orbit** (`ZDerivesEmpty` is Ind-or-chain by `zTag_Ind_or_K_of_ZDerivesEmpty`; the `redZKReady` motive is a
CHAIN obligation). The ∀-node is necessary infrastructure but is not itself the chain. The lap-92 claim is
that the ω-rule's premise-selection ALSO dissolves the chain's conclusion-tracking motive — plausible and
SUPPORTED by the ∀-node result (the same selection-is-conclusion-automatic mechanism), but **the chain
itself is not yet probed.**

**Probe 2 (the genuine remaining design):** how the ⊥-orbit chain/Ind cut-elimination looks in the ω-rule
view. Buchholz §6: induction (`zInd`) becomes an ω-rule node (premises `F(0), F(1), …` from iterating the
step), and the chain's repetition is absorbed into the ω-rule. The probe: define the ω-rule reduct of an
Ind/chain ⊥-orbit node and check it avoids the `redZKReady` hereditary-Rep motive — the direct analogue of
this spike's ∀-node result, on the node that actually walls. Needs the chain's ω-rule reformulation +
likely an ω-node datatype tag in the `zconstruction` Fixpoint (the ~2–3k-line rebuild; `Zinfty.lean`
template).

**NET CALL (honestly scoped):** the evidence favours the Path-C pivot — the ω-rule infrastructure
arithmetizes (this spike), and the lap-92 mechanism (selection dissolves conclusion-tracking) is confirmed
for the ∀-node and plausibly extends to the chain. But the chain probe is the decisive next step before a
full commit. **NEXT LAP:** Probe 2 — the ⊥-orbit Ind/chain ω-rule reduct, the direct test of whether the
ω-rule retires the `redZKReady` motive on the node that actually walls. See `NEXT_STEPS.md`. -/

/-! ## Probe 2 — the ⊥-orbit INDUCTION node under the ω-rule (lap 102, EXECUTED)

The reflection (lap 101) named Probe 2 as the decisive test: does the ω-rule retire the `redZKReady`
hereditary-Rep motive on the node that actually walls (the chain/Ind ⊥-orbit)? Two halves: (A) does the
ω-rule view eliminate the chain conclusion-tracking motive, and (B) does the induction ω-node ARITHMETIZE
(the `iord` question Probe 1 settled for the ∀-node)? This section settles BOTH, with a surprise on (B).

**(A) — the chain motive is retired (already PROVEN, by `Zinfty.lean`).** The meta ω-rule calculus
`ZinftyF.Deriv` (axiom-clean, 1560 lines) carries out the FULL Gentzen cut-elimination (`cutElimStep` /
`cutElimPrincipal` / `cutElim`, Towsner §19) over real `ℒₒᵣ` syntax with **no chain rule and no
`redZKReady`-style conclusion-tracking motive whatsoever**: the only multi-premise rule is `allω`, and
∀/∃-cuts reduce by premise SELECTION (`cutReduceAll`), exactly as the lap-101 ∀-node spike showed
arithmetizes (`zOmegaPrem_valid` + `iord_descent_zOmegaPrem`). The repo's finitary `zK` chain is Buchholz's
device for spreading a finitary cut across an eigenvariable system; the ω-rule has no analogue, so the
`redZKReady` hereditary-Rep obligation (`Crux2Blueprint.redSoundGen`'s open `sorry`) simply does not arise.
`Zinfty.lean` IS the in-kernel certificate that ω-rule cut-elimination needs no chain motive. So (A) = YES.

**(B) — the SURPRISE: the induction ω-node's premise ordinals are NOT constant (contrast Probe 1).** Under
the ω-rule, PA-induction is absorbed: to derive `∀x F` you supply the family `F(0), F(1), F(2), …`, where
`F(k)` is proved by iterating the (fixed) step `k` times from the base. The repo's FINITARY induction
reduct already exhibits this iteration: `red (zInd s a p d0 d1) = zK s (irk p) (iIndReductSeq d0 d1 1)`, and
the `k`-step unfolding `iIndReductSeq d0 d1 k = ⟨d0, d1, …, d1⟩` has õ-ordinal computed below. UNLIKE the
∀-node (whose premises are eigensubsts, ordinal-PRESERVING, hence `iord_zOmegaPrem_constant`), the induction
premise ordinals STRICTLY INCREASE in the unfolding depth `k`. So `o(induction-ω-node) = ⨆_k o(premise k)`
is a GENUINE limit ordinal, not a finite successor — Probe 1's "constant ⟹ finite `iord d0 + 1`" escape
does NOT extend to the induction node. -/

/-- **The induction `k`-step unfolding's õ-ordinal, in closed form.** `iIndReductSeq d0 d1 k` is the chain
`⟨d0, d1, …, d1⟩` (base + `k` copies of the step); its õ (the `#`-natural-sum fold `iotil_zK`) is the
Cantor-normal-form term `ω^{õ d1}·k # ω^{õ d0}`. The coefficient `k` of the `ω^{õ d1}` block is LITERALLY
the unfolding depth — manifest depth-dependence, the obstruction to a constant-ordinal ω-node. -/
theorem iotil_zK_iIndReduct (s r d0 d1 k : V) (hk : 0 < k) :
    iotil (zK s r (iIndReductSeq d0 d1 k))
      = inadd (ocOadd (iotil d1) k 0) (ocOadd (iotil d0) 1 0) := by
  rw [iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 k), iseqNaddIdg_iIndReductSeq hk]

/-- **The `ω^e`-coefficient block strictly grows in its multiplier.** `ω^e·k₁ ≺ ω^e·k₂` for `k₁ < k₂`
(same exponent, no tail): `icmp` reduces to `cmpV k₁ k₂` via `icmp_ocOadd`. The CNF kernel of the induction
ordinal's depth-dependence. -/
theorem ocOadd_coeff_strictMono (e k1 k2 : V) (hk : k1 < k2) :
    icmp (ocOadd e k1 0) (ocOadd e k2 0) = 0 := by
  rw [icmp_ocOadd, icmp_self e e le_rfl, thenV_one_left, icmp_zero_zero,
      cmpV_eq_zero.mpr hk]
  exact thenV_eq_zero.mpr (Or.inl rfl)

/-- **PROBE 2 KEY RESULT — the induction ω-node's premise-family ordinal STRICTLY INCREASES in the
unfolding depth.** For NF premise ordinals (which `ZDerivation`s carry, via `isNF_iotil`), `k₁ < k₂` ⟹
`õ(k₁-unfolding) ≺ õ(k₂-unfolding)` — by `inadd_right_mono` on the depth-`k` coefficient block
(`ocOadd_coeff_strictMono`), the `ω^{õ d0}` summand fixed. **This is the in-kernel REFUTATION of the
constant-ordinal escape for the induction node:** where the ∀-node spike proved `iord_zOmegaPrem_constant`
(premises ordinal-uniform ⟹ `iord = iord d0 + 1`, finite), the induction node's premises are ORDINAL-COFINAL
in the index, so `⨆_k o(premise k) = ω^{õ d1 + 1} # ω^{õ d0}` is a genuine LIMIT. The repo's `iord =
iotower (iotil) (idg)` is a finite-`#`-fold over the STORED finite premise sequence and has no sup/limit
operation, so it cannot assign the induction ω-node its ordinal. The standard fix (Buchholz
operator-controlled derivations) is to STORE the ordinal as node data with the side condition `∀k, o(premise
k) ≺ stored`, NOT compute it — fully arithmetizable, but REPLACES the computed-`iord` layer. -/
theorem iotil_zK_iIndReduct_strictMono (s r d0 d1 k1 k2 : V)
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1))
    (hk1 : 0 < k1) (hk : k1 < k2) :
    icmp (iotil (zK s r (iIndReductSeq d0 d1 k1)))
         (iotil (zK s r (iIndReductSeq d0 d1 k2))) = 0 := by
  rw [iotil_zK_iIndReduct s r d0 d1 k1 hk1,
      iotil_zK_iIndReduct s r d0 d1 k2 (lt_trans hk1 hk)]
  refine inadd_right_mono ?_ ?_ (ocOadd_coeff_strictMono (iotil d1) k1 k2 hk)
    (ocOadd (iotil d0) 1 0) (isNF_omega_pow hd0)
  · exact (isNF_ocOadd _ _ _).mpr ⟨hk1.ne', hd1, isNF_zero, Or.inl rfl⟩
  · exact (isNF_ocOadd _ _ _).mpr ⟨(lt_trans hk1 hk).ne', hd1, isNF_zero, Or.inl rfl⟩

/-! ## SPIKE VERDICT (lap 102 — Probe 2 EXECUTED, fork SETTLED with refinement)

**Evidence (all axiom-clean, in-kernel).** *∀-node (Probe 1):* `zOmegaPrem_valid`, `zOmegaPrem_concl`,
`iord_zOmegaPrem_constant`, `iord_descent_zOmegaPrem`, `zIall_realizes_omega`. *Chain/Ind (Probe 2):*
**(A) chain motive RETIRED** — `Zinfty.lean` proves full ω-rule cut-elimination with no chain, no
`redZKReady`; the lap-92 selection-dissolves-tracking thesis is CONFIRMED (no chain rule to track).
**(B) induction ω-node ordinal is a GENUINE LIMIT** (`iotil_zK_iIndReduct_strictMono`): premise ordinals
strictly increase in depth, so `⨆_k o(premise k) = ω^{õ d1 + 1} # ω^{õ d0}`; the computed `iord` (finite
`#`-fold, no sup) CANNOT assign it.

**NET CALL (refined — supersedes the lap-101 estimate).** Fork settled IN FAVOUR of Path C, but lap-101's
cost estimate ("reuse the ordinal engine + `zsubst` + `Zinfty` template") was wrong on one axis: the ω-rule
retires the chain/`redZKReady` motive (good), but the ORDINAL LAYER must be REPLACED, not reused — the
induction ω-node's ordinal is a limit the computed `iord` cannot express. Path C = Buchholz
operator-controlled derivations with **stored** ordinals (`Deriv` carries `o` as data + side condition
`∀ premise, o(premise) ≺ o(node)`), exactly as `ZinftyF.Deriv`/`o` does at the meta level. MORE
arithmetizable than computing a sup (no limit operation needed), but a from-scratch ordinal/derivation
datatype, not a graft onto `InternalZ`'s `iotower`/`iotil`/`idg`.
- **Path X (finitary) disfavoured AND likely broken:** its linchpin `redZKReady`'s hereditary-Rep invariant
  does NOT follow from Cor 2.1 down a nested-chain spine — a sub-chain's selected premise is permissible
  w.r.t. the sub-chain's OWN conclusion `Γᵢ→Aᵢ` (growing antecedent, arbitrary succedent), which CAN be an
  I-rule/axiom (non-Rep). So `fstIdx (red dᵢ) = fstIdx dᵢ` (the keep-Π replace precondition the repo's `red`
  COMMITS to for non-critical nested chains) can FAIL ⟹ `red` unfaithful there. Cor 2.1 fires only at the
  ∅→⊥ TOP node, not hereditarily. The lap-101 worry, now with a concrete reason.
- **Path C (ω-rule) is the route:** rebuild on `ZinftyF.Deriv`'s shape, arithmetized — stored ordinals,
  `allω` ω-node (premise family by `zsubst`/iterated-step code), cut-elim by the Tait/Schütte recursion
  `Zinfty.lean` certifies. crux-2's `false_of_ZDerivesEmpty` becomes: a cut-bearing ⊥-derivation has stored
  ordinal `< ε₀`; `red` = one `cutElimStep` strictly dropping it; the ⊥-sequent has no cut-free proof, so
  `red` never terminates ⟹ infinite ε₀-descent ⟹ contradicts PRWO(ε₀). No chain, no `redZKReady`.

**NEXT LAP = begin the Path-C arithmetized datatype.** Define the Σ₁-coded stored-ordinal ω-derivation
(`zconstruction` tag for `allω`, ordinal carried as data, validity = premise-family code + `∀-premise
ordinal ≺ node ordinal`), porting `ZinftyF.Deriv`/`o`/`cr` from `Finset Seq`/`Ordinal` to `V`/`iord`-CNF.
First milestone: arithmetized `allω` node + `iord` AS STORED + the single `cutElimStep` ordinal drop on it,
reusing this spike's `zOmegaPrem`/`iord_descent_zOmegaPrem` for the ∀-cut case. Keep `InternalZ`/
`Crux2Blueprint` (Path X) green in `src/` as fallback until Path C reaches `false_of_ZDerivesEmpty`. -/

end GoodsteinPA.InternalZ
