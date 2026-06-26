/-
# `wip/ExistenceEndgame.lean` — lap-132 SPIKE: the existence / least-descending-reduct endgame

**DISCLOSED-SORRY SPIKE (wip, NOT imported by `GoodsteinPA.lean` — cannot affect `lake build
GoodsteinPA`).** Tests the lap-132 reflection's reframing (`REFLECTION-2026-06-26-lap132.md`):

The current endgame `Crux2Blueprint.false_of_ZDerivesEmpty` (bare `sorry`) is meant to close via the
per-step DICHOTOMY `iord_red_iterate_descends` (`red`-fixpoint OR `iord` descends) for the FIXED,
deterministic, `permIdx`-based engine `red`. Closing the fixpoint branch needs "`red`-fixpoint ⟹
cut-free", refuted for the `permIdx` engine (lap 129) — which forced the laps-120→131 no-stall campaign
(`firstBotPrem_reducible`, the `majorIdx` re-key, the tag-5/6 dispatch, the `zReg`/`zFresh`/`seqAntSeq`
folds + the ZPhi exact-shape strengthenings), all in service of making ONE fixed selector not stall.

**The reframe.** Replace the dichotomy with a single UNCONDITIONAL existence lemma (E') — every regular
⊥-orbit code has a SOUND, strictly-`iord`-descending reduct (no fixpoint/cut-free case to dispatch). Then
`false_of_ZDerivesEmpty` is a one-line composition of (E') with the *unchanged* M3 PRWO plumbing — NO
fixpoint branch, NO `iord_descent_red` chain-REPLACE IH, NO `permIdx`/`majorIdx` engine swap.

**What the spike demonstrates (it ELABORATES against the live API):**
1. `ZDerivesEmptyR_descent_step` (E') is the SINGLE crux, cleanly decomposed (its docstring) into
   already-banked suppliers — the laps-112-119 soundness + the per-reduct descent + the banked
   `firstBotPrem_reducible` no-stall fact, each used as a one-shot `∃`, not an engine property.
2. The endgame `false_of_ZDerivesEmpty_existence` is a sorry-FREE composition of (E') with the reused
   PRWO obligation `prwo_forbids_existence_descent` — contrast the current bare-`sorry`
   `Crux2Blueprint.false_of_ZDerivesEmpty`.
3. **The honest constraint surfaced by the spike:** `iord`/`icmp` is NOT internally well-founded in
   nonstandard `V ⊧ IΣ₁` (that is the whole subtlety of arithmetized cut-elimination) — `PRWO(ε₀)`
   forbids only `𝚺₁`-DEFINABLE descents. So the iterator realizing (E') must be the `𝚺₁` LEAST-WITNESS
   function `redLeast d := μ d'. [(E')-predicate]` (`InductionOnHierarchy.least_number`, exactly as
   `firstBotPrem_reducible` is proved), NOT classical choice (a choice-built sequence need not be
   `𝚺₁`/primrec, so PRWO would not apply). `prwo_forbids_existence_descent` is where that `𝚺₁`-ness is
   consumed; it is the existing M3 plumbing (`gentzenDescentφ` graph + `prwoInstance`), UNCHANGED except
   the iterator is `redLeast` instead of `red`.

**Decision rule (mirror lap-101's fork spike):** (E') discharges cleanly at the root from the banked
suppliers ⟹ PIVOT the endgame to this form, drop the stall campaign. (E')'s non-critical-K case
re-imports the stall (the "real cut vs structurally cut-free chain" determination IS the redex-finding)
⟹ fall back to the lap-129 engine swap with that evidence (NEXT_STEPS keeps it as the FALLBACK route).
-/
import GoodsteinPA.Crux2Blueprint

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **K-critical sub-case of (E'), as a PLUMBING assembly of the banked reduct facts.** For a critical
(`zKCritical`) ⊥-orbit K-node `zK s r ds`, the witness is the genuine cut reduct `iRKcCrit (zK s r ds)`;
the existence step is `⟨iRKcCrit …, ⟨⟨sound, ∅-ant, ⊥-succ⟩, regular, fresh⟩, descent⟩`. This lemma makes
that interface EXPLICIT and PROVEN — it shows the K-critical case has NO hidden structural difficulty
beyond the six already-banked-or-pending suppliers:
* `hsound : ZDerivation (iRKcCrit …)` — `ZDerivation_iRKcCrit_botOrbit` (`Crux2Blueprint:648`; `hCwff`/
  `hSeqs` already free at the ⊥-root), modulo `hthread`/`hrank` (from `isChainInf`) + `hAll`/`hNeg`
  (per-node bundle: `seqSucc sⱼ = cutFormula` now derivable, lap 131; the `Seq(seqAnt)` parts = the
  `seqAntSeq` fold residual);
* `hant`/`hsucc` — the reduct keeps the `∅→⊥` conclusion (`fstIdx_red_of_emptyAnt_botSucc`-style);
* `hreg`/`hfr` — `ZRegular_iRKcCrit` (lap 119) / `ZFresh_iRKcCrit` (lap 128);
* `hdesc` — `iord_descent_iRKcCrit_corr`/`_neg` (`RedZKDescent:580/597`).
The lone genuinely-open piece across these is the `seqAntSeq` fold (the lap-131 `Seq(seqAnt sⱼ)`/`(sᵢ)`
residual), which is a KEEP-list item shared with the engine-swap route. -/
theorem descent_step_Kcrit_of_bundle {s r ds : V}
    (hsound : ZDerivation (iRKcCrit (zK s r ds)))
    (hant : seqAnt (fstIdx (iRKcCrit (zK s r ds))) = (∅ : V))
    (hsucc : seqSucc (fstIdx (iRKcCrit (zK s r ds))) = (^⊥ : V))
    (hreg : ZRegular (iRKcCrit (zK s r ds)))
    (hfr : ZFresh (iRKcCrit (zK s r ds)))
    (hsa : ZSeqAnt (iRKcCrit (zK s r ds)))
    (hdesc : icmp (iord (iRKcCrit (zK s r ds))) (iord (zK s r ds)) = 0) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 :=
  ⟨iRKcCrit (zK s r ds), ⟨⟨hsound, hant, hsucc⟩, hreg, hfr, hsa⟩, hdesc⟩

/-- **THE existence-form K-case crux, via the FAITHFUL one-shot `majorIdx` selector** (lap-135 spike
verdict: this is the precise form the PIVOT takes). For a regular `∅→⊥` K-node, a descending sound
reduct is obtained by reducing the **first `⊥`-exit major premise** `dⱼ = znth ds (majorIdx (zK s r ds))`,
which `majorIdx_botOrbit_reducible` (`InternalZ:9155`, BANKED) proves is in range, has succedent `⊥`,
and is NOT a `red`-normal leaf (`zTag ∉ {0,7}`). So `majorIdx` lands on tag `∈ {3,4,5,6}` and the reduct
dispatch is:

* **tag 3 (Ind major)** → the `iRInd dⱼ` reduct in place at `majorIdx`: a `replace` whose descent kernel
  (`iotil_zK_lt_replace`/`idg_zK_le_replace`, banked, INDEX-GENERIC) + `iRedDescent_zInd` give strict
  descent; soundness is `ZDerivation`-of-replace (`ZDerivation_iCritAux_of` / the §5.2.2 wrapper).
* **tag 4 (chain major)** → `replace` with `dⱼ`'s OWN descending reduct: the relocated RECURSION — in the
  existence form this is a STRUCTURAL `<`-induction on the derivation (premise `dⱼ < zK s r ds`), NOT the
  engine's "total `red` descends" claim (which forced the no-stall campaign). The generalized IH must
  cover a premise with non-empty antecedent (the chain threading) — the genuine open recursion core.
* **tag 5/6 (∀/¬-axiom major)** → NOT a `replace` (`red dⱼ = dⱼ`, fixpoint): the PRINCIPAL CUT at the
  redex pair `(i', majorIdx)` where `i'` is the upstream R-introduction of the axiom's active formula,
  PINNED by `majorPrem_zAxAll_cutPartner` / `majorPrem_zAxNeg_cutPartner` (`InternalZ:9217/9245`,
  BANKED). The reduct is `iRcritG`-style (the `iRKcCrit` machinery, laps 112-119) at THIS pair — its
  soundness needs the same `hAll` cutFormula bridge as the critical case (SHARED blocker), its descent
  the banked `iord_descent_iRcritG_*`.

**Why this settles the spike (PIVOT).** The critical/non-critical split DISSOLVES into one selector
(`majorIdx`); `firstBotPrem`/`majorIdx_botOrbit_reducible`/the `cutPartner` lemmas survive only as
ONE-SHOT `∃`-facts (all BANKED), NEVER as a threaded total engine. The fixpoint-⟹-cut-free obstruction
(lap-129 refutation) is GONE — `majorIdx` never stalls on the ⊥-orbit (no leaf). What the reframe does
NOT shed: the `hAll` cutFormula bridge (tag-5/6 + critical, shared) and the tag-4 structural recursion
(relocated to `<`-induction). See `PENDING_WORK.md` lap-135 for the verdict + attack. -/
theorem descent_step_K_majorIdx {s r ds : V}
    (hZ : ZDerivation (zK s r ds)) (hreg : ZRegular (zK s r ds)) (hfr : ZFresh (zK s r ds))
    (hsa : ZSeqAnt (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V)) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  -- The faithful major premise is reducible (no leaf stall) — BANKED, the linchpin the reframe reuses.
  obtain ⟨hmlt, hmbot, hm0, hm7⟩ := majorIdx_botOrbit_reducible hZ hant hsucc
  -- Dispatch on `dⱼ`'s tag (∈ {3,4,5,6} since `≠ 0,7`); see docstring. The tag-3 case is banked-clean,
  -- tag-5/6 routes through the `cutPartner` principal cut + `hAll`, tag-4 is the structural recursion.
  sorry

/-- **(E') THE existence-form crux — the UNCONDITIONAL one-step descent.** Every regular ⊥-orbit code has
a SOUND, strictly-`iord`-descending reduct; NO fixpoint/cut-free case to dispatch (a cut-free `∅→⊥` is
absurd by Cor 2.1, so `majorIdx` always finds a reducible major premise). Reduces cleanly to the two
roots a `∅→⊥` derivation can have (`zTag_Ind_or_K_of_ZDerivesEmpty`, `InternalZ:8643`):

* **Ind** (tag 3) → `red d = iRInd d`, sound + strictly descends (`iord_descent_red_zInd`,
  `Crux2Blueprint:1116`) — PROVEN here, no residual;
* **K** (tag 4) → `descent_step_K_majorIdx` (the lone remaining content, above).

**This REPLACES** `iord_descent_red`'s fixpoint dichotomy, the "fixpoint ⟹ cut-free" obligation, AND the
`permIdx`→`majorIdx` total-engine swap: the major premise is chosen as a ONE-SHOT `∃`, never threaded. -/
theorem ZDerivesEmptyR_descent_step {d : V} (hd : ZDerivesEmptyR d) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord d) = 0 := by
  rcases zTag_Ind_or_K_of_ZDerivesEmpty hd.1 with htag | htag
  · -- **Ind (tag 3): PROVEN from banked lemmas.** `red d = iRInd d` preserves `ZDerivesEmptyR`
    -- (`ZDerivesEmptyR_red`) and STRICTLY descends (`iord_descent_red_zInd`, no fixpoint case for Ind).
    exact ⟨red d, ZDerivesEmptyR_red hd, iord_descent_red_zInd d hd.1.1 htag⟩
  · -- **K (tag 4): reduces to `descent_step_K_majorIdx`.** Destructure `d = zK s r ds`, supply the
    -- regular `∅→⊥` data off `hd`; the major-premise dispatch is the lone open content.
    rcases zDerivation_iff.mp hd.1.1 with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ |
      ⟨s, p, d0, rfl, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
      ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    · simp at htag
    · simp at htag
    · simp at htag
    · simp at htag
    · have hant : seqAnt s = (∅ : V) := by have h := hd.1.2.1; rwa [fstIdx_zK] at h
      have hsucc : seqSucc s = (^⊥ : V) := by have h := hd.1.2.2; rwa [fstIdx_zK] at h
      exact descent_step_K_majorIdx hd.1.1 hd.2.1 hd.2.2.1 hd.2.2.2 hant hsucc
    · simp at htag
    · simp at htag
    · simp at htag

/-- **Reused M3 plumbing (UNCHANGED by the reframing except the iterator).** Given (E') as a hypothesis,
realize the `𝚺₁` LEAST-WITNESS iterator `redLeast d := μ d'. [ZDerivesEmptyR d' ∧ icmp (iord d') (iord d)
= 0]` (`InductionOnHierarchy.least_number` over the `𝚺₁` existence predicate — exactly the construction
`firstBotPrem_reducible` uses), internalize `n ↦ iord (redLeast^[n] z)` as the `𝚺₁` graph
`gentzenDescentφ`, and apply `PRWO(ε₀)` (crux-1) to forbid the strict descent. This is the existing
`Crux2Blueprint` M3 endgame; the ONLY change from the current plan is `red ↦ redLeast`. The iterator's
`𝚺₁`-definability is the load-bearing hypothesis PRWO consumes (a non-`𝚺₁` choice-built sequence would
not be forbidden — `iord` is not internally well-founded in nonstandard `V`). -/
theorem prwo_forbids_existence_descent
    (hstep : ∀ d : V, ZDerivesEmptyR d → ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord d) = 0)
    {z : V} (hz : ZDerivesEmptyR z) : False := by
  sorry

/-- **The existence-form endgame — a sorry-FREE composition** of (E') with the reused PRWO obligation.
Contrast `Crux2Blueprint.false_of_ZDerivesEmpty` (`:1314`), a bare `sorry` that needs the whole
dichotomy + fixpoint-branch + stall machinery. Here the only open content is (E') + the reused plumbing;
the assembly itself is trivial. -/
theorem false_of_ZDerivesEmpty_existence {z : V} (hz : ZDerivesEmptyR z) : False :=
  prwo_forbids_existence_descent (fun _ hd => ZDerivesEmptyR_descent_step hd) hz

end GoodsteinPA.InternalZ
