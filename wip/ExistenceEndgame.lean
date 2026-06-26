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

/-- **(E') THE existence-form crux — the UNCONDITIONAL one-step descent.** Every regular ⊥-orbit code
has a SOUND, strictly-`iord`-descending reduct. There is NO cut-free/fixpoint case to dispatch on:

* a `∅→⊥` derivation is never an axiom leaf — `zTag_reducible_of_emptyAnt` (empty antecedent rules out
  every axiom scheme), and its root is `Ind`/`K` — `zTag_Ind_or_K_of_ZDerivesEmpty` (`InternalZ:8636`);
* **Ind** (tag 3) → the `iRInd` reduct is sound and descends (`iord_descent_red_zInd`,
  `Crux2Blueprint:1116`);
* **K critical** (`zKCritical s ds = ∀ i < lh ds, ¬ iperm (tp (znth ds i)) s`, i.e. no permissible
  premise) → the genuine cut reduct `iRKcCrit` is SOUND (laps 112-119, `ZDerivation_iRKcCrit_all` +
  ¬-twin) and DESCENDS (`iord_descent_iRKcCrit_corr`/`_neg`, `RedZKDescent:580/597`);
* **K non-critical** (a permissible premise exists — possibly a leaf atom, the laps-104-131 STALL case)
  → reduce the FAITHFUL major premise (first `⊥`-exit, Buchholz §14.25), which `firstBotPrem_reducible`
  (`InternalZ:8957`) proves is NEVER a leaf (`zTag ∉ {0,7}`), hence reducible + descending.

Regularity/freshness preservation (`ZRegular_red`/`ZFresh_red` + the pending `seqAntSeq` fold) keep the
reduct inside `ZDerivesEmptyR`. **This single lemma is the entire remaining crux-2 content.** It
REPLACES `iord_descent_red`'s fixpoint dichotomy, the "fixpoint ⟹ cut-free" obligation, AND the
`permIdx`→`majorIdx` engine swap: the major premise is chosen here as a ONE-SHOT `∃`, never as a total
Σ₁ engine threaded through the orbit + every invariant fold. -/
theorem ZDerivesEmptyR_descent_step {d : V} (hd : ZDerivesEmptyR d) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord d) = 0 := by
  rcases zTag_Ind_or_K_of_ZDerivesEmpty hd.1 with htag | htag
  · -- **Ind (tag 3): PROVEN from banked lemmas.** `red d = iRInd d` preserves `ZDerivesEmptyR`
    -- (`ZDerivesEmptyR_red`) and STRICTLY descends (`iord_descent_red_zInd`, no fixpoint case for Ind).
    exact ⟨red d, ZDerivesEmptyR_red hd, iord_descent_red_zInd d hd.1.1 htag⟩
  · -- **K (tag 4): the single remaining content.** Two one-shot existence choices (NOT a total engine):
    -- • critical (`zKCritical s ds`, no permissible premise) → the genuine cut reduct `iRKcCrit` —
    --   sound (`ZDerivation_iRKcCrit_all` + ¬-twin, laps 112-119), descends
    --   (`iord_descent_iRKcCrit_corr`/`_neg`), preserves regularity/freshness (`ZRegular_iRKcCrit`/
    --   `ZFresh_iRKcCrit`); the `Seq(seqAnt)` bundle is the lap-131 `seqAntSeq`-fold residual.
    -- • non-critical (a permissible premise exists, possibly a leaf atom — the laps-104-131 STALL) →
    --   reduce the FAITHFUL major premise (first `⊥`-exit), which `firstBotPrem_reducible` proves is
    --   NEVER a leaf (`zTag ∉ {0,7}`), hence reducible + descending.
    -- This is where the existence form's leverage lives: the major premise is chosen HERE, once, as an
    -- `∃`-witness — not as a `permIdx`/`majorIdx` engine that must be threaded through the orbit.
    sorry

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
