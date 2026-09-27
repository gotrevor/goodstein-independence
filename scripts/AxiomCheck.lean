/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA

/-!
# Axiom audit — the reference point of truth

`#print axioms` for every headline theorem, each wrapped in `#guard_msgs` asserting the EXACT
expected axiom set: the standard mathlib triple `[propext, Classical.choice, Quot.sound]` — no
`sorry` (`sorryAx`), no custom/blueprint axiom, no `native_decide`/`ofReduceBool`.

Why guard instead of a bare `#print axioms`? A bare print only emits an `info` message — a `sorryAx`
or new-axiom regression would still build **green** and nobody would notice. `#guard_msgs` turns the
audit into an assertion: any drift (a new axiom, a `sorry`, or a renamed/removed theorem) makes THIS
FILE fail to elaborate. On success the guards consume their messages, so a clean run is **silent**:

    lake env lean scripts/AxiomCheck.lean   # no output + exit 0 = all clean

CI (`.github/workflows/ci.yml`, the build job's axiom-clean gate) runs exactly that and gates on the
exit code. This is the single source of truth for the headline set — no count to bump, renames caught
automatically. `whitespace := lax` tolerates the pretty-printer wrapping a long qualified name.
-/

-- The summit: `𝗣𝗔 ⊬ ↑goodsteinSentence` (Kirby–Paris), re-pointed to the axiom-clean route-B headline.
/-- info: 'GoodsteinPA.peano_not_proves_goodstein' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.peano_not_proves_goodstein

-- Independence: `goodsteinSentence` is independent of PA.  (FFL renamed the former
-- `peano_not_proves_consistency`; the PA-consistency headline now lives in `Result.ConsistencyPA`.)
/-- info: 'GoodsteinPA.goodstein_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.goodstein_independent

-- ℕ-level truth companion: every Goodstein sequence terminates (the true statement PA cannot prove).
/-- info: 'Goodstein.Dom.goodstein_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Goodstein.Dom.goodstein_terminates

-- Anti-vacuity anchor: the encoding is faithful (`ℕ ⊨ goodsteinSentence ↔ Goodstein terminates`).
/-- info: 'GoodsteinPA.goodsteinSentence_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.goodsteinSentence_faithful

-- Wainer's bound, general (ROADMAP-EPSILON0 stage 1): PA-provable Π₂ ⇒ witness below some `f_o`,
-- `o < ε₀`.
/-- info: 'GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing

-- The Goodstein bound re-derived as a corollary of the general theorem.
/-- info: 'GoodsteinPA.Wainer.wainer_bound_of_pa_proves_goodstein_via_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.Wainer.wainer_bound_of_pa_proves_goodstein_via_general

-- Stage 2: PA does not prove that the canonical hydra battle terminates (every faithful Σ₁
-- encoding).
/-- info: 'GoodsteinPA.Hydra.pa_not_proves_hydra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.Hydra.pa_not_proves_hydra

-- Stage 2 anti-vacuity: a Σ₁ definition of the battle exists.  Inherits the one `native_decide`
-- of `ONote.cmpStep_spec` (computability of `ONote.cmp`, via `primrec_Cnat`).
/--
info: 'GoodsteinPA.Hydra.exists_sigma1_battle_def' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ONote.cmpStep_spec._native.native_decide.ax_1_5✝]
-/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.Hydra.exists_sigma1_battle_def

-- Stage 3: PA does not prove the Paris–Harrington principle (every faithful Σ₁ encoding).
/-- info: 'GoodsteinPA.PH.pa_not_proves_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.PH.pa_not_proves_ph

-- Stage 3 anti-vacuity: a Σ₁ definition of PH exists.
/-- info: 'GoodsteinPA.PH.exists_sigma1_ph_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.PH.exists_sigma1_ph_def

-- Stage 3: Paris–Harrington is true (infinite Ramsey + Rado selection).
/-- info: 'GoodsteinPA.PH.ph_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.PH.ph_true
