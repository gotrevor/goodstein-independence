/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinWu

/-!
# Axiom audit — the `GoodsteinWu` bridge (Wainer's classification)

The companion of `scripts/AxiomCheck.lean` for the non-module library `GoodsteinWu`, which is built
separately (`lake build GoodsteinWu`) because it imports KT. Wu's `OrdinalAnalysis` and so cannot
live in the module library `GoodsteinPA`.

Run it after building that library:

    lake build GoodsteinWu && lake env lean scripts/AxiomCheckWu.lean   # silent + exit 0 = clean

Every guard pins the EXACT expected axiom set, the standard triple
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, no cited mathematical axiom, no
`native_decide`/`ofReduceBool`.  Any drift makes this file fail to elaborate.
-/

-- Wainer's classification of PA's provably total functions: both halves.
/-- info: 'GoodsteinWu.wainer_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinWu.wainer_classification

-- The lower half proper: every `fastGrowing o` with `o < ε₀` is PA-provably total.
/-- info: 'GoodsteinWu.fastGrowing_provably_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinWu.fastGrowing_provably_total

-- The one route ingredient absent from Wu's package: conservation of `PA[X]` over `PA`.
/-- info: 'GoodsteinWu.Conservation.peano_of_paLX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinWu.Conservation.peano_of_paLX

-- The Gentzen upper bound applied: `𝗣𝗔 ⊢ isNF ⌜a⌝ → ∀ n, ∃ y, fgGraph ⌜a⌝ n y`.
/-- info: 'GoodsteinWu.ApplyTI.peano_fg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinWu.ApplyTI.peano_fg

-- The ℕ read-off, the only place well-foundedness is used.
/-- info: 'GoodsteinWu.Readoff.fgGraph_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinWu.Readoff.fgGraph_sound

-- The required external input, for the record.
/-- info: 'OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound
