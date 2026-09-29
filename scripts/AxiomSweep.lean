/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA
import GoodsteinPA.Statement
import GoodsteinPA.Result.ConsistencyPA
import Mathlib.Util.AssertNoSorry

/-!
# Repo-wide axiom sweep — the *unconditional* anti-fraud surface

`scripts/AxiomCheck.lean` pins the axiom set of the four designated headline theorems.  That is the
statement we advertise, but it is a spot check: a `sorry` parked anywhere else in `GoodsteinPA/`
stays invisible to it as long as the summit does not reach that declaration.

This file closes that hole.  It takes the transitive axiom closure of **every** declaration in every
module whose name starts with `GoodsteinPA` — public, `private`, and compiler-internal alike, with no
`isInternalDetail` filter, so nothing can hide behind a name — and throws unless the union is exactly

    {propext, Classical.choice, Quot.sound}

the standard mathlib triple.  In particular any `sorryAx` (a `sorry` or `admit`), any
`Lean.ofReduceBool` (a `native_decide` reachable from a *named* declaration), and any hand-declared
blueprint `axiom` makes THIS FILE fail to elaborate.  A clean run is silent:

    lake env lean scripts/AxiomSweep.lean   # no output + exit 0 = the whole library is clean

## On the `native_decide` anchors

`…/Goodstein/Domination/Anchors.lean` and `…/Hardy/Anchors.lean` hold the anti-vacuity witnesses
(`goodsteinLength 3 = 5`, `bump 2 4 = 27`, …).  Those deliberately use `native_decide`, and are
written as anonymous `example`s precisely so that no named declaration can depend on them — which is
why they do not show up here.  They are still elaborated on every build, so they still guard against
definitional drift; they simply cannot contaminate the trusted base.  The sweep asserts below that
those modules are still *present and imported*, so silently dropping the anchors is also caught.

## Complementary roles of the audit scripts

* `AxiomCheck.lean`    — the four headline *statements* are clean (narrow, human-readable, pinned).
* `AxiomSweep.lean`    — *nothing anywhere* in `GoodsteinPA/` is dirty (broad, unconditional).
* `statement-check.sh` — no declaration's statement drifted from the frozen baseline.
* `deshim-check.sh`    — the Foundation compat shim is gone and nothing re-creates it.

Abandoned proof routes live in `wip/`, which is not a `lean_lib` in `lakefile.toml` and so is
neither built nor importable; its `sorry`s are out of scope here by construction.
-/

open Lean Elab Command

/-- The only axioms any `GoodsteinPA` declaration may depend on. -/
private def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Anti-vacuity anchor modules that must stay imported (see the note above). -/
private def requiredAnchors : List Name :=
  [`GoodsteinPA.ToMathlib.Goodstein.Domination.Anchors, `GoodsteinPA.ToMathlib.Hardy.Anchors]

run_cmd liftTermElabM do
  let env ← getEnv
  -- (1) the anchors must still be present, or the anti-vacuity guard has silently vanished.
  for a in requiredAnchors do
    unless env.header.moduleNames.contains a do
      throwError "AxiomSweep: anti-vacuity anchor module {a} is missing from the import graph"
  -- (2) the transitive axiom closure over EVERY declaration, with no name filter.
  let mut scanned : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? n | continue
    unless (`GoodsteinPA).isPrefixOf env.header.moduleNames[i.toNat]! do continue
    if ci.isUnsafe then continue
    scanned := scanned + 1
    for a in (← Lean.collectAxioms n) do
      unless allowed.contains a do bad := bad.push (n, a)
  if !bad.isEmpty then
    let lines := bad.toList.map fun (n, a) => s!"  {n}  depends on  {a}"
    throwError "AxiomSweep: {bad.size} disallowed axiom dependency/ies \
      among {scanned} GoodsteinPA declarations:\n{String.intercalate "\n" lines}"
