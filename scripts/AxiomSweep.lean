/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA
import GoodsteinPA.Statement
import GoodsteinPA.Result.ConsistencyPA
import Lean
import Mathlib.Util.AssertNoSorry

/-!
# Repo-wide axiom sweep — the *unconditional* anti-fraud surface

`scripts/AxiomCheck.lean` pins the axiom set of the four designated headline theorems.  That is the
statement we advertise, but it is a spot check: a `sorry` parked anywhere else in `GoodsteinPA/`
stays invisible to it as long as the summit does not reach that declaration.

This file closes that hole.  It walks **every** declaration in every module whose name starts with
`GoodsteinPA` and collects its transitive axiom dependencies, then throws unless each one lies in the
allowlist

    {propext, Classical.choice, Quot.sound}

— the standard mathlib triple.  In particular any `sorryAx` (a `sorry` or `admit`), any
`Lean.ofReduceBool` (a `native_decide`), and any hand-declared blueprint `axiom` reachable from
anywhere in the library makes THIS FILE fail to elaborate.  A clean run is silent:

    lake env lean scripts/AxiomSweep.lean   # no output + exit 0 = the whole library is clean

Note the complementary roles of the three audit scripts:

* `AxiomCheck.lean`  — the four headline *statements* are clean (narrow, human-readable, pinned).
* `AxiomSweep.lean`  — *nothing anywhere* in `GoodsteinPA/` is dirty (broad, unconditional).
* `statement-check.sh` — no declaration's statement drifted from the frozen baseline.

Abandoned proof routes live in `wip/`, which is not a `lean_lib` in `lakefile.toml` and so is
neither built nor importable; its `sorry`s are out of scope here by construction.
-/

open Lean Meta Elab Command

private def allowed : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd liftTermElabM do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let mut scanned : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some m := modOf n | continue
    unless (`GoodsteinPA).isPrefixOf m do continue
    if n.isInternalDetail || ci.isUnsafe then continue
    scanned := scanned + 1
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless allowed.contains a do bad := bad.push (n, a)
  if !bad.isEmpty then
    let lines := bad.toList.map fun (n, a) => s!"  {n}  depends on  {a}"
    throwError "AxiomSweep: {bad.size} disallowed axiom dependency/ies \
      among {scanned} GoodsteinPA declarations:\n{String.intercalate "\n" lines}"
