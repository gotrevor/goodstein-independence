/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA
import Lean

/-!
# Statement snapshot

Prints one line per `GoodsteinPA` declaration: `<name> <hash>`, where the hash is taken over the
declaration's type (and, for definitions, its value) after delta-expanding every constant defined in
`GoodsteinPA.ToFoundation.Compat`.  Expanding the shim makes the fingerprint invariant under
replacing a shim spelling by the upstream term it abbreviates, so a notation-only port leaves every
line unchanged.  `scripts/statement-check.sh` diffs this against `scripts/statement-snapshot.txt`.
-/

open Lean Meta Elab Command

private def compatMod : Name := `GoodsteinPA.ToFoundation.Compat

run_cmd liftTermElabM do
  let env ← getEnv
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let isCompat (n : Name) : Bool := modOf n == some compatMod
  let fp (e : Expr) : MetaM UInt64 := do
    let e ← Core.betaReduce (← deltaExpand e isCompat)
    return e.hash
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some m := modOf n | continue
    unless (`GoodsteinPA).isPrefixOf m do continue
    if m == compatMod || n.isInternalDetail || ci.isUnsafe then continue
    let h ← fp ci.type
    let h ← match ci with
      | .defnInfo d => pure (mixHash h (← fp d.value))
      | _ => pure h
    out := out.push s!"{n} {h}"
  logInfo m!"{String.intercalate "\n" (out.qsort (· < ·)).toList}"
