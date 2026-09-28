/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Foundation.FirstOrder.Arithmetic.HFS

/-!
# Comparator challenge support — arithmetization brick 1 (`ipow`)

Verbatim re-declaration of the variable-base power `𝚺₁`-objects from `src/GoodsteinPA/InternalPow.lean`.

**Why this is a separate module and not inline in `Challenge.lean`.** Lean lifts the auto-generated
well-formedness proof of a `.mkSigma`/`PR.Blueprint` into an auxiliary `…_proof_N` declaration, and
*deduplicates* identical such proofs against earlier declarations **in the same module**. The three
`PR.Blueprint 1` objects the sentence closure reaches — `pow.blueprint` (here),
`bumpTable.blueprint`, `goodstein.blueprint` — share one arity-1 proof. In the real development they
live in three different files (`InternalPow.lean`, `InternalBump.lean`, `InternalGoodstein.lean`), so
each gets its *own* `…_proof_N`; co-locating them in one challenge file would make the later two
dedup onto `pow.blueprint._proof_1`, giving a **different `ConstantInfo`** than the solution and
failing comparator's byte-identity check. So these support modules mirror the source-file boundaries
one-for-one. This module carries `pow.blueprint`, exactly as `InternalPow.lean` does.

`Challenge.lean` is still the audit surface; these modules just reproduce the development's own module
structure so the arithmetization objects elaborate byte-identically.
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace GoodsteinPA.InternalPow

/-- Primitive-recursion blueprint for variable-base power: one parameter (the base `x = b`),
`zero ↦ 1`, `succ : ih ↦ ih * b`. Verbatim from `src/GoodsteinPA/InternalPow.lean:31`. -/
def pow.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = 1”
  succ := .mkSigma “y ih n x. y = ih * x”

/-- `𝚺₁`-definition of `ipow` (variable-base power `b ^ x` inside a model of `IΣ₁`), with the
argument order `(output, b, x)`. Verbatim from `src/GoodsteinPA/InternalPow.lean:53`. -/
def _root_.FFL.FirstOrder.Arithmetic.ipowDef : 𝚺ᴬ₁.Semisentence 3 :=
  pow.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

end GoodsteinPA.InternalPow
