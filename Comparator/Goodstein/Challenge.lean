/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Data.Nat.Log
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.HFS
import Comparator.Goodstein.Support.Defs
import Comparator.Goodstein.Support.InternalGoodstein

/-!
# Kirby–Paris independence of Goodstein's theorem — comparator CHALLENGE (the audit surface)

This file is the **thing a human audits.** It imports only `Foundation` and `Mathlib.Data.Nat.Log`
(the full `Mathlib` umbrella cannot be imported alongside Foundation — both generate the auto
equation lemma `Matrix.map.eq_1`, a duplicate-declaration error; Foundation already pulls in most of
Mathlib transitively, and `Nat.Log` is all the trio below adds). It re-derives every repo-owned
notion that appears in the two headline statements — with its **real body** and
under its **real fully-qualified name** — and states the two theorems with `sorry`. `Solution.lean`
(which imports the real development) must prove *these exact statements*, and `comparator`
machine-checks that it did: every declaration in the statement here must be **identical** in the
solution environment, the proofs must be accepted by the Lean kernel *and* the independent `nanoda`
kernel, and they may use no axioms beyond `propext`, `Quot.sound`, `Classical.choice`.

So the trust chain is: *read this file, and only this file* — then comparator certifies the rest.

## Trust base: Mathlib **and** Foundation

Unlike a Mathlib-only entry, this one honestly rests on `Mathlib + Foundation`
(`FormalizedFormalLogic/Foundation`, pinned by rev in `lakefile.toml`). The independence *statement*
`𝗣𝗔 ⊬ ↑goodsteinSentence` is inherently a claim about a **specific formal system**, Peano
Arithmetic, so it can only be phrased over a library that *has* first-order logic, a real `𝗣𝗔`, and
Σ₁ arithmetization — which is what Foundation supplies. "Mathlib-only" is a trust-minimization
convention, not a tool constraint; widening the base to `Mathlib + Foundation` is a one-line
decision (the same basis on which Flypitch's CH-independence sits in comparator's `1000.yaml`).
Because both the challenge and the solution `require` the *same* Foundation at the *same* rev,
Foundation's own constants (`𝗣𝗔`, `⊬`, `Rew.subst`, `PR.Blueprint`, `Sentence ℒₒᵣ`, …) are literally
the same declarations in both environments and match automatically. The only constants written out
in full below are the ones this development *owns*.

⚠️ Deliberately **no definition holes** (`definition_names`). Comparator only checks a hole's name,
type and universe, which is a gameable surface. In particular a hole on `igoodsteinDef` would let a
solution substitute *any* Σ₁ formula for the internal Goodstein run: the faithfulness anchor
`goodsteinSentence_faithful` would **not** stop it, because its right-hand side
`∀ m, ∃ N, goodsteinSeq m N = 0` is a *proved theorem*, so the `↔` collapses to just
`ℕ ⊧ₘ goodsteinSentence`, satisfiable by any ℕ-true PA-unprovable ∀∃-sentence. So every definition
below carries its real body and is covered by the strict statement-identity check instead.

## The two things the headline says

* `peano_not_proves_goodstein` — **Kirby–Paris (1982):** Peano Arithmetic does not prove the
  first-order sentence `goodsteinSentence`, which internalizes "every Goodstein sequence reaches 0".
* `goodsteinSentence_faithful` — **anti-vacuity anchor:** the standard model `ℕ` satisfies
  `goodsteinSentence` *iff* the genuine, small, auditable `goodsteinSeq` (Goodstein's real
  hereditary-base process, below) reaches `0` from every seed. This ties the opaque syntactic object
  to a definition a human can read, ruling out a vacuous or mis-encoded reading.

## The construction (Goodstein 1944; independence: Kirby–Paris 1982)

For a base `b ≥ 2`, the *hereditary base-`b`* representation writes `n` in base `b`, then rewrites
every exponent in base `b`, recursively. `bump b n` replaces every occurrence of the base `b` by
`b + 1` (exponents bumped recursively, digits unchanged). The **Goodstein sequence** seeded at `m`
is `G 0 = m`, and `G (k+1)` bumps the hereditary base `(k+2) ↦ (k+3)` in `G k` and then subtracts
one (`0` is a fixed point). Goodstein's theorem — that every such sequence reaches `0` — is true
(provable in ZFC, hence in Lean), but Kirby–Paris showed PA cannot prove it: that unprovability is
`peano_not_proves_goodstein`.

The `…Def` objects below are the **arithmetization** of that process: `ipowDef`/`ilogDef` are
variable-base power and logarithm as Σ₁-graphs, `bumpNextDef`/`ibumpTableDef`/`ibumpDef` build the
hereditary base-change `bump` inside a model of `IΣ₁` by the standard table reduction of strong
recursion to primitive recursion (`PR.Blueprint`/`PR.Construction`), and `igoodsteinDef` runs the
Goodstein recursion on the step index. `goodsteinSentence := “∀ m, ∃ N, !igoodsteinDef 0 m N”` is
the resulting first-order sentence. Read them against Rathjen / Goodstein 1944.

## References
* R. L. Goodstein, *On the restricted ordinal theorem*, J. Symbolic Logic **9** (1944), 33–41.
* L. Kirby, J. Paris, *Accessible independence results for Peano arithmetic*, Bull. LMS **14**
  (1982), 285–293.
-/

-- Load-bearing despite looking like a no-op: the two headline statements below are `sorry` by
-- design, and the library builds warnings-as-errors. Removing this line fails the Comparator build.
-- (Same load-bearing line as tao-collatz / lean-gallery challenges.)
set_option warningAsError false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol LO.Entailment

/-- Fork models-theory notation `V ⊧ₘ* T` (was `ModelsTheory`), now `V↓[ℒₒᵣ] ⊧* T` (`ModelsSet`).
Copied verbatim from `src/GoodsteinPA/Compat.lean:33`; notation creates no constant, so this brings
the spelling into scope without importing any repo code. -/
notation:45 V:46 " ⊧ₘ* " T:46 => (V↓[ℒₒᵣ]) ⊧* T

/-- Fork single-formula models notation `M ⊧ₘ σ` (`Models`), now `M↓[ℒₒᵣ] ⊧ σ` upstream.
Copied verbatim from `src/GoodsteinPA/Compat.lean:37`. `goodsteinSentence_faithful` uses it. -/
notation:45 M:46 " ⊧ₘ " σ:46 => (M↓[ℒₒᵣ]) ⊧ σ

/-! ## The Mathlib-native trio — the small, human-readable audit core

`base`, `bump`, `goodsteinSeq` verbatim from `src/GoodsteinPA/Defs.lean` (Goodstein 1944), re-declared in
`Support/Defs.lean`. This is
the definition the anti-vacuity anchor `goodsteinSentence_faithful` pins the syntactic sentence to.
-/

-- `base`, `bump`, `goodsteinSeq`: see `Support/Defs.lean` (own module, same import as the source).

/-! ## The Foundation-DSL arithmetization

The syntactic objects reachable from `goodsteinSentence` are re-declared verbatim in
`Comparator/Goodstein/Support/{InternalPow,InternalLog,InternalBump,InternalGoodstein}.lean`, one
module per source file, under their real (`_root_.LO.FirstOrder.Arithmetic.…` or
`GoodsteinPA.InternalPow.…`) names.  The split is load-bearing: Lean shares identical auxiliary
proofs (`…blueprint._proof_N`) within a module, so declaring all three `PR.Blueprint 1` objects in
one file renumbers them and the closure no longer matches the solution's.  Every un-re-declared
`!…Def` splice (`znthDef`, `divDef`, `remDef`, `subDef`, `seqConsDef`, `mkSeq₁Def`) resolves to
the shared Foundation constant. -/

/-! ## The sentence and the two headlines -/

namespace GoodsteinPA

/-- **The Goodstein sentence `γ`.** The `ℒₒᵣ`-sentence "every Goodstein sequence terminates", built
from the development's own `𝚺₁`-definable internal run via `igoodsteinDef`:
`γ := ∀ m, ∃ N, igoodstein m N = 0`. Verbatim from `Encoding.lean:83` (`noncomputable def`). -/
noncomputable def goodsteinSentence : Sentence ℒₒᵣ :=
  “∀ m, ∃ N, !igoodsteinDef 0 m N”

/-- **Kirby–Paris (1982).** Peano Arithmetic does not prove `goodsteinSentence`, i.e. it cannot
prove that every Goodstein sequence terminates. Stated with `sorry`; `Solution.lean` supplies the
development's real proof, footprint `[propext, Classical.choice, Quot.sound]`. -/
theorem peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence := sorry

/-- **Anti-vacuity anchor.** The standard model `ℕ` satisfies `goodsteinSentence` iff every Goodstein
sequence — the genuine hereditary-base process of the `goodsteinSeq` above — reaches `0`. This ties
the syntactic sentence to the small, auditable definition; without it the independence claim could be
about the wrong sentence. Stated with `sorry`; `Solution.lean` supplies the real proof. -/
theorem goodsteinSentence_faithful :
    (ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0 := sorry

end GoodsteinPA
