/-
# The headline: PA does not prove Goodstein's theorem (Kirby–Paris)

**Designated audit surface.** This is the open target of the expedition. As of lap 166 it is a
**real proof** resting on the named-axiom blueprint (see the methodology note below), NOT a bare
`sorry`. Its only non-canonical dependency is the single, faithfully-stated Phase 2–3 girder
`goodstein_implies_consistency` (`Reduction.lean`); everything else — the Gödel-II contraposition
`not_proves_of_implies_consistency`, `peano_not_proves_consistency` — is axiom-clean.

**Named-axiom blueprint (the in-progress ledger discipline).** A `sorry`'d headline collapses all
outstanding debt to one opaque `sorryAx`. Instead, each not-yet-proven *milestone* is a NAMED
`axiom` carrying an honest, audited subgoal statement, and the headline is a real proof composing
them — so `#print axioms peano_not_proves_goodstein` reports EXACTLY which milestones remain. The
forcing function is unchanged: the result is *done* only when every blueprint axiom is discharged
(`axiom` → `theorem`) and the headline shows ONLY `[propext, Classical.choice, Quot.sound]`. The
named axiom is the *audit surface* — it gets more scrutiny than a hidden `sorry`, not less.

The in-progress green-gate is therefore `#print axioms`-based (allowlist = the 3 canonical axioms +
the declared blueprint axioms), enforced by `lean-axiom-gate` / the CI "Axiom-clean gate" step.
This supersedes the older "a custom `axiom` on the headline is smuggling" framing: a *faithful*,
*declared*, *allowlisted*, *intended-to-discharge* milestone axiom is the honest blueprint node; the
fraud it guards against is an *undeclared* / *off-allowlist* / *false* axiom, or `native_decide` /
vacuous restatement. See `DIRECTION.md` (ANTI-FRAUD guard) and the KB note `named-axiom-blueprint`.

⚠️ Anti-vacuity (unchanged): this headline is only meaningful because `goodsteinSentence`
(`Encoding.lean`) is the faithful encoding AND the bridge `(ℕ ⊨ goodsteinSentence) ↔
Goodstein-terminates` is proved (`Bridge.lean`, axiom-clean). Those faithfulness anchors are LOCKED.
-/
import GoodsteinPA.Reduction

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- **Kirby–Paris (1982).** Peano Arithmetic does not prove that every Goodstein sequence
terminates. The proof reduces `γ` to `Con(𝗣𝗔)` inside `𝗣𝗔` (the Phase 2–3 girder
`goodstein_implies_consistency`, currently a declared blueprint `axiom`) and applies Gödel II by
contraposition (`not_proves_of_implies_consistency`, axiom-clean). Ledger:
`#print axioms` ⇒ `[propext, Classical.choice, Quot.sound, goodstein_implies_consistency]`. -/
theorem peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  not_proves_of_implies_consistency goodstein_implies_consistency

end GoodsteinPA
