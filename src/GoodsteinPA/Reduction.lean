/-
# Phase 1 — the Gödel II hook (Milestone M2)

Surfaces Foundation's **Gödel II** (`𝗣𝗔 ⊬ Con(𝗣𝗔)`) in usable form and proves the
**meta-reduction**: the whole headline `𝗣𝗔 ⊬ γ` collapses to the *single* implication

    `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`      (the Phase 2–4 girder)

via contraposition against Gödel II. `not_proves_of_implies_consistency` is fully proved and
**axiom-clean** — it is the honest "collapse to one implication" deliverable. The remaining
girder `goodstein_implies_consistency` is a disclosed `sorry`: the `γ ⟹ Con(𝗣𝗔)`-inside-`𝗣𝗔`
reduction (ordinal analysis `TI(ε₀) ⊢ Con(𝗣𝗔)` + the syntactic Goodstein descent), which is the
deep core of Phases 2–3.

ANTI-FRAUD: the headline `Statement.peano_not_proves_goodstein` itself is left as a literal
`sorry` (per `DIRECTION.md`: discharge it only when `#print axioms` is clean). This file does
*not* smuggle that — `goodstein_implies_consistency` carries the only open obligation, openly.

⚠️ **Foundation-side axiom dependency.** Gödel II for `𝗣𝗔` needs the instance `𝗣𝗔.Δ₁`
(`𝗣𝗔` is Δ₁-definable). Foundation currently provides this as an **axiom**
(`PA_delta1Definable`, a disclosed TODO in `Incompleteness/Examples.lean` — the arithmetization
of the full induction scheme is not yet formalized there). Hence `peano_not_proves_consistency`
and anything chaining through it carry `PA_delta1Definable` in `#print axioms`. Discharging that
axiom (Δ₁-definability of `𝗣𝗔`) is a separate residual on the path to a fully clean headline.
-/
import Foundation.FirstOrder.Incompleteness.Examples
import GoodsteinPA.Encoding

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- **Gödel II, surfaced for `𝗣𝗔`.** Peano Arithmetic does not prove its own consistency.
A direct instance of Foundation's `consistent_unprovable`. -/
theorem peano_not_proves_consistency : 𝗣𝗔 ⊬ ↑𝗣𝗔.consistent :=
  consistent_unprovable 𝗣𝗔

/-- **The meta-reduction (Phase 1 deliverable).** If the Goodstein sentence proves `Con(𝗣𝗔)`
inside `𝗣𝗔`, then `𝗣𝗔` does not prove the Goodstein sentence. So the entire headline collapses
to the one implication `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. Proved by contraposition against Gödel II;
axiom-clean (no `sorry`). -/
theorem not_proves_of_implies_consistency
    (H : 𝗣𝗔 ⊢ ↑goodsteinSentence → 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent) :
    𝗣𝗔 ⊬ ↑goodsteinSentence := fun h => peano_not_proves_consistency (H h)

/-- **The Phase 2–3 girder (disclosed open target).** Inside `𝗣𝗔`, the Goodstein sentence `γ`
implies `Con(𝗣𝗔)`. Held at `sorry` — the honest checkpoint for Phases 2–3.

**Faithful decomposition (Rathjen 2014 "Goodstein revisited" Cor 3.7 / Thm 2.8; lap-46 route
resolution, see memory `route-resolved-prwo-gentzen`).** Two girders, both deep:

1. **§3 reduction `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ PRWO(ε₀)`** — Rathjen §3, all *primitive recursive*: from a primrec
   ε₀-descent (witnessing `¬PRWO`), Cor 3.4 (Grzegorczyk `g`-padding) makes it *slow*, Thm 3.5
   reindexes it to `C(βᵣ) ≤ r+1`, and Lemma 3.6 then yields a non-terminating special Goodstein
   sequence — contradicting `γ`. Status: the ℕ-template is complete (`Grzegorczyk.lean`, sorry-free);
   the model-internal Thm 3.5 block-tail is `InternalThm35.bbtail_*` (lap 46); the crux is the
   *internal* Cor 3.4 (Grzegorczyk hierarchy over `V ⊧ 𝗣𝗔`, internal level `l : V`).
2. **`PRWO(ε₀) → Con(𝗣𝗔)`** — Gentzen Thm 2.8(i) (PRA-provable): a primrec ordinal assignment `ord`
   + reduction procedure `R` with `ord(R D) < ord D`; an empty-sequent derivation would give an
   infinite primrec ε₀-descent, forbidden by `PRWO`. THE deep ordinal-analysis girder.

The free-X back-end `Thm56.peano_not_proves_TI` (Buchholz §5, axiom-clean) does NOT chain here
(free-X-TI ⊢ PRWO, wrong direction); it is a banked asset, off the headline path. NB: this route
surfaces Gödel II for `𝗣𝗔`, hence carries Foundation's `PA_delta1Definable` — a separate residual
to a fully clean headline. ANTI-FRAUD: do not discharge until `#print axioms` is clean. -/
theorem goodstein_implies_consistency :
    𝗣𝗔 ⊢ ↑goodsteinSentence → 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent := by
  sorry

end GoodsteinPA
