# ON-LINE-REQUEST — 2026-06-23 (lap 27)

> **⚠️ LAP-30 — THE ONE OPEN REQUEST BELOW IS NOW MOOT (no action needed).** The descent bridge no
> longer needs a hand-built calculus-internal `paLX ⊢ TI_≺(X)` sequent shape. Foundation's first-order
> **completeness theorem** (`Derivation.completeness_of_encodable`) delivers `Derivation2 paLX {TI prec}`
> from the *semantic* premise "every model `M ⊧ paLX` satisfies `TI prec`" — so the E wall is a standard
> **model-theoretic** argument (Rathjen §3 inside a model `M`), not a bespoke sequent skeleton. See
> `DESCENT-PLAN §5` + `src/GoodsteinPA/DescentSemantic.lean`. The §-below is retained as historical
> context; a fulfiller may delete this whole file (no literature request is open this lap).

> **F-φ (the lap-19 `ONote.cmp` computability request) is RESOLVED** — Aristotle proved
> `rePred_ltPull_natCode` (verified-faithful, in `wip/aristotle-fphi/ONoteComp.lean`). No literature
> needed; only a mechanical `v4.28→v4.31` port remains. Item removed.

## The Route-B descent bridge: how is `paLX ⊢ TI_≺(X)` obtained calculus-internally? (sharpened lap 27)

**Decision context (lap 27).** The back-end is now **committed to Route B**: refute the headline by
contradicting the built, axiom-clean `peano_not_proves_TI : IsEmpty (Derivation2 paLX {TI prec})`
(Buchholz Thm 5.6, Gentzen-1943 sharpness, `paLX ⊬ TI_≺(X)` for the **free** set predicate `X`). Route A
(`PRWO ⟹ Con(PA)` + Gödel II) is rejected: it carries the `PA_delta1Definable` Foundation axiom that the
anti-fraud rule forbids on the headline. So the descent wall **E** must deliver
`𝗣𝗔 ⊢ goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})` **directly** — and the internal-V
`sigma1_pos_succ_induction` route (which lands X-free `𝗣𝗔 ⊢ PRWO`) provably cannot, because a
counterexample to the free-`X` `TI prec` is an `X`-definable (not primrec) descent.

**The precise question (any one helps).** Is there a standard reference — Buchholz's *Beweistheorie*
notes §5 (on disk), Schütte, Takeuti, Pohlers, or a cleaner modern source — that carries out the
**lower bound `Goodstein ⟹ paLX ⊢ TI_≺(X)`** *inside the calculus* with the free predicate `X`? Concretely:

1. From a (lifted, X-free) `paLX`-proof of Goodstein termination, how is `paLX ⊢ TI_≺(X)` built? I.e.
   the calculus-internal "well-foundedness of `≺` ⟹ transfinite-induction-for-free-`X`" step: assume
   `Prog(X)` and `¬X a₀`; extract the `X`-definable `≺`-descent via the **LX least-number / induction
   scheme**; slow it down (Rathjen §3); run inequality (6); contradict the lifted Goodstein at the
   `X`-definable seed `m₀ = T̂²(β₀)`. **Which induction instances does this use, and what is the precise
   sequent-calculus shape of the contradiction?**

2. In particular: Rathjen §3's slow-down + inequality (6) are stated for **primitive recursive**
   `(βₖ)`. What changes when `(βₖ)` is instead `X`-definable (the free-predicate case)? Does the
   argument go through verbatim with `InductionScheme LX` replacing primrec induction, or is there a
   subtlety (e.g. the slow-down construction needing primrec-ness)?

**Why it unblocks me.** This is now THE last wall (E-core(b), Route-B form). The lap-26 arithmetic
substrate (internal Goodstein as definable formulas) is built and reusable; what I need is the precise
calculus-internal descent shape so the paLX construction targets the right inference skeleton. Not
blocking — I proceed on the port + the substrate meanwhile.
</content>
