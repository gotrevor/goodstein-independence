# Goodstein independence over PA

**Goal.** Formalize **Kirby--Paris (1982)**: Peano Arithmetic does *not* prove
Goodstein's theorem. In this repo's notation:

```lean
GoodsteinPA.Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence
```

where `goodsteinSentence` is the faithful arithmetic sentence "every Goodstein
sequence terminates."

## Current route decision

**Decision, 2026-07-01: pivot to the Wainer/Cichon/Caicedo growth-rate route.**

The previous active route tried to finish the headline through Foundation's Godel-II
surface:

```text
PA proves Goodstein -> PA proves Con(PA) -> contradiction by Godel II
```

That forced an IΣ₁-internalized Gentzen/cut-elimination bridge over coded
derivations. After the lap-167--171 M2 probe, the decisive PA-induction leaf exposed
a calculus-expressiveness gap: internal Z has numeral-only forall-left and no
free-variable forall-left/implication-left machinery for the required induction step.
That is not a local proof-engineering snag; it is the finitary-Z versus omega-rule
design fork.

The new mainline is the growth-rate proof:

```text
PA proves Goodstein
  -> the Goodstein length function is PA-provably total
  -> Wainer: every PA-provably-total recursive function is eventually dominated
     by some fast-growing f_alpha, alpha < epsilon_0
  -> Cichon/Caicedo: Goodstein length outgrows every fixed f_alpha below epsilon_0
  -> contradiction.
```

This does **not** make the proof-theoretic strength disappear. It isolates it in the
Wainer provably-total classification instead of spreading it through an internalized
cut-elimination engine. That is the right trade for this repo now: the local Lean
work becomes concrete ordinal/growth arithmetic, and the remaining proof-theory
dependency is a named, citable theorem.

## What is already built

- The Goodstein process itself is local and audited in `GoodsteinPA.Defs`.
- The first-order sentence is faithful:
  `GoodsteinPA.Bridge.goodsteinSentence_faithful`.
- The growth substrate is substantial: `GoodsteinPA.Hardy`,
  `GoodsteinPA.Domination`, and `GoodsteinPA.LowerBound` prove the core
  Cichon/Caicedo lower-bound direction that Goodstein length eventually dominates
  every fixed fast-growing level below `epsilon_0`, up to the documented additive
  slack.
- `GoodsteinPA.WainerRoute` is now the route spine: it records the Wainer-route
  theorem, the machine-backed domination lemma already proved here, and the exact
  no-fixed-bound theorem needed to contradict a fixed Wainer upper bound.

## What remains

The route now has one explicit, non-hidden proof-theory debt:

1. **Wainer classification, specialized:** if PA proves Goodstein, then the
   Goodstein length function is eventually bounded by some `f_alpha`,
   `alpha < epsilon_0`.

The Cichon/Caicedo no-fixed-bound side is now in Lean:
`GoodsteinPA.WainerRoute.cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing`.
It follows from the existing Goodstein lower bound at `osucc alpha` plus the proved
successor-level gap `f_alpha(n) + 2 < f_{osucc alpha}(n)` for large `n`.

See `ROUTE-DECISION-2026-07-01-WAINER.md` and `DIRECTION.md`.

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
