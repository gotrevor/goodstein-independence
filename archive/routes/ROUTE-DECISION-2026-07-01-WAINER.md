# Route Decision — Wainer growth-rate mainline (2026-07-01)

## Decision

Pivot the Goodstein-independence expedition to the **Wainer/Cichon/Caicedo
growth-rate route**.

Operationally:

- **Stop Route A**: no more grinding the IΣ₁-internalized Gentzen bridge unless the
  operator explicitly reopens it.
- **Do not confuse A' with B**: the Towsner operator route remains a banked
  blueprint, not the default pivot.
- **Mainline B = Wainer growth-rate**: prove `PA ⊬ Goodstein` by showing the
  Goodstein length function outgrows every PA-provably-total recursive function.

## Sources reviewed

Directly reviewed from the local corpus:

- Towsner, *Goodstein's Theorem, epsilon_0, and Unprovability*
  (`papers/towsner-goodstein-epsilon0-unprovability.{pdf,md}`).
- Cichon, *A Short Proof of Two Recently Discovered Independence Results Using
  Recursion Theoretic Methods* (`papers/cichon-1983-short-proof-independence.{pdf,md}`).
- Caicedo, *Goodstein's function*
  (`papers/caicedo-goodstein-function-notes.{pdf,md}`).
- Casteran, *Hydra Battles in Coq*
  (`papers/casteran-hydra-battles-in-coq.{pdf,md}`).
- The repo route reviews and generated blueprint ledger.

Access gap:

- The canonical Fairtlough--Wainer Handbook chapter is not present locally and was
  not found as an accessible full text in a quick web search. The route treats that
  classification as the named external proof-theory debt, not as already verified
  locally.

## Why not Towsner A'

Towsner is a clean exposition, and the existing Path-B/A' blueprint contains real
assets: the lower-bound side is banked, the operator-calculus scaffold is
machine-audited, and its omega-rule-shaped induction machinery is better matched to
the obstruction found in the M2 probe.

But it still keeps a cut-elimination wall. Towsner's theorem 19.9 is the load-bearing
cut-elimination theorem, and his `PA+` presentation deliberately skips a formal
arithmetization bridge back to ordinary PA. In Lean, that means A' trades Godel-II
wiring for another large operator-calculus/cut-elimination project plus a PA/PA+
bridge. It is not the wall-dodge.

## Why Wainer B

Cichon and Caicedo isolate the Goodstein-specific work into concrete growth
arithmetic:

1. Encode a Goodstein state as an ordinal notation below `epsilon_0`.
2. Prove the step-count/length function is Hardy/fast-growing at the
   `epsilon_0` frontier.
3. Invoke Wainer's classification: PA-provably-total recursive functions are
   eventually dominated by some fixed `f_alpha`, `alpha < epsilon_0`.
4. Contradict the Goodstein length lower bound.

This avoids the repo's failed local obligation: an internalized simulation of PA
induction inside the finitary Z calculus. The hard proof-theory does not vanish; it
becomes exactly one named theorem, Wainer classification. That is a better audit
surface and a better formalization shape.

## Lean route spine

The route is now represented in `src/GoodsteinPA/WainerRoute.lean`.

Machine-backed asset already in the build:

```lean
GoodsteinPA.WainerRoute.goodsteinLength_eventually_dominates_fixed_fastGrowing
GoodsteinPA.WainerRoute.goodsteinLength_eventually_strictly_dominates_fixed_fastGrowing
GoodsteinPA.WainerRoute.cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing
```

It packages the existing Cichon/Caicedo lower-bound direction:

```text
for every normal-form ordinal notation o < epsilon_0,
eventually f_o(n) <= goodsteinLength(n) + 2.
```

Then it uses the successor level `osucc o` to absorb the additive slack:

```text
eventually f_o(n) < goodsteinLength(n),
so goodsteinLength is not eventually bounded by any fixed f_o.
```

Named route debt:

```lean
GoodsteinPA.WainerRoute.wainer_bound_of_pa_proves_goodstein
```

Final route theorem:

```lean
GoodsteinPA.WainerRoute.peano_not_proves_goodstein_growth
```

This is not "done"; it is the honest new spine. The headline is proved from exactly
the Wainer classification debt plus the now-proved exact no-fixed-bound
Cichon/Caicedo theorem.

## Goal (OPERATOR DECISION, 2026-07-01 — supersedes the earlier "decide accept-vs-campaign" fork)

**Full discharge or abandon. These are the only two options.** Shipping this result "modulo a
named / citable / accepted Wainer axiom" is a **100% non-starter** (operator, verbatim). The end-state
is either a genuinely axiom-free headline (`#print axioms` = the canonical triple + documented
`native_decide` base, every blueprint axiom turned `axiom → theorem`) or the expedition is abandoned.
A named `axiom` is legitimate ONLY as a *live audit surface for a debt being paid* — never as the ship.
This bar applies equally to Route A's `goodstein_implies_consistency`. So the accept-as-axiom option
below is **deleted**; the real question is whether Route B has a genuine path to ZERO axioms.

## Next work

1. Build a small `ProvablyTotal` interface around Foundation's PA provability
   surface, sufficient to state Wainer classification without handwaving.
2. **Decompose `wainer_bound_of_pa_proves_goodstein` into its two logically-distinct debts** (per the
   full-discharge goal): (a) the Goodstein-specific *provable-totality bridge*
   `PA ⊢ goodsteinSentence → ProvablyTotal goodsteinLength` (tractable — the `InternalGoodstein`
   Σ₁-run substrate already exists), and (b) **Wainer's classification proper**,
   `ProvablyTotal f → ∃ α<ε₀, EventuallyLE f f_α` (the deep debt — its own proof is the ordinal
   analysis of PA; a Castéran ε₀/Hardy/Wainer Coq substrate exists to port).
3. **Feasibility gate (honest, before committing years):** produce a written path-to-zero-axioms for
   (b) — is porting Castéran's Wainer substrate to Lean/mathlib actually reachable, or is it the same
   research-grade wall as Route A's M2 internalization? If neither route has a real path to zero, the
   mandate says *abandon*, and that verdict must be stated plainly, not deferred behind an axiom.
