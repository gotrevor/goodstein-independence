# ANALYSIS lap 78 — the criticality-under-substitution wall is DEEPER than the lap-77 plan assumed

**TL;DR.** The lap-77 handoff's front (A) ("generalize `ZDerivation_zsubst` to a freshness
predicate `aNotEigen d` + `a ∉ FV(conclusion)`") is **not sufficient**: I can exhibit explicit
counterexamples showing `ZDerivation_zsubst` *cannot* preserve the `zKValid` **criticality**
conjunct (`∀ i, ¬ iperm (tp dᵢ) s`, `InternalZ.lean:1204`) under a non-vacuous numeral
substitution — **even with full Buchholz regularity**. The wall is an *architecture* problem in the
chain-rule design, not a missing hypothesis. This needs a deep-reflection design decision before
rung 2 can proceed via `ZDerivation_zsubst`.

## The two counterexamples

`fvSubst a t` collapses `^&a ↦ t`; it is **not injective on formulas**. Criticality is a
*formula-inequality* (`tp dᵢ ≠ seqSucc s`, via `iperm_isymR_iff`), which inequalities do **not**
survive a non-injective map.

**CE-1 (kills `aNotEigen`-only).** Inner chain node, conclusion `s'` with
`seqSucc s' = ^∀(0 = ^&a)`, critical premise `dᵢ` with principal `P = ^∀(^&a = ^&a)`.
- Original: `P ≠ seqSucc s'` ⟹ `¬ iperm (tp dᵢ) s'` ✓ (critical).
- After `a ↦ 0`: `fvSubst a 0 P = ^∀(0=0)` and `fvSubst a 0 (seqSucc s') = ^∀(0=0)` — **equal**, so
  `iperm (tp (zsubst dᵢ)) (fvSubstSeqt s')` now HOLDS ⟹ criticality FAILS ⟹ `zsubst d` is not a
  valid `ZDerivation`.
- This is consistent with `aNotEigen d` (`a` is nobody's I∀/Ind eigenvariable — it occurs only
  *free* in principal formulas, which is allowed) and with `a ∉ FV(global conclusion)` (the *inner*
  chain conclusion `s'` may contain `^&a` while the *global* one does not). So the lap-77 hypotheses
  do **not** rule CE-1 out.

**CE-2 (kills even full Buchholz regularity).** Suppose regularity holds: `^&a` occurs only inside
occurrences of the fixed induction formula `F(·)`. Take inner chain conclusion `seqSucc s' = F(2)`
(`a`-free), critical premise principal `P = F(^&a)`.
- Original: `F(^&a) ≠ F(2)` ⟹ critical ✓.
- After `a ↦ 2` (one of the numerals rung 2 substitutes, `i = 0…k-1`): `F(2) = F(2)` — **equal**,
  criticality FAILS.
- Regularity does not save this: the collapse is "substituted numeral coincides with a term already
  present in the (a-free) conclusion." Since rung 2 substitutes the whole range `i = 0…k-1`, any
  inner chain concluding `F(j)` with `j < k` is hit at `i = j`.

## Why this matters for rung 2

Rung 2 (Buchholz 14.24 Ind reduct) builds `K^{rk F}⟨d0, d1(a/0), …, d1(a/k-1)⟩` whose **premises** are
`zsubst d1 at' i`. For the OUTER chain to be `zKValid`, each premise must itself be a genuine
`ZDerivation` — i.e. `ZDerivation_zsubst d1 at' (numeral i)` must hold. CE-2 shows that if `d1`
contains an inner chain concluding `F(j)` (`j<k`) with a critical `F(at')`-premise, then
`d1(at'/j)` is **not** a valid `ZDerivation`. So `ZDerivation_zsubst` — as the exact-validity-preserving
lemma rung 2 wants — is **false** for the derivations rung 2 feeds it, in the current design.

## The fork (next deep-reflection decision — do NOT snap-pick on a grind lap)

1. **Re-reduction semantics.** Don't demand `zsubst d` be *valid*; demand it *reduces to* a valid
   derivation (substitution creates new redexes, which cut-elim then removes). This is the textbook
   picture but it complicates rung 2: the reduct premises aren't `ZDerivation`s on the nose.
2. **Structural criticality.** Redefine the chain rule so the "principal/cut premise" is tracked by
   an explicit index/marker (or by cut-*rank*), not by the formula-inequality `tp dᵢ ≠ seqSucc s`.
   Then a numeral collapse is harmless (the marker is preserved). This is a `zKValid`/`isChainInf`
   redesign touching the whole RedSound architecture and the L3.1 redex finder.
3. **Restrict + discharge the side-condition.** Keep `ZDerivation_zsubst` exact but add a hypothesis
   that rules out CE-2 ("no inner chain conclusion succedent is `F(j)` for `j` in the substitution
   range"), and prove rung 2 only ever substitutes into `d1` satisfying it. Risk: the hypothesis may
   be false for general `d1` (an Ind-step derivation can certainly cut on `F(j)` internally).

Option 2 is the most principled (it matches how Buchholz's *operator-controlled* `H`-derivations
actually track main formulas — by the control/rank, not by syntactic inequality vs the end-sequent)
and most likely correct, but it is the largest rewrite. Option 1 is faithful but heavy. Option 3 is
the cheapest IF the side-condition is true, which is doubtful.

## Bottom line for the grind

`ZDerivation_zsubst` in its lap-77 `d ≤ a` (vacuous) form is **complete and axiom-clean** and stays
banked. The *non-vacuous* generalization that rung 2 needs is blocked on the fork above — a genuine
multi-lap architecture problem, NOT a one-lap freshness-predicate addition. The lap-77 caveat
("freshness-predicate generalization for rung 2") under-scoped it. Until the fork is decided, the
productive front is the independent, mandatory **`PA_delta1Definable`** (this lap) and the eventual
chain-rule redesign (option 2).
