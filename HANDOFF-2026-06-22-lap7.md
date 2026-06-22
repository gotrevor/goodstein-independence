# HANDOFF — 2026-06-22 (lap 7)

> **NEXT LAP FIRST ACTION:** read this + `STATUS.md` + `ANALYSIS-2026-06-22-cutelim-k-threading.md`
> (the whole thing, incl. the ADDENDUM) + `PENDING_WORK.md` step 1. Build is **green**
> (`lake build GoodsteinPA`, 1257 jobs). `wip/BoundedZinfty.lean` compiles standalone **sorry-free**
> (`lake env lean wip/BoundedZinfty.lean`). Headline still a literal `sorry` (anti-fraud, correct).

## What landed this lap (6 commits, all verified)

This was a **crux-resolution + ingredient lap**, not a new-girder-built lap. The §19.6 cut-reduction
that lap 6 pointed at turned out to have a deeper layer; this lap mapped it precisely and proved the
one ingredient that's fully tractable.

1. **RESOLVED the cut-elim `k`/`τ` crux offline** (the open lap-6 `ON-LINE-REQUEST`). Read Towsner
   §15–§20 on disk. The lap-6 "norm grows under addition ⟹ cut-elim breaks `norm<k`" worry was a
   **misframing**: (a) `k` is NOT fixed — it grows (§19.5 `k↦2k`; §19.6 `k↦h_{β#ω}(k)`; §19.7
   `k↦h_{ω^α}(k)`); (b) `lowerBound_hardy_selfcontained` is already `∀k` ⟹ growth harmless; (c) every
   `ONote` is `<ε₀` by construction ⟹ ε₀ side-condition FREE. ⟹ **state the whole cut-elim chain
   existentially in `k`** (`CutFree α Γ := ∃k, Zk α k 0 Γ`); ordinary `+` with slack (no `nadd`).
   Full write-up: `ANALYSIS-2026-06-22-cutelim-k-threading.md` (top section).

2. **Route decision: STAY ROUTE B** (the operator delegated it). Recorded in `STATUS.md` with rationale
   — the one doubtful Route-B girder (the `(α,k)` cut-elim bookkeeping) is exactly what (1) resolved;
   Route A's surface is larger. Archived the operator route-choice note, removed `OPERATOR-NOTE`.

3. **PROVED `norm_addAux_le` + `norm_add_le {α γ NF} : norm(α+γ) ≤ norm α + norm γ`** (axiom-clean,
   banked in `wip/BoundedZinfty.lean`). This is the `τ(α#β)≤τα+τβ` §19.6 budget fact. **NF is essential**
   — the NF-free version is machine-checked FALSE; the equal-exponent coefficient blow-up is killed by
   **additive-principality absorption** (`a + γ = γ` when `repr a < ω^(repr e) ≤ repr γ`, via
   `Ordinal.add_of_omega0_opow_le`). `wip/BoundedZinfty.lean` is now **sorry-free**.

4. **Mapped the real §19.6 frontier — the `allω`-commuting obstruction.** Starting `cutReduceAll`,
   found that the commuting ω-rule case (∃-side's last rule is an ω-rule) **cannot keep the ω-rule's
   `max{k,n}` norm budget after adding `α` to the bound**: `norm(α+βₙ) ~ norm α + n` exceeds `max K n ~
   n` for large `n`, for ANY fixed `K` (norm is not `<`-monotone, so `βₙ<β` does not bound `norm βₙ`;
   natural sum + `τα<k` don't save it). Towsner's "follows from IH" glosses this. This is the genuine
   remaining depth of step 1. Full derivation + 3 attack options in the ANALYSIS **ADDENDUM**;
   `ON-LINE-REQUEST` re-filed (one layer down — Buchholz operator-control / S-W bounding lemma).

## THE NEXT MOVE — §19.6 attack **option 2** (controlled ω-rule index; offline, recommended)

The principal `exI` case of `cutReduceAll` is clean; the live frontier is the commuting `allω` case.
Lap-7 investigation makes **option 2 the recommended path** (lightest, no literature needed):

- **Why it should work:** `hardy_lt_goodsteinLength {α NF} : ∃ N, ∀ m ≥ N, hardy α m < G m`
  (`src/LowerBound.lean:258`) — G beats `hardy α` at *every* large `m`, huge margin. So a **linearly**
  controlled ω-rule premise-index `f n ≤ n + c` is very plausibly absorbable.
- **Plan:** (a) generalize `B.allI` (`src/LowerBound.lean`) and `Zk.allω` (`wip/BoundedZinfty.lean`) to
  carry a controlled increasing index `f` with `f n ≥ n` (instead of the rigid `max k n`); (b) re-prove
  `allInv` + `lowerBound_hardy_selfcontained` with `f` — the lower-bound I∀ case needs
  `hardy α (f x) < G x`; with `f x ≤ x+c`, reduce `hardy α (x+c) < G x` to the banked
  `hardy α' x < G x` via a **new Hardy argument-shift lemma** `hardy α (x+c) ≤ hardy (bump α by c) x`
  (the one new Hardy fact to prove); (c) §19.6 commuting case then reconstructs at
  `f'(n) = norm α + f(n)`, which fits because `norm(α+βₙ) < norm α + f(n) = f'(n)`.
- **Caution:** this REFACTORS the (currently sorry-free) `wip/BoundedZinfty.lean` calculus + the M6
  lower bound. Start fresh-headed; don't half-break the clean state — branch the calculus def first,
  prove the new Hardy shift lemma standalone, then thread it.
- **Fallbacks:** option 1 (Buchholz operator-controlled `Zk`, `buchholz-beweistheorie` §9 on disk —
  larger refactor) or option 3 (Hardy 16.8–16.10, likely insufficient per the `+α` analysis).

## State of the spine (Route B, hardest-first)
- **M1, M2, Phase 0/1** — done, clean.
- **M5 (unbounded `(α,c)` cut-elim, `src/Zinfty.lean`)** — done, clean. Template for `cutReduceAll`
  (lap-3 `cutReduceAllAux` at `src/Zinfty.lean:785` — the structure to port to `Zk`).
- **M6 (Hardy lower bound, `src/LowerBound.lean`)** — done, clean (`∀k`).
- **Step 1 (`Zᵏ` cut-elim, `wip/BoundedZinfty.lean`)** — calculus + §19.2–19.5 (inversions, ∧/∨
  reductions) + `norm_add_le`/`norm_addAux_le` done. **§19.6 (`cutReduceAll`) = the live crux**
  (commuting-`allω` obstruction; option 2 above). Then §19.7 `cutElimStep` + §19.9 `cutElim`.
- **Step 2 (M4 embedding)** — independent of the §19.6 blocker; reconnaissance done lap 6 (see lap-6
  HANDOFF + `PENDING_WORK` step 2). Foundation-heavy. A viable parallel thread if §19.6 stalls.
- **Step 4 (subformula bridge), M7a (language gap), M7b (assembly)** — downstream.

## Notes
- **Aristotle:** left idle — the §19.6 work is not cleanly self-containable (needs the real Hardy/
  domination defs + the calculus). A possible bounded target once option 2 is set up: the **Hardy
  argument-shift lemma** `hardy α (x+c) ≤ hardy (bump α by c) x` (self-contained ordinal/Hardy fact).
- **`WebFetch` is dead in the box; `WebSearch` works.** The re-filed `ON-LINE-REQUEST` is for a
  networked session; meanwhile option 2 is offline-doable, so don't block on it.
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`. Headline `sorry` intact.
- No uncommitted edits; tree clean at `a6a5892`.

## File map (changes this lap)
- `ANALYSIS-2026-06-22-cutelim-k-threading.md` — **NEW**: the `k`/`τ` crux resolution + §19.6 ADDENDUM.
- `wip/BoundedZinfty.lean` — added `norm_addAux_le`, `norm_add_le` (both proved); sorry-free.
- `STATUS.md`, `PENDING_WORK.md` — lap-7 entries, route decision, §19.6 plan + option 2.
- `ON-LINE-REQUEST.md` — re-filed (§19.6 commuting-case bounding).
- `archive/findings/…operator-route-choice.md` — archived; `OPERATOR-NOTE…` removed.
