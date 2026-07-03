# ANALYSIS (lap 10, 2026-06-22) — M5's pure-logic Z∞ cannot host the embedding: the **truth-layer gap**

## TL;DR
While formalizing M4's `axm` case (`PA ⊢ φ ⟹ Z∞ ⊢ {↑σ}` for each PA axiom σ), a hard architectural
tension surfaced **on the critical path**:

- **The embedding REQUIRES Z∞ to have an atomic-truth axiom** (every *true closed atomic* sentence,
  e.g. `nm n + 0 = nm n`, is a leaf). Every PA axiom — PeanoMinus equations and induction — bottoms
  out there once the ω-rule strips the quantifiers into closed numeral instances.
- **M5's `Deriv` (`src/GoodsteinPA/Zinfty.lean`) is PURE LOGIC: no atomic-truth leaf.** Its only
  atomic leaf is `axL` (the identity/em axiom, requiring *both* polarities `rel r v` **and**
  `nrel r v`). Module header line 15 + the `atomCutAux` docstring (line ~1000) state this is a
  **deliberate** design: *"atomic + ⊥ cut elimination — no truth layer needed."*
- **These are incompatible.** Adding a one-polarity true-atomic leaf `axTrue` BREAKS the no-truth-layer
  atomic cut-elimination, which relies on `axL` being the sole atomic leaf (an `axL` clash on the cut
  atom puts `nrel r v` in the context, so set-idempotence dissolves the key case). With `axTrue`, a
  cut of a *true* atomic `A` against its *false* negation `∼A` has no `axL` clash to exploit — the
  `∼A` side must be dropped by a genuine **truth layer** (a false closed literal is removable).

So **M5 as-shipped (axiom-clean, "M5 done") cannot serve as the M4 embedding target.** This is not a
bug in M5's stated theorem; it is an *under-specification of the calculus* relative to what the
headline path needs. Caught now, before M4 was wired to the headline.

## Why the embedding needs true atomics (grounded, not hand-waved)
`𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ` (`Foundation/.../Schemata.lean:52`). The `axm` case must
show `ZProvable {↑σ}` for `σ ∈ 𝗣𝗔`:
- **PeanoMinus** (finite, e.g. `∀x, x + 0 = x`): strip `∀` by the ω-rule `allω` ⟹ for every `n`, need
  `Z∞ ⊢ {nm n + 0 = nm n}` — a **true closed atomic**. M5 cannot prove it: `axL` needs both `rel` and
  `nrel`; there is no rule that introduces a lone true atomic.
- **Induction** `univCl(succInd ψ)`: the worked-out derivation (see `PENDING_WORK.md` lap-10 block)
  reduces, via `allω` + meta-induction on `n`, to needing `ψ(nm n + 1)` to match `ψ(nm (n+1))`. But
  `nm n + 1` and `nm (n+1)` are **equal-valued but not syntactically equal** closed terms (mismatch at
  the base: `0+1` vs `1`). Bridging them is the arithmetic fact `nm n + 1 = nm(n+1)` — again a true
  closed atomic Z∞ must supply. Same gap.

So *both* sub-cases of `axm` (and the `exs` closed-term→numeral collapse) bottom out at the SAME
missing primitive: **true closed atomics as Z∞ leaves.**

## The standard resolution (Schütte / Buchholz ω-logic)
The ω-logic `Z∞` used for PA ordinal analysis **always** takes *all true closed atomic sentences as
axioms* (Schütte's "true atomic formulas are axioms"). The atomic cut-elimination then uses a
**truth layer**: a cut on atomic `A` splits on `atomTrue A`:
- `A` true ⟹ `∼A` false ⟹ drop `∼A` from the other premise (it is a removable false literal).
- `A` false ⟹ `A` was never introduced by `axTrue` (needs truth); only `axL` (with `∼A` present,
  dissolved by set idempotence — the *existing* M5 argument) or incidentally.

**This is exactly what M5's sibling calculus already does.** `LowerBound.B` (`LowerBound.lean:67`) —
the abstract cut-free bounding calculus — HAS `trueR` (`atom m n ∈ Γ`, `atomTrue m n`). The planned
"bounding bridge" maps cut-free `Deriv` leaves to `B.trueR`, which *only typechecks if `Deriv` has a
true-atomic leaf to map from.* The architecture already presupposes `axTrue` on `Deriv`; M5 just
never added it.

## Resolution plan (the next deep thread — multi-lap)
Extend `Deriv` with the true-literal leaf and add the truth layer to its cut-elimination:

1. **New constructor** `axTrue {Γ} (L) (hL : L is a closed literal) (htrue : ℕ ⊧ L) (hmem : L ∈ Γ)`.
   Cleanest: `L` ranges over `rel r v` / `nrel r v` with all `v i` ground; `htrue` via Foundation's
   standard-model evaluation (`Semiformula.Evalbm ℕ …` / `models`). `o = 0`, `cr = 0`.
2. **Trivial mirror cases** (each ≈ the `axL` case): `o`, `cr`, `orInvAux`, `andInvAux`, `allInvAux`,
   `cutReduceAllAux`, `cutElimStepAux`. The true literal survives every erase/insert; re-apply `axTrue`.
3. **Truth layer** (the real work, concentrated):
   - Generalize `removeFalsumAux` (removes `⊥`) → `removeFalseLiteralAux` (removes any *false* closed
     literal `L`, `ℕ ⊭ L`, bound-preserving). The `axTrue` case: the removed `L` is false ⟹ `L ≠` the
     true axiom literal ⟹ survives erase ⟹ re-apply `axTrue`. The `axL` case: if `L` is one polarity
     of the clash, its partner is *true* ⟹ close by `axTrue` on the partner.
   - `atomCutAux`: split on `atomTrue (rel r v)`. True ⟹ `removeFalseLiteral` the `nrel r v` (false)
     off `hNC`. False ⟹ the existing set-idempotence argument. `d`'s new `axTrue` case mirrors.
4. **Re-verify** `#print axioms` clean for `cutElim` and re-run the LowerBound bounding (it is on `B`,
   untouched — `Deriv` is used ONLY in `Zinfty.lean`, so blast radius = one file).

**Faithfulness note:** `axTrue` introduces a dependence of `Provable` on ℕ-truth. This is *sound and
standard* (Z∞ is a semi-formal system tied to the standard model) and does NOT weaken the headline:
the independence proof assumes `PA ⊢ goodsteinSentence`, embeds (needs `axTrue` — sound: PA's axioms
ARE ℕ-true), cut-eliminates, and bounds. `axTrue` only lets Z∞ prove *true* things, never false ones,
so it cannot manufacture a spurious derivation of a false sentence.

## Status this lap
- Finding established + grounded in the code (this note). `PENDING_WORK.md` updated with the worked
  `axm` paper proof and this gap. The M5 surgery (steps 1–4) is the next deep thread; it is contained
  to `src/GoodsteinPA/Zinfty.lean` (9 recursion sites) + a re-verify.
- M4 enabler `provable_rew`/`ZProvable.rew` axiom-clean; `embed` 8/10 (shift+all proved); `axm`/`exs`
  blocked precisely on this gap.
