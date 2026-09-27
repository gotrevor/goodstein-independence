# Kreisel's unnatural well-ordering (treadmill direction)

**Objective.** Formalize Kreisel's example behind the "natural well-ordering" problem: a
primitive recursive relation `≺` on ℕ that, in the standard model, IS the usual order `<` (type ω),
yet PA cannot prove transfinite induction along it, because that induction would prove Con(PA).
Contrast: PA proves transfinite induction along `<` itself, for every formula.  Same relation in ℕ,
different provability: the proof-theoretic "ordinal" depends on the notation, which is exactly
Kreisel's point.

Branch `kreisel` (off `epsilon0`).  New files under `GoodsteinPA/Kreisel/`.  Commit every green
checkpoint with `git-safe`.  Do not push, do not open PRs.  Keep a dated log at the bottom of this
file; it is the lap-to-lap handoff.

## Phase 1: statements ONLY, then stop for ratification

Write `GoodsteinPA/Kreisel/Statement.lean` with the definitions and the headline statements below,
headlines `sorry`d, compiling (`lake env lean GoodsteinPA/Kreisel/Statement.lean`).  Add
known-answer `example`s where cheap.  Then log it, commit, and STOP (self-stop / `box done`).  Do not
start proving until the log carries a ratification line from Ren.

Mathematical content (the Lean shapes are yours to choose, following Foundation's idioms):

- `prfBot : Semisentence ℒₒᵣ 1`: "z codes a 𝗣𝗔-proof of ⊥", built from Foundation's arithmetized
  proof predicate for `𝗣𝗔` (the same one under `𝗣𝗔.consistent` in
  `Foundation/FirstOrder/Incompleteness/`; Gödel II is `consistent_unprovable : T ⊬ ↑T.consistent`
  in `Second.lean`).  Find the real API with `grep` in `.lake/packages/Foundation`; do not guess.
- `good x := ∀ z ≤ x, ¬ prfBot z` ("no contradiction proof coded at or below x").
- `kreiselLT x y :=
    (good x ∧ good y ∧ x < y) ∨ (good x ∧ ¬ good y) ∨ (¬ good x ∧ ¬ good y ∧ y < x)`.
  If PA is inconsistent with least contradiction-proof p, this is `<` below p, everything below p
  precedes everything from p on, and the tail from p on is ordered in REVERSE (ill-founded).
- `TI (≺) (φ) := (∀ x, (∀ y, y ≺ x → φ y) → φ x) → ∀ x, φ x` as a `Sentence ℒₒᵣ`, for a binary
  semisentence `≺` and unary semisentence `φ`.
- `ltRel`: the ordinary `<` as a binary semisentence.

Headlines:
1. `kreiselLT_iff_lt : ∀ x y : ℕ, (ℕ ⊨ kreiselLT at x y) ↔ x < y`: in the standard model the
   relation is exactly `<` (uses that ℕ ⊨ Con(PA), i.e. PA is sound).
2. `pa_not_proves_TI_kreisel : 𝗣𝗔 ⊬ TI kreiselLT good`: the single instance φ := `good` already fails.
3. `pa_proves_TI_lt : ∀ φ : Semisentence ℒₒᵣ 1, 𝗣𝗔 ⊢ TI ltRel φ`: PA proves TI along `<` for every φ.
4. `kreiselLT_primrec`: the relation is primitive recursive (or: `kreiselLT` is Δ₁/ Σ₁ in
   Foundation's hierarchy; pick the notion Foundation supports and say which in the log).

Faithfulness notes for the statement author:
- Headline 1 must quantify over ALL x y and use the real semantics; not a special case.
- Headline 2 must use exactly the `good` above as φ.  Its proof sketch: inside PA, `good` is
  progressive along `kreiselLT` (if `¬ good x`, then `y := x+1` has `¬ good y` and `y ≺ x`), so TI
  would give `∀ x, good x`, which PA proves equivalent to `𝗣𝗔.consistent`; Gödel II finishes.
- Headline 3 is ordinary strong induction inside PA.

## Phase 2 (after ratification): prove 1-4 sorry-free, import from `GoodsteinPA.lean`, add
`#print axioms` pins to `scripts/AxiomCheck.lean`, `lake build` green.

## Hard rules
- No new `axiom`; `native_decide` acceptable.  No network: all packages are in `.lake/packages`.
- Do not change existing statements anywhere in the repo, `GoodsteinPA/Statement.lean` above all.
- Work-in-progress files stay out of `GoodsteinPA.lean` until they compile.

## Log

### 2026-09-27 — Phase 1 done: statements written, STOP for ratification

`GoodsteinPA/Kreisel/Statement.lean` compiles (`lake env lean GoodsteinPA/Kreisel/Statement.lean`:
only the five disclosed `sorry` warnings).  `lake build` still green, 1489 jobs.  The file is
deliberately **not** imported from `GoodsteinPA.lean` yet (phase 2 does that).

**Foundation API actually used** (found by grep, not guessed):

* `LO.FirstOrder.Arithmetic.Bootstrapping.proof 𝗣𝗔 : 𝚫₁.Semisentence 2`, with
  `Proof T d φ := DerivationOf T d {φ}` its ℕ-side meaning
  (`Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean:478`).  This is the same
  arithmetized predicate under `Theory.consistent = .mkPi (∼provabilityPred T ⊥)`, since
  `provable T = “φ. ∃ d, !(proof T).sigma d φ”`.  Gödel II is
  `Incompleteness/Second.lean:18 consistent_unprovable`.
* `𝗣𝗔.Δ₁` is the *theorem-backed* instance `Arithmetic.PA_delta1Definable`
  (`Incompleteness/InductionSchemeDelta1.lean:1380`) — no axiom.  It needed an explicit import.
* `HierarchySymbol.Semiformula`'s `⋏ ⋎ ∼ ball rew` algebra plus the matching `ProperOn.*` closure
  lemmas (`Arithmetic/Definability/Hierarchy.lean`) — this is what makes the `Δ₁` bookkeeping for
  `goodΔ`/`kreiselLTΔ` mechanical in phase 2.

**Definitions.**  `prfBotΔ : 𝚫₁.Semisentence 1` = `proof 𝗣𝗔` rewritten by
`Rew.subst ![#0, ⌜(⊥ : Sentence ℒₒᵣ)⌝]`.  `goodΔ` = `ball ‘x. x + 1’ (∼ prfBotΔ #0)`, i.e.
`∀ z ≤ x, ¬ prfBot z` (Foundation's `ball t` is `#0 < bShift t`, so the `+1` is what makes it `≤`).
`kreiselLTΔ = (good x ⋏ good y ⋏ x<y) ⋎ (good x ⋏ ∼good y) ⋎ (∼good x ⋏ ∼good y ⋏ y<x)`.
`good`/`kreiselLT`/`prfBot` are the `.val` plain formulas; headlines 1–3 use those.

**Answer to KREISEL.md's "pick the notion" question (headline 4).**  Foundation has no
`Primrec`-of-a-formula notion, and the naive *semantic* reading ("`fun x y ↦ x ≺ y` is primitive
recursive") is **vacuous** here — headline 1 already says that relation is `<`.  So headline 4 is
split into the two non-vacuous syntactic claims:
* `kreiselLT_hierarchy` (already **proved**, `by simp`): the `Σ₁` and `Π₁` halves of `kreiselLTΔ`
  really are in `Hierarchy 𝚺 1` / `Hierarchy 𝚷 1`.  True by construction.
* `kreiselLT_delta1` (sorry): `kreiselLTΔ.ProvablyProperOn 𝗣𝗔`, i.e. `𝗣𝗔` proves the two halves
  equivalent.  This is exactly Foundation's `Δ₁`-ness (it is the `isDelta1` field of `Theory.Δ₁`),
  hence "primitive recursively decidable, provably so".

**Binder-notation orientation, pinned by a passing `example`:** in `“x y. …”` the first binder is
`#0`, and `!ψ a b = Rew.subst ![a,b] ψ` puts `a` at `#0`.  So `ℕ ⊧/![3,5] “x y. x < y”` holds.
`TI r φ := “(∀ x, (∀ y, !r y x → !φ y) → !φ x) → ∀ x, !φ x”`, with `!r y x` reading "y ≺ x".

**Five open obligations** (all in `src`, all phase 2): `kreiselLT_iff_lt`,
`pa_not_proves_TI_kreisel`, `pa_proves_TI_lt`, `kreiselLT_delta1`, and the faithfulness unfolding
`good_iff` (`ℕ ⊧/![x] good ↔ ∀ z ≤ x, ¬ Proof 𝗣𝗔 z ⌜⊥⌝`).  `good_iff` is *not* free from `simp`:
the `∼` of a `𝚫₁` formula evaluates via its `𝚷₁` half, so it needs properness of `prfBotΔ`.  Two
cheaper faithfulness checks **are** discharged as `example`s in the file (`ltRel` semantics, and
`prfBot z ↔ Proof 𝗣𝗔 z ⌜⊥⌝`).

Ratification line for Ren goes here. → **STOP.**
