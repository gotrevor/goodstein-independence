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
