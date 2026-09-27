# ROADMAP: PA-independence via ε₀ — Wainer, Goodstein, Hydra, Paris–Harrington

**Opened 2026-09-26.**  Home: `gotrevor/goodstein-independence` (the fork; FFL treats its copy as
abandoned).  Trevor's bar: *not done until Paris–Harrington is done.*

## Why this shape

Every result here has the same skeleton: **(upper) PA-provable Π₂ ⇒ witness bounded by some
`f_α`, `α < ε₀`**, and **(lower) this particular process outgrows every such `f_α`**.  The repo
already proved the upper half, but only for `goodsteinSentence`.  Generalize it once and each
further result costs only its own encoding + lower bound.

Landscape (`archive/findings/ON-LINE-FINDINGS-2026-07-01-independence-formalization-landscape.md`):
the Wainer classification, PA ⊬ Hydra and Paris–Harrington are formalized **nowhere** (~85%).  Coq
`rocq-community/hydra-battles` has hydra termination AND a PA development in one repo but never
connects them.

## Stage 1 — Wainer's bound, general (small: a few laps)

**Statement RATIFIED 2026-09-26** (Trevor + Astra review: Σ₁ matrix is the right interface, "some bounded witness" is the right conclusion since a general Σ₁ least-witness need not be computable, quantifier order and `![N, m]` placement checked; the laps estimate was *not* endorsed) (typechecks against `main` `0628d97`; kept in
`scratch/WainerGeneralDraft.lean`):

```lean
theorem pa_provable_pi2_eventually_witnessed_below_fastGrowing
    (φ : Semisentence ℒₒᵣ 2) (hφ : Hierarchy 𝚺 1 φ)
    (h : 𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ)) :
    ∃ o : ONote, o.NF ∧ ∃ M : ℕ, ∀ m, M ≤ m →
      ∃ N ≤ fastGrowing o m, ℕ ⊧/![N, m] φ
```

Where the Goodstein-specificity lives today (the only things to generalize):
`E1EmbeddingGrind.lean` — `embedding_Zef2TC_V3_linearK`, `goodsteinBodyE_inst_shape`,
`readoff_value_goodstein'`, `goodsteinBodyE_semantic_link`, `wainer_bound_witness`.  The embedding
itself already runs through the generic `BudgetedEmbedsV3` on derivations.

Done when:
- the general theorem is axiom-clean (add it to `scripts/AxiomCheck.lean`);
- `wainer_bound_of_pa_proves_goodstein` is re-derived as a **corollary** (instantiate `φ` with the
  Goodstein body; the least-witness `goodsteinLength` is below any witness);
- a comparator entry `Comparator/Wainer/` certifies the general statement.  Its closure is all
  Foundation + Mathlib, so the Challenge re-declares nothing.

## Stage 2 — PA ⊬ Hydra (large: the Goodstein analogue is ~21.6k lines)

Needs its own (a) hydra datatype + battle, (b) arithmetization inside PA (`Internal*` analogue),
(c) faithfulness bridge, (d) lower bound: battle length outgrows every `f_α`, `α < ε₀`.  Then
stage 1 closes it in a few lines.  `lean-gallery` `LeanGallery/Logic/Hydra` has termination only.

🚦 **Statement decision for Trevor before any grind** (faithfulness risk lives here):
Kirby–Paris Thm 2(ii) quantifies over *recursive strategies*, which is not first-order as stated.
Candidates: (i) one fixed strategy — the K–P strategy `τ` with `[α]_τ(n) = {α}(n+1)`, or the
"standard battle" (always chop the rightmost head); (ii) the Buchholz/Kirby–Paris `n`-th-stage
growth `n` copies convention vs `n+1`.  Pick one, pin it in a small `Statement.lean`, ratify.

## Stage 3 — Paris–Harrington (weeks to months)

`∀ e r k, ∃ N, every r-colouring of [N]^e has a relatively large homogeneous set of size ≥ k`
(relatively large: `|H| ≥ min H`).  Upper half again from stage 1.  New work: the
Ketonen–Solovay α-large-set combinatorics giving the lower bound (PH witness outgrows `f_α`).
Statement risk: "relatively large" is easy to state subtly wrong — pin it early, ratify, and add a
known-answer anchor (small `N` values).  Wikidata-1000 `Q7137494`.

## Discipline carried over

Statements pre-ratified as verbatim Lean before any grind (the copy-not-compose rule that caught
10 statement traps in the Goodstein rebuild); `scripts/AxiomCheck.lean` guards every headline; one
comparator entry per headline.
