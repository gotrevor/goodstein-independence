# Phase 2 decomposition — the ordinal-analysis girder, lemma by lemma

Grounding: **Towsner, _Goodstein's Theorem, ε₀, and Unprovability_** (2020-03-20, on disk at
`papers/towsner-goodstein-epsilon0-unprovability.pdf`). Cross-checks: Buchholz
(`buchholz-on-gentzens-first-consistency-proof.pdf`), Rathjen 2014
(`rathjen-2014-goodsteins-theorem-revisited.pdf`), Buss Handbook ch.2.

This document turns the deep residual `Reduction.goodstein_implies_consistency`
(and, alternatively, the headline `Statement.peano_not_proves_goodstein` directly) into a
concrete, ordered sequence of Lean milestones. Each milestone cites the exact paper result it
formalizes, so a future lap quotes the source rather than reconstructing it (the documented
LLM-confabulation hazard for infinitary proof theory).

---

## Two routes to the headline

### Route A — Gödel II (the current `Reduction.lean` hook)
`𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ TI(ε₀) → 𝗣𝗔 ⊢ Con(𝗣𝗔)`, then Gödel II (`peano_not_proves_consistency`).
- **Reuses** Foundation's Gödel II directly (already surfaced, axiom-clean mod `PA_delta1Definable`).
- **Costs** Gentzen's `TI(ε₀) ⊢ Con(𝗣𝗔)` (an infinitary `PA_∞` cut-elimination, the classic
  girder) **and** the syntactic descent `γ ⟹ TI(ε₀)`.
- **Inherits** the Foundation axiom `PA_delta1Definable : 𝗣𝗔.Δ₁` (needed even to *state* Gödel II
  for `𝗣𝗔`; a disclosed Foundation TODO — `Incompleteness/Examples.lean`).

### Route B — Towsner / direct (recommended spine) ⭐
Show `𝗣𝗔 ⊬ γ` **directly**, with **no Con(𝗣𝗔) and no `PA_delta1Definable`**:
1. Embed any `PA⁺` proof of `γ` into the infinitary ω-rule calculus `Z_∞` with a *bounded* cut
   rank and an ordinal bound `< ε₀`  (Towsner **Thm 16.7 / 18.1**).
2. Eliminate cuts: `Z_∞ ⊢^{α,k}_c Γ  ⟹  Z_∞ ⊢^{ω_c^α, m}_0 Γ` — cut-free, ordinal still `< ε₀`
   when the input is  (Towsner **§19**, esp. **Thm 19.7, 19.9**).
3. No cut-free `Z_∞` deduction of `∀x∃y g_y(x)=0` exists at any `α < ε₀`  (Towsner **Thm 17.1**),
   because the Goodstein length `𝒢(n)` dominates every Hardy `h_α`, `α<ε₀`.
4. Contradiction ⟹ `PA⁺ ⊬ γ`  (Towsner **Thm 20.1**).

Route B is **more self-contained and elementary** (no Con, no second-incompleteness machinery,
every lemma is explicitly written in Towsner) at the cost of building `Z_∞` + cut-elimination +
the Hardy hierarchy from scratch (no Foundation reuse). For an autonomous lemma-by-lemma grind
with a complete reference proof on disk, **Route B is the better spine.** Route A stays available
(its meta-reduction `not_proves_of_implies_consistency` is proved and axiom-clean).

Decision for the treadmill: **pursue Route B**; keep Route A's hook as a proved fallback. The
headline can be discharged by either; whichever lands first wins. Route B additionally *removes*
the `PA_delta1Definable` axiom from the final profile.

---

## The hard structural obstacle (why this is months, not laps)

`Z_∞` derivations carry an **ordinal bound `α`** and the **ω-rule** (`I∀`) has *one premise per
natural number* — infinite branching. So `Z_∞ ⊢^{α,k}_c Γ` is **not** a plain `inductive`: the
∀-rule's premises are an `ℕ`-indexed family, and the bound recursion is over `Ordinal`
(well-founded but not structural). Candidate Lean encodings (a future lap must pick one and
commit — getting this right IS the crux):

- **(E1) `Ordinal`-indexed predicate via well-founded recursion.** Define
  `Derivable : Ordinal → ℕ → ℕ → Multiset (SyntacticFormula ℒₒᵣ) → Prop` by
  `Ordinal`-strong-recursion on the first arg; the `I∀` clause quantifies
  `∀ n, ∃ βₙ < α, Derivable βₙ k n (Γ ∪ {φ[x↦n]})`. Pro: closest to Towsner's `⊢^{α,k}_c`. Con:
  WF-recursion ergonomics; every lemma is an `Ordinal` strong induction.
- **(E2) Inductive tree with ordinal *labels* + a separate `bound`/`rank` measure.** An
  `inductive Deriv : Multiset _ → Type` whose `I∀` constructor stores `(n : ℕ) → Deriv (Γ ∪ …)`
  (an honest infinitely-branching tree, allowed in Lean), then `o : Deriv Γ → Ordinal`,
  `rk : Deriv Γ → ℕ` defined by recursion, with `⊢^{α,k}_c Γ := ∃ d : Deriv Γ, o d ≤ α ∧ …`.
  Pro: the rules are a clean `inductive`; ordinal/rank are derived, matching the paper's
  "count steps" lemmas (16.3, 16.4). Con: the well-founded tree type + its measures.

Recommend prototyping **(E2)** first (the infinitely-branching `inductive` is legal and the
ordinal becomes a *computed* label, so the rule set stays readable and faithful to §16's calculus).

Use **mathlib's `ε₀`** (`Ordinal.epsilon0`, `Mathlib.SetTheory.Ordinal.*`) for the bound and its
well-foundedness; do **not** re-derive Towsner §3–4 (his "ordinals below ε₀ are well-founded" is
mathlib's `Ordinal` well-order restricted below `ε₀`). The natural-sum `#` is `Ordinal` natural
addition; `ω^·` is `Ordinal.opow ω`; `ω_c^α` (Def 19.8) is a `c`-fold `ω^·` tower.

---

## Milestone ladder (Route B)

Ordered; each is a named Lean target. `[mathlib]`/`[Track1]` = reuse available; `[new]` = build here.

### M3 — `Z_∞` calculus + bounds
- **M3.1** `[new]` Define formulas/sequents over `ℒₒᵣ` for `Z_∞` (reuse Foundation
  `SyntacticFormula ℒₒᵣ`; sequents = `Finset`/`Multiset` of sentences). Rules (Towsner §16):
  `True`, `W` (weakening — note: weakens the *bound*, key for the embedding), `I∧`, `I∨`, `I∀`
  (ω-rule), `I∃`, `C` (contraction), `Cut`.
- **M3.2** `[new]` Ordinal bound `o` and cut-rank `c` (rank `rk(φ)` = Towsner **Def 16.2**;
  `rk` of ∧/∨ is `max+1`, of ∀/∃ is `+1`, atoms `0`).
- **M3.3** `[new]` Bound-monotonicity: **Lemma 16.4** (`⊢^{α,k} ⟹ ⊢^{α,m}` for `k<m`),
  **Lemma 19.1** (weaken the *sequent* `Γ⊆Δ` at fixed bound).

### M4 — Embedding `PA⁺ ↪ Z_∞`  (Towsner §16, Thm 16.7 / 18.1)
- **M4.1** `[new]` **Lemma 16.1**: every true universal sentence is `Z_∞`-derivable at finite
  bound (the `True` + `I∀` engine).
- **M4.2** `[new]` **Lemma 16.5 / Cor 16.6**: each PA induction axiom is derivable at bound
  `ω·4 # 2·rk(φ) # 8` (finite ordinal coefficients), cut rank `≤ 2·rk(φ)+8`.
- **M4.3** `[new]` **Thm 16.7 / 18.1**: a `PA⁺` proof of `φ` ⟹ `∃ α<ε₀, ∃ k c, Z_∞ ⊢^{α,k}_c φ`,
  with `c` finite because only finitely many induction instances appear. *(This is where "only
  finitely many cuts, of finite rank" is earned — the hinge of the whole argument.)*

### M5 — Cut elimination  (Towsner §19)
- **M5.1** `[new]` Inversions: **Thm 19.2** (false atomic), **19.3** (∧), **19.4** (∀) — simplify
  a conclusion without raising the bound.
- **M5.2** `[new]` **Thm 19.5** (cut-reduction for ∨/∧ principal) and **19.6** (for ∃/∀, where the
  Hardy `h_{β#ω}` bound enters via the ω-rule premise selection).
- **M5.3** `[new]` **Thm 19.7**: one level of cut-rank elimination,
  `⊢^{α,k}_{c+1} ⟹ ⊢^{ω^α, h_{ω^α}(k)}_c`.
- **M5.4** `[new]` **Thm 19.9**: iterate `c` times ⟹ `⊢^{α,k}_c Γ ⟹ ⊢^{ω_c^α, m}_0 Γ` (cut-free).
  Closure of `<ε₀` under `ω_c^·` for finite `c` keeps the result `< ε₀`.

### M6 — Hardy hierarchy + the lower bound  (Towsner §6, §17)
- **M6.1** `[mathlib/Track1]` Fundamental sequences `α[k]` (**Def 6.1**, `Lemma 6.2 α[k]<α`) and
  Hardy `h_α` (**Def 6.3**). mathlib `ONote.fundamentalSequence`/`fastGrowing`; Track 1
  (`~/src/lean-formalizations` `Logic/FastGrowing`) is building the growth API — **reuse, do not
  duplicate**.
- **M6.2** `[new/Track1]` Hardy monotonicity **Lemma 16.10** (`α<β, τ(α)<k ⟹ h_α(k)<h_β(k)`)
  via the technical **16.8, 16.9**.
- **M6.3** `[Track1]` Goodstein-length domination: `𝒢(n) > h_α(n)` eventually, for each `α<ε₀`
  (the `𝒢 ~ h_{ε₀}` fact; Track 1's growth deliverable). Bridge `𝒢` to *our* `goodsteinSeq`.
- **M6.4** `[new]` **Thm 17.1**: no cut-free `Z_∞ ⊢^{α,k}_0 ∀x∃y g_y(x)=0` for any `α<ε₀`
  (ordinal induction on `α` using M6.2 + M6.3, exactly Towsner's three-case argument).

### M7 — Assembly  (Towsner Thm 20.1)
- **M7.1** `[new]` Connect Towsner's `∀x∃y g_y(x)=0` to **our** `goodsteinSentence`
  (`Encoding.lean`). Two sub-options: (a) prove `goodsteinSentence` and the explicit Π₂ form are
  `𝗣𝗔`-equivalent (needs an arithmetized Goodstein-step formula — partial overlap with the
  Phase-0.2 "transparent Π₂" refactor the `Bridge.lean` docstring anticipates); or (b) re-run the
  embedding M4 directly on `goodsteinSentence`'s defining Σ₁ formula. **(b) is likely cleaner.**
- **M7.2** `[new]` `peano_not_proves_goodstein`: assume `𝗣𝗔 ⊢ goodsteinSentence`; M4.3 ⟹ bounded
  `Z_∞` deriv; M5.4 ⟹ cut-free at `α<ε₀`; M6.4 ⟹ contradiction. Discharge the headline `sorry`.
  Verify `#print axioms` (Route B should be clean mod `[propext, Classical.choice, Quot.sound]`).

---

## Dependency / ordering notes
- M3 → M4 → M5 form one chain (the calculus + embedding + cut-elim). M6 is **independent** and
  can be developed in parallel (and largely lives in Track 1). M7 needs M4, M5, M6.
- **Hardest-first within Phase 2:** M3.1 (the `Z_∞` encoding decision, E1 vs E2) and M5 (cut
  elimination) are the genuine cruxes. M4 and M6.4 are intricate but mechanical once M3 is fixed.
  A lap should first **prototype the E2 `inductive` + ordinal/rank measures (M3.1–M3.2)** — until
  that typechecks, every downstream statement is unstateable. Bank M3 as disclosed-`sorry`
  scaffolding, then attack M5.
- Keep `Z_∞` scaffolding in `wip/` (sorry-holding, outside the build target) until a milestone is
  green; promote to `src/` when its `sorry`s close.

## Open literature requests (none yet)
Towsner is fully self-contained for Route B. If the E2 encoding hits a Lean-specific wall
(infinitely-branching `inductive` + ordinal measure well-foundedness), check mathlib for prior
infinitary-derivation art before filing an `ON-LINE-REQUEST.md`.
