# Wainer (2013) — Fast Growing Functions and Arithmetical Independence Results (Stanford slides)

## Provenance

- **File**: `wainer-fast-growing-independence-slides.pdf` (20 slides; gitignored; local/bind-mount only)
- **Title**: *Fast Growing Functions and Arithmetical Independence Results*
- **Author**: Stanley S. Wainer (Leeds, UK)
- **Venue**: Stanford logic seminar, March 2013.
- **Open access**: `http://www-logic.stanford.edu/seminar/1213/Wainer_stanford1.pdf` (HTTP; downloaded 2026-07-01).
- **Phase**: **fast-growing** (Route B) — accessible modern exposition of the classification, tied directly to Goodstein.

---

## What it is

A clean, self-contained lecture deck by Wainer himself walking from Goodstein/Kirby–Paris through the
Hardy and fast-growing hierarchies to the **classification of provable recursion**. Excellent orientation
material and a faithful statement source; it is **slides, not a paper** — cite the theorems, do not quote
"lemmas" as if from a refereed text (same caveat the repo applies to the Siders deck).

## Key content (grounded in the deck text)

- **§1 Goodstein + Kirby–Paris** stated as *the* natural mathematical incompleteness. Worked example
  `16, 112, 1284, 18753, 326594, …`.
- **§1.1 Hardy functions.** Replacing `ω` by a large `n` throughout a CNF `α ≺ ε₀` gives a "complete
  base-n" numeral; subtracting 1 and restoring `ω` yields a smaller ordinal `P_n(α)` — so Goodstein
  termination = well-foundedness of `≺ ε₀`. Definition `H_0(n)=n`, `H_α(n)=H_{P_n(α)}(n+1)`.
  - **Cichoń (1983) (restated):** `H_α(n)` measures the length of the Goodstein sequence on `(a,n)`.
    "A proof that all G-sequences terminate says `H_{ε₀}` is recursive. But `H_{ε₀}` is **not provably
    recursive in PA**. Hence part 2." — the growth-rate independence argument in three lines.
- **§1.2 Fast growing hierarchy** `B_α := H_{2^α}` (`B_0 = succ`, `B_{α+1}=B_α∘B_α`, `B_λ(n)=B_{λ_n}(n)`),
  the "Schwichtenberg–Wainer" hierarchy.
  - **Classification theorem (the headline):**
    > "`{B_α}_{α<|T|}` **classifies provable recursion in arithmetical theories `T`**, i.e. provides
    > **bounds for witnesses of provable Σ₁ formulas**."
    For `T = PA`, `|T| = ε₀`.
- **§2 EA(I;O) "Input–Output Arithmetic"** — Wainer's technical vehicle: an arithmetic with separated
  **input** constants `x,y,…` and quantified **output** variables `a,b,…`, only *basic terms* (successor/
  predecessor towers) admitted as witnesses, and induction **controlled by a closed basic term `t(x)`**:
  `A(0) ∧ ∀a(A(a)→A(a+1)) → A(t(x))`. This "length-controlled induction" is a **cleaner, more
  computational packaging** of the ε₀ bounding argument than raw infinitary cut-elimination — potentially a
  friendlier formalization target, though still ε₀-strength.

## Relevance to the expedition

- **Best short statement source** for the classification (`wainer_bound_of_pa_proves_goodstein`) and for the
  Cichoń length identity the repo's lower bound already formalizes
  (`GoodsteinPA.Dom.goodsteinLength_dominates_fastGrowing`).
- The **EA(I;O) presentation** is worth reading before choosing the Lean shape of the girder: if the
  axiom-free monument gets built, Wainer's length-controlled-induction route may decompose more cleanly than
  the Tait/Schütte ω-rule + full cut-elimination route.
- Does **not** contain a machine-checked proof; the bounding direction is still un-formalized anywhere (the
  monument). Orientation + statement fidelity only.
