# Arai — "Two remarks on proof theory of first-order arithmetic"

## Provenance

- **File**: `arai-two-remarks-proof-theory-arithmetic.pdf` (this directory)
- **Title**: *Two remarks on proof theory of first-order arithmetic*
- **Author**: Toshiyasu Arai (Graduate School of Mathematical Sciences, University of Tokyo; `tosarai@ms.u-tokyo.ac.jp`)
- **arXiv**: `arXiv:2003.13207v2 [math.LO]`, 31 Dec 2020. 8 pp.
- **Citation**: Toshiyasu Arai, *Two remarks on proof theory of first-order arithmetic*, arXiv:2003.13207 (2020).
- **Scope**: A short note with two independent remarks on the proof theory of PA. **Remark 1** introduces a two-parameter (ordinal `α` + number `c` cut-rank, plus a Hardy-controlled `(γ,k)` index) derivability relation and uses an embedding + cut-elimination (his "Elimination Lemma") to re-prove the classic result that every provably computable function of PA is dominated by a Hardy function `H_α (α<ε₀)`. **Remark 2** reformulates Paris–Harrington's proof of the independence of PH to extract a purely proof-theoretic *"consistency" proof of PA from a combinatorial principle* (diagonal homogeneity, DH).

---

## Abstract (verbatim from the paper)

> In this note let us give two remarks on proof-theory of PA. First a derivability relation is introduced to bound witnesses for provable Σ₁-formulas in PA. Second Paris–Harrington's proof for their independence result is reformulated to show a 'consistency' proof of PA based on a combinatorial principle.

---

## Key content — the two remarks

### Remark 1 (§1) — "A derivability relation to bound witnesses"

The headline target is the classic dominance theorem, stated as:

> **Theorem 1.1.** *Each provably computable function in PA is dominated by a Hardy function `H_α (α < ε₀)`.*

Arai notes this is a classic result (Kreisel, Wainer, Schwichtenberg et al.) and that his contribution is a *new derivability relation* — a variant of one in Schwichtenberg–Wainer ch. 4, itself inspired by Buchholz–Wainer — that bounds the Σ₁-witnesses.

The machinery is a one-sided (Tait-style) infinitary sequent calculus with a **doubly-bounded derivability relation** carrying *three* indices:

> **Definition 1.2.** For ordinals `γ, α < ε₀`, naturals `k, c < ω`, and finite sets `Γ` of sentences, `(γ,k) ⊢^α_c Γ` is defined by recursion on `α`. Let `ℓ = H_γ(k)`.

with rules **(Ax)**, **(cut)** (cut formula `A` with `dg(A) < c`), **(∧)**, **(∨)**, a finitary-witnessed **(∀ω)** rule (premise `A(n)` for all `n ∈ ℕ`), and **(∃)** (a witness `n < ℓ = H_γ(k)` must exist) — i.e. the existential witnesses are explicitly bounded by the Hardy value `H_γ(k)`. The supporting apparatus is exactly the standard ordinal-analysis toolkit:

- **Lemma 1.3 (Bounding).** If `(γ,k) ⊢^α_0 Γ` for a finite set `Γ` of Σ₁-sentences (cut-free, `c=0`), then `H_γ(k) ⊨ Γ` (a true disjunct exists, witnessed below `H_γ(k)`).
- **Lemma 1.4** — structural lemmas: **(1) Weakening**, **(2) False-`Δ₀` elimination**, **(3) Inversion**, **(4)** an ordinal-shift `(γ +̇ δ, k) ⊢` lemma.
- **Lemma 1.5 (Reduction)** and **Lemma 1.6 (Elimination / cut-elimination):**
  > **Lemma 1.6 (Elimination).** Assume `γ +̇ α` is defined for `γ = ω^{γ₀}·m ≥ ω`, and `k ≥ 2`. If `(γ,k) ⊢^α_{c+1} Γ`, then `(ω^{γ+α}, k) ⊢^{ω^α}_c Γ`.

  (One level of cut-rank is removed at the cost of an `ω`-exponential jump in the ordinal bound — the standard Gentzen/Schütte cut-reduction step.)
- **Lemma 1.7 (Embedding).** `PA ⊢ Γ(ā)` yields a bounded cut-rank derivation `(ω²ℓ, max({1}∪n⃗)) ⊢^{ω·d+m}_c Γ(n⃗)` (PA proofs embed into the calculus with ordinal `< ε₀` and finite cut-rank).

Chaining Embedding (1.7) → Elimination (1.6) → Bounding (1.3) proves Theorem 1.1.

- **Remark 1.8** improves the witness bound for the fragments `IΣ_k` to `2_k(ω²)` by working with prenex normal forms and a min-complexity cut-degree `dg₁`, restating Elimination and Bounding in that refined setting.

### Remark 2 (§2) — "A consistency proof of PA based on a combinatorial principle"

Defines a **diagonal homogeneity** principle and uses it to give a proof-theoretic consistency proof of PA, reworking Paris–Harrington:

> **Definition 2.1.** A subset `H ⊂ X` is *diagonal homogeneous* for a partition `P : [X]^{1+n} → c` if `∀x₀ ∈ H ∀a < x₀ ∀Y,Z ∈ [H]^n [x₀ < Y & x₀ < Z ⇒ P({a}∪Y) = P({a}∪Z)]`. **`X →_Δ (m)^{1+n}_c`** asserts a diagonal homogeneous `H ∈ [X]^m` exists for every such `P`. The **Diagonal Homogeneous principle DH** states `∀n,m,c > 0 ∃K > 1 + n[K →_Δ (m)^{1+n}_c]`.

Arai observes (after Def 2.1) "It is easy to see that the infinite Ramsey theorem together with König's lemma implies DH," and that DH is *implicit and crucial* in both the Paris–Harrington and Kanamori–McAloon independence proofs. The remark reformulates the `Con(T) → Con(PA)` step of Paris–Harrington into a direct proof-theoretic statement:

> **Theorem 2.3.** `EA + ∀x∃y(2_x = y) ⊢ DH → 1-Con(PA)`.

i.e., over elementary arithmetic (with the totality of the superexponential), the combinatorial principle DH *proves the 1-consistency of PA*. The proof uses **diagonal indiscernibles** `D` extracted from DH (Prop. 2.2) and runs the consistency argument on a **cut-free** derivation (`PA ⊢^d Γ` = derivable in depth `≤ d`; "The applied calculus admits a cut-elimination"). The core is:

> **Theorem 2.5.** Assume `PA ⊢^d Γ`, and for sequences `(i₀,…,i_{ℓ-1}) ∈ ℕ^ℓ`, let `i = max{i_j : j < ℓ} ≤ 2(d(π)−d)`. Then `⋁{φ^{(i+2)}(β₀,…,β_{ℓ-1}) : φ ∈ Γ}` holds for `⋀_{j<ℓ}(β_j < α_{i_j})`.

with **Corollary 2.7**: a function `D(n) := D(n,n,2n)` built from DH-witnesses **dominates every provably computable function of PA** — recovering, from the combinatorial side, the same fast-growing-domination fact as Remark 1. So both remarks orbit the *same* PA ↔ ε₀ ↔ provably-total-functions triangle, one via cut-elimination on a Hardy-bounded calculus, the other via a Ramsey-type combinatorial principle.

---

## Relevance to the expedition (Route A: Gentzen `TI(ε₀) ⊢ Con(PA)` → Gödel II → PA ⊬ Goodstein)

**Remark 1 is squarely on-target for the crux-2 (cut-elimination) girder; Remark 2 is an interesting but lower-priority alternative.**

### Does it bear on cut-elimination / the reduction / the PA↔ε₀ correspondence?

**Yes — Remark 1 is a complete, compact instance of the exact machinery Route A's "ε₀ girder" needs:**

1. **An ordinal-bounded infinitary calculus with finite cut-rank** — `(γ,k) ⊢^α_c Γ`, with the ordinal bound `α < ε₀`, a numeric/Hardy witness budget `H_γ(k)`, and a cut-rank `c`. This is the *same shape* as Towsner's `Z_∞ ⊢^{α,k}_c` and as the Buss/Buchholz/Siders PA∞ constructions already catalogued. It is a second, independent, fully-worked template for the calculus the expedition must formalize.

2. **A cut-elimination ("Elimination") lemma — Lemma 1.6 — in its cleanest form.** `(γ,k) ⊢^α_{c+1} Γ ⟹ (ω^{γ+α}, k) ⊢^{ω^α}_c Γ`: one cut-rank level removed for one `ω`-exponential ordinal jump, with `α < ε₀` preserved (ε₀ closed under `α ↦ ω^α`). This *is* crux-2, distilled to a single inequality — directly comparable to Towsner Thm 19.7/19.9 and the Buchholz reduction step. As a formalization reference it is unusually terse and self-contained (the whole reduction is Lemmas 1.5–1.6, ~one page), which is exactly what you want when porting the cut-reduction induction to Lean.

3. **The embedding (Lemma 1.7)** `PA ⊢ Γ ⟹ (…)⊢^{<ε₀}_c Γ` is the PA → PA∞ ordinal-assignment step the girder needs.

**Caveat on directness:** Arai's Theorem 1.1 targets **provably-total-function domination** (witness bounds for Σ₁-formulas), *not* `Con(PA)` directly. So Remark 1 gives the embedding + cut-elimination + bounding sub-girders, but it stops at the fast-growing-domination payoff rather than threading through to a consistency statement — the expedition would still need to redirect the cut-free output at `Con(PA)` (the `0=1`/empty-sequent target) the way Gentzen/Buchholz/Siders do, rather than at the Σ₁-witness-bound target Arai aims for. It is a *parallel* use of the same engine, not a drop-in `Con(PA)` proof.

**Remark 2** is the more exotic of the two: it relates a *combinatorial* principle (DH, a Paris–Harrington-flavoured diagonal-Ramsey statement) to `1-Con(PA)`, and re-derives PA-domination combinatorially. It is **not** on the chosen Route A path (it routes through Ramsey/indiscernibles à la Paris–Harrington/Kanamori–McAloon, closer in spirit to the recursion-theoretic "Route B" alternatives like Cichoń), and its own consistency argument *also* relies on cut-elimination ("the applied calculus admits a cut-elimination," Thm 2.5). So it does not buy the expedition out of the cut wall either, and it would add a separate combinatorics layer (DH ⟺ Ramsey+König) the expedition does not currently need.

---

## 2–3 sentence verdict

**Remark 1 is useful — a clean, ~one-page, second template of exactly the Route-A girder (an ordinal-bounded infinitary calculus with finite cut-rank, an embedding `PA → PA∞`, and a single-inequality cut-elimination/"Elimination" Lemma 1.6 keeping `α < ε₀`), valuable as a terse cross-check when formalizing crux-2 alongside the Buchholz/Buss/Towsner expositions — though it aims its output at provably-total-function domination rather than `Con(PA)`, so it supplies the cut-elimination sub-girders, not a finished consistency proof.** Remark 2 is interesting but off-path: it derives `1-Con(PA)` from a Paris–Harrington-style combinatorial principle (DH) and still leans on cut-elimination, so it neither replaces nor shortcuts the crux-2 wall and adds a combinatorics layer the expedition doesn't need. **Net: keep Remark 1 as a supporting cut-elimination reference for crux-2; treat Remark 2 as orientation only.**
