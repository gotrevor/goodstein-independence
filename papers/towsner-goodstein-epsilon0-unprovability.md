# Towsner — "Goodstein's Theorem, ε₀, and Unprovability"

## Provenance

- **File**: `towsner-goodstein-epsilon0-unprovability.pdf` (this directory)
- **Title**: *Goodstein's Theorem, ε₀, and Unprovability*
- **Author**: Henry Towsner (University of Pennsylvania)
- **Date**: March 20, 2020 (expository lecture notes / preprint)
- **Citation**: Henry Towsner, *Goodstein's Theorem, ε₀, and Unprovability* (2020), expository notes. 40 pp., 3 parts.
- **Scope**: A from-scratch, self-contained exposition that (Part 1) proves Goodstein's Theorem via ordinal "timers" below ε₀, (Part 2) shows the Goodstein function dominates every `h_α` with `α < ε₀`, and (Part 3) proves Goodstein's Theorem is **not provable in PA** using an infinitary proof system `Z_∞` plus ordinal-bounded **cut elimination**.

---

## Abstract (plain language)

These notes do three things. **Part 1** proves Goodstein's Theorem (every Goodstein sequence terminates) by attaching to each term `gᵢ(n)` an *ordinal timer* `γᵢ(n) = B_{i+1,ω}(gᵢ(n))` — the term written in hereditary base `i+1` with the base replaced by `ω`. Each Goodstein step strictly *decreases* the ordinal (Lemma 5.2) even though the integer grows, and the ordinals below ε₀ are well-founded (Theorem 4.2), so the sequence must hit 0. **Part 2** shows the Goodstein function `𝒢(n)` (steps-to-terminate) eventually dominates every function `h_α` in the fast-growing hierarchy for `α < ε₀` (Theorem 7.2 / 9.8). **Part 3** is the unprovability result: Towsner builds an infinitary one-sided sequent calculus `Z_∞` with two resource bounds — an **ordinal bound α** (height) and a **numeric bound k** (complexity/witness size) — and shows:

1. **Embedding** (Thm 16.7 / 18.1): everything provable in `PA⁺` (an axiomatized variant of PA) has a `Z_∞`-deduction with bound `α < ε₀` and a *finite cut-rank* `c`.
2. **Cut elimination** (Thm 19.9): cuts can be removed, at the cost of raising the ordinal bound by iterated `ω`-exponentiation `c` times — but `α < ε₀` stays `< ε₀`.
3. **Cut-free lower bound** (Thm 17.1): there is **no** cut-free `Z_∞`-deduction of Goodstein's Theorem `∀x ∃y g_y(x)=0` with any ordinal bound `α < ε₀`.

Chaining these (Thm 20.1) gives the contradiction: a `PA⁺` proof would yield a bounded deduction → a cut-free bounded deduction → which 17.1 forbids. Hence **PA⁺ (and so PA) cannot prove Goodstein's Theorem.**

---

## Key results (exact statements)

### Part 1 — Goodstein's Theorem
- **Theorem 4.2.** The ordinals below ε₀ are well-founded.
- **Lemma 5.1.** If `x < y` then `B_{b,ω}(x) < B_{b,ω}(y)` (the ω-base-change is order-preserving).
- **Lemma 5.2.** For every `i, n`: `γ_{i+1}(n) < γᵢ(n)` (the ordinal timer strictly decreases each Goodstein step), where `γᵢ(n) = B_{i+1,ω}(gᵢ(n))`.
- **Theorem 5.3 (Goodstein's Theorem).** For every `n` there is an `i` with `gᵢ(n) = 0`.

### Part 2 — Growth rate
- **Lemma 6.4.** For `α > 0`, `h_α(n)` is the smallest `n+k` with `α[n][n+1]···[n+k] = 0` (length of the fundamental-sequence descent).
- **Theorem 7.2 / Theorem 9.8.** For every `α < ε₀` there is an `n` such that for all `m ≥ n`, `𝒢(m) ≥ h_α(m)`. (The Goodstein function dominates the whole `< ε₀` fast-growing hierarchy.)

### Part 3 — Unprovability (the load-bearing theorems)
- **Definition 10.2 (PA⁺).** Axioms = (a) **all** true *universal* sentences `∀x₁···∀x_m φ` (φ quantifier-free), plus (b) the induction axiom schema `¬φ[x↦0] ∨ ∃x(φ ∧ ¬φ[x↦x+1]) ∨ ∀x φ` for every formula φ. The language is *enriched* with extra function symbols (exponentiation, base change `B`, and `gᵢ(n)`) — but **not** `𝒢` itself.

- **Remark 10.3 (the "improper axiom system" caveat — see Route-relevance below).** Towsner explicitly flags that `PA⁺` "is not even a proper axiom system." Because PA⁺ takes *all true universal sentences* as axioms, membership in the axiom set is not decidable: e.g. `∀x∀y∀z∀c (c < 3 ∨ ¬(xᶜ + yᶜ = zᶜ))` *is* a PA⁺ axiom — "but this is Fermat's Last Theorem, and we only know it is an axiom because of a very difficult proof. There are other universal sentences where we do not even know whether or not they are axioms in PA⁺!" The whole point is a deliberate trade-off: PA⁺ is non-effective and over-generous, chosen so the unprovability proof can sidestep the painstaking arithmetization of "ordinary" PA. (Quoted verbatim.)

- **Theorem 16.7 (PA⁺ → Z_∞, embedding).** If a sentence φ can be proven in `PA⁺`, then there is an ordinal `α < ε₀` and a natural number `k` so that `Z_∞ ⊢^{α,k} φ`. Proof is by induction over a Hilbert-style PA⁺ proof; each axiom and inference rule is simulated by a bounded `Z_∞` deduction. The extra function symbols are tolerated *only because* each is bounded by some `h_α` with `α < ε₀` (this is where the `∃`-witness-bound machinery, esp. `t ≤ h_α(k)`, is used).

- **Theorem 18.1 (finite cut-rank).** If φ is provable in PA⁺ then there are `α < ε₀` and *finite* `k, c` with `Z_∞ ⊢^{α,k}_c φ` — i.e. cuts only ever occur on formulas of rank `< c`, and `c` is finite because only finitely many induction axioms (hence finitely many cut formulas) appear in any given PA⁺ proof.

- **Theorem 17.1 (cut-free LOWER BOUND — the crux of unprovability).** *It is not the case that* `Z_∞ ⊢^{α,k} ∀x ∃y g_y(x) = 0` *with a cut-free deduction for any* `α < ε₀`. Proof is by induction on `α`, proving a strengthened invariant: a cut-free `Z_∞ ⊢^{α,k} Γ` is impossible whenever every `φ ∈ Γ` is one of (i) `∀x ∃y g_y(x)=0`, (ii) `∃y g_y(n)=0` for some `n ≤ k` with `𝒢(n) > h_α(k)`, or (iii) `g_t(n)=0` for a closed term `t` with value `< 𝒢(n)`. The `∀I` case forces choosing `n` with `𝒢(n) > h_α(n) > h_{β_n}(n)`; the `∃I` case forces a witness `t ≤ h_α(k) < 𝒢(n)` that is too small to be a real solution. **Intuition:** a cut-free deduction can only break the goal into *sub-sentences* of the goal, so the only available witnesses are bounded by `h_α(k)` — but `𝒢` outruns every such `h_α` (Part 2), so a genuine witness can never be produced cut-free below ε₀.

- **§19 — Cut elimination** (inversion lemmas 19.2–19.4; reduction lemmas 19.5–19.7; iteration 19.8–19.9):
  - **Theorem 19.7 (one cut-rank reduction).** If `Z_∞ ⊢^{α,k}_{c+1} Γ` then `Z_∞ ⊢^{ω^α, h_{ω^α}(k)}_c Γ` — removing one level of cut multiplies the ordinal bound by an `ω`-exponential.
  - **Definition 19.8 / Theorem 19.9 (full cut elimination).** Define `ω^α_0 = α`, `ω^α_{c+1} = ω^{(ω^α_c)}`. **Theorem 19.9:** if `Z_∞ ⊢^{α,k}_c Γ` then `Z_∞ ⊢^{ω^α_c, m}_0 Γ` for some `m` (apply 19.7 `c` times). Because `α < ε₀` and `c` is finite, the iterated tower `ω^α_c` is **still `< ε₀`** (ε₀ is closed under `α ↦ ω^α`). This is "the most difficult theorem" of the notes.

- **Theorem 20.1 (Goodstein unprovable in PA⁺).** If PA⁺ proved `∀x ∃y g_y(x)=0`, then by 16.7/18.1 `Z_∞ ⊢^{α,k}_c` it with finite `c`; by 19.9 there's a *cut-free* (`c=0`) deduction with ordinal bound `ω^α_c < ε₀`; but 17.1 says no cut-free `< ε₀` deduction exists. Contradiction. **∴ PA cannot prove Goodstein's Theorem.**

---

## Route relevance to crux-2 (KEY)

The expedition formalizes "PA ⊬ Goodstein." **Route A** = the Gentzen path the expedition has chosen (internalized cut-elimination → `Con(PA)` → Gödel II), whose hard wall is "crux-2." **Route B** = doing it *Towsner's way* (this paper). The box's note says Route B owes "M4 embedding + (α,k) cut-elim wiring + a PA↔PA⁺ arithmetization bridge (Towsner Remark 10.3 skips it — the sleeper wall)." Verdict on each sub-question:

### (a) Towsner's logical skeleton
Three pillars over an infinitary, **ordinal-and-number-bounded** one-sided sequent calculus `Z_∞ ⊢^{α,k}_c Γ` (α = height/well-founded descent, k = witness/complexity budget, c = cut-rank):
1. **Embedding** `PA⁺ → Z_∞` with `α < ε₀`, finite cut-rank (Thm 16.7, 18.1).
2. **Cut elimination** `Z_∞ ⊢_c → Z_∞ ⊢_0` paying `α ↦ ω^α_c`, staying `< ε₀` (Thm 19.9, the hard theorem).
3. **Cut-free lower bound**: no cut-free `< ε₀` deduction of Goodstein (Thm 17.1).
Combine → Thm 20.1. The asymmetry "everything embeds (α<ε₀) but Goodstein can't be cut-free below ε₀" is the whole mechanism — *exactly the same shape* as the Gentzen consistency argument (in fact this IS the Gentzen/Schütte method specialized to a Π₂ statement instead of `0=1`).

### (b) Does Route B also need cut-elimination, or a different mechanism?
**It absolutely needs cut elimination** — Theorem 19.9 is the centerpiece, and Towsner calls it "the most difficult theorem we have encountered." Route B does **not** escape the cut-elimination wall; cut-elimination *is* its load-bearing wall. The mechanism (assign ordinals to a Tait-style calculus, prove inversion + cut-reduction + transfinite induction up to ε₀) is the **same family** as Route A's internalized cut-elimination. The difference is cosmetic: Route A targets `Con(PA)` then invokes Gödel II; Route B targets a *direct* cut-free lower bound on the Goodstein sequent (Thm 17.1) and skips the Gödel-II step. The shared, expensive core — formalizing `Z_∞`, ordinal/numeric bounds, the inversion lemmas, and the `ω^α` cut-reduction induction — is unchanged.

### (c) Remark 10.3 and the PA↔PA⁺ arithmetization bridge it glosses
**Remark 10.3** (p.14) is Towsner conceding that `PA⁺` "is not even a proper axiom system": taking *all true universal sentences* as axioms makes the axiom set **non-decidable** (his FLT example: a sentence is a PA⁺ axiom only because of a hard proof; some universal sentences we don't even know to be axioms). PA⁺ also adds extra function symbols (`exp`, `B_{b,d}`, `gᵢ`) directly into the language. He defends this on p.15 as a deliberate pedagogical trade-off:

> "The conventional definitions are much more parsimonious, and (most of) the definition here is recovered by some painstaking work showing that more complicated notations can be encoded using the basic definitions, and that one has included, not all true universal sentences, but a sufficiently large subset which we can still actually list... for a first presentation of this unprovability result, I think this is a convenient approach, focusing on the proof of unprovability rather than on the details of properly establishing Peano Arithmetic."

That "painstaking work" — encoding the extra symbols by `+`/`·`, replacing "all true universal sentences" with a genuine recursively-axiomatized PA, and proving the two systems agree on the relevant Π₂ sentence — **is the PA↔PA⁺ arithmetization bridge**. For an *informal* unprovability proof it is harmless (PA⁺ is *stronger* than PA on universal sentences, so "PA⁺ ⊬ Goodstein" trivially yields "PA ⊬ Goodstein"). **But for a Lean formalization it is a sleeper wall**: you cannot formalize "PA ⊬ Goodstein" by formalizing "PA⁺ ⊬ Goodstein" *unless* you also formalize (i) that PA⁺'s extra symbols are PA-definable, (ii) that PA proves the relevant defining axioms, and (iii) the soundness direction relating a PA-proof to a PA⁺-proof — i.e. a real arithmetization. Towsner gets to wave this off; a theorem prover does not. This is precisely the bridge the box flags, and it is **additive** to (not a replacement for) the cut-elimination cost.

### (d) On balance: more or less formalizable than Route A? Does it avoid the cut-elimination wall?
**Route B does NOT avoid the cut-elimination wall — it relocates the *Gödel-II* step, not the cut wall.** Net assessment: Route B is **roughly equal-or-harder** to formalize than Route A, for three reasons:
1. **The cut-elimination wall is shared and unavoidable.** Both routes must formalize an ordinal-bounded infinitary calculus, inversion lemmas, and a transfinite `ω^α`-induction cut-reduction up to ε₀. This is crux-2-equivalent work either way. Route B's Thm 19.9 is the same beast.
2. **Route B trades Gödel II for two new obligations**: (i) the cut-free lower bound (Thm 17.1), which is non-trivial but bounded; and (ii) the **PA↔PA⁺ arithmetization bridge** that Remark 10.3 skips — a substantial formalization that Route A's `Con(PA)` framing largely avoids if mathlib/Foundation already gives a proper PA + Gödel II. Route A *reuses* the expedition's existing termination work and an off-the-shelf Gödel II; Route B must build the bridge from scratch.
3. **PA⁺'s non-effectiveness is a formalization liability.** "All true universal sentences" is not a recursive axiom set; a faithful formalization either keeps the non-effective set (then "PA⁺" isn't recognizably PA, undermining the headline) or replaces it (then you've re-incurred the arithmetization). Route A's PA is a proper, effective theory from the start.

**Bottom line:** Route B is a clean, Gödel-II-free *exposition*, but its apparent simplicity comes from informal hand-waves (Remark 10.3) that a prover must pay for. It keeps the full cut-elimination cost and adds an arithmetization bridge — so it does not buy the expedition out of crux-2.

---

## 3-4 sentence verdict (Route B / Towsner vs current Route A)

Route B does **not** escape the cut-elimination wall: Towsner's centerpiece is Theorem 19.9, a transfinite (`α ↦ ω^α`, c times) cut-elimination up to ε₀ that he himself calls the hardest theorem — the same wall Route A faces as crux-2, just aimed at a direct cut-free lower bound (Thm 17.1) instead of `Con(PA)` + Gödel II. What Route B relocates is the *Gödel-II* step, not the cut wall; in exchange it incurs two fresh obligations — the cut-free lower bound and, critically, the **PA↔PA⁺ arithmetization bridge that Remark 10.3 openly skips** (PA⁺ takes *all true universal sentences* as axioms, so it is not even a decidable theory, and relating it back to real PA is the sleeper wall). For a Lean formalization this makes Route B roughly **equal-or-harder** than Route A: the expensive ordinal-bounded infinitary-calculus + cut-reduction core is shared, and Route B layers a non-trivial arithmetization on top while Route A can reuse existing termination work plus an off-the-shelf Gödel II. **Recommendation: stay on Route A — Route B is a Gödel-II-free *exposition* whose simplicity is informal, not a way around the cut-elimination wall.**
