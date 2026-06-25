# Rathjen, "Goodstein's theorem revisited" (2014)

## Provenance

- **Filename**: `rathjen-2014-goodsteins-theorem-revisited.pdf`
- **Source**: arXiv:1405.4484 (v1, 18 May 2014). Published version in: *Gentzen's Centenary: The Quest for Consistency* (R. Kahle, M. Rathjen, eds.), Springer, 2015, pp. 229–242.
- **Author**: Michael Rathjen (School of Mathematics, University of Leeds).
- **Citation**: M. Rathjen, "Goodstein's theorem revisited," arXiv:1405.4484 (2014); in *Gentzen's Centenary*, Springer (2015), 229–242.

## Abstract (plain language)

Inspired by Gentzen's 1936 consistency proof, Goodstein (1944) found a tight correspondence between strictly descending sequences of ordinals below ε₀ and certain sequences of integers (Goodstein sequences). This paper revisits Goodstein's "On the restricted ordinal theorem," using newly surfaced archival material (the Goodstein–Bernays correspondence found by Jan von Plato) to argue that Goodstein came very close to proving a genuine independence result for **PA** in the 1940s — and that an attentive reader of Gentzen + Goodstein *could* have inferred one. The mathematical core of the paper is an **elementary proof** that already the termination of all *special* Goodstein sequences (those induced by the shift function `x ↦ x+2`) is not provable in **PA** — the result first proved by Kirby and Paris in 1982 using model theory. Rathjen's proof deliberately uses only tools available in the 1940s/50s (Grzegorczyk hierarchy + Gentzen's theorem + an ordinal "slowing-down"/padding construction), avoiding the model-theoretic indicator machinery. The paper is historical/expository in spirit; its moral is that Goodstein and Gentzen deserve more credit for the independence story.

## Key results (verbatim statements)

**Definition 2.4** Given any natural number `m` and non-decreasing function `f : ℕ → ℕ` with `f(0) ≥ 2`, define `m₀ᶠ = m, …, m_{i+1}ᶠ = S_{f(i+1)}^{f(i)}(m_iᶠ) ∸ 1`. This `(m_iᶠ)` is a **Goodstein sequence**. The **special** Goodstein sequence is the case `f = id₂` (where `id₂(x) = x+2`), i.e. `m_{i+1} := S_{i+3}^{i+2}(m_i) ∸ 1`. (`S_c^b(m)` rewrites `m` in complete base-`b` representation and replaces base `b` by `c`; `T̂_b^ω(α)` / `T_ω^b(m)` are the inverse ordinal↔integer base-bumping maps of Def. 2.1.)

**Theorem 2.5 (Goodstein 1944)** *Every Goodstein sequence terminates, i.e. there exists `k` such that `m_iᶠ = 0` for all `i ≥ k`.* (Proof: `T_ω^{f(i)}(m_iᶠ) > T_ω^{f(i+1)}(m_{i+1}ᶠ)`, a descending ε₀-sequence, so it must hit 0. NB: this statement is **not** formalizable in PA — it quantifies over arbitrary `f`.)

**Theorem 2.6 (Goodstein 1944)** *Over `RCA₀` the following are equivalent: (i) Every Goodstein sequence terminates. (ii) There are no infinitely descending sequences of ordinals ε₀ > α₀ > α₁ > α₂ > … .* (Establishes the equivalence Goodstein-termination ⟺ PRWO(ε₀)-type well-ordering, even in the weakest reverse-math base.)

**Corollary 2.7 (over PA)** *Over `PA` the following are equivalent: (i) Every **primitive recursive** Goodstein sequence terminates. (ii) There are no infinitely descending **primitive recursive** sequences of ordinals ε₀ > α₀ > α₁ > α₂ > … .* (The PA-formalizable version of Thm 2.6 — restricted to p.r. sequences so it is expressible.)

**Theorem 2.8 (Gentzen 1936, 1938)** *(i) The theory of primitive recursive arithmetic, `PRA`, proves that `PRWO(ε₀)` implies the consistency of `PA`. (ii) Assuming that `PA` is consistent, `PA` does not prove `PRWO(ε₀)`.* (Proof of (ii): "of course, one invokes Gödel's second incompleteness theorem." Here `PRWO(ε₀)` = "there are no infinitely descending primitive recursive sequences of ordinals below ε₀." The text stresses Gentzen assigns `ord(D) < ε₀` to derivations and gives a reduction `R` with `ord(R(D)) < ord(D)`, both **primitive recursive**, the key (5).)

**Theorem 2.9** *Termination of primitive recursive Goodstein sequences is not provable in `PA`.* (Proof: combine Theorem 2.8(ii) + Corollary 2.7. This is the "inferrable in 1944" result.)

**Definition 3.1 / Lemma 3.2 / Lemma 3.3** — machinery for "slowing down": explicit ordinal addition/multiplication on Cantor normal forms (3.1); the Grzegorczyk hierarchy `f₀(n)=n+1`, `f_{l+1}(n)=(f_l)ⁿ(n)` majorizes every p.r. function (Lemma 3.2, "known in the 1950's"); and Lemma 3.3 (PA): for p.r. `f` there is a p.r. `g : ℕ² → ω^ω` with `g(n,m) > g(n,m+1)` whenever `m < f(n)`, and `|g(n,m)| ≤ K·(n+m+1)`.

**Corollary 3.4 (PA)** *From a given primitive recursive strictly descending sequence ε₀ > β₀ > β₁ > β₂ > … one can construct a **slow** primitive recursive strictly descending sequence ε₀ > α₀ > α₁ > α₂ > …, where slow means there is a constant `K` such that `|α_i| ≤ K·(i+1)` holds for all `i`.* (The padding/slowing-down step; credited via Simpson [16, Lemma 3.6] to Harvey Friedman.)

**Theorem 3.5 (PA)** *Let ε₀ > α₀ > α₁ > α₂ > … be a slow primitive recursive descending sequence of ordinals, i.e. there is a constant `K` such that `|α_i| ≤ K·(i+1)` for all `i`. Then there exists a primitive recursive descending sequence ε₀ > β₀ > β₁ > β₂ > … such that `C(β_r) ≤ r+1` for all `r`.* (Converts a "slow length" bound into a "bounded coefficients" bound `C(β_r) ≤ r+1`, the form needed to feed a special Goodstein sequence.)

**Lemma 3.6 (PA)** *Let ε₀ > β₀ > β₁ > β₂ > … be a primitive recursive descending sequence of ordinals such that `C(β_n) ≤ n+1`. Then the special Goodstein sequence `(m_i)_{i∈ℕ}` with `m₀ = T̂₂^ω(β₀)` and `m_{i+1} = S_{i+3}^{i+2}(m_i) ∸ 1` does **not** terminate.* (Proof: claim `m_k ≥ T̂_{k+2}^ω(β_k)` for all `k`, by induction using Lemma 2.3(iii) and `C(β_i) ≤ i+1 < i+2`; this entails `m_k ≠ 0` for all `k`. So a descending ε₀-sequence with bounded coefficients yields a **non-terminating** special Goodstein sequence.)

**Corollary 3.7** *The statement that any special Goodstein sequence terminates is not provable in `PA`.* (This is the headline = the elementary re-proof of Kirby–Paris [9, Theorem 1(ii)]. **Proof, verbatim:** "Let `GS` be the statement that every special Goodstein sequence terminates. Arguing in `PA` and assuming `GS`, we obtain from Lemma 3.6, Theorem 3.4 and Corollary 3.4 that there is no infinite primitive recursive descending sequence of ordinals below ε₀, i.e. `PRWO(ε₀)`. However, by Theorem 2.8 the latter is not provable in `PA`." [The "Theorem 3.4" here is a typo for **Theorem 3.5**.])

**Lemma 4.1 / Appendix proof of Lemma 3.2** — purely technical majorization facts about the Grzegorczyk hierarchy `f_l` (monotonicity, `fᶻ(x) ≥ x`, `f_{l+1} ≥ f_l`), used to finish the proof that every p.r. function is majorized in the hierarchy.

## Route relevance to crux-2 (THE KEY QUESTION)

The expedition's route is: `PA ⊢ γ` (Goodstein/special-Goodstein termination) → `PA ⊢ PRWO(ε₀)` → (Gentzen) `PA ⊢ Con(PA)` → Gödel II contradiction. **Rathjen's paper uses exactly this route.** It does *not* offer an escape from the Gentzen / Con(PA) wall.

**(a) Does Rathjen go through Con(PA) + Gödel II, or a different method?**

Through Con(PA) + Gödel II. This is explicit and is the load-bearing step in **both** independence proofs in the paper:

- **Theorem 2.8(ii)** is *defined* by this route. The proof reads, in full: *"For (ii), of course, one invokes Gödel's second incompleteness theorem."* And 2.8(i) is the Gentzen content: *"The theory of primitive recursive arithmetic, `PRA`, proves that `PRWO(ε₀)` implies the consistency of `PA`."*
- **Corollary 3.7** (the headline special-Goodstein result) bottoms out by citing Theorem 2.8: *"there is no infinite primitive recursive descending sequence of ordinals below ε₀, i.e. `PRWO(ε₀)`. However, by Theorem 2.8 the latter is not provable in `PA`."*

So the chain is verbatim: special-Goodstein termination ⟹ (Lemmas 3.6 + 3.5 + Cor 3.4) PRWO(ε₀) ⟹ (Theorem 2.8(i), Gentzen) Con(PA) ⟹ (Gödel II) not provable in PA. This is **the same logical spine as crux-2** — Rathjen does *not* avoid it; he relies on it as a cited black box (Theorem 2.8).

The paper explicitly contrasts this with the *original* Kirby–Paris (1982) and Cichoń (1983) proofs, which used different machinery: Kirby–Paris used **model theory** (indicators); Cichoń used **ordinal-recursion-theoretic classification** of PA's provably-total functions (Kreisel's `<ε₀`-recursive functions, Schwichtenberg/Wainer's fast-growing-hierarchy classification, `F_{ε₀}` not provably total in PA). Rathjen's contribution is precisely to *replace* those modern methods with the older, more elementary Gentzen-route argument. So:

> "[Termination of special Goodstein sequences] was shown to be unprovable in `PA` by Kirby and Paris in 1982 using model-theoretic tools. [9] prompted Cichoń [4] to find a different (short) proof that harked back to older proof-theoretic work of Kreisel's from 1952 which identified the so-called `<ε₀`-recursive functions as the provably recursive functions of `PA`. … As `F_{ε₀}` eventually dominates any of these functions it is not provably total in `PA`. Cichoń verified that `F_{ε₀}` is elementary in the function `f_good`. Thus termination of special Goodstein sequences is not provable in `PA`."

**(b) Does it require Gentzen cut-elimination / an internalized reduction, or avoid it?**

It **requires** it — packaged inside Theorem 2.8(i) (= PRWO(ε₀) ⟹ Con(PA)). Rathjen spells out exactly the internalized-reduction content the expedition is calling crux-2 (page 9):

> "He defined a reduction procedure `R` on derivations (proofs) and showed that if successive application of a reduction step on a given derivation always leads to a non-reducible derivation in finitely many steps, then the consistency of `PA` follows. … he defined an assignment `ord` of ordinals to derivations of `PA` such [that] for every derivation `D` of `PA` … `ord(D)` is an ordinal `< ε₀`. He then defined a reduction procedure `R` such that whenever `D` is a derivation of the empty sequent in `PA` then `R(D)` is another derivation of the empty sequent in `PA` but with a smaller ordinal assigned to it, i.e., `ord(R(D)) < ord(D)` (5). Moreover, both `ord` and `R` are primitive recursive functions and only finitist means are used in showing (5)."

This *is* the internalized cut-elimination / coded-derivation-reduction step. Rathjen's paper does **not** re-prove or formalize it; it cites Gentzen [5],[6] and treats Theorem 2.8 as given. The paper's own novelty (`Slowing down`, §3) lives entirely on the *other* side of the chain — converting "termination ⟹ PRWO(ε₀)" elementarily (padding + Grzegorczyk majorization), which is the EASY direction for the expedition. It contributes nothing toward discharging the Gentzen step itself.

**(c) What exactly is Corollary 3.7 and what does it depend on?**

Corollary 3.7: *"The statement that any special Goodstein sequence terminates is not provable in PA."* It is the elementary re-derivation of Kirby–Paris [9, Thm 1(ii)]. Its dependency chain (from its own proof) is:
- **Lemma 3.6** — bounded-coefficient descending ε₀-sequence ⟹ non-terminating special Goodstein sequence (so termination ⟹ no such bounded sequence). Uses only Lemma 2.3(iii).
- **Theorem 3.5** (the proof miscites it as "Theorem 3.4") — slow sequence ⟹ bounded-coefficient sequence `C(β_r) ≤ r+1`.
- **Corollary 3.4** — arbitrary p.r. descending ε₀-sequence ⟹ slow one (`|α_i| ≤ K·(i+1)`); rests on Lemma 3.3 + Grzegorczyk hierarchy (Lemma 3.2).
- **Theorem 2.8** — the *only* genuinely non-elementary dependency: PRWO(ε₀) not provable in PA (= Gentzen + Gödel II = crux-2).

In short: 3.7 = (3.6 ∘ 3.5 ∘ 3.4) [all elementary, PA-formalizable] + **Theorem 2.8** [the Gentzen/Con(PA) wall]. The novelty is the elementary front half; the back half is the cited Gentzen result.

**(d) Is there a route in this paper that would AVOID the cut-elimination wall?**

**No.** Every independence statement in the paper (Theorem 2.9 and Corollary 3.7 alike) terminates at Theorem 2.8(ii), whose only proof is "invoke Gödel's second incompleteness theorem," and whose companion 2.8(i) *is* the Gentzen reduction. The paper surveys the two genuinely-different routes (Kirby–Paris model theory; Cichoń fast-growing-hierarchy / classification of PA-provably-total functions) but **does not adopt either** — it explicitly chooses the Gentzen route as its method, because the whole point of the paper is the historical thesis that the Gentzen-based argument was available in the 1940s. So the alternatives that *would* sidestep crux-2 are *named but not pursued* here; this paper is not the place to find them worked out. If the expedition wants an indicator-free / cut-elimination-free path, the references to chase are **Cichoń [4]** (recursion-theoretic, via Kreisel [10] + Schwichtenberg [15] + Wainer [18]) and **Kirby–Paris [9]** (model-theoretic indicators) — not Rathjen 2014, which is firmly on the Gentzen rails.
