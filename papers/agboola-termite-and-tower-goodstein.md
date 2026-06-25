# The Termite and the Tower: Goodstein sequences and provability in PA

## Provenance

- **File**: `agboola-termite-and-tower-goodstein.pdf` (in this repo's `papers/`)
- **Title**: *The Termite and the Tower: Goodstein sequences and provability in PA*
- **⚠️ Author discrepancy**: the filename and the requesting task name the author **"Agboola"**, but the PDF's own title page credits **Will Sladek**, dated **May 17, 2007**, with thanks to **Andrés Caicedo** for "innumerable suggestions and corrections." No "Agboola" appears anywhere in the body. Treat the byline as **Will Sladek (2007)**; the `agboola-` filename prefix is almost certainly a mislabel (possibly the course/instructor under whom it was written). Worth renaming the file if provenance matters downstream.
- **Type**: expository survey article (undergraduate/graduate-accessible), ~20 pp, not a research paper.
- **Suggested citation**: W. Sladek, *The Termite and the Tower: Goodstein sequences and provability in PA* (2007), expository manuscript.

## Abstract (plain language)

A self-contained exposition of **Goodstein's Theorem** — a purely finitary statement ("every Goodstein sequence eventually hits 0") whose *only known proofs require infinite (ordinal) machinery*, and which **Kirby–Paris (1982) showed is unprovable in Peano Arithmetic (PA)**. The paper assumes very little logic background and builds up the tools needed to (a) prove Goodstein's theorem using ordinals below ε₀, and (b) explain *at a high level* why no finitary (PA) proof can exist. The vehicle for the "why" is the **fast-growing (Wainer) hierarchy**: the Goodstein function grows like `f_{ε₀}`, but PA can only prove totality of functions dominated by `f_α` for some `α < ε₀` (Kreisel's theorem), so PA cannot prove Goodstein's theorem.

## Key content

**The "termite and tower" image.** A Goodstein sequence's complete base-`b` representation is a tower of exponents. The change-of-base operation `R_b` (replace every `b` by `b+1` in the complete base-`b` rep) blows the number up super-exponentially (the "tower"), but then subtracting 1 slowly gnaws at the rightmost part of the tower (the "termite"). The point: bumping the base never *creates* new towers larger than what's destroyed, so subtracting 1 eventually wins.

**Definitions/examples built up:**
- Complete base-`b` representation; change-of-base `R_b` (Defs 4–6).
- **Goodstein sequence** `(n)_k`: `(n)_0 = n`, `(n)_{k+1} = R_{k+2}((n)_k) − 1` (Def 7).
- **Goodstein function** `𝒢(n) = k+1` for the least `k` with `(n)_k = 0` (Def 8). Concrete explosion: `𝒢(1)=2, 𝒢(2)=4, 𝒢(3)=6, 𝒢(4) = 3·2^{402653211} − 2`. Worked sequences for `n = 4` and `n = 266` show the giant growth.

**Ordinals (§3):** von Neumann ordinals, ordinal arithmetic, limits/successors, well-ordering, **transfinite induction (Thm 3)**, "no infinite strictly-decreasing sequence of ordinals" (Thm 4), Cantor Normal Form (Def 19), `ε₀` as the limit of the towers `ω, ω^ω, ω^{ω^ω}, …`.

**Fast-growing hierarchy (§4):** the Wainer–Löb hierarchy `f_α` for `α ≤ ε₀` (Defs 18, 20–21), with `f_0(n)=n+1`, `f_{α+1}(n)=f_α^n(n)`, and `f_λ(n)=f_{d_n[λ]}(n)` at limits via the canonical fundamental sequence `d_n[α]`. Domination theorem: `α > β ⟹ f_α` dominates `f_β` (Thm 9). Anchors: Ackermann ~ `f_ω` (Fact 21); primitive-recursive functions all sit below some `f_n` (Fact 20).

**Goodstein's Theorem proper (§5):** the proof (Thm 22) defines a **companion ordinal sequence** `(n)'_k = R^ω_{k+2}((n)_k)` — replace the base `b` by `ω` in the complete base-`b` representation — that *bounds* `(n)_k` from above and is **strictly decreasing**; since ordinals have no infinite descending chain, it hits 0, dragging `(n)_k` to 0. Worked for `n = 266`. **Corollary 23:** `𝒢` is therefore a *recursive, total* function — established "by entirely finitary means" (this is the hook for the independence argument).

**PA vs finitary math (§6):** PA, ZFCfin, and hereditarily-finite sets `HF` are bi-interpretable; PA *is* finitary mathematics. So Goodstein (provable only with infinite ordinals) is true but not provable in this finitary frame.

## Route relevance to crux-2 (KEY)

The expedition formalizes **"PA ⊬ Goodstein"** via Gentzen-style internalized cut-elimination ("crux-2"). Verdict on this paper as a route source:

### (a) Which unprovability argument does it use — growth-rate/Hardy hierarchy, or proof theory?

**Growth-rate / fast-growing-hierarchy, decisively — NOT proof theory.** The paper's independence proof is the **Kreisel–Kirby–Paris route**, three theorems chained:

- **Corollary 23**: PA proves `𝒢` is a *total recursive function* (this falls straight out of the finitary content of Goodstein's theorem).
- **Theorem 24 (Kirby–Paris)**: *"The Goodstein function 𝒢 grows on the order of `f_{ε₀}`."* (stated, not proved here).
- **Theorem 19 (Kreisel)**: *"If a recursive `f : ℕ → ℕ` is provably total in PA, then `f_α` dominates `f` for some ordinal `α < ε₀`."* (stated, citing Kreisel [14]).

> **Corollary 25.** *Goodstein's Theorem is not provable in PA.*
> *Proof.* Assume that Goodstein's Theorem is provable in PA. Then by the proof of Corollary 23, 𝒢 is provably total in PA. However, Kreisel's Theorem 19 then implies that 𝒢 is dominated by `f_α` for some `α < ε₀`. This contradicts Theorem 24. Therefore, Goodstein's Theorem is not provable in PA. □

So the unprovability is entirely a **growth-rate dominance** argument: provably-total-in-PA functions are exactly those eventually dominated below `f_{ε₀}`, and `𝒢` is *exactly* at the `f_{ε₀}` ceiling.

The paper *mentions* the Hardy hierarchy by name only obliquely — it uses the **Wainer (`f_α`) hierarchy**, not the Hardy (`H_α`) one. It is not a proof-theoretic (cut-elimination / ordinal-analysis-of-derivations) argument.

### (b) Does anything here suggest a cleaner formalization route avoiding cut-elimination?

**Yes — this paper IS the cut-elimination-avoiding route, in outline.** Two key passages point at it:

> *(§1/§2 setup)* "In 1952, Georg **Kreisel** gave an upper bound on the growth rate of any recursive function that is provably total in PA. Thus, to show that a theorem is unprovable in PA, we first use the theorem to prove in (PA + theorem) that some fast-growing recursive function is total. Then, we just need to show that the fast-growing function grows too quickly for PA."

> *(§5, after Cor 23)* "...this corollary is derived from Goodstein's Theorem by entirely finitary means."

This is the standard "**provably-total bound**" packaging of independence and it **sidesteps internalized cut-elimination entirely** at the headline level. It bottoms out on Kreisel's Theorem 19 (the bounding theorem) as a *black box*, exactly the modular boundary you want: you don't formalize Gentzen's `ε₀`-induction cut-elimination — you formalize **(i)** PA proves `𝒢` total (a finitary computation argument, Cor 23), **(ii)** `𝒢 ⪰ f_{ε₀}` (Kirby–Paris, the growth lower bound, Thm 24), and **(iii)** the Kreisel bound "provably-total ⟹ dominated below `f_{ε₀}`" (Thm 19) as the imported hard lemma.

**BUT** — the paper is explicit that the hard part has merely been *relocated*, not eliminated. §6 spells out exactly where the cut-elimination wall reappears:

> "One can consider the equivalent problem of formalizing transfinite induction within PA. **Gerhard Gentzen** [7, 8] showed that for any `α < ε₀`, transfinite induction of length `α` is formalizable in PA, but that transfinite induction of length `ε₀` is **not** formalizable. ... we would need a proof in PA that every ordinal below `ε₀` is well-ordered, or, equivalently, a proof in PA that `ε₀` is well-ordered, but such a proof does not exist. ... we can thus pinpoint `ε₀` as the limit of PA in the sense that `ε₀` is the first ordinal that PA cannot prove to be well-ordered."

So the real content of "crux-2" (the unformalizability of `ε₀`-induction / equivalently the consistency-strength jump) lives inside **Kreisel's Theorem 19**, which this paper *cites and does not prove*. **The paper offers a cleaner route only if you are willing to take Theorem 19 (or `Con(PA)`-via-`ε₀`-induction / the Wainer-bound) as an axiom or imported lemma** rather than reproving Gentzen internally. It gives you the *modular decomposition* that isolates cut-elimination behind one citation — useful for structuring the Lean development and for justifying an axiom boundary — but it provides **no new mathematical shortcut that discharges the cut-elimination obligation itself**. The `ε₀`-well-ordering / Gentzen content is acknowledged as the irreducible wall (§6), consistent with the expedition's crux-2 framing.

### (c) Exact lemmas connecting Goodstein length to a fast-growing function

Yes — several, with clean statements:

- **Theorem 24 (Kirby–Paris [22]):** "The Goodstein function 𝒢 grows on the order of `f_{ε₀}`." — the direct length-to-`f_{ε₀}` link (lower bound on growth).
- **Theorem 9 (domination):** "For ordinals `α, β`, if `α > β`, then `f_α` dominates `f_β`." — the monotonicity backbone.
- **Theorem 19 (Kreisel [14]):** "If a recursive `f : ℕ → ℕ` is provably total in PA, then `f_α` dominates `f` for some ordinal `α < ε₀`." — the upper-bound / barrier lemma that turns growth into unprovability.
- **Theorem 17 (Caicedo, via the `ω`-change-of-base `R^ω_b`):** an *exact* closed form for the Goodstein function in terms of the hierarchy. If `n = 2^{m_1} + ⋯ + 2^{m_k}` with `m_1 > ⋯ > m_k`, and `α_i = R^ω_2(m_i)`, then
  > `𝒢(n) = f_{α_1}(f_{α_2}(…(f_{α_k}(3))…)) − 2`.
  Worked examples: `𝒢(4) = f_ω(3) − 2`, `𝒢(266) = f_{ω^{ω+1}}(f_{ω+1}(f_1(3))) − 2`. This is the tightest, most directly-formalizable Goodstein-length ↔ `f_α` identity in the paper, and it expresses `𝒢` *exactly* (not just "on the order of") in fast-growing-hierarchy terms.
- **Corollary 23:** 𝒢 is recursive and total (finitary), the bridge that makes the "provably total ⟹ bounded" argument applicable.

---

## Verdict

This is a **growth-rate / Wainer-hierarchy** independence proof (Kreisel + Kirby–Paris domination), **not** a proof-theoretic cut-elimination one — and at the headline level it *does* sidestep internalized cut-elimination by importing Kreisel's "provably-total ⟹ dominated below `f_{ε₀}`" bound (Thm 19) as a black box, giving a clean modular decomposition (PA proves 𝒢 total + 𝒢 ⪰ `f_{ε₀}` + Kreisel barrier). However, the paper is explicit (§6) that the hard cut-elimination content has only been *relocated into Thm 19 / Gentzen's unformalizability of `ε₀`-induction*, which it cites and does not prove, so it offers **no mathematical shortcut that discharges crux-2 itself** — only a justification for treating it as an axiom boundary. The genuinely useful formalization asset is **Theorem 17 (Caicedo)**, an *exact* `𝒢(n) = f_{α_1}(…f_{α_k}(3)…) − 2` closed form tying Goodstein length to the fast-growing hierarchy.
