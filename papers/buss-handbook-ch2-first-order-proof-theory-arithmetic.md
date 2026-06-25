# Buss — "First-Order Proof Theory of Arithmetic" (Handbook of Proof Theory, ch. II)

## Provenance

- **File**: `buss-handbook-ch2-first-order-proof-theory-arithmetic.pdf`
- **Author**: Samuel R. Buss (Departments of Mathematics and Computer Science, UC San Diego)
- **Title / venue**: *First-Order Proof Theory of Arithmetic*, Chapter II of the *Handbook of Proof Theory* (ed. S. R. Buss), Elsevier 1998, pp. 79–147.
- **Citation**: S. R. Buss, "First-order proof theory of arithmetic," in *Handbook of Proof Theory*, ed. S. R. Buss, Studies in Logic and the Foundations of Mathematics vol. 137, Elsevier, 1998, pp. 79–147.
- **Source URL**: https://mathweb.ucsd.edu/~sbuss/ResearchWeb/handbookII/ChapterII.pdf (author's open copy)
- **Prerequisite stated by the author**: "knowledge of the sequent calculus and cut-elimination, as contained in Chapter I of this volume" (= `buss-handbook-ch1-intro-proof-theory.pdf`).

> ⚠️ **The local PDF is a partial extract — pages 79–88 only (Contents page + §1 *Fragments of arithmetic*, through §1.2.7).** The full chapter (79–147) also contains §2 Gödel incompleteness, §3 On the strengths of fragments (witnessing theorems for `S₂¹`/`T₂ⁱ`, `BΣₙ` vs `IΣₙ`), and §4 the Paris–Wilkie strong incompleteness for `I∆₀+exp`. The Contents page (p.79) is included, so the chapter's full scope is known even though §2–§4 text is not in this file. Re-download the author's open copy if §2–§4 text is needed.

---

## Abstract / scope

A proof-theoretic survey of the **first-order theory of arithmetic** and, especially, its **axiomatizable fragments** — from the very weak `R`/`Q` up through bounded arithmetic, `I∆₀`, `IΣₙ`, to full Peano arithmetic (`PA`). Buss states the emphasis explicitly: *"Our emphasis has instead been on weak fragments of arithmetic and on finitary proof theory, especially on applications of the cut-elimination theorem."* He also names the deliberate boundary: *"the most notable omission is theories stronger than Peano arithmetic,"* and points the reader to the companion Handbook articles **Fairtlough–Wainer** (ch. III), **Pohlers**, **Troelstra**, and **Avigad–Feferman** for the rest of the proof theory of arithmetic.

The chapter's organizing line between "strong" and "weak" fragments is itself cut-elimination-flavored: §1 draws it *"between those theories which can prove the arithmetized version of the cut-elimination theorem and those which cannot; in practice, this is equivalent to whether the theory can prove that the superexponential function `i ↦ 2ᵢ¹` is total"* (p.81).

---

## Key content

### §1 Fragments of arithmetic (pp. 81–112 — the part in this PDF, 81–88)
- **Languages** (§1, p.81): `0, S, +, ·, ≤`; for weak/bounded arithmetic also `⌊½x⌋`, `|x| = ⌈log₂(n+1)⌉` (bit-length), Nelson's *smash* `#` (`m#n = 2^{|m|·|n|}`), and the `ωₙ`/`#ₙ` growth-rate generalizations. Strong theories may add function symbols for **all primitive recursive functions** (p.82).
- **Very weak fragments** (§1.1, p.82): Robinson's `Q` (six axioms, no induction) and the weaker `R` (Tarski–Mostowski–Robinson 1953). A *bounded* theory = axiomatizable by `Π₁`-sentences.
- **Arithmetic hierarchy** (Def. 1.2.1, p.83): `∆₀` = bounded formulas; `Σₙ/Πₙ` by quantifier-alternation; the `Σₙ⁺/Πₙ⁺` variants (allow extra bounded quantifiers, §1.2.5).
- **Induction / minimization / collection schemes** (Def. 1.2.2–1.2.3, pp.83–84): `Φ-IND`, `Φ-MIN` (least-number principle), `Φ-REPL` (collection/replacement). Defines `IΣₙ`, `I∆₀`, `LΣₙ`, `BΣₙ`, and `PA = Q + induction for all formulas`.
- **Containment diagram** (§1.2.4, p.84): `IΣₙ₊₁ ⇒ BΣₙ₊₁ ⇔ BΠₙ ⇒ IΣₙ`, with the two `⇒` proper (Parsons 1970; Paris–Kirby 1978).
- **Bootstrapping `I∆₀`** (§1.2.6): commutativity/associativity/distributivity, `≤`-order properties, and **Theorem: `I∆₀ ⊢ ∆₀-MIN`** (p.86 — minimization for `A` reduces to `∆₀`-induction on `(∀y≤x)¬A(y)`).
- **Conservative language extensions / provably-total functions** (§1.2.7, pp.86–88): the **`Σ₁`-definable (= "provably recursive" / "provably total") functions of a theory** (p.87); **Parikh's Theorem 1.2.7.1** (a bounded theory proving `∀x̄∃y A` proves `∀x̄(∃y≤t)A` for a term `t`); **Theorem 1.2.7.3** (Gaifman–Dimitracopoulos): adding `∆₁`-defined predicates and `Σ₁`-defined functions is conservative and preserves quantifier complexity.

### §2 Gödel incompleteness (pp. 112–122 — *not in this PDF*)
Per the Contents: §2.1 Arithmetization of metamathematics; §2.2 the Gödel incompleteness theorems.

### §3 On the strengths of fragments of arithmetic (pp. 122–137 — *not in this PDF*)
Per the Contents: **witnessing theorems** (§3.1–§3.2 for `S₂¹`, §3.3 for `T₂ⁱ` plus conservation results), and §3.4 the `BΣₙ` vs `IΣₙ` relationships. This is the chapter's main cut-elimination *application* layer — but aimed at **bounded arithmetic / feasible complexity**, not at `PA`'s ordinal strength.

### §4 Strong incompleteness theorems for `I∆₀+exp` (pp. 137–143 — *not in this PDF*)
The Paris–Wilkie result that `I∆₀+exp` cannot prove `Con(Q)`.

---

## Relevance to crux-2 (the ordinal/cut-elimination internalization)

**Indirect / supporting, not a primary source.** Buss ch. II is the canonical *English* reference for the **finitary-proof-theory machinery and the fragment taxonomy** that crux-2 lives inside, but it does **not** carry out the `ε₀`-bounded ordinal analysis of `PA` itself:

- **(a) The cut-elimination reduction.** Buss ch. II does **not** prove cut-elimination here — it is treated as a *prerequisite imported from ch. I* (`buss-handbook-ch1-intro-proof-theory.pdf`). Ch. II's contribution is the *arithmetized / fragment-relative* angle: it pins down exactly the **strength needed to internalize cut-elimination** — the superexponential `2ᵢ¹` totality threshold (§1, p.81) that separates theories which can prove the arithmetized cut-elimination theorem from those which can't. That threshold framing is directly useful for crux-2's "what does the meta-theory (`IΣ₁`) need to formalize the reduction" question, but the actual ordinal-decreasing cut-reduction on coded PA-derivations is in **Buchholz** (`buchholz-on-gentzens-first-consistency-proof.md`, Thm 4.2 `o(d[n]) < o(d)`) and **Towsner** (`towsner-…`, Thm 19.9), not here.
- **The `Σ₁`-definability / Parikh / Gaifman–Dimitracopoulos apparatus** (§1.2.7) is genuinely on-point for the *meta-theory* of crux-2: it is the standard toolkit for showing that the coding predicates and the reduction operation are `∆₀`/`Σ₁` and can be used freely in `IΣ₁`-induction without raising quantifier complexity.

## Relevance to the growth-rate route (Wainer's classification)

**Negative — Wainer's classification is NOT in this chapter; it is in the *next* Handbook chapter.**

- Buss ch. II contains **no ordinal analysis of `PA`, no Hardy / fast-growing hierarchy, and no "`PA`-provably-total ⟺ dominated by `H_{α<ε₀}`" classification.** Its only "provably total" content (§1.2.7) is the *general* definition of `Σ₁`-definable functions of a theory plus the **bounded-theory** refinements (Parikh, `I∆₀` definability) — i.e., feasible/bounded-complexity territory, not the `ε₀`/fast-growing characterization of `PA`.
- The chapter **explicitly defers** this material. Buss's intro names **Fairtlough–Wainer** as a Handbook companion article on the proof theory of arithmetic, and §1's "stronger than `PA`" omission notice points there. SOURCES.md confirms the split: Wainer's classification is the subject of **Handbook ch. III** — Fairtlough, M. & Wainer, S. S. (1998), *"Hierarchies of provably recursive functions,"* Handbook of Proof Theory, ch. III, pp. 149–207 (Elsevier; paywalled, not the open Buss copy). **That is the canonical citable home for the growth-rate route's key lemma, not this file.**
- Within this repo, the *content* of the growth-rate route is already captured by **Towsner Part 2** (`towsner-goodstein-epsilon0-unprovability.md`, Thm 7.2/9.8: the Goodstein function dominates every `h_α`, `α < ε₀`) — but for a clean *external* statement of "PA-provably-total ⟺ `<ε₀` in the Hardy/fast-growing hierarchy," cite **Fairtlough–Wainer ch. III**.

---

## Verdict

Buss ch. II does **not** contain a clean citable form of Wainer's classification — that lemma lives in the sibling Handbook chapter (Fairtlough–Wainer, ch. III, pp. 149–207), which Buss explicitly defers to; ch. II's "provably total" material (§1.2.7) is only the general `Σ₁`-definable / bounded-theory toolkit. It likewise does **not** prove the cut-elimination reduction itself (imported as a prerequisite from ch. I); its on-point contribution to crux-2 is the **fragment-strength framing** — the superexponential-totality threshold for internalizing arithmetized cut-elimination (§1) plus the `Σ₁`/Parikh/Gaifman–Dimitracopoulos definability apparatus (§1.2.7) — making it a strong *background/meta-theory* reference but not a primary source for either route. (Caveat: §2–§4 are absent from the local PDF, but the Contents page confirms they cover incompleteness, bounded-arithmetic witnessing, and `I∆₀+exp` — none of which is ordinal analysis of `PA`.)
