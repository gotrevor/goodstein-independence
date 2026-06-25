# Rathjen (2006) — The Art of Ordinal Analysis

## Provenance

- **File**: `rathjen-2006-art-of-ordinal-analysis.pdf`
- **Title**: *The Art of Ordinal Analysis*
- **Author**: Michael Rathjen (University of Leeds)
- **Source**: *Proceedings of the International Congress of Mathematicians* (ICM), Madrid 2006, Vol. II, pp. 45–69. European Mathematical Society, 2006. MSC 2000: 03F15, 03F05, 03F35 (primary); 03F03, 03-03 (secondary).
- **Citation**: M. Rathjen, "The art of ordinal analysis," in *Proceedings of the International Congress of Mathematicians (Madrid, 2006)*, Vol. II, Eur. Math. Soc., Zürich, 2006, pp. 45–69.
- **Type**: ICM survey / expository overview (a "history + state of the art" of ordinal-theoretic proof theory).

---

## Abstract / scope

A survey of "ordinally informative" proof theory — i.e. **ordinal analysis**, the branch of proof theory that classifies formal theories by assigning each a **proof-theoretic ordinal** measuring its "consistency strength" and "computational power." Rathjen traces the field from its **birth in Gentzen's 1936 consistency proof of arithmetic** (which assigns `ε₀` to `PA`) through Schütte, Veblen, Bachmann, Takeuti, and the Munich school, up to **recent advances in analyzing strong subsystems of second-order arithmetic** (the ordinal analysis of `Π¹₂-CA`). The level rises steeply: the second half is a research-level tour of impredicative collapsing functions, admissible proof theory, reflection, stability, and large-cardinal-inspired ordinal representation systems. The abstract explicitly flags that the proof-theoretic ordinal "also serves to characterize [a theory's] **provably recursive functions** and can yield both **conservation** and **combinatorial independence results**" — but these rewards are *named*, not developed, in the body.

This is an **orientation document**, not a how-to. It explains *why* `ε₀` is the ordinal of `PA` and *how* the cut-elimination machinery delivers it, but it stops short of the explicit independence/growth-rate apparatus.

---

## Key content (section-by-section)

### §1 Introduction + §1.1 Gentzen's result
- **Hilbert's programme** framing: ordinal analysis grew out of the search for finitistic consistency proofs.
- **Gentzen's theorem**, given precisely (eq. (1)): `F + EC-TI(ε₀) ⊢ Con(PA)`, where `F` is a finitistically acceptable base theory (identified with **Elementary Recursive Arithmetic, ERA**), and `EC-TI(ε₀)` is **transfinite induction up to `ε₀` for elementary computable predicates**. Conversely `PA` proves `TI(α)` for every `α < ε₀` — so `ε₀` is *exactly* the non-finitist part of `PA`.
- **Definition of proof-theoretic ordinal** (eq. (2)): `|T|_Con = least α such that F + EC-TI(α) ⊢ Con(T)`.
- `ε₀ = sup{ω, ω^ω, ω^{ω^ω}, …} = least α with ω^α = α`.

### §1.1 (cont.) Ordinal representation systems
- **Cantor normal form** (Thm 1.4, Cantor 1897): every `β > 0` is uniquely `ω^{β₀} + … + ω^{βₙ}` with `β₀ ≥ … ≥ βₙ`.
- Ordinals `< ε₀` are **coded by natural numbers** via a recursive (in fact elementary computable) coding `⌜·⌝ : ε₀ → ℕ`, with `+`, `·`, `α ↦ ω^α` all elementary computable on the codes. This is what lets `EC-TI(ε₀)` be *stated in the language of `PA`*.

### §1.2 Cut elimination: Gentzen's Hauptsatz — **the central mechanism**
- Sequent calculus rules laid out (identity, cut, structural, logical, ∀/∃).
- **Hauptsatz (Thm 1.5)**: any provable sequent has a **cut-free** proof.
- **Cost of cut-elimination is hyper-exponential**: turning a height-`|D|` deduction with cut-rank `rank(D)` into a cut-free one yields height `H(rank(D), |D|)` where `H(0,n)=n`, `H(k+1,n)=4^{H(k,n)}` — a **stack of exponentials**. *This tower of exponentials is the seed of the `ε₀` measure.*
- **Subformula property** (Cor 1.6) + **consistency corollary** (Cor 1.7: the empty sequent `∅ ⇒ ∅` is not cut-free derivable, hence not derivable).
- **Why this fails for `PA`**: the induction axioms have *unbounded* syntactic complexity, so partial cut-elimination doesn't apply. The fix is to go **infinite**.

### §1.2 (cont.) The infinitary route — `PAω` and the ω-rule
- The **ω-rule** (infinitary inferences `ωR`/`ωL`) replaces the induction scheme: deductions become **infinite well-founded trees**, each with a **natural ordinal height**.
- **`PAω`** cut-elimination (Thm 1.8): lowering cut-rank from `k+1` to `k` costs an `ω`-base exponential (`α ↦ ω^α`). Iterating the embedding `PA ⊢ Γ⇒Δ ⟹ PAω ⊢^{ω+m}_k Γ⇒Δ` and then eliminating cuts pushes the height below `ε₀`.
- **Punchline (p. 9)**: "the passage from finite deductions in `PA` to infinite cut-free deductions in `PAω` provides an explanation of how the ordinal `ε₀` is connected with `PA`." Buchholz [9] later showed Gentzen's original ordinal assignment to finite derivations and the `PAω` height assignment are intrinsically the same.

### §1.3 History of ordinal representation systems (1904–1950)
- **Hardy (1904)**: fundamental sequences, the slow-growing idea — representations of ordinals `< ω²`. (*Hardy appears here only as ordinal-representation history, not as a fast-growing function hierarchy.*)
- **Veblen**: derivation + transfinite iteration of normal functions → the `φ`-hierarchy, `Γ₀` (Feferman–Schütte, the limit of **predicativity**), the "great Veblen number" `E(0)`.
- **Bachmann (1950)**: uses **uncountable ordinals** + collapsing to outrun all Veblen-style hierarchies.

### §2 Ordinal analyses of second-order arithmetic and set theory
- **Reverse mathematics** framing (Friedman): the "big five" `RCA₀ ⊆ WKL₀ ⊆ ACA₀ ⊆ ATR₀ ⊆ Π¹₁-CA₀`.
- **Proof-theoretic ordinals at scale**: `|RCA₀| = |WKL₀| = ω^ω`; `|ACA₀| = |ATR₀| = ε₀` (`ACA₀` has the same strength as `PA`); `|ATR₀| = Γ₀`; `|Π¹₁-CA₀|` is the Bachmann–Howard ordinal `ψ_Ω(ε_{Ω+1})` and needs **impredicative** collapsing.
- §2.2–2.4: **Admissible proof theory** — Kripke–Platek `KP`, the collapsing function `ψ_Ω`, the **Bachmann–Howard ordinal** as `|KP|`, and the line of admissible/reflecting theories.

### §2.5 Rewards of ordinal analysis — **the directly relevant section**
Rathjen states the four payoff groups verbatim:
> "(1) Consistency of subsystems … relative to constructive theories, (2) reductions of theories formulated as conservation theorems, **(3) combinatorial independence results**, and **(4) classifications of provable functions and ordinals**."

He points to **Friedman's EKT / Kruskal-theorem** and the **Robertson–Seymour graph minor theorem** (Thm 2.1) as combinatorial independence results whose proofs hinge on ordinal notation systems. **He does not develop a fast-growing-hierarchy treatment of (3)/(4) here** — they are cited as *rewards*, with a pointer to [31, §3] for the detailed account.

### §3–§4 Beyond admissible proof theory
- The ordinal analysis of `Π¹₂-CA` via reflection (`Πₙ`-reflection, stability, `δ`-`Πₙ`-reflecting ordinals) and **large-cardinal-inspired** ordinal representation systems ("shrewd" cardinals). Research-frontier material, **not relevant** to the Goodstein routes.

---

## Relevance to the expedition (the two routes)

The repo's two candidate skeletons for `PA ⊬ Goodstein`:

- **Route A — cut-elimination / Con(PA) ("crux-2")**: `PA ⊢ Goodstein → PA ⊢ PRWO(ε₀) → (internalized cut-elimination) → PA ⊢ Con(PA) → ⊥` (Gödel II).
- **Route B — growth-rate / fast-growing hierarchy**: encode the Goodstein step-count as a Hardy function `Hₐ`, cite Wainer's classification that `H_{ε₀}` outgrows every PA-provably-recursive function (the Cichoń / Kirby–Paris skeleton).

**What this paper is good for**: it is the **canonical orientation document for Route A**. §1.1–§1.2 give the cleanest survey-level account of *exactly* the machinery crux-2 must internalize:
- the precise Gentzen statement `F + EC-TI(ε₀) ⊢ Con(PA)` (eq. 1),
- the hyper-exponential cost of cut-elimination (the source of the `ε₀` tower),
- the `PAω`/ω-rule re-derivation that *explains why `ε₀`*, and
- the elementary-computable coding of `ε₀` into `PA`'s language (what makes `EC-TI(ε₀)` even expressible).
For someone formalizing crux-2, this is the best one-stop conceptual map of the target, with the right section pointers (and the Buchholz [9] pointer tying Gentzen's finite assignment to the infinitary one — relevant to choosing which assignment to formalize).

**Does it cleanly state the `PA ↔ ε₀ ↔ fast-growing-hierarchy` correspondence a Route-B citation would need? — No.** This is the key limitation for the growth-rate route:
- It states the **`PA ↔ ε₀`** half rigorously and repeatedly (Gentzen, eq. 1; the `PAω` height argument; `|ACA₀| = ε₀`).
- It **does not** state the **`ε₀ ↔ fast-growing/Hardy hierarchy`** half. The abstract mentions "characteriz[ing] provably recursive functions," and §2.5 lists "(4) classifications of provable functions and ordinals" as a *reward* — but there is **no Hardy hierarchy `Hₐ`, no slow-growing hierarchy `Gₓ`, no Wainer classification theorem, no majorization/domination lemma, and no statement of the form '`f` is PA-provably-total iff `f` is dominated by some `Hₐ`, `α < ε₀`'** anywhere in the paper. Hardy appears (§1.3) only as 1904-era ordinal-representation history, not as a function-growth hierarchy. **For Route-B you must cite Cichoń (1983), Wainer, or a fast-growing-hierarchy reference — not this survey.** Rathjen merely *gestures at* group (4) and forwards the reader to [31, §3].

So: **orienting/context value is high for Route A, low for Route B.** It situates Gentzen's `ε₀` result, the cut-elimination mechanism, and the place of `PA` in the broader ordinal-analysis landscape; it does *not* supply the growth-rate correspondence the Kirby–Paris/Cichoń independence argument depends on.

---

## Verdict

The best survey-level **orientation for the cut-elimination / Con(PA) route**: §1.1–§1.2 lay out, cleanly and with exact statements, precisely what crux-2 must internalize — Gentzen's `F + EC-TI(ε₀) ⊢ Con(PA)`, the hyper-exponential cost of cut-elimination that produces the `ε₀` tower, and the `PAω`/ω-rule re-derivation that *explains why* `ε₀` is `PA`'s ordinal (plus the elementary coding of `ε₀` into `PA`'s language). But it is **not** a Route-B source: it proves the `PA ↔ ε₀` correspondence yet never states the `ε₀ ↔ fast-growing/Hardy-hierarchy ↔ provably-total-functions` correspondence (no Hardy hierarchy, no Wainer classification) — those appear only as a named "reward" in §2.5 with a forward pointer, so a growth-rate independence argument must cite Cichoń/Wainer instead. Most useful single takeaway: it is the map of the cut-elimination wall and why `ε₀` measures it.
