# Buss — "An Introduction to Proof Theory" (Handbook of Proof Theory, ch. I)

## Provenance

- **File**: `buss-handbook-ch1-intro-proof-theory.pdf`
- **Author**: Samuel R. Buss (Departments of Mathematics and Computer Science, UC San Diego)
- **Title / venue**: *An Introduction to Proof Theory*, Chapter I of the *Handbook of Proof Theory* (ed. S. R. Buss), Elsevier 1998, pp. 1–78.
- **Citation**: S. R. Buss, "An introduction to proof theory," in *Handbook of Proof Theory*, ed. S. R. Buss, Studies in Logic and the Foundations of Mathematics vol. 137, Elsevier, 1998, pp. 1–78.
- **Source URL**: https://mathweb.ucsd.edu/~sbuss/ResearchWeb/handbookI/ChapterI.pdf (author's open copy)
- **Companion in this repo**: this chapter is the **prerequisite** cited by ch. II (`buss-handbook-ch2-first-order-proof-theory-arithmetic.md`): "knowledge of the sequent calculus and cut-elimination, as contained in Chapter I of this volume." Local PDF is the **full 78-page chapter** (unlike the partial ch. II extract).

---

## Abstract / scope

An overview/introduction to **mathematical proof theory**, concentrating on **classical logic** — propositional logic and first-order logic. The chapter develops three families of proof systems and then proves the central structural theorems about them. Buss's own organizing claim (p.3): *"Next we consider some applications of cut elimination, which is arguably the central theorem of proof theory."*

Contents (page refs in the PDF):
- **§1 Proof theory of propositional logic** (pp.3–25): §1.1 Frege (Hilbert-style) systems; §1.2 the propositional sequent calculus `PK`; §1.3 propositional resolution.
- **§2 Proof theory of first-order logic** (pp.26–63): §2.1 syntax/semantics; §2.2 Hilbert-style systems; §2.3 the first-order sequent calculus `LK`; **§2.4 cut elimination**; §2.5 Herbrand's theorem, interpolation, definability; §2.6 first-order resolution.
- **§3 Proof theory for other logics** (pp.64–73): §3.1 intuitionistic logic; §3.2 linear logic.

The relevant spine for this repo is the sequent calculus (`PK`/`LK`) and **cut elimination** (§1.2, §2.3, §2.4).

---

## Key content

### Sequent calculus (§1.2 propositional `PK`, §2.3 first-order `LK`)
- **Sequents** (§1.2.1): a sequent `A₁,…,A_k ⟶ B₁,…,B_ℓ` (antecedent → succedent, both called *cedents*) means `⋀Aᵢ ⊃ ⋁Bⱼ`. Empty antecedent = `True`, empty succedent = `False`; the empty sequent `⟶` is false.
- **`PK` rules** (§1.2.2): **weak structural rules** (exchange / contraction / weakening, left & right), the **cut rule**
  ```
        Γ ⟶ Δ, A    A, Γ ⟶ Δ
        ─────────────────────  (A is the cut formula)
              Γ ⟶ Δ
  ```
  and the **propositional logical rules** (`¬:left/right`, `∧:left/right`, `∨:left/right`, `⊃:left/right`). Initial sequents (axioms) are `A ⟶ A` with `A` **atomic**.
- **`LK`** (§2.3.2) = `PK` + the **quantifier rules** `∀:left, ∀:right, ∃:left, ∃:right`; the `∀:right`/`∃:left` free variable `b` is the **eigenvariable** (must not appear in the lower sequent). `LK_𝔖` (§2.3.3) = `LK` allowing extra initial sequents from a set 𝔖; `LK_e` adds the equality initial sequents. Free vs bound variables and *semiterms*/*semiformulas* are distinguished (§2.3.1) so that `A(t)` substitution and the eigenvariable conditions stay clean.
- **Ancestors / descendants / subformula property** (§1.2.3): principal / auxiliary / side / cut formulas; a *cut-free* proof contains no cut inferences. **Subformula Property (Prop. 1.2.4):** in a cut-free `PK`-proof every formula is a subformula of a formula in the endsequent. (First-order version: Prop. 1.2.4 / the cut-free completeness machinery of §2.3.7.)
- **Soundness / inversion / cut-free completeness** (§1.2.6–1.2.8, §2.3.6–2.3.7): `PK`/`LK` are sound; the **inversion theorem** (§1.2.7) says (except for weakening) a valid lower sequent forces valid upper sequents; **cut-free completeness** (Thm 1.2.8 propositional; Cut-free Completeness Thm 2.3.7 first-order) — every valid sequent has a **cut-free** proof.

### The Hauptsatz / cut-elimination theorem (§2.4 — the load-bearing section for this repo)

Buss gives a **constructive** cut-elimination proof (§2.4, p.37): *"this proof will give an effective procedure for converting a general `LK`-proof into a cut-free `LK`-proof,"* with explicit size bounds, structured by *global* changes to the proof rather than Gentzen's local rank reductions.

- **Depth of a cut** (Def. 2.4.1) = depth `dp(A)` of its cut formula (`dp(atomic)=0`; one more than the max over immediate subformulas). **Superexponentiation** `2ₓⁱ` (Def. 2.4.1): `2₀ˣ = x`, `2_{i+1}ˣ = 2^{2ᵢˣ}` — a stack of `i` twos with `x` on top.

- **Cut-Elimination Theorem (2.4.2).** Let `P` be an `LK`-proof in which every cut formula has depth `≤ d`. Then there is a cut-free `LK`-proof `P*` with the **same endsequent** and size
  ```
        ‖P*‖  <  2_{2d+2}^{‖P‖}
  ```
  (`‖P‖` = number of *strong* inferences in the tree-like proof.) Proved by **iterating the key lemma**:

  - **Lemma 2.4.2.1** (one round): if `P` ends with a cut of depth `d` and every *other* cut has depth `< d`, there is `P*` (same endsequent) with all cuts of depth `< d` and `‖P*‖ < ‖P‖²`. (Proof by cases on the cut formula's outermost connective `¬,∨,∧,⊃,∃,∀,atomic`; the `∃`/`∀` cases use *free variable normal form*, §2.3.5, to keep eigenvariable conditions intact.)
  - **Lemma 2.4.2.2** (one depth layer): from "all cuts depth `≤ d`" to "all cuts depth `< d`", `‖P*‖ < 2^{2^{‖P‖}}` — squaring per layer; iterating over the `d`+constant depth layers gives the superexponential tower.

- **General bound (Prop. 2.4.3):** dropping the depth hypothesis, any `LK`-proof of `Γ⟶Δ` has a cut-free proof with `‖P*‖ < 2_{2‖P‖}^{‖P‖}` (bound in terms of `‖P‖` alone, via the *term-variant / formula-skeleton* trick that caps formula depth by `‖P‖`).

- **Free-cut elimination (§2.4.4–2.4.5)** — the version that actually matters once non-logical axioms/induction are present. For `LK_𝔖`-proofs (initial sequents drawn from a set 𝔖 closed under substitution), a cut is *anchored* if its cut formula traces back to an 𝔖-sequent (Def. 2.4.4.1); otherwise it is *free*.
  - **Free-cut Elimination Theorem (2.4.5):** if `LK_𝔖 ⊢ Γ⟶Δ` then there is a **free-cut free** `LK_𝔖`-proof of `Γ⟶Δ`; with the depth-`≤d` hypothesis the same `2_{2d+2}^{‖P‖}` size bound holds. (Due essentially to Gentzen; Takeuti [1987].)
  - **With induction rules (§2.4.6) — directly on-target for arithmetic.** Induction is recast as a *rule*
    ```
        A(b), Γ ⟶ Δ, A(b+1)
        ───────────────────   (b eigenvariable, t arbitrary term)
        A(0), Γ ⟶ Δ, A(t)
    ```
    equivalent to the induction axiom for `A`. For a theory `T = 𝔖 + Φ-IND` (Φ closed under term substitution), the **Free-cut Elimination Theorem** holds with the same size bounds; **Cor. 2.4.7:** a `T`-consequence whose every formula is in Φ has a `T`-proof using **only Φ-formulas** (the formulas in a free-cut-free proof are subformulas of the endsequent or of induction/axiom formulas). This is the standard lever for analyzing `IΣₙ`/`I∆₀`/`T₂ⁱ` and is the proof-theoretic foundation under the ε₀-girder phase.

- **Slick (non-constructive) version** (§1.2.11 propositional): cut-elimination is *immediate* from soundness + cut-free completeness — but gives **no proof transformation and no bounds**, which is exactly why §2.4's constructive procedure is what one cites for the ordinal/size analysis.

### Other content (background, lighter relevance)
- **Frege / Hilbert-style systems** (§1.1, §2.2): modus ponens + schematic axioms; soundness & completeness of `F`; *Frege systems*; the open `P` vs `NP`-flavored proof-length questions (Chapter VIII).
- **Resolution** (§1.3, §2.6): clauses, the resolution rule, refutations — proof-search oriented, peripheral here.
- **Herbrand's theorem, interpolation, definability** (§2.5): Herbrand's theorem reduces `Π₂`-consequences of universal theories to (quasi)tautologies; Skolemization / Herbrandization. Proved *via* free-cut elimination — a clean illustration of cut-elimination as a tool.
- **Tait calculus** (§1.2.14): one-sided sequents (sets of formulas), used for **infinitary logic** — cut-elimination there is the *normalization theorem*; Lopez-Escobar's result that cut-elimination holds for countably-infinite formulas. This is the bridge to the **PA∞ / ω-rule** infinitary cut-elimination the ε₀ girder actually uses (carried out in this repo by Buchholz/Siders/Arai, not here).
- **Intuitionistic / linear logic** (§3): `PJ` = `PK` with at-most-one succedent formula; both formalize cleanly in the sequent calculus.

---

## Relevance to the Goodstein-independence box

**Foundational background — the finitary cut-elimination engine, not the ε₀ argument itself.** This is the canonical, self-contained English reference for the **sequent calculus + cut-elimination machinery** that the ε₀ girder is built on (matching SOURCES.md's tag: *"the cut-elimination engine, finitary version"*).

- **What it gives the repo.** Clean, citable statements of: the sequent calculus `LK`/`LK_𝔖` and its rules; the **subformula property** of cut-free proofs; and especially the **constructive Cut-Elimination Theorem (Thm 2.4.2)** with explicit superexponential bounds `2_{2d+2}^{‖P‖}` plus the **free-cut elimination with induction rules (§2.4.6, Cor. 2.4.7)** — which is the exact mechanism by which an arithmetic theory's proofs reduce to subformula-bounded form. For crux-2 (the ordinal/cut-elimination internalization), §2.4 is the textbook home of "what the cut-reduction step *is*" at the finitary level.

- **What it does NOT give.** This chapter is **finitary** and **logic-general**: there is **no ordinal assignment, no ε₀, no PA∞/ω-rule, and no Goodstein/independence content here.** The cut-elimination bound is a superexponential *function of proof size*, not an *ε₀-indexed ordinal* on coded PA∞-derivations. The actual ε₀-bounded, ordinal-decreasing cut-reduction on infinitary PA-derivations — the thing that powers `TI(ε₀) ⊢ Con(PA)` — lives in **Buchholz** (`buchholz-on-gentzens-first-consistency-proof.md`, ordinal-decreasing reduction `o(d[n]) < o(d)`), **Siders**, **Arai**, and the German **Beweistheorie** notes. The Tait-calculus / infinitary-cut-elimination pointer (§1.2.14) is the only place this chapter even gestures at the infinitary setting, and it does not carry it out. The growth-rate / Route-B (Hardy/fast-growing) material is likewise absent (it is Fairtlough–Wainer ch. III; see ch. II summary).

- **Pairing.** Use this file for the *finitary* cut-elimination theorem statement, the `LK`/`LK_𝔖` definitions, and the subformula property; switch to Buchholz/Siders/Arai for the *infinitary, ε₀-indexed* version that the consistency proof needs, and to ch. II for the fragment-strength (superexponential-totality) framing of internalizing arithmetized cut-elimination.

---

## Verdict

The most useful single reference in this repo for the **finitary cut-elimination machinery itself**: §2.4 gives a fully constructive, effective Hauptsatz with clean superexponential size bounds (Thm 2.4.2, `2_{2d+2}^{‖P‖}`) and — crucially for an arithmetic application — **free-cut elimination with induction rules** (§2.4.6, Cor. 2.4.7), the lever that bounds proofs of a fragment by subformulas of its induction/axiom formulas. But it stops at the finitary, logic-general level: **no ordinals, no ε₀, no PA∞, no Goodstein**, so it is solid *background/engine* for crux-2 rather than a primary source for the ε₀-bounded argument — that ordinal-decreasing infinitary cut-elimination is in Buchholz/Siders/Arai, with the only bridge here being the brief Tait-calculus / infinitary-normalization pointer (§1.2.14).
