# Siders — Gentzen's consistency proofs for arithmetic

## Provenance

- **File**: `siders-gentzen-consistency-proofs-arithmetic.pdf` (26 slides — a Beamer presentation deck, NOT a journal article).
- **Author**: Annika Siders (Department of Philosophy, University of Helsinki).
- **Title / date**: *Gentzen's Consistency Proofs for Arithmetic*, March 2012. Lecture/seminar slides (open course notes; SOURCES.md lists the JAIST `jss12` course mirror, `http://www.jaist.ac.jp/~mizuhito/jss12/Siders.pdf`).
- **Citation**: A. Siders, "Gentzen's consistency proofs for arithmetic" (slides, 2012). The new technical content (the height-line-free reduction) is the author's own then-submitted paper: A. Siders, "Gentzen's Consistency Proof Without Heightlines" (Submitted) — slide reference (5). Background references on the deck: Buss, *Handbook Proof Theory* ch. (1998); Gentzen, *Collected Papers* (ed. Szabó, 1969); Howard, "Assignment of ordinals to terms for primitive recursive functionals of finite type" (1970); von Plato, "From Hilbert's programme to Gentzen's Programme" (2007).
- **Why it's in this repo**: a **compact English companion** to the German Buchholz [6] notes for the same ε₀-bounded Gentzen Con argument (its catalogued role in `SOURCES.md`). Of independent interest for **crux-2** because the deck's *new* result is an alternative way to discharge the one hard piece — the cut on a compound formula (eq-(5)'s critical case) — via a Howard-style **vector assignment** instead of Gentzen's **height-line** construction.

> ⚠️ **Caveat: this is a slide deck.** It states the architecture, the operations, and one worked case (conjunction), but it does NOT contain full proofs of the vector inequalities or the termination argument — those live in the (separately-submitted) "Without Heightlines" paper, which is NOT in this repo. Treat the deck as a *route map*, not a citable lemma source. The substrate the box actually ports remains **Buchholz [6]** (classical PA, finitary Z, `o(d)=ω_{dg(d)}(õ(d))`); Siders is a cross-check / alternative-technique reference, not a drop-in.

---

## Abstract (plain language)

The deck has two halves.

**Part 1 — Gentzen's quest for consistency (historical survey).** Recaps Gentzen's *four* consistency proofs of Peano Arithmetic (PA), worked out 1934–1939:

- **First proof** (1935, withdrawn after Bernays' critique; galley + posthumous editions): formulated as a verifier-vs-falsifier *game*. From any derivable sequent `Γ → A`, effectively construct a *reduction* to an "endform" (true atomic succedent, or false atomic antecedent). Derivable ⟹ the verifier has a winning strategy; the contradictory sequent `→ 0=1` cannot be reduced, hence is not derivable. Bernays/Gödel objected to an *implicit use of the fan theorem*; later analysis (Kreisel 1987, Tait 2005, von Plato) recasts the implicit principle as **bar recursion / recursion on well-founded trees**.
- **Second proof** (published 1936): adds an explicit **ordinal assignment** and relies on a constructive proof of **transfinite induction up to ε₀**.
- **Third proof** (1938, standard sequent calculus): a primitive-recursive **reduction procedure** on derivations of contradictions (the empty sequent); each step yields a *less complex* derivation of the empty sequent; termination is impossible for a "simple" derivation, so no derivation of the empty sequent exists. The combinatorics live in **PRA** (quantifier-free), so finitistic reasoning + **quantifier-free transfinite induction up to ε₀** gives Con(PA).
- **Fourth proof** (1943): consistency via a **non-derivability** — represents TI up to ε₀ as an arithmetical formula, shows it is *not* provable in PA but every weaker (`< ε₀`) induction principle is.

It also makes the standard metatheoretic point: the theory formalizing the proof is **incomparable** to PA (it can't prove full induction; but it *can* prove Con(PA)).

**Part 2 — A Gentzen-style proof without height-lines (the new contribution).** Gentzen's third proof uses a **height-line argument**: to lower the ordinal of a derivation of the empty sequent, you locate a reducible cut on a compound formula and simplify it — but (because the cut formula may have been *contracted*) the simplification is NOT a straightforward conversion of the cut into cuts on shorter formulas; it requires a *height-line construction* introducing additional cuts on compound formulas, which permutes "height-drop" points upward and lowers the ordinal only through the height-of-a-sequent notion. Siders' result **eliminates the height-line construction**: a **Howard-style vector assignment** lets you *directly* turn a suitable cut on a compound formula into cuts on shorter formulas. The deck presents this for **intuitionistic Heyting Arithmetic (HA)**, building on Howard (1970)'s ordinal/vector assignment for Gödel's T.

---

## Key content

### The four-proof taxonomy (Part 1)

The single most useful sentence for orienting the repo's sources: today "Gentzen's consistency proof" means the **1938** sequent-calculus / reduction-procedure version (third proof); the **1936** (second/first) version is the one Buchholz [6] reconstructs. Siders' Part 1 is exactly the map of which Gentzen paper is which — a clean English gloss on the same territory the German Buchholz notes cover.

> *"The combinatorial methods of Gentzen's reduction procedure described in the third proof can be represented in primitive recursive arithmetic (PRA)... Therefore, finitistic reasoning together with the principle of transfinite induction restricted to quantifier-free formulas gives the consistency result."*

This is **eq-(5)'s finitistic-means clause** stated in words: `ord` and `R` are primitive recursive, and only finitist means show `ord(R(D)) < ord(D)`.

### The height-line problem (the obstruction the deck attacks)

> *"He uses a construction called the height-line argument to produce a derivation with a lower ordinal from a given derivation of the empty sequent... The simplification is however not a straightforward conversion of the cut into cuts on shorter formulas, due to the fact that we can have contractions on the cut formula. (Compare to a cut elimination theorem.)"*

That parenthetical is the crux-2 connection: **lowering the ordinal IS internalized cut-elimination**, and the difficulty is contraction on the cut formula — the same nut Buchholz isolates as the *critical case 5.1* (degree-drop).

### Howard's vector assignment (the new mechanism)

Instead of a scalar ordinal, assign each sequent in a derivation a **vector** whose components are Howard "expressions":

- *"Whenever a copy of a formula `A` is first introduced in the antecedent of a sequent by a left rule (but not by weakening), then a variable `x^A` ... is introduced in the vector."* — so the vector tracks every uncontracted introduction of the cut formula.
- Two operations on vectors: the **box-operation** `□` (a form of addition + iteration of exponentiation) and the **delta-operation** `δ^A h` (gives a vector with no component of the variable vector `x^A`).
- **Main property** (the load-bearing inequality):

  > `((δ^A h) □ e)_i  >  (h[e / x^A])_i`   for all `i ≤ length(h)`.

  In words: the vector `(δ^A h) □ e` dominates the vector obtained by **substituting `e` for the `x^A`-components of `h`** — i.e. *substituting the right cut-premise into each place the cut formula was introduced strictly decreases the assignment*. This is what makes the direct duplication-of-the-cut-on-a-shorter-formula sound: duplicate the shorter cut once per uncontracted introduction; the `δ`-operation's design makes that duplication ordinal-decreasing even after contraction.

- **First component = ordinal `< ε₀`.** *"The reduction reduces the first component of the vector and this component can be interpreted as an ordinal less than ε₀, thus ordering the derivations by complexity and proving termination."* The vector's *length* codes the complexity of the succedent formula. So the scalar Gentzen ordinal is recovered as the vector's head; the rest of the vector is the bookkeeping that replaces the height-line.

### The reduction procedure + the worked conjunction case (Part 2)

- Substitute constants for all free variables, then **trace up from the end-sequent** for a "suitable reduction." The trace rules **preserve the vector inequality**, so the `δ`-operation never runs on the reduced vector.
  - If the last rule is arithmetical / induction → that's a suitable reduction (the all-arithmetical-rules derivation of the empty sequent is "simple," hence impossible).
  - If the last rule is a **cut**, trace up the left premises of the lowermost cuts to a non-cut-derived empty-antecedent sequent — derivable by induction, arithmetical rule, right weakening, or a logical right rule → the suitable reduction.
- **Worked case — cut formula `A & B`** (conjunction; the other connectives "are similar, except disjunction, which is a defined concept"):
  - Vector at the cut conclusion: `δ^{A&B} μ₂ □ μ₁ = δ^{A&B} μ₂ □ (α + β)` (where `→α A`, `→β B` feed `R&` to give `→ A&B`, then cut against `A&B → C`).
  - **Trace** the right premise to the first occurrences of `A&B` in the antecedent (a left-weakening or a logical-left rule `L&`, never an initial sequent — those are restricted to atomic formulas).
    - (i) first occurrence by **left weakening** → remove the weakening and the formula in each context (and any later contraction on `A&B`); this **does not alter the vectors**.
    - (ii) a **logical left rule** `L&` is reached with active formula (say) `A`: rule `A,Γ →^γ D ⟹ A&B,Γ →^γ D`, conclusion vector `λ = x^{A&B} □ δ^A γ`. **Replace** it by a cut against the *left* rule's premise (`→^α A`), giving `→^{λ'} D` with `λ' = α □ δ^A γ = λ[α / x^{A&B}]` — i.e. the `x^{A&B}` slot is filled by `α`, dropping the connective rank by one (cut on `A`, shorter than `A&B`).
  - The reduced derivation's cut-conclusion vector is `μ₂[ν / x^{A&B}]` with `ν ∈ {α, β}`, and (since `α ≤ α+β`, `β ≤ α+β`) the main inequality gives it `< δ^{A&B} μ₂ □ (α+β)` — **the original vector strictly dominates the reduced one.** ∎ (for the conjunction case)

### The consistency theorem (stated for HA)

> **Theorem (consistency of HA).** *The empty sequent `→` is not derivable in HA; that is, HA is consistent.*

Proof shape: a derivation of the empty sequent reduces, indefinitely, to ones of strictly lower ordinal (the vector's first component, all `< ε₀`); an infinite descending `< ε₀` sequence contradicts the well-ordering of the ordinals; so no derivation of the empty sequent exists.

### The cut-elim flavor (relationship to standard results)

> *"The reductions resemble proofs of direct cut elimination without multicut. See (Buss, 1998), (Troelstra & Schwichtenberg, 1996) and (von Plato, 2001)."*

So the deck's reductions are essentially a **direct (non-multicut) cut-elimination**, with the vector assignment supplying the ordinal control that the height-line otherwise gave.

---

## Relevance to crux-2 (internalized cut-elimination / the eq-(5) step)

**Bottom line: useful as a cross-check and a *conceptual* alternative, but NOT a drop-in shortcut, and probably the wrong vehicle for THIS architecture. Keep Buchholz [6].**

Crux-2's hard nut (per `E-CRUX2-DECOMPOSITION-2026-06-24.md`, `CRUX2-GENTZEN-2026-06-23.md`) is exactly the **critical cut-elimination case** where the pre-ordinal `õ` can jump up and the descent survives only because the **degree `dg` strictly drops** — i.e. internalizing Rathjen's eq-(5) `ord(R(D)) < ord(D)` on coded derivations, M-internally. Siders attacks the *same* obstruction (contraction-on-the-cut-formula blocking a naive "cut → shorter cuts" conversion). What it adds, and the costs:

1. **It confirms the difficulty is real and localized** (medium confidence the box benefits). Siders independently identifies *contraction on the cut formula* as the thing that makes the height-line necessary in Gentzen's 1938 proof. This matches the box's own diagnosis (the nut is case 5.1, gated on the rank bound T3.4). So the deck is corroborating evidence that the plan's "one hard case" framing is correct — not new lemmas.

2. **It offers a genuinely *different* descent mechanism** (the conceptual contribution). Buchholz's route absorbs the cut-formula's contractions through the **tower `o(d)=ω_{dg(d)}(õ(d))` + a degree-drop** (height/degree IS the scalar that falls). Siders **eliminates the height-line entirely**: a Howard-style **vector** assignment whose `δ`/`□` algebra makes the *direct* duplication-of-the-cut-on-a-shorter-formula ordinal-decreasing, via the one inequality `((δ^A h)□e)_i > (h[e/x^A])_i`. If the box's tower bookkeeping (the `idg`/`iõ`/`iord` + F1–F4 + `icmp_iotower_*` machinery, and especially the degree-drop lemma C3b) turns out to be the painful part to internalize, Siders' vector approach is a **candidate redesign** that trades the tower for a vector-of-Howard-expressions algebra. The conjunction worked-case shows the shape concretely.

3. **But the costs make it a poor swap for *this* expedition** (higher confidence it's not the move):
   - **Wrong logic + wrong system.** The deck proves consistency of **intuitionistic HA**, in a system where disjunction is *defined* and built on **Howard (1970)'s assignment for Gödel's T**. The box targets **classical PA** via Buchholz's finitary **Z** (chain rule, `zK`/`zInd` codes). Adopting Siders means importing a normalization-of-T-flavored vector calculus and re-deriving everything classically — a different substrate from Foundation's calculus, on top of the already-flagged Foundation→Z bridge seam (C0.5).
   - **Not a citable proof.** It's a slide deck; the vector inequalities and termination are asserted, with the proofs in the un-repo'd "Without Heightlines" submission. You cannot port lemmas from it — only ideas.
   - **The primrec-PRWO hinge still has to be re-established.** Crux-2's whole *point* (vs. just "Con(PA)") is that the finitary reduction yields a **primitive-recursive** descent `n ↦ ord(Rⁿ d₀)` that joins crux-1's Goodstein→PRWO slow-down. Siders' first-component-is-the-ordinal does preserve a finitary, primrec-shaped descent (good — unlike the PA_ω route in the Bryce–Goré finding), but you'd have to verify the vector reduction is primrec on *coded* derivations and re-prove that hinge in the new calculus. No free lunch over Buchholz, where the box has already mapped `o(d)`/`R` to `iord`/`iR`.

**Net for the internalized cut-elimination:** Siders adds (a) a clean English statement of the four Gentzen proofs and the contraction-on-cut-formula obstruction (orientation + corroboration), and (b) one *alternative* technique — the Howard vector / `δ`-operation that discharges eq-(5)'s critical case **without** a height-line or a tower. It is worth a read as a *Plan-B mechanism* if the Buchholz degree-drop (C3b) proves intractable to internalize, but it is not a citable lemma source, it's built for the wrong logic/base-system, and switching to it re-opens the primrec-descent hinge. **Recommendation: keep Buchholz [6] as the porting substrate; file Siders as the fallback-redesign reference and as the cross-source that validates "the difficulty is the one critical cut case."**
