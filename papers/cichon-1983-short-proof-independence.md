# Cichoń (1983) — A Short Proof of Two Recently Discovered Independence Results Using Recursion Theoretic Methods

## Provenance

- **File**: `cichon-1983-short-proof-independence.pdf`
- **Title**: *A Short Proof of Two Recently Discovered Independence Results Using Recursion Theoretic Methods*
- **Author**: E. A. Cichoń (Penn State University)
- **Source**: *Proceedings of the American Mathematical Society*, Vol. 87, No. 4, April 1983, pp. 704–706. AMS classification 03F30 (primary), 03F15, 03D20.
- **Citation**: E. A. Cichoń, "A short proof of two recently discovered independence results using recursion theoretic methods," *Proc. Amer. Math. Soc.* **87** (1983), no. 4, 704–706.
- **Note**: A handwritten version appeared in the lecture notes of the AMS Summer Institute on Recursion Theory, Cornell, June–July 1982.

---

## Abstract (plain language)

Kirby and Paris (1982) showed that **Goodstein's Theorem is independent of Peano Arithmetic (PA)**. Cichoń gives a much shorter, self-contained proof using only **recursion-theoretic facts about subrecursive hierarchies of functions** — specifically the **slow-growing hierarchy** `Gₓ` and the **Hardy hierarchy** `Hₐ`. The whole argument fits in about two pages. The trick: Goodstein's process, run from a number `N`, is shown to be **exactly mirrored** by a computation in the slow-growing hierarchy, and the number of steps to termination is shown to equal (essentially) the value of a **Hardy function** `Hₐ`. Because `H_{ε₀}` is already known (Wainer) to be **not provably total in PA**, the termination statement cannot be a theorem of PA. A second, closely related result of Beckman–McAloon falls out by the same method. The proof **never mentions cut-elimination, ordinal analysis of proofs, or Con(PA)**.

---

## The two processes

- **Process 1 (ordinary Goodstein)**: write `N` in base `x` as a sum of powers of `x`; bump the base by 1; subtract 1; repeat (bump base, subtract 1). The exponents are left as ordinary numerals.
- **Process 2 (pure-base / hereditary Goodstein)**: same, except `N` is written in **pure base `x`** — base-`x` *hereditarily*, so exponents (and exponents of exponents, …) are themselves written in base `x`. This is the standard hereditary Goodstein sequence.

A process **terminates** if it eventually reaches 0.

---

## Key results (exact statements)

> **THEOREM 1.** *For any integer `N` and base `x`, Process 1 eventually terminates, but this is not provable in Primitive Recursive Arithmetic.*

> **THEOREM 2.** *For any integer `N` and base `x`, Process 2 eventually terminates, but this is not provable in Peano Arithmetic.*

Theorem 2 is the Goodstein independence result (Kirby–Paris). Theorem 1 is the analogous statement for the non-hereditary process against the weaker theory PRA (this is the Beckman–McAloon flavored result).

### The machinery (definitions)

- **CNF(ε₀)**: Cantor normal form for ordinals `< ε₀` (where `ε₀ = ω^{ε₀}`).
- **Fundamental sequences** `{α}(x)` for limit ordinals: `{ω^{α+1}}(x)` and `{ω^α}(x)` defined as in Wainer. *The specific choice matters* — Cichoń remarks (Def. 2) that with a different choice **Lemma 1 would fail**.
- **Slow-growing hierarchy** `Gₓ` (Def. 3): `Gₓ(0)=0`; `Gₓ(α+1)=Gₓ(α)+1`; at limits `Gₓ(α)=Gₓ({α}(x))`.
- **`Pₓ`** (Def. 4): a "predecessor / subtract-1 on an ordinal" function. `Pₓ(0)=0`; `Pₓ(α+1)=α`; at limits `Pₓ(α)=Pₓ({α}(x))`. (`Pₓ` is what implements the "subtract 1" half of the Goodstein step at the ordinal level.)
- **Hardy hierarchy** `Hₐ` (introduced near the end): `H₀(x)=x`; `H_{α+1}(x)=Hₐ(x+1)`; at limits `Hₐ(x)=H_{{α}(x)}(x)`. (Fast-growing; `H_{ε₀}` is Ackermann-ish-and-beyond.)

### Core lemmas (what bounds/equates what)

> **LEMMA 1.** `Gₓ(α+β) = Gₓ(α)+Gₓ(β)` and `Gₓ(ω^α) = x^{Gₓ(α)}`.

(Proof: induction on `β` and on `α`.) **Remark 1** notes the consequence: `Gₓ(α)` is just "take the CNF of `α` and replace every `ω` by `x`." **Remark 2**: if you write `N` in pure base `x` and replace each `x` by `ω`, you get an ordinal `α ∈ CNF(ε₀)` with `N = Gₓ(α)`. So **a Goodstein number IS a slow-growing value of its associated ordinal.**

> **LEMMA 2.** `Gₓ Pₓ(α) = Pₓ Gₓ(α)  (= Gₓ(α) − 1)`.

(Proof: induction on `α`.) This is the crux algebraic identity: **"subtract 1 from the number" and "subtract 1 from the ordinal" commute through `Gₓ`** — applying `Pₓ` to the ordinal and then reading it off via `Gₓ` gives exactly the integer one less.

### The reduction (the heart of the proof)

Process 2 step-by-step becomes, in ordinal terms (writing `N = Gₓ(α)`):

- Change base `x → x+1`: `Gₓ(α) → G_{x+1}(α)`.
- Subtract 1 (Lemma 2): `G_{x+1}(α) → G_{x+1}(P_{x+1}(α)) = P_{x+1}G_{x+1}(α)`.
- Next step: base `→ x+2`, subtract 1: `→ P_{x+2}G_{x+2}P_{x+1}(α)`, etc.

So after the whole run, the iterated composition of `P`'s applied to the ordinal `α` is what drives termination. Since (by an easy induction) `Gₓ(α)=0 ⟺ α=0`, Theorem 2 is **equivalent** to the purely ordinal/number-theoretic statement:

> *"For all `α ∈ CNF(ε₀)` and all `x ≠ 0`, there exists `y > x` such that `Pᵧ P_{y−1} ⋯ P_{x+2} P_{x+1}(α) = 0`"* — true, but not provable in PA.

Finally, the number of steps is pinned to a **Hardy function value**:

> **THEOREM 2 now follows from**: if `α ∈ CNF(ε₀)` with `α ≠ 0` and `x ≠ 0`, then by induction on `α`,
> `μy[ Pᵧ P_{y−1} ⋯ P_{x+2} P_{x+1}(α) = 0 ] = Hₐ(x+1) − 1`.

That is, **the least number of base-increments needed for the Goodstein sequence (from ordinal `α`, base `x`) to hit 0 is `Hₐ(x+1) − 1`** — a Hardy function. By **Wainer's classification** (refs [3],[4]), `H_{ε₀}` is **not provably recursive in PA** (and `H_{ω^ω}` is a version of the Ackermann function, hence not provably recursive in PRA). Since the termination/step-count function reaches the `Hₐ` for arbitrary `α < ε₀`, PA cannot prove the totality of this step-count function, so PA cannot prove Process 2 always terminates. ∎

**Theorem 1 is identical**, except one observes that when `N` is written in *traditional* (non-hereditary) base `x` and `x` is replaced by `ω`, the resulting ordinal is **`< ω^ω`** (not all of `ε₀`); hence the relevant Hardy function is `H_{<ω^ω}`, which is exactly the Ackermann-level function not provably recursive in **PRA**.

---

## Route relevance to crux-2 (KEY)

The expedition's current route is:
`PA ⊢ Goodstein  →  PA ⊢ PRWO(ε₀)  →  (Gentzen internalized cut-elimination = "crux-2")  →  PA ⊢ Con(PA)  →  contradiction with Gödel II.`

Cichoń's proof is a **completely different skeleton**. Answering the four questions precisely:

### (a) Exact logical skeleton of Cichoń's proof

It is a **provable-totality / growth-rate** argument, run *forward* and entirely arithmetically:

1. **Encode** each Goodstein number `N` (in pure base `x`) as an ordinal `α < ε₀` via `ω ↦ x`, so that `N = Gₓ(α)` (slow-growing hierarchy; Remarks 1–2).
2. **Simulate** the Goodstein step (bump base, subtract 1) by `Gₓ` + `Pₓ`, using the two algebraic identities Lemma 1 (`Gₓ` is a hom on `+` and sends `ω^α ↦ x^{Gₓ(α)}`) and Lemma 2 (`Gₓ` and `Pₓ` commute = subtract-1).
3. **Count steps**: prove by induction on `α` that the number of steps to reach 0 equals `Hₐ(x+1) − 1`, a **Hardy (fast-growing) function** value.
4. **Independence by growth rate**: cite **Wainer's theorem** that `H_{ε₀}` is not provably recursive in PA. A theory that proved Goodstein-termination for all inputs would prove the totality of a function dominating all PA-provably-recursive functions — impossible. So PA ⊬ Goodstein. (PRA-version: ordinals stay `< ω^ω`, Hardy function is Ackermann-level, not provably recursive in PRA.)

The independence is delivered by **the speed of the termination/step-count function**, not by any consistency statement.

### (b) Does it go through Con(PA) / cut-elimination at all?

**No — neither, at all.** The words "consistency," "Con(PA)," "Gödel," "cut-elimination," "proof-theoretic ordinal," and "Gentzen" **do not appear**. The proof never internalizes a derivation, never performs ordinal-indexed cut-reduction, and never derives `Con(PA)` inside PA. The only "deep" external input is a **recursion-theoretic classification result** (Wainer) about which functions are provably recursive in PA — a fact about the **growth rate of provably-total functions**, proved once, off-stage, and merely cited. So Cichoń's route **does not touch crux-2's wall**.

### (c) Machinery a Lean formalization would need

To formalize Cichoń's route you would need, roughly:

- **Ordinals `< ε₀` in Cantor normal form** as a concrete datatype with `+` and `ω^(·)` — a hereditary-base / ordinal-notation type. (Mathlib has `Ordinal`, `Ordinal.CNF`, and `ε₀`-relevant material, plus there are standalone `ε₀`/`ONote`/`NONote` notation developments; a usable computable CNF-notation type is the foundation.)
- **Fundamental sequences** `{α}(x)` with *exactly* Cichoń's choice (Def. 2) — and the discipline that Lemma 1 depends on this choice.
- **Slow-growing hierarchy `Gₓ`** (Def. 3) and **`Pₓ`** (Def. 4) as recursive functions on the notation type, with well-founded recursion on ordinals/notations.
- **Hardy hierarchy `Hₐ`** (`H₀(x)=x`, `H_{α+1}(x)=Hₐ(x+1)`, limit via fundamental sequence).
- **The two algebraic lemmas**: Lemma 1 (`Gₓ` additive + `Gₓ(ω^α)=x^{Gₓ(α)}`) and Lemma 2 (`Gₓ Pₓ = Pₓ Gₓ = (·) − 1`), each by transfinite/structural induction.
- **The simulation correctness**: that the Goodstein step on `N` equals the `Gₓ`/`Pₓ` step on `α` (Remarks 1–2 made rigorous).
- **The step-count identity** `μy[ Pᵧ ⋯ P_{x+1}(α) = 0 ] = Hₐ(x+1) − 1` by induction on `α`.
- **The independence input** — and this is the heavy, irreducible piece: **Wainer's classification**, i.e. "PA proves the totality of `f` iff `f` is dominated by some `Hₐ` with `α < ε₀`" (equivalently the Hardy/fast-growing hierarchy classifies the PA-provably-recursive functions). This requires **majorization / domination lemmas** for the Hardy hierarchy and a characterization of PA's provably-total functions. **Mathlib does not have this**; it is a substantial subrecursive-hierarchy + proof-theory development in its own right.

So the formalization splits into (i) a **clean, finite, computational core** (ordinal notations, `G`, `P`, `H`, the three induction lemmas, the simulation) and (ii) a **single deep cited theorem** (Wainer's provable-recursiveness classification).

### (d) Is this genuinely SIMPLER to formalize than internalized cut-elimination?

**Mostly yes — but the difficulty is relocated, not eliminated.** The *core* of Cichoń's argument (steps 1–3 above) is dramatically simpler than Gentzen-style internalized cut-elimination: it is a few well-founded recursions and three inductive identities over an ordinal-notation type, with no need to reflect PA derivations inside PA, no proof-term induction, no ε₀-indexed reduction of sequent proofs. That whole apparatus — the genuine "crux-2 wall" — **disappears**.

What it is replaced by is **Wainer's theorem** (the Hardy/fast-growing classification of PA's provably-recursive functions). That is the hard residue. The honest comparison:

- **Cut-elimination route**: one big, deeply self-referential meta-mathematical construction (internalize a proof system, prove cut-elimination terminates with ε₀-induction, derive Con(PA)). Hard to formalize end-to-end; this is the wall.
- **Cichoń route**: an *easy* concrete core + *one* hard imported classification theorem (Wainer) about growth rates of provably-recursive functions. The independence is then a domination/non-provable-totality argument rather than a consistency argument.

Whether Cichoń is *strictly* easier in Lean depends on how cheaply Wainer's classification can be obtained or assumed. If that classification is taken as a (well-justified, citable) axiom or a separate sub-project, the rest of Cichoń's proof is **far lighter** than internalized cut-elimination. If you insist on formalizing Wainer from scratch, you have merely **traded one deep proof-theory development for another** — but one that is arguably more modular and reusable (subrecursive hierarchies, majorization), and one that the literature treats as the "short" path.

### Key passages (quoted)

- The slow-growing encoding: *"if `N` is written in pure base `x` and `x` is then replaced throughout by `ω` we obtain an ordinal `α ∈ CNF(ε₀)` and we have `N = Gₓ(α)`."* (Remark 2)
- The reduction to ordinals: *"Theorem 2 is equivalent to: 'For all `α` in `CNF(ε₀)` and for all `x ≠ 0`, there exists `y > x` such that `Pᵧ P_{y−1} ⋯ P_{x+2} P_{x+1}(α) = 0` is true but not provable in Peano Arithmetic.'"*
- The Hardy step-count identity: *"Theorem 2 now follows from: If `α ∈ CNF(ε₀)` with `α ≠ 0` and `x ≠ 0`, by induction on `α` we have `μy[ Pᵧ P_{y−1} ⋯ P_{x+2} P_{x+1}(α) = 0 ] = Hₐ(x+1) − 1`."*
- The independence input (the only cited deep fact): *"By the work of Wainer in [3,4], `H_{ε₀}` is not provably recursive in Peano Arithmetic and `H_{ω^ω}` is precisely a version of the Ackermann function and so is not provably recursive in Primitive Recursive Arithmetic."*
- PRA vs PA distinction: *"The proof of Theorem 1 is identical. We only need to observe that when `N` is written in traditional base `x` and then `x` is replaced throughout by `ω`, the ordinal thus obtained is smaller than `ω^ω`."*

---

## Verdict

**Cichoń's route entirely sidesteps crux-2.** It never internalizes cut-elimination, never proves `Con(PA)` inside PA, and never invokes Gödel II — independence is obtained instead by showing the Goodstein step-count equals a **Hardy function `Hₐ(x+1) − 1`** and citing **Wainer's theorem** that `H_{ε₀}` outgrows every PA-provably-recursive function. The replacement machinery is moderate-and-modular: an ordinal-notation type below ε₀, the slow-growing (`Gₓ`/`Pₓ`) and Hardy (`Hₐ`) hierarchies, three short inductive lemmas, and a clean simulation — **all genuinely lighter than internalized cut-elimination** — except for the **one heavy imported fact**, Wainer's classification of PA's provably-total functions via the fast-growing hierarchy (majorization/domination lemmas), which mathlib lacks and which becomes the new (more tractable, reusable) hard residue. Net: a real shortcut for the formalization if Wainer's classification can be assumed/axiomatized or staged as its own sub-project; if formalized from scratch it trades one deep proof-theory development for a better-factored one.
