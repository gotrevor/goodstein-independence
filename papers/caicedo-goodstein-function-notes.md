# Goodstein's Function (Caicedo)

## Provenance

- **File**: `caicedo-goodstein-function-notes.pdf`
- **Author**: Andrés Eduardo Caicedo (California Institute of Technology, Dept. of Mathematics)
- **Title**: *Goodstein's function*
- **Date**: September 26, 2007
- **MSC**: 03F30 (03D20)
- **Keywords**: Goodstein function, Hardy hierarchy, fast growing hierarchy, Peano Arithmetic
- **Source**: Expository notes; later published (Caicedo, "Goodstein's function," *Revista Colombiana de Matemáticas* 41 (2007), special issue). Caltech homepage `http://www.its.caltech.edu/~caicedo/`.

## Abstract (plain language)

Goodstein's function `𝒢 : ℕ → ℕ` returns the number of steps a Goodstein sequence
takes to reach zero. Goodstein (1944) proved every such sequence terminates, so `𝒢`
is total. Kirby–Paris (1982) showed via model theory (indicators) that this totality
statement, though purely arithmetic and finitary in appearance, is **not provable in
first-order Peano Arithmetic (PA)**. Caicedo's contribution is to give an **explicit
formula** for `𝒢(n)` in terms of the Löb–Wainer fast-growing hierarchy `(f_α)_{α<ε₀}`.
From that formula plus standard proof-theoretic facts about the hierarchy, the
Kirby–Paris unprovability result drops out **immediately as a corollary** — no model
theory, no internalized cut-elimination required. He also computes the Hardy hierarchy
in terms of the Löb–Wainer functions, recovering Cichoń's analogous theorem.

## Key results / content

### The objects

- **Complete (super) base-b representation** (Defs 1.1–1.2): write `n` in base `b`,
  then recursively rewrite every exponent in base `b`, until stable. E.g.
  `266 = 2^(2^2+1) + 2^(2+1) + 2`.
- **Change-of-base** `R_b` (Def 1.3): in the complete base-`b` representation, replace
  every `b` by `b+1`. Goodstein sequence (Def 1.4): `(n)_1 = n`, and
  `(n)_{k+1} = R_{k+1}((n)_k) − 1` (or 0 if already 0).
- **Goodstein function** (Def 1.5): `𝒢(n)` = least `k` with `(n)_k = 0`.
- **Theorem 1.6 (Goodstein)**: `𝒢` is well defined (total) — `𝒢(n)` exists for all `n`.

### Growth rate (the headline numbers)

```
𝒢(0)=1,  𝒢(1)=2,  𝒢(2)=4,  𝒢(3)=6,
𝒢(4) = 3·2^402653211 − 2 ≈ 6.895 × 10^121210694
```

> "the values of `𝒢` grow incredibly fast, so fast that `𝒢` in fact eventually
> dominates any recursive function that PA can prove is defined for all inputs. This
> was originally proved by Kirby and Paris."

### The fast-growing (Löb–Wainer) hierarchy `f_α`

For limit `α < ε₀`, a canonical fundamental sequence `d(α,n)` cofinal in `α` is fixed
(Def: `d(ω^β·γ + ..., n) = ω^β·γ + ω^δ·n` if `β = δ+1`; `+ ω^{d(β,n)}` if `β` limit).
Then (Def 1.7):

```
f_0(n) = n+1
f_{α+1}(n) = f_α^n(n)        (n-fold iterate)
f_α(n) = f_{d(α,n)}(n)       (α limit)
```

with `f_1(n)=2n`, `f_2(n)=n·2^n`, `f_ω` ≈ diagonal of Ackermann.

- **Fact 1.8**: each `f_α` is strictly increasing; `α<β ⟹ f_α` eventually dominated by
  `f_β`; **each `f_α` is recursive and provably total in PA**.
- **Theorem 1.9 (Wainer)**: if `f` is recursive and provably total in `IΣ_{k+1}`, then
  `f` is eventually dominated by some `f_α`, `α < ζ_{k+1}`. **In particular, any
  recursive `f` provably total in PA is eventually dominated by some `f_α` with
  `α < ε₀`.** ← *This is the proof-theoretic engine.*

### The explicit formula — Theorem 1.11 (the paper's main result)

Write `n = 2^{m_1} + ... + 2^{m_k}` (`m_1 > ... > m_k`), let `α_i = R_2^ω(m_i)` (the
ordinal `< ε₀` obtained by reading the complete base-2 rep of `m_i` with 2 replaced by
`ω`, in Cantor normal form). Then

```
𝒢(n) = f_{α_1}(f_{α_2}( ... (f_{α_k}(3)) ... )) − 2.
```

(Part 2 generalizes to any starting base `b`.) Examples given:
`𝒢(266) = f_{ω^ω+1}(f_{ω+1}(6)) − 2` and
`𝒢(4) = f_ω(3) − 2 = f_3(3) − 2 = 3·2^3·2^{3·2^3}·2^{3·2^3·2^3·2^3} − 2`.

- **Theorem 1.6 (totality) follows at once from Theorem 1.11**, since each `f_α` is
  total.

### The Hardy hierarchy and Cichoń

- **Hardy hierarchy** (Def 1.13): `H_0(n)=n`, `H_{α+1}(n)=H_α(n+1)`,
  `H_α(n)=H_{d(α,n+1)}(n)` for `α` limit.
- **Theorem 1.14** computes `H_α` via the `f_β`; in particular the key identity
  **`H_{ω^α}(n) = f_α(n+1) − 1`** (eq. 1), i.e. `H_{ω^α} = F_α` for the
  Ketonen–Solovay/Fairtlough–Wainer variant `F_α(n) = f_α(n+1)−1`.
- **Corollary 1.15**: `α ≥ β ⟹ H_α ∘ H_β = H_{α+β}`.
- **Corollary 1.16 (Cichoń)**: `g(n) = H_{R_2^ω(n)}(1)` for the "subtract-then-increase-base"
  variant `g` of Goodstein's function. Cichoń's theorem is an immediate consequence of
  Theorems 1.11 and 1.14.

### Proof structure (Section 2)

The proof of Theorem 1.11 is reduced to **Lemma 2.1**: `B_a(a^m − 1) = f_{R_a^ω(m)}(a) − 1`
(where `B_a(n)` is the first base at which the process started at the complete base-`a`
rep of `n` reaches 0). The core is **Lemma 2.5** /  **Lemma 2.8**, proved by
**transfinite induction of length ε₀** on the ordinal `α`, using a relation `α →_n β`
(à la Ketonen–Solovay) tracking walks down fundamental sequences. Caicedo notes the
argument "organizes itself in a natural way as a transfinite induction of length ε₀."

## Route relevance to crux-2 (KEY)

The expedition currently proves "PA ⊬ Goodstein" via **Gentzen-style internalized
cut-elimination ("crux-2", the hard wall)**. Caicedo's paper is squarely the
**growth-rate / Hardy-hierarchy alternative**, and the answers are:

### (a) Does Caicedo connect Goodstein termination to a growth-rate unprovability argument that AVOIDS cut-elimination?

**Yes — emphatically, and that is the whole point of the paper.** The unprovability is
obtained as a one-line corollary of the explicit-formula computation plus Wainer's
domination theorem (Theorem 1.9). There is **no cut-elimination, no internalized
consistency proof, no Gentzen ordinal analysis carried out in the paper**:

> "the Kirby-Paris result is an immediate corollary of our computation and standard
> proof theoretic results about this hierarchy."

> "Theorem 1.11 also gives immediately as corollaries the unprovability results of
> Kirby and Paris, see Section 3."

The "standard proof theoretic result" being leaned on is **Theorem 1.9 (Wainer)** — the
characterization of the PA-provably-total recursive functions as exactly those
eventually dominated by some `f_α`, `α < ε₀`. The hard proof-theoretic work
(the `ε₀` analysis of PA) is **black-boxed as a cited theorem**, not redone.

### (b) The exact chain (Goodstein length ↔ which fast-growing function ↔ why PA can't prove it total)

1. **Goodstein length ↔ fast-growing function.** Theorem 1.11:
   `𝒢(n) = f_{α_1}(f_{α_2}(...f_{α_k}(3)...)) − 2`. Critically, as `n → ∞` the leading
   ordinal `α_1 = R_2^ω(m_1)` ranges **cofinally up to ε₀** (read off the top exponent
   of `n`). So `𝒢` **eventually dominates `f_α` for every fixed `α < ε₀`** — i.e. `𝒢`
   has growth rate at the level of `f_{ε₀}` (equivalently the Hardy function `H_{ε₀}`,
   via `H_{ω^α} = F_α`, Cor 1.16's `g = H_{R_2^ω(n)}(1)`).
2. **Which fast-growing function.** The `ε₀`-level diagonal function. Concretely `𝒢`
   (and the variant `g`) sits at `f_{ε₀} ≍ H_{ε₀}` — strictly above every `f_α` with
   `α < ε₀`.
3. **Why PA can't prove it total.** Wainer (Theorem 1.9): every recursive function
   **provably total in PA** is eventually dominated by some `f_α` with `α < ε₀`. But
   `𝒢` dominates *all* such `f_α` (step 1). Therefore `𝒢` is **not** provably total in
   PA — i.e. PA ⊬ "`𝒢` is total" = PA ⊬ Goodstein's theorem. ∎

This is the classic "Goodstein outgrows the PA-provable bound at `ε₀`" argument,
made fully explicit by the `f_α` formula.

### (c) Would this be a cleaner route to formalize?

**Likely cleaner in principle, but it relocates the hard wall rather than removing it.**
What it buys you: the *combinatorics* of Goodstein → ordinals → `f_α` (Theorem 1.11,
Section 2) is elementary, concrete, transfinite-induction-of-length-ε₀ bookkeeping —
the kind of thing that formalizes well. The unprovability then reduces to **one cited
black box: Wainer's Theorem 1.9** (the `f_α`-characterization of PA-provably-total
functions, i.e. the `ε₀` proof-theoretic strength of PA).

The catch for the expedition: **Theorem 1.9 *is* the cut-elimination / ε₀ ordinal
analysis of PA in disguise.** Proving Wainer's theorem from scratch in Lean would
itself require (or be equivalent to) the Gentzen-style content of crux-2. So the
growth-rate route is cleaner **only if** you are willing to *assume* Theorem 1.9 (or an
equivalent statement of PA's proof-theoretic strength / `ε₀` unprovability of
`f_{ε₀}`-totality) as an axiom or imported lemma. If the expedition's goal is a
**fully self-contained, axiom-clean** "PA ⊬ Goodstein," this route does **not** avoid
the wall — it just isolates the wall into a single named theorem (Wainer 1.9) instead of
spreading it through an internalized cut-elimination. That isolation is itself valuable:
it gives a clean `Statement.lean`-style audit surface where the one deep dependency is
explicit, and the rest is elementary ordinal arithmetic. But "growth-rate route =
no crux-2" is **false**; "growth-rate route = crux-2 packaged as one citable theorem" is
**true**.

## Key passages (quoted)

> "In this paper we present a computation of Goodstein's function in terms of a classical
> 'fast growing' hierarchy of functions due to Löb and Wainer... the Kirby-Paris result
> is an immediate corollary of our computation and standard proof theoretic results about
> this hierarchy."

> "Theorem 1.9 (Wainer). If `f` is a recursive function, provably total in `IΣ_{k+1}`,
> then `f` is eventually dominated by some `f_α`, `α < ζ_{k+1}`. In particular, any
> recursive `f` provably total in PA is eventually dominated by some `f_α`, `α < ε₀`."

> "the values of `𝒢` grow incredibly fast, so fast that `𝒢` in fact eventually dominates
> any recursive function that PA can prove is defined for all inputs."

> "Goodstein's Theorem 1.6 follows at once from Theorem 1.11. ... Theorem 1.11 also gives
> immediately as corollaries the unprovability results of Kirby and Paris."

> "it is perhaps interesting to note that the argument organizes itself in a natural way
> as a transfinite induction of length `ε₀`."
