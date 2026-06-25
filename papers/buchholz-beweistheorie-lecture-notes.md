# Buchholz, *Beweistheorie* (Proof Theory) — Lecture Notes

## Provenance

- **File**: `buchholz-beweistheorie-lecture-notes.pdf` (this directory)
- **Author**: Wilfried Buchholz (Mathematisches Institut der Universität München)
- **Title**: *Beweistheorie* ("Proof Theory")
- **Form**: *Skriptum* of a 4-hour lecture course, **Wintersemester 2002/03** (German lecture notes). 67 pages.
- **Language**: English body text with German section headings/conventions (e.g. "Beweis" for "Proof").
- **Cited literature** (front matter): Gentzen (1936/1938/1943), Girard, Pohlers, Schütte, Takeuti, Troelstra–Schwichtenberg, Tait *Normal Derivability in Classical Logic* (LNM 72, 1986), Schwichtenberg, Wainer–Wallen, Buss (ed.) *Handbook of Proof Theory*.
- **Secondary source for crux-2**: this is the *longer* Buchholz treatment of the same system-Z (first-order arithmetic) cut-elimination that the expedition is internalizing; the primary source is the short Buchholz paper.

## Abstract

A complete, self-contained development of classical first-order proof theory in the **Tait sequent-calculus** style, building from finite cut-elimination up to the ordinal analysis of Peano/first-order arithmetic (here called **Z**) via an **infinitary system Z^∞** (ω-rule) and its **finite recursive notations Z\***. The notes deliver, in order: (§1) the Tait calculus PL1 with finite cut-elimination (`PL1 ⊢^k_{m+1} Γ ⟹ PL1 ⊢^{2^k}_m Γ`) and a semantic completeness/cut-elimination proof; (§2) an application of *partial* cut-elimination characterizing the provably recursive functions of **PRA** and **IΣ₁** as exactly the primitive recursive functions, with IΣ₁ shown Π⁰₂-conservative over PRA; (§3) a rigorous de-Bruijn-index theory of variable binding and substitution that makes α-equivalence *literal identity*; (§4) an **inference-symbol** ("derivation-as-term") presentation of the Tait calculus, where a node carries an *inference symbol* I and the sequent is recomputed by tree recursion — the technical vehicle for everything afterward; (§5) the proof-theoretic analysis of Z via the infinitary Z^∞, establishing `‖≺‖ < ε₀` for any ≺ with `Z ⊢ TI_≺(X)`, with the Beckmann-sharpened fragment bounds `Z_m ⊢ TI_≺(X) ⟹ ‖≺‖ < ω_{m+1}`, plus the arithmetization of ordinals `< ε₀` as a primitive-recursive `(OT, ≺)`; and (§6) **recursive notations Z\*** for Z^∞-derivations, culminating in `PRA + QF-TI(ε₀) ⊢ Con(Z)` (Gentzen consistency) and an explicit primitive-recursive characterization of Z's provably recursive functions via a `red(h)` reduction function. The arc is Gentzen's program executed in the modern operator-controlled / notation style, with every infinitary object eventually pinned to a finite, primitive-recursively manipulable code.

## Key content

### §1 — Tait calculus PL1; finite cut-elimination
- **Language & calculus**: classical 1st-order predicate logic, negation pushed to literals (`neg(A)`), formulas built from literals by `∧, ∨, ∀, ∃`. Sequents Γ = finite *sets* of formulas read disjunctively. Rules `(∧),(∨),(∀),(∃),(Cut)` + `(LogAx) Γ,A,¬A`.
- **Measures**: `rk(A)` = logical complexity (`rk(literal)=0`, `rk(A∘B)=max+1`, `rk(QxA)=rk+1`). `crk(d)` = cut-rank, `hgt(d)` = height. Notation `d ⊢^k_m Γ` (height ≤ k, cut-rank ≤ m).
- **Structural lemmas**: 1.1 Substitution, 1.2 Weakening, 1.3 Inversion.
- **Cut-elimination** (the finitary engine):
  - **Lemma 1.4** (the reduction step): `⊢^k_m Γ,C  &  ⊢^l_m Γ,¬C  &  rk(C) ≤ m  ⟹  ⊢^{k+l}_m Γ`.
  - **Theorem 1.5** (Cut-Elimination): `PL1 ⊢^k_{m+1} Γ ⟹ PL1 ⊢^{2^k}_m Γ` — one rank-level removed at exponential height cost.
  - **Subformula property** for cut-free derivations.
- **Partial cut-elimination** (§1, "Partial Cut Elimination"): given an extra family of rules 𝔖⁺ closed under substitution with principal-formula set Φ, define `rk_Φ` (`rk_Φ(A) = -1` for `A ∈ Φ̄`) and `⊢_{Φ,m}`. **Theorem 1.8**: `𝔖 ⊢_{Φ,m+1} Γ & m ≥ 0 ⟹ 𝔖 ⊢_{Φ,m} Γ` — pushes all cuts down to Φ-rank −1 (cut formulas confined to the extra rules' principal formulas). **This is the lever for §2.**
- **Completeness / semantic cut-elimination** (Theorem 1.10): `⊨ Γ ⟹ PL1 ⊢_0 Γ`, via a König's-Lemma search tree Π_ν over 0-1 sequences.

### §2 — Provably recursive functions of PRA and IΣ₁
- **PRA** (Tait-style) = PL1 + equality/Successor/PR-defining axioms (G1)–(PR3.1) + **QF-induction rule**. **IΣ₁** = PRA with QF-induction replaced by the **Σ₁-induction rule**. Both have rules closed under substitution, so 1.6–1.9 (partial cut-elim with Φ = QF resp. Σ₁) apply.
- Develops `+, ·, ∸, prd`, pairing `π/π₁/π₂` (Lemma 2.6), the **bounded μ-operator** `μ̄_{z≤y}A` (Lemma 2.7), and Δ₀/Σ-formula normal forms.
- **Theorem 2.9 / Corollary 2.9**: the provably recursive functions of **PRA are exactly the primitive recursive functions** (proof by induction on a partially-cut-eliminated derivation).
- **Theorem 2.10 / Corollary 2.10**: **IΣ₁ is Π⁰₂-conservative over PRA**; in particular same provably recursive functions.

### §3 — General framework for variable binding and substitution
- Replaces named bound variables by **de Bruijn indices** `{∘_k : k ∈ ℕ}` and *binders* `♭`. Quasiterms 𝒯′, terms 𝒯, the index-shift `t_x[n]`, `♭x.r := ♭r_x[0]`.
- **Lemma 3.1–3.5** establish a clean substitution algebra; crucially **α-equivalence becomes identity** ("substitution can be carried out without renaming"). The binding operator β with `β(♭x.r, s) := r_x(s)`.
- 1st-order syntax is recovered as a special case (`QxA` is shorthand for the binder term). Truth-value `[C]^M_ξ` defined with a fixed witness map `v` (Lemmas 3.7–3.11). **This is the substitution infrastructure that lets §4–§6 treat derivations as honest finite terms.**

### §4 — Inference-symbol ("derivation-as-term") presentation of Tait calculus
- A **proof system 𝔖** = a set of *inference symbols* I, each with arity `|I|`, principal sequent Δ(I), minor sequents (Δ_ι(I))_{ι∈|I|}, and an eigenvariable set Eig(I) (∅ or singleton).
- A derivation `d = I(d_ι)_{ι∈|I|}` is now a **tree of inference symbols**; the endsequent `Γ(d)` is *recomputed by tree recursion*, not stored. Measures `crk(d), hgt(d)` defined on the term. Abbreviation `𝔖 ⊢^α_m Γ`.
- **Finitary PL1** restated as inference symbols `Ax_{A,¬A}, ⋀_{A₀∧A₁}, ⋁^k_{A₀∨A₁}, ⋀^x_{∀xA}, ⋁^t_{∃xA}, Cut_C`.
- **System Z** (1st-order arithmetic) introduced as PL1 + arithmetic axioms (as principal parts Δ ∈ 𝒜𝒳(Z)) + the **induction inference symbol** `Ind^{x,t}_F : (¬F, F_x(Sx)) / (¬F_x(0), F_x(t))`.
- Substitution `dθ`, free variables `FV(d)`, **closed** derivations developed at term level (Lemmas 4.1–4.3). The point: derivations are now objects you can do primitive recursion on. *(This is the modern presentation that the short Buchholz paper compresses.)*

### §5 — Proof-theoretic analysis of Z via the infinitary Z^∞
- **Transfinite induction** machinery: for a wellfounded arithmetic ≺ defined by an ℒ₀-formula R, the **≺-norm** `|n|_≺` and `‖≺‖ := sup{|n|_≺+1}`. `Prog_≺(ℱ)`, `TI_≺(ℱ)`, `TI_≺(X)`.
- **Goal**: ε₀ is the least α with `TI` up to α not provable in Z. The two halves: **(I)** `Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀`; **(II)** for each `α < ε₀` a PR wellordering `≺_α` of ordertype α with `Z ⊢ TI_{≺_α}(X)`.
- **The infinitary system Z^∞**: replace each `⋀^x_{∀xA}` by the **ω-rule**
  `(⋀_{∀xA})  …A_x(t)…(t∈T₀) / ∀xA`,
  and add as axioms the true closed literals (TRUE₀) and `Xs, ¬Xt` for `s^N = t^N`. Sequents are *sets of closed sentences*; ∧/∨/∀/∃ identified with infinitary `⋀/⋁` over T₀. Derivations carry an **ordinal height** α and cut-rank m: `d ⊢^α_m Γ`. A `Rep` (repetition) inference is included (matters later).
- **The cut-elimination operators** (the heart):
  - **Theorem & Definition 5.1** — the **reduction operator** ℛ_C: `d ⊢^α_m Γ,C & e ⊢^β_m Γ,¬C & rk(C) ≤ m ⟹ ℛ_C(d,e) ⊢^{α#β}_m Γ`. Defined by recursion on the natural (Hessenberg) sum `α#β`; eliminates one top cut on C, gluing the two derivations.
  - **Theorem & Definition 5.2** — the **cut-rank-lowering operator** ℰ: `d ⊢^α_{m+1} Γ ⟹ ℰ(d) ⊢^{3^α}_m Γ`. Built from ℛ_C; lowers cut-rank by one at cost `α ↦ 3^α`. Iterating ℰ^m collapses to cut-free.
  - **Theorem 5.3** (Inversion), **Theorem 5.4 / 5.8** (**Boundedness**): for X-positive Γ, `Z^∞ ⊢^β_1 ¬Prog_≺(X), ¬Xs₁,…,¬Xs_k, Γ & |s_i|_≺ ≤ α ⟹ ⊨^{α+2^β} Γ`; **Corollary** `Z^∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`.
- **Embedding** (Theorem 5.5 / Corollary): each closed Z-derivation d has an interpretation `d^∞ ∈ Z^∞` with `Z^∞ ∋ d^∞ ⊢^{ō(d)}_{dg(d)} Γ(d)`; hence `Z ⊢ Γ (closed) ⟹ Z^∞ ⊢^{ω·k}_m Γ` for some k, m < ω. The `Ind` rule is unfolded into a stack of cuts (the displayed `Ind^{x,t}_F` interpretation). 
- **Theorem 5.6**: `Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀` (from 5.5 + 5.2 + 5.4). This is the upper-bound half of the ordinal analysis.
- **Fragments / sharpening (Beckmann)**: Z_m = Z with induction restricted to formulas of rk_QF < m. **Theorem 5.9**: `Z_m ⊢ TI_≺(X) ⟹ ‖≺‖ < ω_{m+1}` (with `ω₀=1, ω_{n+1}=ω^{ω_n}`). Sharper Boundedness via `|n|_U` / `U^α`.
- **Arithmetization of ordinals < ε₀**: a PR bijective coding of finite sequences; `(OT, ≺)` a *primitive recursive* set of ordinal notations with `o : OT → ε₀` an order-isomorphism onto (ε₀, <) (Lemma 5.10). Natural-sum-with-`ω^b·k` operations `a ⊕ ω^b·k`. **Lemma 5.11**: `(OT, ≺)` is provably-in-PRA a linear ordering. `Π_n`-IA fragments; **Theorem 5.14**: `Π_{m+1}-IA ⊢ Π₁-TI(α)` for `α < ω_{m+2}` but `⊬ Π₁-TI(ω_{m+2})`.

### §6 — Recursive notations Z\*; consistency and provably-recursive functions of Z
*(This section is the most directly relevant to crux-2 — see below.)*
- **Motivation**: every true ℒ₀-sentence has a Z^∞-derivation of height < ω, so §5's method can't bound *finitary* unprovability or extract provably-recursive functions. Fix: **finite recursive notations** for Z^∞-derivations.
- **System Z\*** = Z + a single new inference symbol **E** (`∅/∅`), with ordinal `o(h)` and degree `deg(h)` defined on the finite term h:
  - `o(Cut_C h₀ h₁) := o(h₀)#o(h₁)`, `o(Ind^{x,t} h₀) := o(h₀)·ω`, `o(E h₀) := 3^{o(h₀)}`, else `sup_{i<n}(o(h_i)+1)`.
  - `deg(E h₀) := deg(h₀) ∸ 1`, else `max`. (Motivated so that E *codes one application of* ℰ.)
- **Interpretation `h ↦ h^ω ∈ Z^∞`** (the bridge): `(Cut_C h₀h₁)^ω := ℛ_C(h₀^ω,h₁^ω)`, `(E h₀)^ω := ℰ(h₀^ω)`, ω-rule and Ind cases unfolded. So **a finite Z\*-term denotes an infinitary derivation, and E denotes cut-elimination**.
- **The `tp(h)` / `h[ι]` machinery — the d↦d[n] reduction made syntactic** (page 35):
  > By recursion on the build-up of h we define a Z^∞-inference `tp(h)` and closed Z\*-derivation(s) `h[ι]` (for `ι ∈ |tp(h)|`) such that
  > `h^ω = tp(h)(h[ι]^ω)_{ι∈|tp(h)|}`.
  - For the **ω-rule** (`tp(h) = ⋀_C`), the index `ι` ranges over T₀ ≅ ℕ, so `h[t] := h₀(x/t)` (clause 1.3) — i.e. **`h[n]` is the n-th immediate subnotation**. For `E` and `Cut` the clauses (3, 4) read off directly from the ℰ/ℛ_C definitions. This `h[ι]` is exactly the "reduction `d ↦ d[n]`" the expedition tracks, expressed on *finite* notations.
- **Theorem 6.2** (the reduction lemma stated on notations, with the **validity invariant** carried syntactically): if `h ⊢^α_m Γ` and `I = tp(h)` then (a) `Δ(I) ⊆ Γ`, (b) `I = Cut_C ⟹ rk(C) < m`, (c) for each `ι ∈ |I|`: **`h[ι] ⊢^{α_ι}_m Γ, Δ_ι(I)` with `α_ι < α`**. This is the local-correctness + strictly-decreasing-ordinal step that an internalization rests on.
- **Lemma 6.3 (Consistency of Z) + Theorem 6.4**: Let `Z\*_⊥` = closed Z\*-derivations with `Γ(h)=∅, deg(h)=0`. Then `h ∈ Z\*_⊥ ⟹ h[0] ∈ Z\*_⊥ & o(h[0]) < o(h)` (a, b) — and by **transfinite induction up to ε₀** there is no Z-derivation of ∅. Hence
  > **Theorem 6.4: `PRA + QF-TI(ε₀) ⊢ Con(Z)`** — the Gentzen consistency proof, executed entirely on the finite Z\* notations. The `Π₁`-induction formula is `F(α) := ∀h(o(h)=α → h ∉ Z\*_⊥)`, derived from QF-TI(ε₀).
- **`deg_QF` refinement (Lemma 6.5)** so cut-elimination of *quantifier* cuts can be tracked separately.
- **Theorem 6.6 (provably recursive functions of Z)** — the fully primitive-recursive `red`: assuming a canonical PR coding `q ↦ ⌜q⌝` of all syntax (terms, formulas, finite derivations, derivation terms), define on a *finite* restricted notation system `Z̃\*` a primitive recursive **reduction function `red : D ∪ {0} → D ∪ {0}`**:
  > `red(h) := h[1]` if `tp(h)=Cut_C` with `C ∈ TRUE_QF`; `h[1]` if `tp(h)=⋀_{A₀∧A₁}` with `A₀ ∈ TRUE_QF`; `0` for axiom/true cases; else `h[0]`.
  Then `h(n,k) := red^{(k)}(E…E d(n))` (m copies of E, `α := 3_m(o(d))`) "goes upwards searching for a true literal." This realizes Z's `∀x∃y A(x,y)` provability by primitive recursive `g, θ` with `α < ω_{m+2}` — i.e. **the provably recursive functions of Π_{m+1}-IA are bounded at `ω_{m+2}`**. The `red`/`h[n]` apparatus is the concrete, internalizable form of d↦d[n].

## Relevance to crux-2

**Yes — this is a more detailed and more *portable*/internalizable treatment of the d↦d[n] reduction and the validity invariant than the short Buchholz paper, in three specific ways:**

1. **The reduction d↦d[n] is made fully syntactic on finite notations (§6).** Where the short paper carries `d[n]` somewhat schematically over infinitary derivations, these notes (a) build the de-Bruijn substitution algebra in §3 so that `h₀(x/t)` is a literal, rename-free operation; (b) present derivations as finite *inference-symbol terms* in §4; and (c) in §6 define `tp(h)` and `h[ι]` by **recursion on the finite term h**, with the governing identity `h^ω = tp(h)(h[ι]^ω)`. For the ω-rule, `h[n] = h₀(x/n)` is exactly d↦d[n]. This is the form that survives coding into IΣ₁/PRA, because every operation is primitive recursive on Gödel numbers.

2. **The validity invariant is isolated as Theorem 6.2 (a)+(b)+(c).** It states precisely what an internalization must verify at each reduction step: the principal sequent stays inside Γ, cut-formulas have rank `< m`, and **each subnotation `h[ι]` has strictly smaller ordinal `α_ι < α`** while still deriving `Γ, Δ_ι`. That decoupling — local correctness + a strictly-descending ε₀-ordinal — is the IΣ₁-formalizable core; the short paper states the analogous fact but these notes give the full case analysis (ω-rule, E, Cut, Ind) you would mirror in Lean/IΣ₁.

3. **Extra steps the short paper elides are shown in full.** The cut-elimination is *operator-controlled*: ℛ_C (5.1, recursion on `α#β`) and ℰ (5.2, `α ↦ 3^α`), and §6 then re-packages ℰ as the single symbol **E** with `o(E h)=3^{o(h)}`, `deg(E h)=deg(h)∸1`. Crucially, the notes prove **`o(hθ)=o(h)` and closure under substitution (Lemma 6.1, 5.1-Corollary)** — the lemmas an IΣ₁ internalization needs but a short presentation usually assumes. They also supply the **primitive-recursive `(OT, ≺)` arithmetization of ε₀** (§5) and the concrete primitive-recursive reduction function **`red`** (Theorem 6.6) — i.e. the *executable* version of d↦d[n] together with the consistency derivation `PRA + QF-TI(ε₀) ⊢ Con(Z)` (Theorem 6.4). For internalizing into IΣ₁, that `red`/OT/`Theorem 6.2` package is materially more usable than the short paper.

**Caveat for matching against the primary source**: these notes never use the literal `d[n]`-with-a-validity-predicate *notation* of the short Buchholz paper; the corresponding object here is `h[ι]` (and `red(h)`) on Z\* notations, with the invariant spread across Theorem 6.2 and Lemma 6.3. The cut-elimination is also in the **operator/notation** idiom (ℛ_C, ℰ, E, `tp`/`[·]`) rather than a single named `d ↦ d[n]` recursion. So it is a richer *secondary* development of the same content, not a notational twin — expect to translate `h[ι] / red` ↔ `d[n]` when aligning the two.

---

## Verdict

This longer Buchholz script gives a **more detailed and more portable** treatment than the short Buchholz paper: §3's de-Bruijn substitution + §4's derivations-as-terms + §6's finite Z\* notations turn the infinitary cut-elimination into primitive-recursive operations (`tp(h)`, `h[ι]`, the operators ℛ_C/ℰ/E, and the explicit reduction function `red`), with the d↦d[n] reduction realized as `h[n] = h₀(x/n)` and the validity invariant pinned down as Theorem 6.2 (principal sequent ⊆ Γ, cut-rank `< m`, strictly-descending ordinal `α_ι < α`). It also supplies the supporting lemmas an IΣ₁ internalization needs but a short paper omits — substitution-invariance of the ordinal, the primitive-recursive ε₀ notation system `(OT, ≺)`, and the Gentzen consistency derivation `PRA + QF-TI(ε₀) ⊢ Con(Z)`. The one cost is notational: it speaks in operators (`h[ι]`, `red`, E) rather than the short paper's literal `d[n]`-with-validity-predicate, so aligning the two requires translating `h[ι] ↔ d[n]`.
