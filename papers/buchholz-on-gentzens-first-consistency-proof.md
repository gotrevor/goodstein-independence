# Buchholz — On Gentzen's first consistency proof for arithmetic

## Provenance

- **File**: `buchholz-on-gentzens-first-consistency-proof.pdf` (19 pp.)
- **Author**: Wilfried Buchholz (Ludwig-Maximilians-Universität München)
- **Title / date**: *On Gentzen's first consistency proof for arithmetic*, February 14, 2014 (unpublished note / preprint).
- **Citation**: W. Buchholz, "On Gentzen's first consistency proof for arithmetic" (2014). Modernizes Gentzen [Ge36] (*Die Widerspruchsfreiheit der reinen Zahlentheorie*, Math. Ann. 112 (1936) 493–565); ordinal assignment follows Kogan-Bernstein [KB81]; related to Buchholz [Bu97].
- **Why it's in this repo**: PRIMARY source for the Goodstein-independence expedition's **crux-2** — the ordinal assignment on coded derivations plus the reduction/cut-elimination step that must be internalized in IΣ₁.

---

## Abstract (plain language)

When people say "Gentzen's consistency proof" today they mean the 1938 sequent-calculus version [Ge38]. Gentzen's *first* (1936) proof [Ge36] is largely forgotten. This note re-presents the 1936 method in a cleaned-up, modern form.

The method works on a **finitary proof system Z** (a natural-deduction-flavored system for first-order arithmetic, with a *chain rule* standing in for cut). For each closed derivation `d`, Buchholz defines, by recursion on the build-up of `d`:

1. a **reduction step** `d ↦ d[n]` (`n` a "choice" numeral, default 0) that transforms `d` into another closed derivation whose endsequent is the *reduced* endsequent — this is Gentzen's reduction procedure, but driven by the derivation rather than by the sequent;
2. an **ordinal** `o(d) < ε₀` assigned to `d`,

and proves the single decisive fact: **`o(d[n]) < o(d)`** whenever `d[n]` is defined (Theorem 4.2). Combined with the fact that a derivation of falsum (`→⊥`) always reduces to another derivation of falsum (Corollary 2.1 / the §3 Corollary), this gives consistency of Z by quantifier-free transfinite induction up to ε₀: an infinite descending reduction chain of ordinals `< ε₀` is impossible, so no derivation of `⊥` can exist.

`§6` re-derives the same reduction and ordinals semantically by embedding Z into an infinitary ω-system `Z^∞` (`d ↦ d^∞`); `§7` lifts everything to multisuccedent sequents; the Appendix shows Buchholz's `o(d)` is, up to base-ω vs base-2 notation, exactly Gentzen's 1936 "Ordnungszahl" assignment (via [KB81]).

---

## Key results

### The system Z (§2, §3)

- Formulas: built from prime/minimal formulas (with truth values "true"/"false"), `¬`, `∀`. Conjunction `&` is deliberately omitted "to keep the focus on the essential things." `⊥` = a fixed false minimal formula.
- Derivable objects are **sequents** `Γ→B` (single succedent; `Γ` a finite list of antecedent formulas).
- Inference rules: ∀-introduction, ¬-introduction, complete induction, and the **chain rule** (the cut surrogate). `§3` re-presents Z so every chain rule inference carries an explicit **rank `r`** (an upper bound on the ranks of all its cut formulas), where `rk(C) = 0` if `C` atomic, `rk(∀xA) = rk(¬A) = rk(A)+1`.
- **Inference symbols** name reduction steps on sequents: `R_∀xF`, `R_¬A` (right rules), `L^k_∀xF`, `L^0_¬A` (left rules), and `Rep` (repetition, "do nothing"). For an inference symbol `I` and sequent `Π`, `I(Π,n)` is the reduced sequent under choice `n`; `|I|` is its arity; `I ◁ Π` means "`I` is permissible for `Π`."

**Inductive Definition of `d ⊢ Π`** (§3, p. 8) — `d` is a Z-derivation with endsequent `Π`:

> 1. Atomic derivations (axioms): cf. §5.
> 2. If `d₀ ⊢ Γ→F(a)` and `a ∉ FV(Γ→∀xF(x))`, then `I^a_∀xF(x) d₀ ⊢ Γ→∀xF(x)`.
> 3. If `d₀ ⊢ A,Γ→⊥`, then `I_¬A d₀ ⊢ Γ→¬A`.
> 4. If `d₀ ⊢ Γ→F(0)` and `d₁ ⊢ F(a),Γ→F(Sa)` and `a ∉ FV(Γ→F(t))`, then `Ind^{a;t}_F d₀ d₁ ⊢ Γ→F(t)`.
> 5. If `dᵢ ⊢ Πᵢ` with `FV(Πᵢ) ⊆ FV(Π)` for `i = 0,…,l`, and if `(Π₀ … Πₗ)/Π` is a chain rule inference of rank `r`, then `K^r_Π d₀ … dₗ ⊢ Π`.

A *chain rule inference of rank `r`*: `(Γ₀→A₀ … Γₗ→Aₗ)/(Γ→C)` such that there is `j ≤ l` with `Aⱼ ∈ {C,⊥}` and `∀i ≤ j (Γᵢ ⊆ Γ, A₀,…,A_{i−1})` and `∀i < j (rk(Aᵢ) ≤ r)`.

### The ordinal assignment (§4, p. 10)

For non-atomic `d`, define `dg(d) < ω` (degree) and `õ(d) < ε₀` (pre-ordinal):

> `dg(d) :=`
> - `dg(d₀)` if `d = I^a_∀xF d₀` or `d = I_¬A d₀`
> - `max{dg(d₀)−1, dg(d₁)−1, r}` if `d = Ind^{a;t}_F d₀ d₁` with `r := rk(F)`
> - `max{dg(d₀)−1, …, dg(dₗ)−1, r}` if `d = K^r_Π d₀ … dₗ`
>
> `õ(d) :=`
> - `õ(d₀) + 1` if `d = I^a_∀xF d₀` or `d = I_¬A d₀`
> - `ω^{õ(d₀)} # ω^{õ(d₁)+1}` if `d = Ind^{a;t}_F d₀ d₁`
> - `ω^{õ(d₀)} # … # ω^{õ(dₗ)}` if `d = K^r_Π d₀ … dₗ`
>
> `o(d) := ω_{dg(d)}(õ(d))`, where `ω₀(α) := α`, `ω_{n+1}(α) := ω^{ω_n(α)}`.

(`#` = natural/Hessenberg sum.) So the ordinal is a tower of height `dg(d)` over the natural-sum pre-ordinal. Atomic-derivation values: `dg = 0`, `o = õ`, with `õ(Ax⁰) = 0`, `õ(Ax¹_{Γ→C}) = 2·rk(C)`, `õ(Ax^{C,t}) = 2·rk(C)−1`, `õ(Ax^{¬¬}) = 2` (§5, p. 13).

### `tp(d)` and the reduction `d ↦ d[n]` (Definition 3.2, p. 9)

For each closed `d`, define an inference symbol `tp(d)` ("type" — the reduction step the endsequent undergoes) and, for `n ∈ |tp(d)|`, a closed derivation `d[n]`. In the main chain-rule case (5.1, `d` *critical*) two auxiliary derivations `d{0}, d{1}` and a formula `A(d)` are also defined. Recursion on build-up. Verbatim:

> 1. `d` atomic: cf. §5.
> 2. `d = I^a_∀xF d₀`: Then `tp(d) := R_∀xF` and `d[n] := d₀(a/n)`.
> 3. `d = I_¬A d₀`: Then `tp(d) := R_¬A` and `d[0] := d₀`.
> 4. `d = Ind^{a;k}_F d₀ d₁` with `d₀ ⊢ Γ→F(0)` and `d₁ ⊢ F(a),Γ→F(Sa)`:
>    Then `tp(d) := Rep` and `d[0] := K^r_{Γ→F(k)} d₀ d₁(a/0) … d₁(a/k−1)`, where `r := rk(F)`.
> 5. `d = K^r_Π d₀ … dₗ` with `Π = Γ→C` and `dᵢ ⊢ Πᵢ = Γᵢ→Aᵢ` (`i ≤ l`):
>    Abbreviation: `K^r_{Π'}(i/d'ᵢ … d'_m) := K^r_{Π'} d₀ … d_{i−1} d'ᵢ … d'_m d_{i+1} … dₗ`.
>    Let `j₀` minimal s.t. `A_{j₀} ∈ {C,⊥}` & `∀i ≤ j₀ (Γᵢ ⊆ Γ, A₀,…,A_{i−1})`.
>    We say `d` is *critical* if `∀i ≤ j₀ (tp(dᵢ) ⋪ Π)`.
>
>    **5.1. `d` critical:**
>    Then due to Lemma 3.1, and since `∀i ≤ l (tp(dᵢ) ◁ Πᵢ)`, there exists a pair `(i,j)` such that `i < j ≤ j₀`, `tp(dᵢ) = R_{Aᵢ}`, `tp(dⱼ) = L^k_{Aᵢ}` (for some `k`) and `0 < rk(Aᵢ)`.
>    We take the **least** such pair and set `tp(d) := Rep` and `d[0] := K^{r−1}_Π d{0} d{1}` where
>    `d{0} := K^r_{Π·A(d)} { (i/dᵢ[k])  if Aᵢ = ∀xF ; (j/dⱼ[0])  if Aᵢ = ¬A }`,
>    `d{1} := K^r_{A(d),Π} { (j/dⱼ[0])  if Aᵢ = ∀xF ; (i/dᵢ[0])  if Aᵢ = ¬A }`,
>    and `A(d) := { F(k)  if Aᵢ = ∀xF ; A  if Aᵢ = ¬A }`.
>
>    **5.2. `d` not critical:** Let `i ≤ j₀` minimal such that `tp(dᵢ) ◁ Π`.
>    **5.2.1. `dᵢ` critical:** Then `tp(d) := Rep` and `d[0] := K^{r'}_Π (i/dᵢ{0}, dᵢ{1})` with `r' := max{rk(A(dᵢ)), r}`.
>    **5.2.2. `dᵢ` not critical:** Then `tp(d) := tp(dᵢ)` and `d[n] := K^r_{tp(d)(Π,n)}(i/dᵢ[n])`.

The earlier §2 form (14.253, "Principal case", pp. 5–6) is the unmodernized version of the same critical-case reduction: it spells out the three new chain-rule inferences with conclusions `Θ→F(k)`, `F(k),Θ→D`, `Θ→D` (for `V = ∀xF`) or `A,Θ→⊥`, `Θ→A`, `Θ→D` (for `V = ¬A`) — i.e. the cut of rank `r` on `Aᵢ` is replaced by cuts on the *immediate subformula* `A(d)` of rank `r−1`, fed by `d{0}` and `d{1}`.

### Lemma 3.1 — the critical-pair / redex finder (p. 8)

> Assume `Πᵢ = Γᵢ→Aᵢ` (`i = 0,…,j₀`) and `Π = Γ→C` with `A_{j₀} ∈ {C,⊥}` and `∀i ≤ j₀ (Γᵢ ⊆ Γ, A₀,…,A_{i−1})`. Further let `I₀,…,I_{j₀}` be inference symbols such that `∀i ≤ j₀ (Iᵢ ◁ Πᵢ & Iᵢ ⋪ Π)`. Then `∃ i,j,k (i < j ≤ j₀ & Iᵢ = R_{Aᵢ} & Iⱼ = L^k_{Aᵢ} & 0 < rk(Aᵢ))`.

This is the heart: in a *critical* chain inference there is always a matching **right-rule / left-rule pair on the same non-atomic cut formula `Aᵢ`** — i.e. a genuine cut redex to reduce. (`§7` Lemma 7.1 "Existence of a suitable cut" is the multisuccedent analog.)

### Theorem 3.4 — rank bound + validity of `d{0}, d{1}` (p. 9)

> For `d ⊢ Π`:
> (a) If `d = K^r_Π d₀ … dₗ` is critical, then `d{0} ⊢ Π·A(d)`, `d{1} ⊢ A(d),Π`, and `rk(A(d)) < r`.
> (b) `∀n ∈ |tp(d)| ( d[n] ⊢ tp(d)(Π,n) )`.

Theorem 3.4 is the **validity / type-soundness theorem**: it certifies that `d[n]` *is a genuine `⊢`-derivation* whose endsequent is exactly the reduced sequent `tp(d)(Π,n)`, and that the auxiliary `d{0}, d{1}` are valid derivations of `Π·A(d)` and `A(d),Π` with the cut formula's rank strictly dropped (`rk(A(d)) < r`). Proved by simultaneous induction on the build-up of `d`. (Its §2 ancestor is **Theorem 2.1**, p. 4: "If `d` is a closed Z-derivation of `Π` and `n ∈ arity(d)`, then `d[n] ⊢ tp(d)(Π,n)`.")

### Lemma 4.1 + Theorem 4.2 — the descent (p. 11)

> **Lemma 4.1.** For each closed Z-derivation `d`:
> (a) If `d` is **not critical** then `dg(d[n]) ≤ dg(d)` & `õ(d[n]) < õ(d)`, for all `n ∈ |tp(d)|`.
> (b) If `d` is **critical** then
>    (i) `dg(d{ν}) ≤ dg(d)` & `õ(d{ν}) < õ(d)`, for `ν = 0,1`;
>    (ii) `dg(d[0]) < dg(d)` & `õ(d[0]) < ω^{õ(d)}` & `rk(A(d)) < dg(d)`.

Critical reduction *lowers the degree* (`dg(d[0]) < dg(d)`) at the cost of blowing up the pre-ordinal by one ω-power; non-critical reduction *keeps the degree* and *lowers the pre-ordinal*. Both are absorbed by the tower:

> **Theorem 4.2.** If `d` is a closed Z-derivation, then `o(d[n]) < o(d)` for all `n ∈ |tp(d)|`.
>
> Proof: By Lemma 4.1, `õ(d[n]) < ω_{dg(d)−dg(d[n])}(õ(d))`, hence `o(d[n]) = ω_{dg(d[n])}(õ(d[n])) < ω_{dg(d)}(õ(d)) = o(d)`.

The §2 termination corollary (**Corollary 2.1**, p. 7) closes the loop: `if d ⊢ →⊥ then d[0] ⊢ →⊥` — a falsum-derivation always reduces to another falsum-derivation (because `tp(d)` can only be `Rep` for `→⊥`), so an infinite reduction chain would give an infinite ε₀-descent.

### Supporting / orienting material

- **§5** treats atomic (axiom) derivations and their `tp`, `d[n]`, ordinals (the postponed base cases).
- **§6** embeds Z into an infinitary ω-system `Z^∞` via `d ↦ d^∞` (Theorem 6.3: `d^∞ ⊢^{õ(d)}_{dg(d)} Π`), giving a *semantic* explanation of why the reduction and the §4 ordinals work (cut-elimination in `Z^∞`). Theorem 6.5 shows `d^∞` and `d[n]^∞` mesh with Definition 3.2.
- **§7** adapts §§3–4 to **multisuccedent** sequents (the modern Gentzen [Ge38] setting), replacing the chain rule by a generalized chain rule (GCR) and Lemma 3.1 by Lemma 7.1; the construction is reorganized into "Assumption 0–3" + Theorem 7.2, an *axiomatic skeleton* that isolates exactly what the reduction needs.
- **Appendix** shows `õ(d)/o(d)` is Gentzen's 1936 Ordnungszahl assignment up to base-ω vs base-2 Cantor normal form (via [KB81]).

---

## Relevance to crux-2 (KEY)

The expedition is internalizing this reduction in IΣ₁ as "**RedSound**": the reduct of a contradiction-derivation must itself be a *genuine valid* derivation. The current obstacle is that the expedition's *ordinal-faithful* reduct is **not** derivation-valid, forcing a "genuine reduct" redesign. Buchholz answers all three sub-questions directly.

### (a) Is the reduct `d[n]` automatically a VALID derivation, and which lemma ensures it?

**Yes — validity is a theorem, proved simultaneously with the construction.** This is exactly **Theorem 3.4(b)** (its §2 ancestor is Theorem 2.1):

> (b) `∀n ∈ |tp(d)| ( d[n] ⊢ tp(d)(Π,n) )`.

`d[n] ⊢ …` is the *inductively-defined valid-derivation judgment* `⊢` (the `d ⊢ Π` relation, §3 p. 8). So `d[n]` is not merely a code with the right ordinal — it is *certified to inhabit the `⊢` relation*, with endsequent precisely the reduced sequent. The key sub-fact making the critical case go through is **Theorem 3.4(a)**: the two halves `d{0} ⊢ Π·A(d)` and `d{1} ⊢ A(d),Π` are valid derivations, with `rk(A(d)) < r`, so they can legally be combined by a rank-`(r−1)` chain rule `K^{r−1}_Π d{0} d{1}` — that combination *is* `d[0]`, and it typechecks. **Lemma 3.1** is the enabling lemma underneath: in a critical chain inference it *guarantees a real right/left cut-redex `(R_{Aᵢ}, L^k_{Aᵢ})` exists*, so the construction is never stuck and the resulting `d[0]` is well-formed.

**Critically, Buchholz proves validity (Thm 3.4) and ordinal-descent (Lemma 4.1 / Thm 4.2) as TWO SEPARATE inductions over the same construction `d ↦ d[n]`.** Validity (`⊢`) and the ordinal drop are *both* properties of the *one* reduct — there is no tension between "ordinal-faithful" and "derivation-valid." This is precisely the structure the expedition wants: a single reduct that is simultaneously a genuine `⊢`-derivation *and* ordinal-decreasing. If the expedition's current reduct is ordinal-faithful but not `⊢`-valid, the diagnosis is that it skipped Buchholz's Theorem-3.4 discipline (validity is not automatic from the ordinal bookkeeping; it must be carried as a parallel invariant proved by the same recursion).

### (b) How heavy is the reduction's definition — is there a portable primitive-recursive construction?

**The reduction is fully explicit and primitive-recursive in the derivation code**, and is *deliberately* structured to be portable:

- `Definition 3.2` defines `tp(d)` and `d[n]` (and `d{0}, d{1}, A(d)`) by a **structural recursion on the build-up of `d`** — five cases (atomic, `I^a_∀xF`, `I_¬A`, `Ind`, `K^r`), with the `K^r` case splitting into critical (5.1), critical-subderivation (5.2.1), non-critical (5.2.2). Each clause is a finite, decidable case analysis over the top inference symbol plus the `tp(dᵢ)` of the immediate subderivations. No ε₀-recursion, no unbounded search — the only "search" is *Lemma 3.1's* "least pair `(i,j)`" and "minimal `i`/`j₀`", which are **bounded** searches over `i,j ≤ j₀ ≤ l` (the finitely many premises). That is straightforwardly primitive recursive on the Gödel-coded derivation tree.
- The arithmetic on ordinals (`dg`, `õ`, `o`) is likewise primitive-recursive (`#` natural sum, `ω^·`, the `ω_n` tower), and is *separate* from the reduct construction — you can port `d ↦ d[n]` without yet touching ordinals.
- **`§7`'s "Assumption 0–3" + Theorem 7.2 is essentially a pre-packaged abstraction interface**: it lists exactly the data (`End(d)`, `tp(d)`, `d[n]`, `A(d)`, `d{0}`, `d{1}`, `dg`, `õ`) and the closure properties needed, and proves descent/validity from them. That is the cleanest target to mirror in a Lean/IΣ₁ formalization — implement the four `D₁/D₂/D₃` predicates (≈ validity, degree-bound, pre-ordinal-bound) and discharge Theorem 7.2.

So the construction is moderately heavy (it is the full Gentzen reduction), but it is *explicit, structurally recursive, bounded, and already factored* into a portable axiomatic skeleton — the opposite of an inexplicit existence proof.

### (c) Does Buchholz make "genuine reduct" easier than redesigning from scratch?

**Yes, substantially — Buchholz's central design choice is that the reduct is a genuine `⊢`-derivation *by construction*, not after the fact.** The reason it works is the **two-invariant simultaneous induction**: `tp(d)`/`d[n]` are *defined* (Def 3.2) at the same time Theorem 3.4 *proves* `d[n] ⊢ tp(d)(Π,n)`. The validity invariant is threaded through every clause (e.g. case 5.1 only fires after Lemma 3.1 supplies a real redex, and the recombination `K^{r−1}_Π d{0} d{1}` is exactly a legal chain-rule application certified by Thm 3.4(a)). The expedition's "genuine reduct" redesign should not invent a new reduct — it should **adopt Buchholz's Definition 3.2 as the reduct and carry Theorem 3.4(b) as the validity invariant alongside the Lemma-4.1 ordinal invariant**. The `§7` Assumption-0–3 framing already separates the two invariants (`d ∈ D₁` = `tp(d) ◁ Π & ∀n (d[n] ⊢ tp(d)(Π,n))` = validity; `d ∈ D₃` = pre-ordinal descent), so the formalization can prove "reduct is valid" (D₁) and "reduct's ordinal drops" (D₃) as independent inductions over the *same* `Definition 3.2` construction.

---

## Verdict (3–4 sentences)

Buchholz's reduction gives the expedition almost exactly the "genuine valid reduct" it needs: the reduct `d ↦ d[n]` (Definition 3.2) is **provably a genuine `⊢`-derivation of the reduced sequent by Theorem 3.4(b)** (with the critical-case halves `d{0}/d{1}` validated by Theorem 3.4(a) and a real cut-redex guaranteed by Lemma 3.1), and crucially this *validity* invariant is proved by a **separate simultaneous induction** from the ordinal-descent invariant (Lemma 4.1 / Theorem 4.2) — showing there is no inherent conflict between "ordinal-faithful" and "derivation-valid," only a missing parallel invariant. The construction *is* portably primitive-recursive: a bounded structural recursion on the coded derivation tree (five cases, the only searches being Lemma 3.1's `i,j ≤ j₀ ≤ l` bounded minimizations), with ordinal arithmetic kept entirely separate, and §7's "Assumption 0–3 + Theorem 7.2" already packages it as an axiomatic skeleton whose `D₁` (validity) and `D₃` (descent) predicates map directly onto the IΣ₁ formalization targets. Recommendation: don't redesign the reduct — port Buchholz's Definition 3.2 verbatim and carry Theorem 3.4(b)/§7-`D₁` as the RedSound invariant rather than trying to recover validity from the ordinal-faithful reduct after the fact.
