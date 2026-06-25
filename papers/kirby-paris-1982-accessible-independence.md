# Kirby & Paris (1982) — Accessible Independence Results for Peano Arithmetic

## Provenance

- **File**: `kirby-paris-1982-accessible-independence.pdf` (this directory)
- **Title**: *Accessible Independence Results for Peano Arithmetic*
- **Authors**: Laurie Kirby and Jeff Paris (Department of Mathematics, University of Manchester)
- **Source**: *Bulletin of the London Mathematical Society*, **14** (1982), 285–293. Received 1 February 1982.
- **Citation**: L. Kirby and J. Paris, "Accessible independence results for Peano arithmetic", *Bull. London Math. Soc.* 14 (1982), 285–293.

This is the **original** paper establishing that Peano Arithmetic (denoted `P` throughout) does not prove **Goodstein's theorem**, and introducing the **Hydra game** (Hercules vs. the hydra) as a second, "unashamedly combinatorial" independent statement. Both independence results are proved by the **same model-theoretic / indicator-theoretic method**, building on the Ketonen–Solovay analysis of ordinals below ε₀ and Paris's earlier indicator-theory machinery — **not** by Gentzen-style cut-elimination.

---

## Abstract (plain language)

Kirby and Paris present what they describe as "perhaps the first" first-order statement independent of PA that is, informally, **purely number-theoretic in character** (as opposed to metamathematical or combinatorial) — namely the statement that every Goodstein sequence eventually reaches 0. They prove:

1. **(Theorem 1)** Every Goodstein sequence does in fact terminate (a true theorem of arithmetic, provable using transfinite induction up to ε₀), **but** the formalized statement "∀m ∃k mₖ = 0" is **not provable in PA**.
2. **(Theorem 2)** The Hydra game: *every* strategy for Hercules is a winning strategy (Hercules always eventually kills the hydra), yet the statement "every recursive strategy is a winning strategy" is **not provable in PA**.

The methods are model-theoretic and combinatorial. The key engine is a correspondence between **base-n representations of integers** and **ordinals below ε₀** (replace the base `n` by `ω`), so that a terminating Goodstein/hydra process maps to a strictly **decreasing sequence of ordinals** below ε₀. Termination is then just well-foundedness of ε₀; unprovability comes from **indicator theory** — the rate at which the sequences grow outstrips every PA-provably-total recursive function, which is detected inside a **nonstandard model of PA**.

---

## Key results — exact theorem statements

### Goodstein sequences (definitions)

For `n > 1`, the **base-n representation** of `m` is obtained by writing `m` as a sum of powers of `n`, then writing each exponent in base `n`, recursively, until the representation stabilizes (hereditary base-n notation). E.g. `266 = 2^(2^2+1) + 2^(2+1) + 2`.

`G_n(m)`: if `m = 0`, `G_n(m) = 0`; otherwise replace every `n` in the base-`n` representation of `m` by `n+1`, then subtract 1.

The **Goodstein sequence for m starting at n** is `m₀ = m, m₁ = G_n(m₀), m₂ = G_{n+1}(m₁), m₃ = G_{n+2}(m₂), …` (the base "bumps" by 1 each step, then 1 is subtracted). The sequences explode astronomically before crashing to 0 (e.g. the sequence for 4 starting at 2 first hits 0 at `k = 3·2^(402653211) − 3 ≈ 10^(121210700)`).

> **THEOREM 1.** (i) (Goodstein) `∀m ∃k mₖ = 0`. More generally for any `m, n > 1` the Goodstein sequence for `m` starting at `n` eventually hits zero.
>
> (ii) `∀m ∃k mₖ = 0` (formalized in the language of first-order arithmetic) is **not provable in P**.

### Hydra game

> **THEOREM 2.** (i) Every strategy is a winning strategy.
>
> (ii) The statement "every recursive strategy is a winning strategy" is **not provable from P**.

(A *hydra* is a finite tree rooted at a fixed node. Hercules chops a head; at stage `n` the hydra grows `n` replicas of the subtree just below the severed segment. Theorem 2(i) cannot be formalized in first-order arithmetic directly because arbitrary strategies are infinitary objects; restricting to **recursive** strategies makes it expressible, and then it is independent.)

### The ordinal engine (heart of both proofs)

Given `m = n^k a_k + n^(k−1) a_{k−1} + … + n a_1 + a_0`, define `o_n(m)` (Cantor Normal Form) by replacing every `n` in the hereditary base-`n` representation with `ω`. Formally, for `x ∈ N` or `x = ω`,
`f^(m,n)(x) = Σ_{i=0}^k a_i · x^(f^(i,n)(x))`, with `G_n(m) = f^(m,n)(n+1) − 1` and `o_n(m) = f^(m,n)(ω)`.

- **Lemma 3(ii)**: `⟨o_n(m)⟩(n) = o_{n+1}(G_n(m))`. So each Goodstein step corresponds to applying the ordinal operation `⟨α⟩(n)`, where `⟨α⟩(n) < α` for `α > 0`.

- Hence a Goodstein sequence `b₀, b₁, b₂, …` induces a sequence of ordinals `o_n(b₀), o_{n+1}(b₁), o_{n+2}(b₂), …` that is **strictly decreasing below ε₀** — impossible by transfinite induction below ε₀. **This proves Theorem 1(i).**

- The **hydra version** (Theorem 2 sketch, p. 292): assign top nodes ordinal 0, and each internal node `ω^(α₁) + … + ω^(α_n)` from the ordinals `α₁ ≥ … ≥ α_n` assigned to the nodes directly above it. The "ordinal of the hydra" is the ordinal at the root. Each chop strictly decreases this ordinal, so every strategy wins (Theorem 2(i)).

### The unprovability machinery — Ketonen–Solovay / indicators (heart of Theorem (ii))

Kirby–Paris introduce a second ordinal operation `{α}(n)` and the notion of an **α-large finite set** (`X ⊆ N` is α-large by induction on α; `X` is 1-large iff `|X| ≥ 2`; `X` is α-large iff `X − {X₀}` is `{α}(X₁)`-large). These notions, with "ordinals < ε₀ replaced by suitable notations", **make sense in a nonstandard model of P**.

> **THEOREM 4** (Ketonen–Solovay; see [3], [4]).
> (i) The function `Y(a,b)` = the greatest `c` such that `[a,b]` is `ω_c`-large is an **indicator for models of P**.
> (ii) The statement `∀a ∃c ∃b ([a,b] is ω_c-large)` is **independent of P** and is equivalent in P to `Con(P + T₁)`, where `T₁` is the set of true Π₁ sentences.
> (iii) The functions `g_n(x)` = least `y ≥ x` such that `[x,y]` is `ω_n`-large are **provably total recursive functions**, and for any provably total recursive `f` there exists `n ∈ N` such that `f(x) < g_n(x)` for all sufficiently large `x`. (I.e. the `g_n` cofinally dominate every PA-provably-total function.)

- **Proposition 8**: If `b₀, …, b_k` is the Goodstein sequence for `m` starting at `n` (`b_k = 0` first), then `[n−1, n+k]` is `o_n(m)`-large. This ties the **length** of a Goodstein sequence directly to α-largeness, hence to the indicator `Y`.

### The independence proof (p. 291, the logical skeleton)

Suppose for contradiction `P ⊢ ∀m ∃k mₖ = 0`. (\*)

> "By Theorem 4 and the methods of indicator theory (see [5]) we can find `M ⊨ P` and nonstandard `c ∈ M` such that `M ⊨ ¬∃y ([1,y] is ω_c-large)`. (Briefly, this is done by taking a countable nonstandard model `J` of P and nonstandard `c, a ∈ J` such that `Y(c, a)` is nonstandard but less than `c − 1`, where `Y` is as in Theorem 4(i). … We can let `M` be such an initial segment.)"

> "In `M`, take `d = 2^(2^(…2))` with `c` iterated exponentiations, so `o₂(d) = ω_c`. By (\*) take `e ∈ M` such that `d_e = 0`. Since the proof of Proposition 8 can be carried out in P … we have in `M` that `[1, 2+e] is ω_c-large`, a contradiction."

So unprovability is obtained by **exhibiting a nonstandard model `M` of PA in which the Goodstein statement fails** — concretely, by cutting `J` down to an initial segment `M` (a "cut") on which the indicator `Y` takes the right value, so that no `y` making `[1,y]` `ω_c`-large exists, contradicting termination.

The Hydra Theorem 2(ii) is proved "by a proof like that of Theorem 1": one exhibits a recursive strategy `τ` with `[α]_τ(n) = {α}(n+1)`, whose totality (= `τ` is winning) would give `ε₀`-induction / total-recursiveness of `λnx.g_n(x)`, impossible in P.

### Refinement (Theorem 1′) and the `IΣ_k` hierarchy

> **THEOREM 1′.** (i) For each fixed `p ∈ N`, `IΣ_k ⊢ ∀m, n > 1` (if `m < n^(…n^p)`, `n` occurring `k` times) then the Goodstein sequence terminates.
> (ii) `IΣ_k ⊬ ∀m, n > 1` (if `m < n^(…n)`, `n` occurring `k+1` times) then the Goodstein sequence terminates.

(Also: restricting hydras to height `k+1` gives the analogous independence over `IΣ_k`; the length-of-battle function for height-2 hydras under `τ` is not provably total in `IΣ₁`, hence not primitive recursive.)

---

## Route relevance to crux-2 (KEY)

The expedition formalizes **"PA ⊬ Goodstein"** and currently routes through **Gentzen-style internalized cut-elimination ("crux-2")** to obtain PA-internal `Con(PA)` and then Gödel's second incompleteness theorem. The Kirby–Paris proof is a *different* proof of the same independence fact. Here is how it bears on the route choice.

### (a) Logical skeleton of the Kirby–Paris unprovability proof

1. **Ordinal correspondence (purely combinatorial/inductive).** Map hereditary base-`n` integers to ordinals below ε₀ (replace `n` by `ω`): `m ↦ o_n(m)`. One Goodstein step = one application of `⟨α⟩(n)`, and `⟨α⟩(n) < α` (Lemma 3, Prop 7). Termination (Thm 1(i)) is then *exactly* well-foundedness / transfinite induction below ε₀.
2. **Largeness / indicator bridge.** Define `{α}(n)` and "α-large finite set". The length of a Goodstein sequence is pinned to α-largeness (Prop 8: `[n−1, n+k]` is `o_n(m)`-large).
3. **Ketonen–Solovay fast-growth (Thm 4).** The indicator `Y(a,b)` (greatest `c` with `[a,b]` `ω_c`-large) is an *indicator* for models of P; `∀a∃b([a,b] is ω_c-large)` is independent of P; the `g_n` cofinally dominate every PA-provably-total recursive function.
4. **Model-theoretic contradiction (the actual independence step).** Assume `P ⊢ Goodstein`. Take a countable nonstandard `J ⊨ P`, pick nonstandard `c, a` with `Y(c,a)` nonstandard but `< c−1`, and take the **initial-segment cut `M`** of `J` on which `Y` has that value. Then `M ⊨ P` but `M ⊨ ¬∃y([1,y] is ω_c-large)`. Pick `d` = tower of `c` exponentials (`o₂(d) = ω_c`); the assumed termination yields, *inside `M`* (Prop 8 is provable in P), that `[1, 2+e]` IS `ω_c`-large — contradiction.

The independence is thus delivered by **producing a model of PA where Goodstein fails** (via the cut/indicator construction), i.e. by **failure of provability ⟺ existence of a countermodel** (soundness/completeness), not by a syntactic consistency argument.

### (b) Does it avoid cut-elimination and Con(PA)-internalization?

**Yes — it sidesteps both, in the sense the expedition cares about.**

- There is **no cut-elimination** anywhere. The references are Gentzen [1], Ketonen–Solovay [3], Paris [4], Paris [5]; the proof technology is the **indicator method + model cuts**, and the ordinal facts it needs are the *combinatorial* Ketonen–Solovay analysis of ε₀, which the authors explicitly contrast with Gentzen: *"Gentzen [1] showed that using transfinite induction on ordinals up to ε₀ one can prove the consistency of P, and the Ketonen–Solovay machinery we use here can be viewed as illuminating in more detail the relationship between ε₀ and P."* So Gentzen's result is cited as *context*, not used as a lemma.

- It **does not internalize `Con(PA)` and invoke Gödel II.** Crucially, the Kirby–Paris argument is **not** "Goodstein → Con(PA), and Con(PA) is unprovable by Gödel II." Instead it is a **direct model construction**: assume provability, build a cut-model of PA refuting the statement, derive a contradiction. Note that Theorem 4(ii) does relate the *largeness* statement to `Con(P + T₁)` — but that equivalence is **not** the lever used for the Goodstein independence; the Goodstein contradiction (p. 291) is purely the indicator/cut construction (Prop 8 carried out inside `M`). The proof never needs PA to internally prove its own consistency. (The deep input is instead the Ketonen–Solovay *dominance* result, Thm 4(iii) — a quantitative growth fact — together with the existence of suitable cuts.)

**Net:** the model-theoretic route **avoids crux-2** (internalized Gentzen cut-elimination → PA-internal Con(PA) → Gödel II). It replaces that entire pipeline with: ε₀ well-foundedness (for the *true* direction) + Ketonen–Solovay fast-growth + an indicator/cut construction of a nonstandard countermodel (for the *unprovability* direction).

### (c) What a Lean / mathlib formalization would need

The model-theoretic route trades the proof-theoretic wall for a **different, substantial set of prerequisites**:

1. **Goodstein ↔ ε₀ ordinal machinery.** *Largely already in mathlib.* mathlib has `Ordinal`, `Ordinal.IsNormal`, Cantor Normal Form, and an existing formalization of **Goodstein's theorem (termination)** via the map to ε₀ (`Mathlib` `Goodstein`/`Ordinal.CNF` material — this is the green, "true direction" the expedition already has). So Lemma 3 / Prop 7 territory is friendly.
2. **A theory of nonstandard models of PA.** This is the heavy lift. Need: a formal language and structures for PA, the **completeness theorem** (to get models from non-provability), countable nonstandard models, and the **initial-segment "cut" construction** (definable cuts that are themselves models of PA / `IΣ_n`). mathlib has `FirstOrder.Language`, `BoundedFormula`, `ModelTheory.Satisfiability`, and the **completeness/compactness** results — but **models of arithmetic specifically** (PA's nonstandard models, cuts, overspill, the fact that a definable cut closed under the right operations models `P`) are **not present** and would be a major development.
3. **Indicator theory.** Formalize indicators `Y(a,b)`, the notion of an indicator *for a theory*, and the cut-from-indicator lemma ("nonstandard indicator value yields an initial segment that is a model"). **Not in mathlib at all.**
4. **Ketonen–Solovay combinatorics.** The `{α}(n)` operation, **α-large finite sets**, the largeness ↔ length correspondence (Prop 8), and the **fast-growth dominance** (`g_n` cofinally above every provably-total recursive `f`, Thm 4(iii)). This is **Paris–Harrington-style finite combinatorics of ε₀** and is **not in mathlib**. This is essentially the same hard combinatorial core that a Paris–Harrington formalization would need.
5. **Provably-total recursive functions / the `IΣ_k` hierarchy** for the Theorem 1′ refinement (optional for the headline result).

### (d) More or less formalizable in Lean/mathlib than the proof-theoretic route?

**Honest assessment: it trades one hard wall for a different hard wall, and is plausibly NOT easier — possibly harder — in the current mathlib.**

- **Pro (model-theoretic):** It reuses the *existing* mathlib Goodstein-termination + ordinal/ε₀ infrastructure, and mathlib's `ModelTheory`/completeness layer gives a foothold the proof-theoretic route lacks. The argument is "find a countermodel," which is conceptually clean and maps onto soundness/completeness already in mathlib.
- **Con (model-theoretic):** The *specific* prerequisites — **nonstandard models of PA, definable cuts that model `P`, indicator theory, and the Ketonen–Solovay/Paris–Harrington combinatorics** — are **wholly absent from mathlib** and are each a research-grade formalization effort. There is **no existing formalization of nonstandard models of arithmetic with cuts** in mathlib, and the α-large / indicator combinatorics is exactly the notoriously delicate Paris–Harrington machinery.
- **Comparison:** The cut-elimination / crux-2 route needs a **proof-theory tower** (sequent calculus, ordinal-assignment, cut-elimination for PA, arithmetization of provability/Con(PA), Gödel II). The model-theoretic route needs a **model-theory + finite-combinatorics tower** (models of PA, cuts/overspill, indicators, Ketonen–Solovay growth). **Both towers are large and largely un-formalized.** The model-theoretic route does *avoid* having to internalize and arithmetize cut-elimination — a genuine simplification of the *logical idea* — but it substitutes an arguably comparable burden (cut models + indicator combinatorics). So it is **not clearly more formalizable**; the realistic verdict is "different wall, similar height, possibly higher because of the indicator combinatorics."

### Key passages (quoted)

- On character and method (p. 285): *"Here we present perhaps the first which is, in an informal sense, purely number-theoretic in character … The methods used to prove it, however, are combinatorial."*
- Gentzen contrast (p. 287): *"Gentzen [1] showed that using transfinite induction on ordinals up to ε₀ one can prove the consistency of P, and the Ketonen–Solovay machinery we use here can be viewed as illuminating in more detail the relationship between ε₀ and P."*
- The ordinal-descent argument for termination (p. 289): *"the corresponding sequence of ordinals would be an infinite, strictly decreasing sequence which is an impossibility (by transfinite induction below ε₀)."*
- The model-cut step (p. 291): *"By Theorem 4 and the methods of indicator theory (see [5]) we can find `M ⊨ P` and nonstandard `c ∈ M` such that `M ⊨ ¬∃y ([1,y] is ω_c-large)` … the indicator `Y` having nonstandard value on `(c, a)` means precisely that there is an initial segment of `J` which is a model of P and lies 'between' `c` and `a` … We can let `M` be such an initial segment."*
- The closing contradiction (p. 291): *"Since the proof of Proposition 8 can be carried out in P … we have in `M` that `[1, 2+e] is ω_c-large`, a contradiction."*

---

## Bottom line (verdict)

**Yes — the Kirby–Paris model-theoretic route avoids crux-2.** It never internalizes Gentzen cut-elimination and never routes through a PA-internal `Con(PA)` + Gödel II; instead it proves unprovability *directly* by constructing a nonstandard cut-model of PA in which Goodstein fails, using the Ketonen–Solovay analysis of ε₀ and Paris's indicator theory. **But it is not plausibly more Lean-formalizable than the cut-elimination route** in today's mathlib: it swaps the proof-theory tower (sequent calculus + cut-elimination + arithmetized Con(PA)) for an equally absent model-theory + finite-combinatorics tower — **nonstandard models of PA, definable cuts modeling `P`, indicators, and the Paris–Harrington-style α-large/Ketonen–Solovay growth combinatorics** — none of which exists in mathlib. It reuses mathlib's Goodstein-termination/ε₀ and `ModelTheory`/completeness foundations (a real advantage over the proof-theoretic route's bare cupboard), but the indicator + fast-growth combinatorics is a research-grade lift comparable to, and arguably harder than, crux-2.
