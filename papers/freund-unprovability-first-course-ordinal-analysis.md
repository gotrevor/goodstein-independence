# Freund — Unprovability in Mathematics: A First Course on Ordinal Analysis

## Provenance

- **File**: `freund-unprovability-first-course-ordinal-analysis.pdf` (this directory)
- **Author**: Anton Freund
- **Source**: arXiv:2109.06258 (v2, 21 Apr 2022), `math.LO`
- **Citation**: Anton Freund, *Unprovability in Mathematics: A First Course on Ordinal Analysis*, lecture notes (arXiv:2109.06258), 2021/2022. ~30 pp, 12 lectures + 6 exercise sessions.
- **MSC 2020**: 03-01, 03B30, 03F05, 03F15, 03F35, 03F40

## Abstract / scope

Introductory lecture-note course on **ordinal analysis** (a subfield of proof theory). Prerequisites: a solid intro to mathematical logic, *no* specialized proof theory. The whole course is engineered toward **one** concrete independence result:

> **Theorem 1.2.** Kruskal's theorem for binary trees is unprovable in conservative extensions of Peano arithmetic.

(Made precise as **Theorem 6.8**: `ACA₀` does not prove Kruskal's theorem for binary trees.) Along the way it gives a "reasonably general" intro to sequent calculus, cut elimination, and the ordinal analysis of PA (Gentzen, `proof-theoretic ordinal = ε₀`). Note: **Goodstein's theorem is never treated**; the target combinatorial statement is Kruskal/binary-trees, and the internal "hard" statement is transfinite induction up to ε₀.

## Key results / chapter map

| § | Topic | Main results |
|---|-------|--------------|
| 1 | Introduction | Kruskal (Thm 1.1); goal = Thm 1.2 (Kruskal unprovable in conservative ext. of PA). Friedman/de Jongh attribution. |
| 2 | Sequent calculus for predicate logic | Tait-style calculus (Def 2.2). **Completeness via deduction chains with cut-free derivations** (Thm 2.6) → **semantic** cut elimination (Cor 2.7). Discussion of "cuts as lemmata," non-elementary blow-up of cut-free proofs. |
| 3 | Induction and infinite derivations | PA, PA[X] (extra uninterpreted predicate X). ω-rule; **infinitary derivations** `⊢^α_d Γ` with ordinal height α and cut-rank bound d (Def 3.4). **Embedding** (Thm 3.7): theorems of PA[X] get infinite derivations. **Conditional independence** (Thm 3.12): *if* the infinite system admits cut elimination, then PA[X] cannot prove `TI_◁` (transfinite induction along ◁) when its order embeds ℕ. Parsons' theorem (IΣ₁ provably-total = primitive recursive) appears only as **Exercise 3.1** ("not used in the rest of the course"). |
| 4 | Cut elimination for infinite derivations | Inversion (Prop 4.3), Reduction (Prop 4.6), and the keystone **Theorem 4.7 ('Cut elimination')**: `⊢^α_{d+1} Γ ⟹ ⊢^{ω^α}_d Γ`, so eliminating cuts costs an ω-exponential in the ordinal height. This is the **internalized Gentzen cut-elimination** that the rest of the course rides on. |
| 5 | An ordinal notation system | Builds ε₀ as terms / nested sequences (Def 5.1), addition + and ω-exponentiation (Def 5.3), Cantor normal form (Rmk 5.5). ε₀, ≺ shown primitive recursive / PA-definable. Culminates in **Theorem 5.7 (Gentzen): PA[X] does not prove `TI_≺`** (transfinite induction up to ε₀). Sharpness (PA proves TI along every proper initial segment of ε₀) sketched in Exercise 5.8 via Gentzen's "jump" φ^J. |
| 6 | Unprovability of Kruskal's theorem | `(B, ≤_B)` = finite binary trees as a well partial order. ACA₀ defined; **Prop 6.5: ACA₀ is a conservative extension of PA[X]**. **Prop 6.6**: a primitive-recursive order-reflecting `f : ε₀ → B` ("reification" of ε₀ into the trees). **Theorem 6.8**: ACA₀ ⊬ Kruskal-for-binary-trees, because Kruskal ⟹ `TI_≺` (well-foundedness of ε₀), contradicting Thm 5.7. **Cor 6.9 / Rmk 6.10**: over RCA₀, Kruskal-for-binary-trees ⟺ well-foundedness of ε₀ (de Jongh / Schmidt reification). |
| 7 | Conclusion (other applications) | Briefly *mentions* — but does **not develop** — (a) extraction of **provably-total recursive function** bounds from an ordinal analysis (Kreisel's "what more do we know"), and (b) relative consistency / conservativity (e.g. Rathjen–Setzer). Graph-minor theorem ↔ Π¹₁-CA₀ noted. |

**Method, in one line:** infinitary sequent calculus + ω-rule (embed PA[X]) → **syntactic cut elimination for infinite derivations** (Thm 4.7) → derive ε₀-well-foundedness `TI_≺` would be provable if PA proved it, but cut-free proofs of small height can't reach `TI` along a "large" order (Thm 3.12) → **Gentzen Thm 5.7** → reify ε₀ into binary trees (Prop 6.6) → Kruskal unprovable (Thm 6.8).

## Route relevance to crux-2 (the expedition's "PA ⊬ Goodstein via internalized cut-elimination")

**(a) Which method does Freund use for PA unprovability?**
**Cut-elimination / Con(PA)-style ordinal analysis — emphatically.** The entire spine is internalized Gentzen cut-elimination: Section 4's **Theorem 4.7** (`⊢^α_{d+1} Γ ⟹ ⊢^{ω^α}_d Γ`) *is* the cut-elimination wall, and Theorems 3.12 + 5.7 turn it into unprovability of `TI_≺` (ε₀-induction = essentially Con(PA)). This is **the same hard route as crux-2**, not an alternative to it. The book does **not** use the fast-growing-hierarchy / provably-total-functions classification as its method — that whole apparatus is essentially absent (see (c)).

**(b) Does it give a self-contained, formalization-friendly chain to unprovability that AVOIDS internalized cut-elimination?**
**No.** There is exactly one route here and it goes *through* cut elimination for infinite derivations. Section 2's "semantic cut elimination" (Thm 2.6/2.7) is a teaching detour and is explicitly noted as **unusable inside PA** (truth is not arithmetically definable — Tarski), so the course must do the **syntactic** version (Thm 4.7) precisely to internalize it. So Freund offers a *clean, modern, carefully-staged* presentation of the cut-elimination route, but it is **not a cut-elimination-avoiding** route. If anything it confirms crux-2 is the standard hard wall. (The course is also targeting **Kruskal**, not Goodstein; Goodstein is not formalized here at all.)

**(c) Does it state the classification "f is PA-provably-total iff f ≼_dom H_α for some α<ε₀" cleanly?**
**No.** The book contains **no statement of the H_α (fast-growing) hierarchy at all**, and **no provably-total-functions classification theorem**. The only provably-total-recursive-function content is:
- **Exercise 3.1** — Parsons' theorem for IΣ₁ (provably-total Σ₁-functions are primitive recursive), stated as an exercise, explicitly **"not used in the rest of the lecture."**
- **Section 7, ¶"provably total recursive function"** — an informal *mention* that an ordinal analysis of a theory T "will yield a bound on a function f," answering Kreisel's question, with a pointer to Fairtlough–Wainer [5] (*Hierarchies of provably recursive functions*) — but **no theorem, no H_α, no "iff" statement.**

So the growth-rate route's key lemma is **not** available off-the-shelf in Freund. The natural reference for it is **Fairtlough–Wainer [5]** (cited in §7), not this course.

### Quoted/cited theorem numbers for reuse
- **Theorem 4.7 (Cut elimination, infinitary):** `⊢^α_{d+1} Γ ⟹ ⊢^{ω^α}_d Γ` — the internalized cut-elimination engine (= crux-2's wall).
- **Theorem 3.7 (Embedding):** PA[X] theorem ⟹ `⊢^α_d φ`.
- **Theorem 3.12 (conditional independence):** cut-elim ⟹ PA[X] ⊬ `TI_◁`.
- **Theorem 5.7 (Gentzen):** **PA[X] does not prove `TI_≺`** (ε₀-induction). This is the cleanest reusable "PA ⊬ ε₀-induction" statement in the book.
- **Prop 6.5 (conservativity):** ACA₀ conservative over PA[X].
- **Prop 6.6 + Theorem 6.8 + Rmk 6.10:** reification ε₀ → binary trees; Kruskal-binary ⟺ WF(ε₀) over RCA₀; ACA₀ ⊬ Kruskal-binary.

## Verdict (3-4 sentences)

**No — Freund's course does not offer a cleaner, cut-elimination-avoiding route; it *is* the cut-elimination route, presented cleanly.** Its whole spine is internalized Gentzen cut-elimination for infinite derivations (Theorem 4.7) → PA ⊬ ε₀-induction (Theorem 5.7) → reify into trees → Kruskal unprovable (Theorem 6.8), which is exactly the "crux-2" wall the expedition is fighting, not an alternative to it. Crucially, the book contains **no fast-growing-hierarchy chapter and no "PA-provably-total iff f ≼ H_α for some α<ε₀" classification** — that growth-rate route is not developed here (only gestured at in §7, pointing to Fairtlough–Wainer [5]), and Goodstein itself is never treated (the target is binary-tree Kruskal). The single most reusable theorem for a formalization is **Theorem 5.7 (Gentzen: PA[X] ⊬ TI_≺)**, the clean "PA ⊬ ε₀-induction" anchor — but it still arrives *through* cut elimination, so this text confirms rather than circumvents the hard wall.
