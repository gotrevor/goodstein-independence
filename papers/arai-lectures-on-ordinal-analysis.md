# Arai — Lectures on Ordinal Analysis

## Provenance

- **File**: `arai-lectures-on-ordinal-analysis.pdf` (84 pp.)
- **Author**: Toshiyasu Arai (University of Tokyo, Japan)
- **Title / date**: *Lectures on Ordinal Analysis*, lecture notes for a mini-course at the Department of Mathematics, Ghent University, 14–25 March 2023. arXiv:2304.00246v1 [math.LO], 1 Apr 2023.
- **Citation**: T. Arai, "Lectures on Ordinal Analysis," arXiv:2304.00246 (2023). Builds on Buchholz (Normalfunktionen 1975; simplified local predicativity 1992), Jäger (KP analysis 1982/83), Rathjen (proof theory of reflection 1994; parameter-free Π¹₂-CA 2005).
- **Why it's in this repo**: catalogued (SOURCES.md) for the **ε₀-girder + encoding** phase as "modern, self-contained ordinal-analysis lecture notes (ordinal notations, infinitary derivations, cut-elimination, proof-theoretic ordinals)." ⚠️ **That description is over-optimistic for this expedition's needs** — see Relevance below. The notes are real ordinal analysis, but pitched at the **impredicative / large-cardinal** end (KPω and beyond), *not* at the PA/ε₀ level the Goodstein routes live in.

---

## Abstract / scope

A graduate mini-course on the **ordinal analysis of strong set theories** by the operator-controlled-derivation method (Buchholz's "simplified local predicativity"). The stated aim (p. 2): "compute and/or describe the proof-theoretic ordinals of natural theories, thereby measuring the proof-theoretic strengths of theories with respect to Π¹₁-consequences," where `|T| := sup{|≺| : T ⊢ TI[≺,U] for some recursive well order ≺}` (Def 0.2).

The **floor** of these notes is `KPω` (Kripke-Platek set theory with Infinity) — whose proof-theoretic ordinal is the **Bachmann-Howard ordinal** `ψ_{Ω₁}(ε_{Ω+1})` — and the course climbs **upward** from there:

- §1 `KPω` → Bachmann-Howard (the worked baseline).
- §2 `KPΠ₃` — Rathjen's Π₃-reflection analysis (needs a **weakly compact / Π¹₁-indescribable cardinal** 𝕂 and "stationary collapsing").
- §3 Well-foundedness proof for the `OT(Π₃)` notation system.
- §4 `KPΠ₄` — recursively Mahlo operations `RM_i`, Mahlo classes `Mh`.
- §5 First-order Π_N-reflection (an "exponential ordinal structure" of nested Mahlo operations).
- §6 Π¹₁-reflection, stability (`σ` is `(σ+1)`-stable iff Π⁰₁-reflecting; `σ⁺`-stable iff Π¹₁-reflecting).

The technical apparatus throughout is **uniform**: Buchholz ψ-collapsing functions + a computable ordinal notation system `OT(Ω)` + ramified set theory `RS` + operator-controlled infinitary derivations `H_γ[Θ] ⊢^a_b Γ` + predicative cut-elimination + a Collapsing Theorem + a Truth lemma + a well-foundedness proof of the notation system in a base theory (`ID` / `KPΠ_N`).

The whole development takes place at or **above** KPω, i.e. far above `PA = Z`. PA / ε₀ appears only implicitly as the trivial bottom rung; it is never treated.

---

## Key content

### The ordinal-analysis method, as instantiated here (§1, the reusable template)

1. **ψ-collapsing functions (§1.3, Def 1.7).** Work in `KPω`. With `Ω = ω₁` (or `ω₁^{CK}`), define Skolem hulls `H_α(X)` = closure of `{0,Ω} ∪ X` under `+, φ` (Veblen) and `β ↦ ψ_Ω(β)` for `β<α`, and the collapse
   > `ψ_Ω(α) = min({Ω} ∪ {β<Ω : H_α(β) ∩ Ω ⊂ β})`   (eq. 2).

   Prop 1.8 collects the collapsing facts; `ψ_{Ω₁}(ε_{Ω+1})` is the Bachmann-Howard ordinal. `ψ_Ω(α)` is the Mostowski collapse of Ω in the hull `H_α(0)`.
2. **Computable notation system `OT(Ω)` (§1.4).** Every ordinal `< ψ_Ω(ε_{Ω+1})` is denoted by a term over `0,Ω,+,φ,ψ`. **Prop 1.9: `EA` proves `(OT(Ω),<)` is a linear order** (elementary recursive arithmetic suffices to define the order; well-foundedness is the deep part, deferred to §1.6).
3. **Ramified set theory `RS` (§1.5).** RS-terms `L_α` of level `|L_α|=α`; `Δ₀`/`Σ(Ω)`/`Π(Ω)` formula ranks `rk(A) < Ω+ω` (Def 1.10–1.15).
4. **Operator-controlled derivations (§1.5, Def 1.16).** A derivability relation `H_γ[Θ] ⊢^a_b Γ` with **inference rules `(⋁), (⋀), (cut), (Δ₀(Ω)-Coll)`** — the infinitary calculus with a height `a`, cut-bound `b`, and the operator `H_γ[Θ]` tracking which ordinals are "available."
5. **The workhorse lemmas (§1.5):**
   - **Tautology** (1.17), **Inversion** (1.18), **Boundedness** (1.19) `Λ ↦ Λ^{(β,Ω)}`.
   - **Embedding** (1.20): finite `KPω` proofs embed as `H_0 ⊢^{Ω+l}_{Ω+m} Γ`.
   - **Predicative Cut-elimination** (1.21): `H_γ[Θ] ⊢^a_{b+c} Γ ⇒ H_γ[Θ] ⊢^{θ_c(a)}_b Γ` (below Ω), where `θ` is the Veblen-iterate that absorbs cut-rank into height.
   - **Collapsing** (Thm 1.22): `H_γ[Θ] ⊢^a_Ω Γ ⇒ H_{γ̂+1}[Θ] ⊢^β_β Γ` for `β=ψ_Ω(γ̂)` — collapses transfinite (`≥Ω`) heights down below Ω.
   - **Truth** (1.23): a cut-free `Δ(Ω)` derivation gives `L_Ω ⊨ Γ`.
   - **Wrap-up (Thm 1.24):** `KPω ⊢ Γ (Σ(Ω₁)) ⇒ ∃m<ω [L_Ω ⊨ Γ^{(ψ_Ω(ω_m(Ω+1)),Ω)}]` — i.e. the Π¹₁-ordinal of `KPω` is `ψ_Ω(ε_{Ω+1})`.
6. **Well-foundedness of `OT(Ω)` (§1.6, Thms 1.25–1.26).** The "lower bound" half: the base theory `ID` (non-iterated positive inductive definitions) **proves `TI[<↾ ψ_Ω(ω_n(Ω+1)), B]`** for each `n` (Thm 1.25), via the accessible-part / distinguished-classes argument (`Acc = least fixed point`, progressivity, `W`-sets). This is the part that establishes the notation system is a genuine well-order in a weak metatheory.

### Cut-elimination

Two distinct cut-elimination engines appear, and the notes lean on the same *shape* the Goodstein box uses for its Thm56 monument:
- **Predicative cut-elimination** (Lemma 1.21): below `Ω`, raise the height by a Veblen-function `θ_c(a)` to drop the cut-rank by `c`. The Veblen-tower bookkeeping (`θ₁(a)=ω^a`, `θ_{ωᶜ}(a)=φ_c(a)`) generalizes the ε₀-level `ω`-tower descent.
- **Collapsing** (Thm 1.22): handles cuts of rank `≥Ω` by Mostowski-collapsing the derivation height through `ψ_Ω`. This is the **impredicative** ingredient with no analog below Bachmann-Howard.

For §2+ (KPΠ₃/Π₄/Π_N), cut-elimination is interleaved with **reflection-rule elimination** `(rfl_{Π_N})` and "stationary collapsing" (collapsing one derivation into a stationary *family* of derivations), requiring the large-cardinal apparatus.

### ε₀ and the fast-growing / Hardy hierarchy

- **ε₀** is present only as scaffolding inside the larger ordinals: `ε_{Ω+1}` and `ε_{𝕂+1}` are the *upper indices* of the collapsing functions (the domain of `ψ_Ω`, `ψ_𝕂`). The notes never isolate `ε₀ = ψ_Ω(...)` as the PA ordinal, never define Cantor normal form at the ε₀ level as a standalone object, and never discuss `PA ⊬ TI(ε₀)`. (Contrast: the box's Thm56 `peano_not_proves_TI` is exactly that ε₀-level statement; Arai's §1 is the next storey up.)
- **Hardy / fast-growing hierarchy, Wainer classification, provably-total / provably-recursive functions: ABSENT.** The notes measure strength purely via **proof-theoretic ordinals and Π¹₁-consequences** (`|T|`, Def 0.2), not via fast-growing function hierarchies. There is no `H_α`/`F_α` growth-rate hierarchy (the `H_γ[Θ]` symbol here is an operator/Skolem-hull, not a Hardy function), no statement of "the provably-total functions of `T` are exactly those `<` some level," and no Wainer-style classification theorem. The closest the notes come is the abstract "Π¹₁-strength" framing and the well-foundedness/`TI` machinery — none of it growth-rate-shaped.

---

## Relevance to the Goodstein-independence expedition

### Honest bottom line: thin for *both* routes, modestly useful as a worked exemplar of the method.

The expedition lives at the **ε₀ / PA** level (Goodstein ⇒ `PRWO(ε₀)`, `PA ⊬ TI(ε₀)`, internalized in `IΣ₁`). Arai's notes start one full storey higher (KPω → Bachmann-Howard) and climb to large cardinals. So the notes are **the right *method*, the wrong *altitude*.** They will not give a drop-in for any current crux. Two specific questions the task asked:

#### Q1 — Alternative ordinal-assignment exposition to cross-check the box's `idg`/`iõ`/`iord` (the `InternalONote`/`InternalNadd`/`InternalTower` kernel = Buchholz `o(d)=ω_{dg(d)}(õ(d))`)?

**Limited.** The box's ε₀ ordinal-assignment-on-derivations follows **Buchholz's *On Gentzen's first consistency proof*** (see `buchholz-on-gentzens-first-consistency-proof.md`), where `o(d)=ω_{dg(d)}(õ(d))` is an `ω`-tower over a natural-sum pre-ordinal — a **PA/ε₀-level, derivation-indexed** assignment. Arai's notes use a *different* style of ordinal assignment: **height-indexed operator-controlled derivations** `H_γ[Θ] ⊢^a_b Γ`, where the "ordinal" is the derivation *height* `a` (an `OT(Ω)`-term), not a recursively-defined `o(d)` on a finitary proof tree. The two are cousins (both are Buchholz-lineage, both use Veblen `φ` and natural sum), but Arai does **not** reproduce the `dg`/`õ`/`o(d)` recursion the box internalizes, so it is a *weak* cross-check at best.
- **What it *can* cross-check:** the **Veblen / natural-sum / `ω`-tower arithmetic** that `InternalNadd` (Hessenberg `#`, F1–F4) and `InternalTower` (`ω_n(α)`) formalize. Arai's `H_α` hull arithmetic, `θ_c`/`φ` Veblen iterates (Lemma 1.21), and the `ω_m(Ω+1)` towers (Thm 1.24) exercise exactly that algebra at a higher base. If a sign/monotonicity question arises in the box's `icmp_iotower_mono` or `nadd` order theory, Arai's predicative-cut-elimination height bookkeeping is an independent worked instance of the same `θ`/`φ`/`#` laws.
- **What it does *not* help with:** the *derivation-indexed* `o(d)` recursion, the `dg(d)` degree, or the descent `o(d[n])<o(d)` — those are Buchholz-1936/Gentzen territory, covered by the Buchholz note, not here.

#### Q2 — Does Arai state Wainer's classification cleanly for a growth-rate (Route B) route?

**No.** There is **no Wainer classification, no Hardy hierarchy, no fast-growing hierarchy, no provably-total-function theorem** anywhere in these notes. Route B (Goodstein via slow-growing/Hardy hierarchy; `Fairtlough–Wainer 1998` is the canonical reference in SOURCES.md) gets **nothing** from Arai. The notes' notion of "strength" is the proof-theoretic ordinal / Π¹₁-consequence framing (Def 0.2), which is *adjacent* to but not the same as a growth-rate classification, and Arai never crosses over to functions. The box's existing Route-B substrate (`InternalGrz`/`Grzegorczyk`/`IIter`, Rathjen §3 Cor 3.4) is already the right machinery; Arai adds nothing to it.

### Where Arai *is* genuinely useful

- **As a structural exemplar for the Thm56 monument.** The box's banked `peano_not_proves_TI` is built from "embedding + cut-elimination + boundedness (Thm 5.4) + Hardy/Domination." Arai §1 is a textbook-clean instance of *exactly* that pipeline (Embedding 1.20 → Predicative Cut-elimination 1.21 → Boundedness 1.19 → Collapsing 1.22 → Truth 1.23 → well-foundedness 1.25/1.26). If the Thm56 apparatus ever needs a sanity reference for the *shape* of operator-controlled cut-elimination and the boundedness lemma, §1 is the cleanest modern statement (more streamlined than Buchholz '92, which it modernizes).
- **As the "next storey" map.** If the expedition or a HARVEST spin-off ever wants to generalize beyond ε₀ (e.g. an independence result for a `KPω`-level theory, or contributing a Bachmann-Howard `OT` to Foundation/gallery), these notes are the canonical entry point and the `OT(Ω)` + `EA`-provable-linearity (Prop 1.9) + `ID`-provable-well-foundedness (Thm 1.25) recipe is directly reusable.
- **Provenance correction for SOURCES.md.** The catalog line "ordinal notations, infinitary derivations, cut-elimination, proof-theoretic ordinals … ε₀ girder + encoding" should be qualified: the notes are **KPω-and-above (Bachmann-Howard → large cardinals)**, not ε₀/PA. Re-tag as a *method exemplar / next-storey reference*, not a girder-phase source.

---

## Verdict (most reusable content)

Arai's most reusable asset for either route is **§1's worked KPω pipeline as a clean modern exemplar of the operator-controlled-derivation method** — Embedding (1.20) → Predicative Cut-elimination (1.21, the Veblen `θ_c` height-for-cut-rank trade) → Boundedness (1.19) → Collapsing (1.22) → Truth (1.23) → `ID`-provable well-foundedness of `OT(Ω)` (Thms 1.25/1.26) — which is the exact *shape* of the box's banked Thm56 (`PA ⊬ TI(ε₀)`) monument, one storey up. **For the active cruxes it is thin:** it offers only a *weak, height-indexed* cross-check on the box's derivation-indexed Buchholz `o(d)` assignment (the real source is `buchholz-on-gentzens-first-consistency-proof.md`), it covers ε₀ only as scaffolding inside Bachmann-Howard, and it contains **no Wainer classification, Hardy hierarchy, or fast-growing/provably-total material at all** — so it gives Route B nothing. Recommend keeping it as a method-exemplar / "next-storey" reference (and re-tagging the over-optimistic SOURCES.md line), not as a girder-phase or Route-B working source.
