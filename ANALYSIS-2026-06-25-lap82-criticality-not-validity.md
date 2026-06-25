# Lap 82 — crux-2 root cause: criticality ≠ chain-validity (`zKValid` over-constrained)

**Operator redirect (lap 82):** Front 2 (`PA_delta1Definable`) moved to a parallel box — accept it as a
tracked rest-point, STOP touching `PADelta1.lean`. Drive **crux 2 (`RedSound`)** only, using Buchholz
(both papers, read in full and validated against the code here — not trusted blind).

## The diagnosis (validated in-kernel this lap)

`RedSound : ∀ d, ZDerivesEmpty d → ZDerivation (iR2 d)` is the sole remaining `InternalZ` obligation. The
repo had *proven* (`not_zKValid_iCritReduct`) that the ordinal-faithful reduct `iR2` can **never** be a
`ZDerivation`, because the critical reduct `iCritReduct` is a chain `zK Π (r−1) ⟨d{0}, d{1}⟩` whose
premises `d{0} = d{1} = iCritAux … = zK …` are themselves chains, hence `tp = isymRep` (`tp_zK`),
permissible for every conclusion (`iperm_isymRep`). `zKValid`'s **criticality conjunct**
`(∀ i < lh ds, ¬ iperm (tp (znth ds i)) s)` demands every premise be NON-permissible for the conclusion —
so the reduct fails validity.

**Root cause (Buchholz, validated):** the criticality conjunct does NOT belong in chain-validity.

- Buchholz's `K^r_Π d₀…dₗ ⊢ Π` (short paper §3 clause 5; long notes §6 Thm 6.2) is valid iff
  `(Π₀…Πₗ)/Π` is a *chain rule inference of rank r*: ∃ j₀ ≤ l with `A_{j₀} ∈ {C,⊥}`, threading
  `Γᵢ ⊆ Γ,A₀…A_{i−1}` (i ≤ j₀), and `rk(Aᵢ) ≤ r` (i < j₀). **No criticality.**
- This is *exactly* the repo's `isChainInf s r ds` (`InternalZ.lean:1066`). So Buchholz-validity =
  `isChainInf` + premises valid (the `ZPhi` recursion) + formula-hood bookkeeping = the repo's
  `zKValidF` (defined this lap). The criticality conjunct is the lone spurious extra.
- *Criticality* (`d` is critical iff `∀ i ≤ j₀, tp(dᵢ) ⋪ Π`, Def 3.2 case 5) is a property the
  **reduction** uses to choose its clause (5.1 critical vs 5.2 non-critical), NOT a validity condition.
  Baking it into `zKValid` forces `ZDerivation` to be *only-critical* chains — false to Buchholz, and
  the precise reason `RedSound`-on-`iR2` is false. The reduct was "built ordinal-first" (operator).

**Key structural fact (both papers agree):** validity (short Thm 3.4(b) = long §6-D₁ / Thm 6.2 a,b) and
ordinal descent (short Lemma 4.1/Thm 4.2 = long Thm 6.2(c)/Lemma 6.3) are **two SEPARATE inductions over
the same reduct**. There is no "ordinal-faithful vs derivation-valid" tension — only a missing parallel
validity invariant. Buchholz's `d ↦ d[n]` (Def 3.2) / `red` (long Thm 6.6) is genuine-valid *by
construction*, with the recombination `K^{r−1}_Π d{0} d{1}` certified by Thm 3.4(a)
(`d{0} ⊢ Π·A(d)`, `d{1} ⊢ A(d),Π`, `rk(A(d)) < r`) and a real R/L cut-redex guaranteed by Lemma 3.1
(= the repo's `inference_critical_pair`).

## This lap's banked step (axiom-clean, green)

`InternalZ.lean` after `zKValid_definable`:
- `zKCritical s ds := ∀ i < lh ds, ¬ iperm (tp (znth ds i)) s` — the decoupled criticality.
- `zKValidF s r ds` — faithful validity = `zKValid` minus criticality (= `isChainInf` + own-permissibility
  + §5 formula-hood).
- `zKValid_iff_zKValidF_and_zKCritical : zKValid ↔ zKValidF ∧ zKCritical` (in-kernel confirmation that
  criticality is a *separable* conjunct #3 — the build accepting this split IS the validation).
- `zKValidF_of_zKValid`.

These are the load-bearing bridge for the swap below; nothing existing changed, so build stays green.

## The redesign plan (multi-lap; hardest-first)

1. **Re-point `ZPhi`'s `zK` disjunct** (`InternalZ.lean:3644,3691`) from `zKValid` → `zKValidF`. This
   weakens `ZDerivation` to Buchholz's genuine `⊢`. Producers of `zKValid` get easier; the lone hard
   consumer is the descent proof (`iord_descent_*`, ~4657) which destructures `hnperm0` (criticality).
2. **Repair the K-descent with the critical/non-critical split** (Buchholz Lemma 4.1):
   - *critical* (`zKCritical` holds — recover it at the reduction site, since `iR2`/the reduct only fires
     the critical clause when case 5.1 applies): existing redex-finder route
     (`inference_critical_pair_of_chain`) — already in place, now gated on `zKCritical` as a hypothesis
     rather than read from validity.
   - *non-critical* (Def 3.2 case 5.2): NEW. `tp(d) := tp(dᵢ)`, `d[n] := K^r_{tp(d)(Π,n)}(i/dᵢ[n])`;
     descent 4.1(a) `õ(d[n]) < õ(d)` because `õ` is the natural sum `#ᵢ ω^{õ(dᵢ)}` and one summand's
     exponent strictly drops (IH `õ(dᵢ[n]) < õ(dᵢ)`). The reusable ordinal lemma to build:
     **natural-sum strict monotonicity** in one summand's `ω`-exponent, over the internal `iord`/`õ`.
3. **Build the genuine reduct** following Def 3.2 case 5 (critical 5.1 / sub-critical 5.2.1 / non-critical
   5.2.2). The long notes' `red` (Thm 6.6) is the primitive-recursive, IΣ₁-portable form; align
   `h[ι] ↔ d[n]` (the long notes use Z\* notations, the repo uses coded `d`). Do NOT retrofit `iR2`; if
   `iR2` can't be made to dispatch case 5.2, define a new reduct and re-point `RedSound` + descent onto it.
4. **Prove `RedSound`** as Thm 3.4(b)/D₁: the parallel validity invariant, by the same recursion that
   proves descent — carrying `zKValidF` (not the old over-strong `zKValid`).

Fallback descent mechanism if the degree-drop stays intractable: Siders' Howard vector assignment
(`papers/siders-gentzen-consistency-proofs-arithmetic.md`) — HA/intuitionistic, cross-check only.

## Why this is the unblock, not a reshuffle

`not_zKValid_iCritReduct` is *not refuted* — it correctly says the reduct fails the OLD validity. The
decomposition shows the failure is **entirely** on the spurious `zKCritical` factor: `zKValidF` (the part
that is Buchholz-faithful) is what the reduct must — and, per Thm 3.4(a), does — satisfy. Step 1 makes
`ZDerivation` ask only for `zKValidF`, removing the false obstruction. The remaining work (steps 2–4) is
genuine math (non-critical descent + the Def-3.2 reduct), exactly Buchholz's content, no longer fighting a
self-inflicted constraint.
