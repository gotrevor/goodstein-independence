# Crux 2 — Buchholz `ord`/`R` grounded from the source (lap 58)

**Source.** `papers/buchholz-on-gentzens-first-consistency-proof.pdf` (W. Buchholz, *On Gentzen's first
consistency proof for arithmetic*, 2014), extracted to `scratchpad/buchholz-gentzen.txt`. All formulas
below are **verbatim from §§2–5** (not reconstructed). This grounds the C1–C5 milestones for discharging
`GentzenCon.gentzen_descent_of_inconsistent` and prevents confabulating the ordinal assignment.

## The consistency argument (Buchholz §2, the shape crux 2 internalizes)
- Buchholz works in a **finitary** proof system **Z** for first-order arithmetic with a *repetition* rule
  `Rep` and *chain* rules `K^r`, simulating cut-free ω-arithmetic finitely.
- To each closed Z-derivation `d` he attaches `tp(d)` (an inference/reduction-step symbol) and a family
  `(d[n])_{n ∈ |tp(d)|}` with **Thm 2.1**: `d[n] ⊢ tp(d)(End(d), n)`.
- **Key (intro, lines 12–18):** if `d ⊢ ⊥` (derives the empty/false-minimal sequent), then `tp(d)` can
  only be a `Rep`, so `d[0] ⊢ ⊥` again — the reduction never terminates on a ⊥-derivation.
- **§4 ordinal `o(d) < ε₀`** with **Thm 4.2**: `o(d[n]) < o(d)` for all `n ∈ |tp(d)|`. So a ⊥-derivation
  gives the infinite primrec descent `n ↦ o(d^{[n]})` below ε₀ ⟹ contradicts PRWO(ε₀) ⟹ Con. ∎

## §4 ordinal assignment (VERBATIM — the C1 target)
Auxiliary: `dg(d) < ω` (degree), `õ(d) < ε₀` (pre-ordinal), `# ` = natural (Hessenberg) sum, `rk` = formula
rank. Atomic `d`: see §5. Otherwise:

```
dg(d) :=
  dg(d0)                                   if d = I^a_∀xF d0  or  d = I_¬A d0
  max{dg(d0)-1, dg(d1)-1, r}               if d = Ind^{a,t}_F d0 d1,   r := rk(F)
  max{dg(d0)-1, …, dg(dl)-1, r}            if d = K^r_Π d0 … dl

õ(d) :=
  õ(d0) + 1                                if d = I^a_∀xF d0  or  d = I_¬A d0
  ω^{õ(d0)} # ω^{õ(d1)+1}                  if d = Ind^{a,t}_F d0 d1
  ω^{õ(d0)} # … # ω^{õ(dl)}               if d = K^r_Π d0 … dl

o(d) := ω_{dg(d)}(õ(d)),   where  ω_0(α) := α,   ω_{n+1}(α) := ω^{ω_n(α)}.
```
(`ω_{dg(d)}` is the dg(d)-fold ω-exponential tower over the pre-ordinal — this is the [KB81] assignment.)

## §3 system-Z inference rules (the C1 recursion domain)
1. atomic (axioms, §5)
2. `I^a_∀xF d0 ⊢ Γ→∀xF`   from `d0 ⊢ Γ→F(a)`, `a ∉ FV`
3. `I_¬A d0 ⊢ Γ→¬A`        from `d0 ⊢ A,Γ→⊥`
4. `Ind^{a,t}_F d0 d1 ⊢ Γ→F(t)` from `d0 ⊢ Γ→F(0)`, `d1 ⊢ F(a),Γ→F(Sa)`
5. `K^r_Π d0 … dl ⊢ Π`     chain rule of rank `r` (the cut/structural workhorse; `tp`/`d[n]` via Def 3.2)
`tp(d)`/`d[n]` (Def 3.2): rule 2 ↦ `R∀xF`, `d[n]=d0(a/n)`; rule 3 ↦ `R¬A`, `d[0]=d0`; rule 4 ↦ `Rep`,
`d[0]=K^r d0 d1(a/0)…d1(a/k-1)`; rule 5 ↦ critical/non-critical case split (Lemma 3.1).

## ⚠️ LOAD-BEARING ARCHITECTURE FINDING (lap 58) — calculus mismatch
**Buchholz's `ord`/`R` are defined over HIS system Z, NOT Foundation's arithmetized calculus.** Foundation's
`Theory.Derivation : V → Prop` (`Bootstrapping/Syntax/Proof/Basic.lean`) is a **Tait-style** calculus with
`axL`/`verumIntro`/`andIntro`/`orIntro`/`allIntro`/`exsIntro`/`wkRule`/`shiftRule`/**`cutRule`**/`axm` — there
is no `K^r` chain rule, no `Ind` rule, no `Rep`/`tp(d)`/`d[n]` ω-simulation. Foundation's `Hauptsatz.lean` is
**meta-level** (Type-level `⊢ᵀ Γ` realizability/`Forces` cut-elimination, NO arithmetized ordinals) —
confirmed no shortcut (consistent with laps 50/53). Consequences for the formalization route:

- **Route A (port Z).** Arithmetize system Z (rules 2–5 + atomic) as a `V → Prop` à la `Theory.Derivation`,
  define `dg`/`õ`/`o` and `R`(=`d ↦ d[·]`) by recursion on it, prove Thm 4.2 (`o` descends). Then a
  **translation** `𝗣𝗔-Tait-derivation of ⊥ → Z-derivation of ⊥` bridges to Foundation's calculus. The
  translation must turn PA's induction *axioms* (`axm` leaves) into Z's `Ind` rule and cuts into `K^r`.
  Faithful to the source; the translation is the new work.
- **Route B (Schütte assignment on Tait+cut directly).** Assign `o(d)` to Foundation's Tait derivations via
  the standard (cut-rank, height) ω-tower and let `R` = one topmost-maximal-cut reduction. BUT PA-induction
  is finitary here only because induction is an *axiom schema* (`axm`), so plain finite cut-elimination
  does NOT terminate to cut-free (the `axm` leaves block it) — the ω-rule/`Ind` handling Buchholz's Z exists
  precisely to absorb. So Route B still needs an ω-arithmetic embedding step. **Route A is cleaner/closer to
  the source.**

**Recommendation: Route A.** The C1–C5 milestones (GentzenCon footer) refine to:
- **C0 (NEW, prerequisite)** — arithmetize system Z: `ZDerivation : V → Prop` (Fixpoint.Construction, mirror
  of `Theory.Derivation`), with coded constructors `zI∀`/`zI¬`/`zInd`/`zK` + atomic, `fstIdx`/subterm-`<`
  lemmas. Plus `rk` (formula rank, primrec on coded formulas — Foundation may already have formula
  complexity) and the `tp`/`d[·]` operator.
- **C1** — `iord`/`idg`/`iõ : V → V` by `<`-strong-recursion on `ZDerivation` codes (needs a
  recursion-on-coded-derivations combinator — Foundation has `Language.TermRec.Construction` for *terms*
  (`Term/Basic.lean:301`); build the derivation analog, or define each as a `Fixpoint` graph). Uses repo
  `InternalONote`: `#`(natural sum — CHECK it exists, may need building), `ω^`(`ocOadd`/`iomega`?), the
  ω-tower `ω_{n}`.
- **C2** — `iR := d ↦ d[0]` (the reduction = `tp`/`d[n]` operator); `iR` preserves ⊥-derivations (Buchholz
  intro: ⊥ ⟹ `tp = Rep` ⟹ `d[0] ⊢ ⊥`).
- **C3** — Thm 4.2 internalized: `ZDerivation d → derives-⊥ → icmp (iord (iR d)) (iord d) = 0` (via Lemma 4.1
  `dg`/`õ` monotonicity, the deep induction-on-build-up). THE core.
- **C4** — `isNF (iord d) ∧ iord d ≠ 0` for ⊥-derivations.
- **C5** — `gentzenDescentφ` = graph of `n ↦ iord (iR^[n] d₀)`; `d₀ := μ d. ZDerivationOf d ⊥` obtained by
  translating the Foundation `𝗣𝗔.Proof _ ⌜⊥⌝` witness (Route-A translation).

This is multi-lap. C0 (arithmetize Z) + the InternalONote natural-sum/ω-tower gaps are the first concrete,
checkable, source-faithful targets — independent of the deep C3 induction.
