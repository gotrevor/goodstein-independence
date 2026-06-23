# ANALYSIS — lap 37: the `hbound` order-reflection wall faces `prec`-opacity (wall-B redux), and the route out

## TL;DR

The lone remaining wall `hbound` (in `no_min_descent_absurd_of_goodstein`, `DescentSemantic.lean`)
needs the Rathjen §3 slow-down run **inside a model `M ⊧ paLX`** on the `X`-definable `≺`-descent.
Two halves were re-scoped this lap:

- **Base-change / evaluation half — now substrate-direct** (lap-37 brick `evalNat_succ_base`):
  `evalNat (b+1) o = bump (b+1) (evalNat b o)` for `Canon b o`, so the internal `ibump` substrate
  realizes `T̂`'s base-bump in `M` without coding ONote evaluation separately.
- **Order-reflection half — the genuine wall, and it faces `prec`-opacity.** The descent is
  `Mlt f y x = M ⊧ precφ(y,x)` where `precφ := codeOfREPred₂ (fun a b ↦ natCode a < natCode b)`
  (`SeamDefinability.lean:59`) — Foundation's **opaque** `Classical.epsilon` r.e.-code blob, the
  SAME opacity that was **wall B** (dissolved lap 36 for `goodsteinSentence`). And `natCode :=
  (Denumerable.eqv NONote).symm` (`Epsilon0Complete.lean:233`) is an **arbitrary** enumeration.

So to run the slow-down I must read the **CNF of each descent element** `natCode(aₙ)`, but
`natCode⁻¹` is an opaque/arbitrary decode. This is the irreducible obstruction.

## Why the CNF is genuinely needed (grounded in Rathjen 2014 §3, on disk)

Read `papers/rathjen-2014-goodsteins-theorem-revisited.pdf` §3 this lap. The construction:

- **Cor 3.4** slows a strictly-descending `ε₀ > β₀ > β₁ > …` to a *slow* one
  `|αᵢ| ≤ K·(i+1)`, via `αⱼ = ω^ω·βₙ + g(n,m)` (explicit ordinal-CNF addition/mult, Def 3.1).
- **Thm 3.5** turns a slow descent into `ε₀ > β₀ > … ` with `C(βᵣ) ≤ r+1`, via
  `βⱼ := Σ_{i<K-j} ω_{s-i}` (head) and `β_{K(n+1)+i} := ω·αₙ + (K-i)` (tail), using the tower
  `ω₀=1, ωₙ₊₁=ω^{ωₙ}` and `C(ω·α) ≤ C(α)+1`.
- **Lemma 3.6** is inequality (6): `mₖ ≥ T̂^{k+2}_ω(βₖ)`, hence `mₖ ≠ 0` — **already in the repo**
  (`DescentCore.ineq6_step`/`lemma36_nonterminating`, ONote-level).

Every step manipulates the **complete Cantor normal form** of the descent elements (`ω·αₙ`,
`ω^ω·βₙ`, `C(·)`, `T̂(·)`). The bare order relation `≺` is not enough — the CNF structure is
essential. ⟹ the descent elements must be decodable to CNF inside `M`.

**Rathjen's own route is Route A** (`PA + GS ⊢ PRWO(ε₀)`, Cor 3.7; descents are *primitive
recursive*). The repo deliberately runs the *model-internal* analogue (lap-30 completeness route)
because `peano_not_proves_TI` is about the **free-`X`** `TI prec`, which primrec-`PRWO` cannot
refute (the lap-24 free-`X` correction). So the descent here is `X`-definable, not primrec — but
it still lives in `M`'s `precφ`-order, hence the opacity.

## The route out — (b) transparent HFS-CNF coding (recommended)

Three logically-possible routes; (b) is the principled one.

- **(a) Bridge the opaque `precφ` to a decode inside `M`.** Prove
  `𝗜𝚺₁ ⊢ precφ(a,b) ↔ icmp(decode a, decode b)`. Requires internalizing the `natCode` algorithm
  (an arbitrary `Denumerable.eqv` inverse) — no natural arithmetization. **Reject** (same dead-end
  shape as the abandoned wall-B `ON-LINE-REQUEST`).

- **(b) Refactor the order onto a TRANSPARENT coding.** Build internal ONote **CNF codes** as
  nested HFS pairs (`0 ↦ 0`, `oadd e n r ↦ ⟪⟪ec,n⟫,rc⟫+1`), so a code *is* its CNF and decode is
  projection. Define `natCodeT : ℕ ≃ NONote` from this coding and a transparent `𝚺₁`/`𝚫₁`
  comparison formula `precT`. Re-wire the seam (`SeamDefinability`) + F (`Epsilon0Complete`:
  `epsilon0_le_orderType_ltPull` is stated for **any** `e : ℕ ≃ NONote`, so the order-type half
  transfers; the F-φ computability is *easier* for the transparent CNF compare than for `natCode`).
  Then the descent is directly CNF-coded, internal `evalNat`/`C`/order-reflection apply, and the
  slow-down runs. **This is the route.** Cost: a multi-lap refactor of the (axiom-clean) girder's
  order argument — but `peano_not_proves_TI`'s structure (embedding + boundedness + cut-elim) is
  order-agnostic; only `precφ`/`natCode`/F-φ/seam touch the coding.

- **(c) Keep `natCode`, but prove `natCode`'s order = a transparent CNF compare externally** and
  internalize only that. Hybrid; still needs internal CNF codes, so subsumed by (b)'s foundation.

**Shared foundation for (b)/(c): internal ONote CNF codes in `V ⊧ₘ* 𝗜𝚺₁`** — the next subproject:
1. Coding + `isONoteCode` predicate (HFS `⟪,⟫`/`π₁`/`π₂`/`fstIdx`/`sndIdx`; bound via
   `le_pair_left`/`le_pair_right`). Recursion = course-of-values table over the code value (subterm
   codes `<` the code by the pairing bound), à la `InternalBump.ibumpTable`.
2. `iC : V → V` (max coefficient), `ievalNat : V → V → V` (base, code → value) — table recursions;
   `ievalNat` matches `evalNat_succ_base`'s `ibump` base-bump on standard inputs.
3. `icmp : V → V → V` CNF comparison (`𝚫₁`), with internal `evalNat_lt_iff` (order-reflection) —
   the piece the descent needs.
4. CNF addition/mult (`Def 3.1`), tower `ωₙ`, `iC(ω·α) ≤ iC(α)+1` — the Thm 3.5 toolkit, internal.
5. The slow-down `βₖ` from the `X`-descent (`descent_seq_exists`), `C(βₖ)≤k+1`, then `hbound`.

This is the genuine multi-year-class heart (re-formalizing ε₀ ordinal notations + Rathjen §3 inside
`IΣ₁`). Each lap = one brick. Lap-37 banked the numeric substrate bricks (`ilog_mono`,
`evalNat_succ_base`) and dispatched `ibump_mono` to Aristotle (UUID `7c8bb0e8`).

## Anti-fraud note

`precφ`/`natCode`/`prec` are NOT in the operator's LOCK list (`Defs.lean`, `Bridge.lean` RHS,
`goodsteinTerminates`, headline `sorry`). Route (b) is a sanctioned refactor — BUT it re-touches the
proven `peano_not_proves_TI`; every change must be re-validated with `#print axioms` (girder must
stay `[propext, choice, Quot.sound, native_decide]`-clean). Do NOT silently weaken F or the seam.
