# Lap 86 — the gating criticality question RESOLVED (in-kernel): `red` needs the 5.2 dispatch

**Operator objective:** discharge `peano_not_proves_goodstein` axiom-free. Sole blocker = crux-2 =
`redSound` (internalized cut-elimination). The lap-85 handoff flagged ONE gating decision (its NEXT
priority 2): *does a `ZDerivesEmpty` K-chain always have a critical redex?* — "decide this first, it
gates whether `red` is complete." This lap answers it, with an in-kernel witness.

## The answer: **NO.** The critical-only `red` is provably incomplete.

Buchholz Def 3.2 case 5 (the chain-rule reduction) splits into THREE sub-cases:
- **5.1 critical** (`∀ i ≤ j₀, tp(dᵢ) ⋪ Π`): cut reduction via Lemma 3.1's redex pair →
  `K^{r−1}_Π⟨d{0}, d{1}⟩`. **This is the only case the repo's `red`/`iR2` implement** (`iRcritG` /
  `iCritReduct`, always fired on tag 4).
- **5.2.1 sub-critical splice** (minimal `i ≤ j₀` with `tp(dᵢ) ◁ Π`, and `dᵢ` critical):
  `tp(d) := Rep`, `d[0] := K^{r'}_Π(i/dᵢ{0}, dᵢ{1})` — splice `dᵢ`'s two halves into the chain.
- **5.2.2 non-critical replace** (`dᵢ` not critical): `tp(d) := tp(dᵢ)`,
  `d[n] := K^r_{tp(dᵢ)(Π,n)}(i/dᵢ[n])` — replace premise `i` by its own reduct.

**Why the critical-only reduct cannot iterate.** The 5.1 reduct `red(K^r_Π …) = K^{r−1}_Π⟨d{0}, d{1}⟩`
(`iCritReductG`, `InternalZ.lean:3068`) is a chain whose distinguished `⊥`-half
`d{1} = K_{A(d),Θ→D} ds1` is a `K`-rule. So `tp(d{1}) = isymRep` (`tp_zK`), and `Rep ◁ Π` for ANY
conclusion (`iperm_isymRep`). Therefore the reduct is **non-critical**: `zKCritical (fstIdx (red d))
(zKseq (red d))` FAILS (at premise index 1). A contradiction derivation's reduct is non-critical after
the very first step, so the critical-only `red` has nothing valid to do at step 2.

**In-kernel witnesses (`InternalZ.lean`, after `red_zK`; axiom-clean `[propext, choice, Quot.sound]`):**
- `not_zKCritical_iCritReductG` — the genuine critical reduct object is non-critical.
- `not_zKCritical_iRcritG` — corollary on `iRcritG`.
- `not_zKCritical_red_zK : ¬ zKCritical (fstIdx (red (zK s r ds))) (zKseq (red (zK s r ds)))` — the
  headline: `red` of a K-chain is a non-critical K-chain.

## Consequence for the plan — two corrections to the lap-85 handoff

1. **The lap-85 priority-1 bridge `iord (red x) = iord (iR2 x)` is necessary but NOT sufficient.** It
   would let descent-on-`red` inherit descent-on-`iR2` — but `iord_descent_iR2_of_ZDerivesEmpty` /
   `iord_iR2_iterate_descends` themselves carry an explicit `zKCritical` hypothesis (lap-85 re-point),
   and `not_zKCritical_red_zK` shows that hypothesis is **unsatisfiable on the iterates**. The descent
   ASSEMBLY is gated on a false premise. So the bridge does not close `iord_descent_red`.

2. **`red`'s tag-4 case must DISPATCH** (Buchholz 5.1 / 5.2.1 / 5.2.2), not always `iRcritG`. The
   ordinal descent for each target is already banked (lap-82 survey): `iord_descent_iRcrit_of_chain`
   (5.1), `iord_descent_iSpliceEnd` (5.2.1), `iord_descent_iCritAux` (5.2.2). The genuinely new content
   is (a) the DISPATCH definition in `iRNextG`'s tag-4 branch (a criticality test + bounded redex
   search), and (b) `redSound` (validity, `zKValidF`) for the 5.2 reducts.

## Next-lap attack plan (corrected `red` — the 5.2 dispatch)

The tag-4 branch of `iRNextG` (`InternalZ.lean:4842`) currently is `iRcritG d ρ` unconditionally.
Replace by the Def-3.2 case 5 dispatch:

- **Decidability prerequisite.** `zKCritical s ds = ∀ i < lh ds, ¬ iperm (tp (znth ds i)) s` is bounded
  (Δ₀ over the `tp`/`iperm` Δ₀ pieces) — establish `zKCritical` (or its `i ≤ j₀` restriction) as a
  Δ₁/decidable predicate so `iRNextG` can branch on it. NOTE Buchholz's criticality is `∀ i ≤ j₀`, the
  repo's `zKCritical` is `∀ i < lh ds`; reconcile (the `j₀`-restricted form is the faithful one — see
  `isChainInf`'s `j₀`).
- **5.2.1 splice** (`iSpliceEnd` / `iord_descent_iSpliceEnd` banked): `red d =
  zK s (max (irk A(dᵢ)) r) (replace ds[i] by dᵢ's two halves)`. Needs the genuine splice OBJECT
  (analogue of `iCritReductG` but in-place at index `i`) + its `zKValidF`.
- **5.2.2 replace** (`iCritAux` / `iord_descent_iCritAux` banked; `zKValidF_seqUpdate` for validity):
  `red d = zK (tp(dᵢ)(s,n)) r (seqUpdate ds i (red dᵢ))`. The conclusion's succedent changes by
  `tp(dᵢ)(s,n)` — wire the reduced-sequent op.
- **`redSound`** then = `zDerivation_induction` with the tag-4 case split into 5.1 / 5.2.1 / 5.2.2,
  each producing a `zKValidF` chain. The descent `iord_descent_red` becomes UNCONDITIONAL (no `hcrit`).

## Why this is the unblock, not a setback

The lap-84/85 `red`/`iRcritG`/`ZDerivation_iRcritG_of` work is NOT wasted — it IS the 5.1 case, fully
needed. The finding only shows 5.1 is one of three branches. Resolving the gating question now (with a
kernel proof) prevents future laps from building `redSound`/`iord_descent_red` on the broken
critical-only `red` and chasing the unsatisfiable `hcrit`. The corrected target — a 3-way dispatching
`red` whose descent is banked and whose only new content is 5.2 validity — is the precise remaining wall.
