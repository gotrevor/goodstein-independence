# Lap 94 — the `iRK` splice dispatch is Buchholz-UNFAITHFUL (in-kernel obstruction); `hseltag` is FALSE

## The finding (verified in-kernel: `not_permIdx_lt_zKseq_zAtom`, `Zsubst.lean`)

`ZRegular_red_zK` (the zK case of "red preserves ZRegular") was reduced last lap to a single leaf
`hseltag`: in the 5.2.1 SPLICE branch, the selected premise `dᵢ = znth ds (permIdx (zK s r ds))` is a
chain (`zTag dᵢ = 4`). **`hseltag` is false**, and the in-kernel witness pins exactly why.

`iRK`'s inner dispatch (`InternalZ.lean:6108`) is

```
if permIdx dᵢ < lh (zKseq dᵢ) then iRKr (replace, 5.2.2) else iRKs (splice, 5.2.1)
```

For a NON-chain `dᵢ` (atom/I-rule/axiom), `zKseq dᵢ` is junk of length `0`:
- `zKseq (zAtom s) = π₂ (zRest (zAtom s)) = π₂ 0 = 0` (`zKseq_zAtom`), so `lh (zKseq (zAtom s)) = 0`
  (`lh_zKseq_zAtom`).
- Hence `permIdx (zAtom s) < lh (zKseq (zAtom s))` is `0 < 0 = false` (`not_permIdx_lt_zKseq_zAtom`),
  so the dispatch takes the **SPLICE branch by default** — even though `dᵢ` is an atom, not a chain.

So the splice branch fires for EVERY non-chain selected premise (atoms, I-rules, axioms — all have
`lh (zKseq) = 0`), and then `red dᵢ`'s "halves" `znth (zKseq (red dᵢ)) {0,1}` are junk. The branch
condition `¬ permIdx dᵢ < lh (zKseq dᵢ)` does NOT imply `dᵢ` is a chain — it is *satisfied* by every
non-chain node. This is the regularity analog of the lap-69/90 `not_zKValid_iCritReduct` obstruction.

## Why this matters — same wall for both halves of `redSound`

- **Regularity half** (`ZRegular_red_zK`'s `hseltag`): cannot be closed against the current `iRK`.
- **Validity half** (`ZDerivation_red_zK_splice`, `Crux2Blueprint` sorry): needs the SAME `zTag dᵢ = 4`
  to read genuine reduct-halves; equally false.

Both block at the unfaithful splice dispatch. This is the concrete, in-kernel form of the lap-90 route-B
finding (discrepancy 2: "`dᵢ` need not be a chain"). Note it is NOT cured by the ⊥-orbit / Cor 2.1: a
selected `Rep` premise has `tp = isymRep` = tag ∈ {0,3,4} (atom/Ind/chain), and atoms/Ind are Rep too, so
even on the ⊥-orbit the selected premise can be an atom ⟹ splice mis-fires.

## The fix — route B's `tp`-driven dispatch (Buchholz Def 3.2 case 5.2)

Buchholz branches the 5.2 reduct on the **inference SYMBOL** `tp(dᵢ)` of the selected premise, NOT on a
chain-criticality sentinel:
- `tp(dᵢ) = Rep` AND `dᵢ` is a critical chain → 5.2.1 splice (genuine reduct-halves `dᵢ{0},dᵢ{1}`).
- otherwise (`dᵢ` an atom / I-rule / axiom / non-critical chain) → 5.2.2 replace `d[n] := K^r_{tp(dᵢ)(Π,n)}
  (i/dᵢ[n])`, with the conclusion REDUCED by `tp(dᵢ)` (= `tpReduce`, already Σ₁-def'd in `InternalZ`).

So the splice branch must additionally test `zTag dᵢ = 4` (chain) before reading halves; a non-chain
selected premise is the conclusion-reducing replace case. **`iRK` must dispatch on `zTag dᵢ`/`tp dᵢ`, and
the replace branch must emit `tpReduce (tp dᵢ) Π n` (the route-B conclusion reduction) rather than keeping
`Π`.** This is the genuine next architectural step; the lap-93/94 regularity layer + `redexI_redexJ_lt_of_zKValid`
+ the eigensubst reducts are the bricks the redesigned dispatch will reuse.

## What stands (lap 93–94, all axiom-clean, in the build)

- "red preserves ZRegular": `ZRegular_red_of_not_zK` (non-zK) + `ZRegular_red_zK` (zK, modulo `hseltag`).
  The replace (5.2.2) and critical (5.1) branches are FULLY closed; `hredex` is discharged internally.
  Only the splice (5.2.1) branch is blocked — and now provably so (`hseltag` false), localizing the wall.
- `redexI_redexJ_lt_of_zKValid`, `zKCritical_of_not_permIdx_lt` — reusable validity-data extractors.
- The eigensubst route-B reducts `ZDerivation_zsubst_zIall_premise/_zInd_premise1` (consume regularity).

## NEXT
Redesign `iRK`'s inner dispatch to gate the splice on `zTag dᵢ = 4` and route non-chain selected premises
through a conclusion-reducing replace (`tpReduce`). This is a definition change with blast radius on the
banked `iord`-descent lemmas — scope it carefully (a `wip/` spike first, per the lap-92 de-risk doctrine).
Until then `hseltag`/`ZDerivation_red_zK_splice` stay disclosed as the route-B frontier.
