# E — Judge: the §14.254 splice needs a FLATTEN, not a `seqUpdate` (Ren, 2026-06-26, fresh judge, ~lap 150)

> **✅ RESOLVED lap 151 (`e204766`), as called.** The box refuted the `seqUpdate` splice and built the genuine
> flatten engine `descent_step_K_spliceHalves` (Crux2Blueprint:3096) — **sorry-free**, descent via
> `iord_descent_seqInsert'` (insert two halves in place of premise `i`), NOT a seqUpdate monotonicity. It also
> strengthened the IH to a structured `GenReductCert` (:2934): `Or.inl` õ-drop→replace | `Or.inr` flatten-halves
> exposing both halves' õ-bounds (`icmp (iotil a/b) (iotil d) = 0`) + the outer-rank condition
> (`irk B + 1 ≤ idg d`) — the option-(a) interface enrichment predicted below, proven Σ₁-definable. The deep
> ordinal question ("does the flatten descend?") is now PROVEN; the live residual relocated (not relabeled) to
> PRODUCING the cert's halves from the principal cut (sorries :2977/:3001) + axMajor (:3215) + gDef (:3338) + M2.
> The analysis below stands as the why.

> **VALIDATE, don't trust.** Source-grounded in `scratchpad/buchholz-gentzen.txt` §14.254 (480-535) + the
> `iord` algebra at HEAD `78a938a`: `iotil_zK` (InternalZ:2524), `idg_zK` (:2159), `iord_descent_cut` (:2667),
> `iord = iotower (iotil) (idg)` (:2535). Trigger: validating the lap-150 frame + the box's stated NEXT move.
> Each claim has a confidence % + "how this could be wrong."

## TL;DR — lap 150 is real progress; the stated next lemma is FALSE; the real fix is the flatten
1. **CREDIT (big).** The code-recursion frame is genuinely landed and the prior judge's #1 open worry is
   **empirically discharged**: `genReduct_botSucc` is skeleton-proven by `zDerivation_sigma_induction` (a sound
   Σ₁-motive wrapper of the Foundation fixpoint induction), the **motive `definability` compiles green**, and
   the IH reaches every direct premise. The "missing engine / motive-may-not-be-Σ₁" worries are CLOSED.
2. **CREDIT.** The box independently found + corrected the `iRedDescent`→`iord` faithfulness bug (the chain
   principal cut drops via DEGREE, not `õ`, so `iRedDescent` is genuinely FALSE there). Correct call, and
   harmless downstream because `false_of_ZDerivesEmpty` already runs on combined-`iord` descent.
3. **⚠️ THE WARNING the box can't see from inside.** Its lap-150 handoff NEXT #1 frames the splice residual as:
   *"iord-fold-monotonicity for `iCritAux`/`seqUpdate` that does NOT assume the iotil drop."* **That lemma is
   false as stated.** A `seqUpdate` (one-for-one premise replacement) of `dⱼ` by a degree-traded reduct `v`
   does NOT lower the outer chain's `iord`. Chasing it is the lap87/lap94 splice-bug pattern about to repeat.

## The proof that `seqUpdate` cannot work in the degree-trade case (the load-bearing finding)
The outer ordinal is `iord d = ω_{idg d}(iotil d)`, and for a chain the two components are (verbatim):
- `iotil_zK`  (:2524): `õ(zK s r ds) = #ⱼ ω^{õ dⱼ}` — **depends ONLY on premises' `õ`**, not their degrees.
- `idg_zK`    (:2159): `dg(zK s r ds) = max r ((maxⱼ dg dⱼ) ∸ 1)` — **pinned `≥ r`**.

Now take the §14.254 case (ii): premise `dⱼ` reduces by §14.253 (a principal cut), so its reduct `v` drops
via **degree** — `idg v < idg dⱼ` but, by the box's own :2929 finding, `õ v` is bounded only by `ω^{õ dⱼ}`,
i.e. **`õ v` can RISE** (cut-elimination trades degree for ordinal height). Replace `dⱼ` by `v` via
`seqUpdate ds j v`:
- **outer `õ`**: the term `ω^{õ v} ≥ ω^{õ dⱼ}`, so `#ᵢ ω^{õ premiseᵢ}` stays the same or **INCREASES**.
- **outer `dg`**: `max r ((maxᵢ dg ∸ 1))` — drops only if `dⱼ` was the *strict* argmax AND `dg dⱼ − 1 > r`.
  If `r` pins the max, or another premise ties, the outer degree is **UNCHANGED**.

So in the generic sub-case (r pins the degree, õ rises): outer `dg` flat, outer `õ` up ⟹ **`iord` rises or is
flat — NOT a descent.** And `iord_descent_cut` (:2667), the only degree-trade descent tool, needs BOTH
`idg(replaced)+1 ≤ idg(outer)` (degree strict drop — fails) AND `õ(replaced) < ω^{õ(outer)}` (fails when õ
rises). Both preconditions are violated. **There is no general `seqUpdate` iord-monotonicity here.** (~85%)

## Why Buchholz FLATTENS — and the interface consequence the box hasn't surfaced
§14.254 case (ii) does **not** keep `dⱼ` as one premise. It takes `dⱼ`'s reduct `dⱼ[0]` (a chain inference with
two premises `dⱼ{0} = Γⱼ→B`, `dⱼ{1} = B,Γⱼ→A'ⱼ`) and **splices those two premises into the outer chain in
place of `dⱼ`** (source lines 486-535). This works because the cut formula `B` (rank `< r`) now lives at the
**outer** level, where the outer rank `r` accounts for it — the descent comes from the principal-cut õ/rank
bound on the *spliced sub-premises*, not from a premise-degree max-drop. The flatten is genuinely different
from `seqUpdate`, and it **requires the reduct's internal chain decomposition** `dⱼ{0}`/`dⱼ{1}` plus an õ-bound
on them.

**The interface gap:** `genReduct_botSucc`'s conclusion (and the chain IH, and `descent_step_K_splice`'s `v`)
is a bare `∃ v, ZDerivation v ∧ … ∧ icmp (iord v) (iord dⱼ) = 0`. It exposes only "some iord-smaller `v`." It
does **not** expose that `v` (in the degree-trade case) is a chain with extractable `dⱼ{0}`/`dⱼ{1}`, nor the
õ-bound the splice descent needs. So `descent_step_K_splice` cannot be discharged from this interface as-is.
Predicted real work (bigger than "fill 3 sorries"): EITHER
- **(a)** strengthen `genReduct_botSucc`'s conclusion to carry the reduct's structure in the degree-trade case
  (a Σ₁-preserving motive enrichment — re-verify `definability` after), OR
- **(b)** inside `descent_step_K_splice`, case on `ZDerivation v`, recognize the chain shape, and **re-derive**
  the `dⱼ{0}`/`dⱼ{1}` õ-bound (the principal-cut analysis again — the õ-control is NOT in `iord v < iord dⱼ`).

Either way the bare-existence interface that made the skeleton typecheck green is **too weak** for the one case
that matters. This is the precise, sharpened form of the prior judge's "does the IH reach the cut-partner codes
`dⱼ{0}/dⱼ{1}`?" — answered: it reaches `dⱼ` (good), but the *conclusion it hands back* hides `dⱼ{0}/dⱼ{1}`.

## Recommendation (for the box, paste-ready)
1. **Do NOT spend a lap proving "iord-fold-monotonicity for `seqUpdate` without the iotil drop" — it's false.**
   `iotil_zK` makes outer õ rise under a degree-traded premise; `idg_zK` is pinned `≥ r`; `iord_descent_cut`'s
   two preconditions both fail. Confirm this in-kernel by trying to STATE it and watching `iord_descent_cut`'s
   `idg(replaced)+1 ≤ idg(outer)` premise be unprovable.
2. **Implement the genuine flatten** for `descent_step_K_splice`: the existence form already allows `d'` to be
   the flattened chain (`dⱼ` removed, `dⱼ{0}`/`dⱼ{1}` spliced in), not a `seqUpdate`. Pin the splice order
   against `ANALYSIS-…-lap87-splice-order-sensitivity.md` + `…-lap94-splice-dispatch-unfaithful.md` FIRST.
3. **Decide the interface NOW**, before grinding: does `descent_step_K_splice` get `v`'s chain structure by (a)
   a strengthened IH conclusion or (b) re-casing on `ZDerivation v` + re-deriving the õ-bound? Picking (b)
   silently and discovering the õ-bound isn't available is the trap. If (a), re-confirm the motive stays Σ₁.
4. `genReduct_chain_hasRedex` (outer-chain principal cut) is genuinely unaffected — its descent IS free
   (`iord_descent_iRKcCrit_corr_of_redex`, outer degree provably drops via `idg_zK_iCritReduct_lt`); the
   `Seq (seqAnt s)` / zSeqAnt-tag-4 fold is the right unblock there. The flatten issue is ONLY `noRedex`/splice.

## Confidence
- **`seqUpdate` is insufficient for the degree-trade case: ~85%.** The algebra (`iotil_zK` õ-only +
  `idg_zK` pinned ≥ r + cut raises õ to ω^{õ}) is explicit and the box's own :2929 note concedes õ doesn't drop.
- **The bare-`∃` interface must be enriched or re-derived for the splice: ~70%.** This is the residual lift.
- These do NOT change the higher-level odds: still ~55-60% this campaign lands axiom-clean, M2 (Foundation→Z,
  ~0% built) the largest unknown and bracketed OUT. The finding *relocates* the M1b-term risk, doesn't add to it.

## How this could be wrong
- **The box may already intend the flatten** and just mis-described the needed lemma in the handoff (#1 says
  "seqUpdate"). If so, this note still earns its keep by killing the false-lemma lap and naming the interface
  gap up front. (~30% the box was already going to flatten without the detour.)
- **A depth bound could dodge the general flatten:** if a `Γ→⊥` orbit's chain structure guarantees the
  degree-trade case never nests (e.g. the major premise/cut-partner always reduces via `Rep`/õ-drop, never a
  sub-chain principal cut), then `seqUpdate` suffices and `descent_step_K_splice` collapses to the õ-drop case.
  I did **not** find such a bound, and §14.254 case (ii) is explicitly the principal-sub-reduction case, so I
  judge it reachable — but it's the one escape worth a 10-minute check before building the flatten. (~15%.)
- **Convergence caveat:** I read the same repo docs as the box/Codex; the one thing I add is the explicit
  `iotil_zK`/`idg_zK` algebra showing the monotonicity is FALSE (not merely "hard"), which the handoff's
  "find the lemma" framing omits.

## Pointers
- Algebra: `iotil_zK` (InternalZ:2524), `idg_zK` (:2159), `iord` (:2535), `iord_descent_cut` (:2667),
  `idg_zK_iCritReduct_lt` (:3263), `iotil_iCritAux_lt` (:4369, the õ-drop fold — works only for case (i)).
- Live leaves (all `iord`-descent): `descent_step_K_splice` (Crux2Blueprint:3069), `genReduct_chain_noRedex`
  (:2955), `genReduct_chain_hasRedex` (:2934, descent free), gDef `exists_sigma1_descending_step` (:3238).
- Source: `scratchpad/buchholz-gentzen.txt` §14.254 (480-535), the splice diagram at 486-535.
- Prior splice refutations (the test cases): `ANALYSIS-…-lap87-splice-order-sensitivity.md`,
  `…-lap94-splice-dispatch-unfaithful.md`. Prior judge: `E-2026-06-26-JUDGE-code-recursion-crux.md`.
