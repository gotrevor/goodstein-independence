# HANDOFF — 2026-06-23 (lap 28, **F-φ DISCHARGED — Thm 5.6 fully axiom-clean; ONE wall left**)

> **Branch** `plan` · HEAD = `c561559` · build **green** (`lake build GoodsteinPA`, **1300 jobs**) ·
> headline `GoodsteinPA.peano_not_proves_goodstein` = honest `sorry` (anti-fraud intact). Tree clean,
> no uncommitted edits.

Durable overview = **`STATUS.md`** (lap-28 top). Attack paths = **`PENDING_WORK.md`** (lap-28 top has the
`ibump_nat` Foundation-ℕ div/mod diamond blocker + `div_eq_of` fix path). F-φ port detail =
**`wip/aristotle-fphi/PORT-STATUS.md`** (now marked COMPLETE).

## Lap-28 commits (3, all green): `582123e` F-φ discharge · `af9293a` STATUS/HANDOFF · `c561559` PENDING note
The headline deliverable is `582123e` (F-φ). Late-lap attempt at the route-neutral `ibump_nat`/
`igoodstein_nat` bricks hit a Foundation-ℕ `/`,`%` instance diamond (noncomputable `Classical.choose`
ops, not defeq to Nat's); reverted to keep `src/` green+sorry-free; fix path recorded in `PENDING_WORK.md`.

## What landed this lap (1 green commit)
**`582123e` — F-φ DISCHARGED.** Completed the v4.28→v4.31 port of Aristotle's `rePred_ltPull_natCode`
(comparison of CNF notations is r.e./computable) and wired it into the headline route:
- Promoted `wip/aristotle-fphi/ONoteComp.v431-port-wip.lean` → `src/GoodsteinPA/ONoteComp.lean`
  (in the build, green, **sorry-free**).
- `SeamDefinability.rePred_ltPull_natCode`: `axiom` → `theorem` (chains `ONoteComp.rePred_ltPull_natCode`).
- Port fixes over the lap-27 wip (~12 v4.31-drift errors): `ordCode_cmp` (`LT.lt.not_lt` field gone →
  `Nat.not_lt.mpr`); deleted 2 unused `getElem?_range_map` lemmas; **rewrote `computable_cmpStep`/
  `computable_nfTB`/`computable_nthNF` as direct combinator terms** (new helpers `primrec_thenNat`/
  `primrec_cmpNat`/`primrec_cmpNV`; `PrimrecPred` is `∃ DecidablePred, Primrec decide` so use `.decide`
  not `.to_comp` directly); `of_eq` id/eta goals → `exact` (defeq); `import Mathlib.Tactic.Linarith`
  (nlinarith/linarith weren't transitively imported); **reproved `enc_strictMono`** structurally via the
  `Nat.Subtype.ofNat` enumeration + `Denumerable.ofEquiv_ofNat` (the genuine drift item — instance
  coherence); replaced the slow 8-hint `nlinarith` index bound in `cmpStep_spec` with `pair_lt_pair`+
  `omega` (the only thing that needed >20k heartbeats).

## Real `#print axioms` (lap 28, build 1300 jobs)
- `peano_not_proves_goodstein` (headline) = `[propext, sorryAx, choice, Quot.sound]` (honest `sorry`,
  **0 math axioms**).
- `peano_not_proves_TI` (Thm 5.6) = `[propext, Classical.choice, Quot.sound,
  ONoteComp.cmpStep_spec._native.native_decide.ax_1_5]` — **F-φ math axiom GONE.** Thm 5.6 is now
  FULLY axiom-clean modulo the trust base + one 🟢 `native_decide` finite base-case witness.

## Next actions (priority) — ONE wall left
1. **E-core, Route-B form — THE ONLY REMAINING CRUX.** Inside a paLX derivation, set up the X-definable
   `≺`-descent from `¬TI prec` (LX least-number scheme), define the Goodstein run via the lap-26
   arithmetic substrate (`InternalPow/Digits/Log/Bump/Goodstein`+`InternalBridge`) as `LX`-formulas, run
   inequality (6) as an **`InductionScheme LX`** step (NOT `sigma1_pos_succ_induction` — that lands X-free
   `𝗣𝗔 ⊢ PRWO` = Route A's antecedent, which can't feed `peano_not_proves_TI`; free-`X` obstruction,
   lap-24 correction), contradict the lifted X-free `goodsteinSentence` at the X-definable seed. See
   `DESCENT-PLAN.md §1 CORRECTION` + `PENDING_WORK.md` + `ON-LINE-REQUEST.md` (lap-27 sharpened question).
   E-lift (X-free proof translation) is DONE (lap 23); E-core(b) is the arithmetization + X-induction.
2. On discharge of E-core: `DescentE` becomes real ⟹ `peano_not_proves_goodstein_of_descent` discharges
   the headline `sorry`. **Anti-fraud: only replace it when `#print axioms peano_not_proves_goodstein`
   is clean (`[propext, choice, Quot.sound]` + documented 🟢 native_decide) AND it genuinely chains.**

## Notes / state
- **Aristotle:** F-φ (`aris_onotecmp`) is now fully consumed (ported + in build). E-core is
  paLX-syntactic, not a clean standalone lemma, so nothing obvious to feed. If architecting a bounded
  E-core sub-lemma, inline its defs + hard prereqs as `axiom`s and submit.
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **src/ sorries (2):** `Statement.lean:22` (headline), `Reduction.lean:50` (Route-A hook, REJECTED —
  keep as documented escape hatch, do not build toward it).
- **Two cosmetic linter warnings** in `ONoteComp.lean` (unused simp args at ~226 `[n]`, ~419
  `Nat.Subtype.denumerable`) — harmless, left as-is to avoid risking the heavy proofs.
- **No uncommitted edits** after the STATUS/HANDOFF commit. Tree clean.
