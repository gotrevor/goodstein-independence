# SERIES-3 JUDGE PASS — VERDICT: **PASS** · SERIES-4 FINAL-DISCHARGE ORDER

**Judge**: host session (Ren), seated per the SERIES-2 supersession note.
**Scope**: SERIES-3, baseline `1e29f64` (fire shape) → HEAD `54e9da3` (lap-209 baton) — **73 commits, laps 198–209**.
**Date**: 2026-07-03. All machine gates re-run by the judge host-side (box stopped, tree clean).

---

## 1. Verification record (judge-run, not grinder-claimed)

### Machine gates
- Bare `lake build`: 🟢 **1342 jobs** (the only valid gate; re-run twice, incl. after the ledger edit below).
- `lake exe blueprint_audit`: ✅ **PASSED — 16 nodes consistent, 0 warnings** (re-run twice).
- Headline surface **git-verified undrifted**: `git diff 1e29f64..54e9da3` on `Statement.lean`,
  `WainerRoute.lean`, `Domination.lean` = **empty**. The frozen trusted base never moved all series.
- Audit-printed endgame bill for `routeB_headline`: non-clean axioms = `wainer_bound_of_pa_proves_goodstein`
  + the 12 `goodsteinLength_base_cases` native_decide axioms — **nothing else**. That is the full
  remaining scope of SERIES-4.

### Kernel table — src (judge `#print axioms`, scratch elaboration)
All exactly `[propext, Classical.choice, Quot.sound]`:
`cutElimPass_Zef2` (rung P) · `rankToZero_Zef2` (rung R) · `readoff_delta0_Zef2` (rung D) ·
`ewIter_swap` · `hslack_kit_ge`.

### Kernel table — wip live chain (judge re-elaboration of both crux files, exit 0)
All exactly `[propext, Classical.choice, Quot.sound]` (a few are cleaner — no `Classical.choice`):
- `wip/E1EmbeddingGrind.lean` (56 witnesses): `embedding_Zef2TC_V3` · `budgetedEmbeddingV3` ·
  `allω_inversion` · `metaInduction_Zef2TC` · `passAuxTC` · `rankToZero_TC` · `sound0_TC` ·
  `readoffVTC_core` · `readoff_value_Zef2TC` · `readoff_value_pipeline` · `readoff_value_goodstein` ·
  `goodsteinBodyE_semantic_link` — the full E→P→R→D(value) chain.
- `wip/HardyMajorization.lean` (17 witnesses): `ewIter_hardy_le` · `ewIter_hardy_le_of_dom` ·
  `ewIter_hardy_le_of_dom_pad` · `ewRootSlot_dom_pad` · `rel1_dom_pad` · `hardy_double_collapse` ·
  `Wpow_add_lt_Wpow_succ` — the growth-conversion bank.
- ⚠️ Exactly **two** decls carry `sorryAx`: `readoffTC_core` + `readoff_delta0_Zef2TC` — the
  **retired route (a/b)** read-off pair, superseded by route (c) at lap 207. **No live consumer**;
  they stay in wip as retirement evidence. Anyone auditing later: these two are *supposed* to be sorried.

## 2. Rulings

### Ruling 1 — R-4′ conformance: **CONFORMANT**
`readoff_delta0_Zef2` (src `OperatorZef2.lean:1457`) is **byte-identical** to the ratified R-4′ text
(`E-2026-07-03-JUDGE-series2-validation.md` §Ruling 2). Landed by kernel-proven **vacuity**
(`zef2_rank0_singleton_ex_underivable`); the trapped structural route is parked verbatim in
`wip/ReadoffDAuxRetired.lean`. Judge note: this makes Zef2-side rung D a *dead limb* — the **live**
read-off is the TC value-budget route (`readoff_value_goodstein`), which is kernel-clean (above).
No faithfulness exposure: the endgame's only trusted statement is the axiom's frozen type (§1).

### Ruling 2 — the ∃K / V3 embedding statement: **RATIFIED**
`embedding_Zef2TC_V3` (wip, realized sorry-free, kernel-clean) is ratified as rung E's statement:
- Its **hypothesis end is the frozen headline hypothesis** `𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence` —
  the only faithfulness-bearing end. No stand-in, no weakening.
- The conclusion (`∃ B d e α, … ∀ m, ∃ K, … Zef2TC … {goodsteinBodyE/[nm m]}`) is internal plumbing
  consumed by the in-flight splice; DRAFT2's ∃K env-local relativization is *strengthened* (α also
  m-uniform). Its residual risk is **completability, not faithfulness** — and the splice work
  (laps 204–209) is already consuming it successfully.
- Grounds trail: block-1 connective-gap kernel proof forced Zef2TC; block-3 STATEMENT DISCOVERY
  showed fixed-slot cannot pay the exI witness gate; the amendment was flagged for judge at draft
  time (correct discipline), realized at lap 203, ratified here.

### Ruling 3 — Ax2-deferred: **RESOLVED**
E-0 answered the Ax2-need probe **YES** on kernel evidence (Zef2 rank-0 singleton underivability;
Zef2T closes the PA-refl leaf). The embedding correctly targets the full Def-23 rule set `Zef2TC`.
The Series-2 deferral is discharged; no residue.

## 3. Judge findings (non-blocking)
- **F-1**: legacy `hg_base`/`ewN_add_le_comp` (src `OperatorZef2.lean:256`) has no live consumer on
  the TC chain — bystander. Optional S4 lane-B cleanup; NOT required for the headline.
- **F-2**: ledger row 14 rebased **20-40@65 → 3-8@85** (this pass); NODE_NOTEs for rungs P/R/D/E/W
  flipped to their real states; `blueprint/annotate_depgraph.py` had an idempotency-by-*skip* bug
  (stale notes survived regeneration forever) — fixed to idempotency-by-*overwrite* (+ a re.sub
  backslash-escape corruption caught and healed in the same pass; regen now verified idempotent).
- **F-3**: src sorry census (real, via `lean-sorry`): **15** = 12 pins in `Crux2Blueprint.lean` +
  `WainerLadder.lean:41` + 1 `OperatorZeh` + 1 `DescentSemantic`. This is the completion-gate stock
  for lane B-2.

---

## 4. ⚔️ SERIES-4 ORDER — FINAL DISCHARGE (binding on grind laps)

**Baseline**: this commit (on `plan`). **Mission**: flip `wainer_bound_of_pa_proves_goodstein`
axiom → theorem, burn the 12 native_decide axioms and the 15 src sorries, and hand the SERIES-4
judge a package from which the summit goes green on exactly `[propext, Classical.choice, Quot.sound]`.

**Standing discipline (unchanged)**: bare `lake build` is the only gate · develop in `wip/` ·
**DO NOT self-ratify E/W artifacts into src** · consume ratified statements **verbatim,
copy-not-compose** · baton every lap · ledger blocks diff-verifiable · ONE judge package at series
end · src sorries clear by **proving** (or judge-ordered retirement) — never by parking.

### Lane S — the splice (serial; the mandate; est. 2-5 laps @ 85%)
- **S-1 `ewIterTower_dom_pad`** — the d-fold tower induction. Statement + full proof plan + pad
  bookkeeping are **spelled out in `HANDOFF-2026-07-03-lap209.md` §NEXT** (all bricks green:
  `ewIter_hardy_le_of_dom_pad`, `rel1_dom_pad`, `Wpow_add_lt_Wpow_succ`, `hardy_double_collapse`,
  `collapseIter_NF`). ⚠️ the pad must stay ≥ the collapse norm gate at every level (add
  `norm(Wpow A + Wpow B)` into `c'` explicitly — see the handoff's warning).
- **S-2 `P*`-domination + `Sslot_dom_pad`** — `P* = gvb goodsteinBodyE` elementary bound; `S*` = max
  of the two Hardy bounds, aligned to one level. (Cross-wip-import constraint: state with the tower
  bound as hypothesis if the modules can't import each other — lap-209 gotcha.)
- **S-3 2b(c)** Sslot assembly (`Sslot_mono_slot` may need proving; `ewIter_mono_slot` banked).
- **S-4 2b(e)** EventuallyLE package — one fixed `fastGrowing o` dominates via
  `hardy_le_fastGrowing` / `hardy_omega_pow_lt_fastGrowing`.
- **S-5 THE SPLICE (wip-side summit)** — prove, in wip, a theorem whose statement is **verbatim**
  the axiom's type (`src/GoodsteinPA/WainerRoute.lean:119-121`):
  ```lean
  (𝗣𝗔 ⊢ ↑goodsteinSentence) →
    ∃ o : ONote, o.NF ∧ EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n)
  ```
  Copy the type, do not compose it. End the file with its `#print axioms` witness. This is the
  series summit and the judge package's centerpiece. **The src swap itself is JUDGE-GATED — do not
  touch `WainerRoute.lean`.**

### Lane B — burndown (interleave when S blocks; est. 2-5 laps total)
- **B-1 W7** (est. 1-3 @ 75%): replace the 12 `goodsteinLength_base_cases` native_decide axioms with
  kernel-checked proofs. **Statements FROZEN** — proof-term swaps in `Domination.lean` only. If a
  value is genuinely kernel-infeasible, do NOT restate — ledger the obstruction for the judge.
- **B-2 src sorry burndown** (est. 1-2 @ 90%): the 15 of F-3. Re-point pins to landed theorems where
  they exist; where a pin's route is dead (Route-A / superseded scaffolding), write a **retirement
  proposal** in the ledger — the judge executes deletions, grind laps don't delete src decls.

### JUDGE-GATED (grind laps MUST NOT)
The axiom → theorem swap in `WainerRoute.lean` · the rung-C crown re-point (summit body) · any
`Statement.lean` edit · deleting src decls. These happen at the SERIES-4 judge pass, whose expected
end-state is: `peano_not_proves_goodstein` on exactly `[propext, Classical.choice, Quot.sound]`,
`blueprint_audit` all-green, treadmill completion gate (src sorries 0) unblocked.

### STOP condition
S-5 + B-1 + B-2 ledgered (or hard-blocked with kernel evidence) → stamp the judge package
(ledger blocks + in-file kernel witnesses) → **STOP for the SERIES-4 judge pass**.

*Fire shape: operator's call — SERIES-3's shape (fable/low, review-every-4, max-laps 12,
stop:when-done) performed 73 green commits / 4 rungs / 0 gate failures.* 🪷⚖️
