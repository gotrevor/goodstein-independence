# REBUILD-Z — LAP-8 ENTRANCE ORDER: the judged src port + ladder erection (architect, 2026-07-02) 🔒

> **Binding.** Written by the judge/architect pass that ratified lap 7
> (`E-2026-07-02-JUDGE-rebuild-z-lap7-validation.md`). This lap PORTS the ratified wip statement
> layer into `src/` and erects the wainer ladder as named pins with ledger rows. It is a PORT +
> STATEMENT lap — the only permitted `sorry` bodies are the disclosed pins named below; the pass
> grind stays FORBIDDEN until the port is judged. Self-ratification of any statement change =
> VOID; a lap that believes a ratified form is wrong STOPS and escalates.

## 1. Port deliverables (P-items)

- **(P-a) `src/GoodsteinPA/EwIter.lean`** — port `wip/EwIter.lean` VERBATIM (ewN, ewBall,
  `mem_ewBall_of_ewN_le`, EwF1/EwF2, ewStep/ewIter + unfold/zero, lower/infl/monotone/rel1_le,
  the lift + P1). The P2/P3 instance probes STAY in wip (evidence artifacts; they carry
  native_decide, src stays anchor-free). Wire the module into the root import + `mk_all` check.
- **(P-b) `src/GoodsteinPA/OperatorZef2.lean`** (new file; OperatorZeh is not touched) — port
  `wip/Zef2Calculus.lean`: `Zef2` + `mono_f`/`change_H`/`mono_Hf` + `Zef2Prov` + `ewRootSlot`
  (+ its EwF1/EwF2 proofs) + the C3 exit corollary, statements verbatim (freeze-checked against
  the wip file at the next judge pass — the wip files are the reference hashes).
- **(P-c) Discharge BOTH read-off pins by the forgetful map** (ruling §4, MANDATED route):
  define `Zef2.toZef` (6-case induction, drop `hαN`/`hcutRead`), then
  `readoff_sigma1_Zef2 := readoff_sigma1 ∘ toZef`-style reuse and likewise
  `headline_readoff_Zef2`. Zero re-proof. `toZef` doubles as the conservativity witness.
- **(P-d) Re-prove pins 1–2 over `Zef2`**: `cutReduceAllAuxRunning_Zf2`, `stepAllω_Zf2` — the
  Zef proofs re-thread with the HYP (`ewN α ≤ f 0`) and cut-read clauses carried through each
  rebuilt node (slot moves are `mono_f`-mediated; the input nodes carry the needed inequalities;
  composition slots `g∘f` need `ewN`-side arithmetic at 0 only). Statements = the Zef pin
  statements with `Zef→Zef2` and the (f.1)-class hypotheses as needed — any OTHER statement
  change escalates. The inversion suite (`allInv`/`orInv`/`andInvL`/`andInvR`) ports the same way.
- **(P-e) Port the pass pin**: `cutElimPass_Zef2` into `OperatorZef2.lean` (body `sorry`,
  the laps-9+ gate) + `cutElimPass_exit_root_Zef2` (real derivation, sorryAx via the pin only).
- **(P-f) Supersession bookkeeping, no deletion**: the old `Zef` layer, `iterSlot` + §5b lemmas,
  and old pin 3 STAY in `OperatorZeh.lean` (frozen evidence; docstring-annotate them SUPERSEDED
  by `OperatorZef2.lean` — docstrings only, statement tokens untouched).

## 2. Ladder erection (L-items; `WAINER-LADDER-2026-07-02.md`)

Erect the rungs as NAMED PINS with ledger rows (attributes 17+; check the committed max id
first). Every pin's statement enters through this order's constraints; bodies `sorry` with the
discharging rung named in the docstring:

- **(L-R) `rankToZero_Zef2`** (rung R): iterate `cutElimPass_Zef2` down the cut rank —
  `Zef2 α e H f d Γ → EwF1 f → EwF2 f → Zef2Prov (collapseIter d α) e H (ewIterTower f d α) 0 Γ`
  with `collapseIter`/`ewIterTower` the d-fold composites (explicit defs; NF-preservation lemmas
  stated). Ledger: debt, "1", 90.
- **(L-D) the Δ₀ read-off extension pin** (rung D): the bounded-∀ matrix form of
  `readoff_sigma1_Zef2` (Towsner-§5.4 pattern) — statement only, discharge is its own grind.
  Ledger: debt, "2-3", 80.
- **(L-E) the embedding pin** (rung E) — **JUDGE AMENDMENTS BINDING** (ruling §5):
  (i) any budget is EXISTENTIAL (`∃ B, …` — `Zeh`/provability are Prop; no function-of-derivation);
  (ii) the statement targets the **PA-proof-sourced pipeline** — re-base the W3-ratified
  K-hypothesis exit statement onto `Zef2` at a budgeted `ewRootSlot`-class slot — NOT an
  arbitrary-`Zeh` transport (ω-branching + information-free membership make that class
  non-uniform; a `∀ Zeh`-transport pin is REFUSED at entry). If the W3 shape re-bases without a
  kernel obstruction, state it; if not, STOP and escalate with the probe (potential trap 9 —
  architect's, not the lap's). Ledger: debt, "8-20", 65.
- **(L-W) the splice pin** (rung W): from the L-E/L-R/L-D composites + the banked Hardy
  Lemma-19 brackets + `goodsteinLength_dominates_fastGrowing`, conclude
  `wainer_bound_of_pa_proves_goodstein`'s statement as a theorem-with-sorry pinned on the rungs
  (the composition itself should be REAL where the rungs' statements allow — leave `sorry` only
  where a rung pin is consumed). Ledger: debt, "2-4", 75.
- **(L-14/16 bookkeeping)**: ledger row 14 (`wainer_axiom`) gets its citation updated to point
  at the rung rows; row 16 (crown) unchanged. `lake exe blueprint_audit` MUST pass with all new
  rows; then `blueprint/annotate_depgraph.py --web` (the tex nodes for R/E/W already exist —
  decl-less; move them to `\lean{}`-bound as part of this lap so the reconciler picks the ledger
  rows up and the NODE_NOTE hand estimates retire).

## 3. Gates (every one, before the lap ends)

Build 🟢 (`lake build`, expect job count growth from the new modules) · headline
`peano_not_proves_goodstein` quadruple UNDRIFTED · `lean-sorry src/` delta = EXACTLY the named
pins above (old pin 3 + L-R/L-D/L-E/L-W/pass-pin + any P-d sub-pins, each disclosed) ·
`blueprint_audit` passes · NO new `axiom` decls · NO native_decide in `src/` beyond the blessed
base · wip evidence files byte-identical (freeze reference). Write `REBUILD-Z-LAP8-VERDICT.md`;
**STOP for the judge.**

## 4. FORBIDDEN

Grinding the pass (`cutElimPass_Zef2` body). Touching `Zeh` core / old `Zef` statement tokens /
old pin 3 / read-off block (docstring supersession notes only). Route-A, `(k,d)`, the old
fs-`iterSlot` (kernel-refuted — evidence only). Arbitrary-`Zeh` embedding pins (ruling §5).
Self-ratification (VOID).

## 5. Treadmill shape (operator fires)

`--max-laps 2 --max-duration 6h` — the port (P-items) and the ladder erection (L-items) are
separable; a clean lap-1-port + lap-2-ladder split is the expected shape, a single lap doing
both is fine. Estimate: 1–2 sessions (port is mechanical; L-E's re-base is the one place
thinking happens — escalate rather than improvise there).
