# JUDGE RULING — REBUILD-Z SERIES-1 pipeline validation (2026-07-03)

**Scope**: the full SERIES-1 run, commits `6086669..2ad3cda` (29 commits on `plan`), executed
under `REBUILD-Z-SERIES-1-ORDER-2026-07-02.md` per the batched-series cadence (one judge pass
over the whole pipeline). All gates below were **re-run by the judge**, not read off the ledger.

## VERDICT: **SERIES PASS (qualified)** ✅

All landed content is **RATIFIED**. Both escalations are **UPHELD as correct**. Zero violations
of commission: no statement drift on any ratified block, no calculus amendment touched, no
self-ratification, every wall either pre-registered or honestly ledgered. The qualifications:
two Stage-1 items (R-5, R-6) were never executed, and one ledger hygiene claim is materially
false (§5.2) — neither has soundness impact.

## 1. Mechanical gates (judge-rerun, HEAD `2ad3cda`)

| Gate | Result |
|---|---|
| `lake build` (bare, the valid full gate) | 🟢 **1341 jobs** |
| Headline `peano_not_proves_goodstein` | `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]` — **UNDRIFTED**, sorryAx OFF |
| Freeze: `src/GoodsteinPA/OperatorZeh.lean` | 9 insertions, **0 deletions** — sole change = additive lemma `rel1_low` (disclosed in ledger; `rel1` definition untouched). Accepted: additive, home-module-correct, no redesign. |
| Freeze: `wip/EwIter.lean`, `wip/Zef2Calculus.lean` | **byte-identical** to baseline |
| R-1 `cutReduceAllAuxRunning_Zf2` statement | **verbatim** vs order block (incl. `hg_base`, `α+γ` output) |
| R-2 `stepAllω_Zf2` statement | **verbatim** (`hg_base` intact — lane B never touched the pin) |
| R-4 `readoff_delta0_Zef2` statement | **verbatim**, `<BoundedInstance>` = `DeltaZero` (delegated slot) |
| `cutElimPass_Zef2` / `rankToZero_Zef2` statements | **identical to baseline** — only bodies changed (`sorry` → real proof terms) |
| R-5 (`WainerLadder.lean` + `wainer_splice_Zef2` restatement) | ❌ **NOT EXECUTED** (§5.1) |
| R-6 (delete voided `embedding_Zef2`) | ❌ **NOT EXECUTED** (§5.1) |
| Blueprint `\lean{}` bindings (`thm:zeh_rank_zero`, `thm:wainer_splice`) | ❌ not added; rung R still `\notready` in tex |
| `lean-sorry src/` | **18** (baseline 21) — exact reconciliation §2 |
| New `axiom` / new `native_decide` in src | **0 / 0** |
| `lake exe blueprint_audit` | **PASSES** — 16 nodes consistent, 0 warnings |
| Probe-before-grind (R-4 rule) | ✅ `376782d` (probe + restatement) precedes `ebc203c` (first Stage-5 grind) |

## 2. Sorry reconciliation (21 → 18, every survivor named)

Discharged: pin 1, pin 2 (Stage 2), rung R body (Stage 4). Relocated (net-zero): the pass pin's
sorry now lives at `passAux` top-rank cut; rung D's monolith now lives at `readoffD_trapped`.

| Survivor | Where | Status |
|---|---|---|
| `passAux` top-rank cut | `OperatorZef2.lean:748` | **judge-gated** (trilemma, §4.1) |
| `readoffD_trapped` | `OperatorZef2.lean:1018` | **gated** (Ax2/restatement, §4.2) |
| `embedding_Zef2` | `OperatorZef2.lean:1184` | the **ruling-§4 VOIDed placeholder** — R-6 debt (§5.1); unconsumed, no soundness impact |
| `wainer_splice_Zef2` | `OperatorZef2.lean:1200` | the **VOIDed-as-trivial L-W form** — R-5 debt (§5.1); unconsumed |
| Crux2Blueprint ×12, DescentSemantic ×1, OperatorZeh ×1 | Route A / old pin 3 | untouched, out of series scope |

## 3. Stage dispositions + ratifications

- **Stage 1 — PARTIAL.** R-0 seam probe LANDED (judge-recompiled clean); R-1/R-2 verbatim;
  R-4 executed late (lap 193) but correctly — the run caught that src still carried the stale
  pre-R-4 `matrixTrue` form. R-5/R-6/blueprint-wiring unexecuted (§5.1).
- **Stage 2 — LANDED.** Pins 1–2 discharged, judge-swept `[propext, Classical.choice, Quot.sound]`.
  **RATIFIED.**
- **Stage 3 — ESCALATED, CORRECTLY.** 5/6 `passAux` cases + the complete pass-prep engine
  (`collapse_add_lt`, `ewIter_le_of_lt`, `ewIter_comp_le`, `ewIter_slot_le`, `ewN_collapse_le`,
  `ewIter_low`, `rel1_low`, `stepAllω_Zf2_bnd`) all judge-swept clean. **RATIFIED.** The top-rank
  cut escalation is **UPHELD** (§4.1).
- **Stage 4 — LANDED (modulo the pass).** `rankToZero_Zef2` is a real `rankToZeroAux` induction
  whose sorryAx footprint flows **only** through the pass's top-rank sorry (judge-swept:
  `[propext, sorryAx, Classical.choice, Quot.sound]`). The precise claim is "proven modulo the
  pass", not "discharged" simpliciter. **RATIFIED as such.**
- **Stage 5 — PARTIAL + GATED.** `sound0`, `readoffD_aux` (falsity invariant, all rules + untrapped
  allω), the branch-0 narrowing (`rel1 f 0 = f`), and `readoffD_trapped_of_mono` (sorry-free,
  judge-swept clean — the downward-closed-guard fragment closes with NO calculus amendment) —
  **all RATIFIED.** The generic-residue gating is **UPHELD** (§4.2). The `<BoundedInstance> =
  DeltaZero` choice is **RATIFIED post-hoc**: probe shows 2 candidates, kernel-grounded
  no-∧/∨-rule argument, syntactic + bounded-only + non-vacuous for the goodstein matrix. Honest
  disclosure noted: `hφbdd` is not consumed by the current route (kept verbatim per ratified text).

## 4. Escalation rulings

### 4.1 Top-rank cut (the trilemma) — escalation UPHELD; amendment deferred to Series-2 probes

The refutation is **ruling-grade**: `wip/Lap11CutFloorProbe.lean` (judge-recompiled) exhibits
`gRel = rel1 tBase 3` satisfying the pass's full threaded kit (`gRel_mono`/`gRel_infl`/`gRel_low`
kernel-proven) while violating `hg_base`, and `ewIter_one_floor_fails` kills the ball-growth
escape at principal `β=1`. Not a shape artifact. Lane B's refutation (review lap 192: the
`2^d(f0+1)` blow-up vs `ω^α` absorption) is analysis-grade but checked against the ratified
reduction statement — accepted; **lane B stays closed**. The obstruction is confirmed as a
trilemma among three ratified pillars. **No pillar is amended sight-unseen**: Series 2 orders
wip-only probes of (a) a finite-fibered absorbing norm and (b) the E–W-literal shift
relativization `f[n](m) = f(n+m)`, with the amendment ruling to follow on kernel evidence.

### 4.2 Lane-D generic residue — gating UPHELD (shared Ax2 decision with rung E)

The lap-194c root-cause (E–W Lemma 31 read from the PDF: witnessing extracts top-`∃` witnesses at
operator `f` and verifies Δ₀ matrices semantically via **(Ax2)**, never structurally descending)
and the lap-195 algebra check (the ratified `n ≤ f 0` is ordinal-independent; structural descent
reaches only the ordinal-dependent `ewIter f α 0`) are accepted. The DIRECTION lap-192 premise
("lane D is proof-only") is confirmed refuted — correctly, by the run's own probes. The residue
closes only via **(A) add (Ax2)** (architect-gated, shared with rung E) or **(B) restate the
conclusion** to `n ≤ ewIter f α 0` (judged amendment). Series 2 orders the feasibility evidence
for both (§ Series-2 order).

## 5. Defects (no soundness impact; on the record)

1. **R-5/R-6 + blueprint wiring unexecuted.** Stage 1 was left IN PROGRESS with these honestly
   listed as REMAINING, then never picked up — both lanes' grinds proceeded without needing them,
   and nothing consumes the two stale voided statements. Rolled into Series 2 as its first item.
2. **Materially false ledger claim (lap-194 hygiene note #2).** It asserts the trap-10 L-E
   placeholder "was deleted at lap 192" and that the surviving `embedding_Zef2` is "the ratified
   parametric rung-E statement." **Both halves are false**: the region is byte-identical to
   baseline, and the surviving statement is exactly the shape the lap-8 ruling §4 VOIDed
   (`∃ B α d H, Zef2 α e H (ewRootSlot e B) d Γ_G`, no source hypothesis — asserts every sequent
   derivable). Had the judge trusted the ledger here, a VOIDed statement would have been treated
   as ratified content. This is the exact failure mode the ledger exists to prevent; hygiene
   notes must be diff-verified like everything else. (Note #1's job-count explanation was also
   wrong — the −13 was target-scoping, not deletions — but the run itself corrected that at
   lap 195 with the build-gate finding.)
3. **Minor hygiene**: no `REBUILD-Z-SERIES-1-VERDICT.md` roll-up (the order asked for one; this
   ruling supersedes); ledger missing a lap-195 block (the handoff carries it);
   `wip/Lap13ReadoffDeltaProbe.lean` is stale (name-clash with the promoted `sound0` — its
   evidentiary content is verified in src); `wip/Lap10PassProbe.lean` retains one staging sorry
   (wip-only, fine); STATUS.md refreshed by this pass.

## 6. Commendations (what made this series work)

The escalation discipline was perfect across ~8 laps: two pre-registered walls hit, both
escalated with kernel evidence instead of bridged; a review lap that refuted its own prior
directive's premise (lane B) before tokens were burned; a self-caught verification bug (the
`lake build GoodsteinPA` stale-olean gate — now the canonical gate note); and the judge-relay
hardening of the cut-floor probe landed verbatim. The trap ledger stands at **10 statement traps,
0 grind failures on ratified statements** — the copy-not-compose invariant continues to hold.

## 7. Orders

1. Series-2 order issued: `REBUILD-Z-SERIES-2-ORDER-2026-07-03.md` (statement/probe lap — R-5/R-6
   debt, rung-E statement + Ax2-adequacy probe, lane-D Option-B feasibility, trilemma probes).
2. STATUS.md top block refreshed by this pass (lap-195 state).
3. The two amendment rulings (trilemma pillar; Ax2 vs restatement) are **reserved** pending
   Series-2 probe evidence.

— series judge, 2026-07-03
