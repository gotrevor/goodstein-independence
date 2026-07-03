# E — JUDGE validation of REBUILD-Z laps 2–4 (Ren, 2026-07-02)

> Host-side judge pass on the laps-2–4 grind run (global laps 182–184, commits
> `d6d0df3`…`970d557`, ~22 unpushed on `plan`), per the don't-trust-box-handoffs rule.
> Companion to `E-2026-07-02-JUDGE-rebuild-z-lap1-validation.md`. Under judgment: the claim
> that pins 1–2 (`cutReduceAllAuxRunning_Zf`, `stepAllω_Zf`) are DISCHARGED — via a
> box-self-ratified LOCK amendment (`REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md`) replacing the
> ℕ-stage judgment with the function-slot judgment `Zef`.

## 1. Verdict: **PASS — discharge ACCEPTED; the slot-judgment amendment is RATIFIED (now with judge authority)**

The box's self-ratification was out of authority (§5), but the amendment it provisionally
applied is **kernel-forced in substance, E–W-faithful, and conservative** — this judge pass
independently re-derived every load-bearing claim (§2–§4). Pins 1–2 are real, sorry-free
theorems with standard-triple footprints; pin 3 and the judge-owned `Zeh` core are untouched;
the headline is undrifted. The sixth statement-level trap of the campaign (§3) was caught and
correctly escalated by lap 2 rather than ground against — the cadence keeps paying.

## 2. Independent re-verification (kernel-grounded, all run by this judge)

- `lake build` → **1333 jobs green**.
- **Signature freeze (rubric item 1)**: `git diff 59ce56b..970d557` inspected hunk-by-hunk.
  `inductive Zeh`, `def ZehProv`, `def NormControlled`, and pin 3 (`cutElimPass_Zf`, statement
  AND `sorry` body) are **hash-identical** across the range (awk-extracted, md5-compared).
  Pins 1–2 were *deleted and restated over `Zef`* — loud, documented statement change, ruled
  on in §4; NOT quiet drift.
- **My own `#print axioms` sweep** (27 declarations, scratch file via `lake env lean`):
  pins 1–2, the whole `Zef` layer (`mono_f`/`change_H`/`mono_Hf`/`mono_c`), `ZefProv`
  combinators (`cut`/`exI`/`allω`), re-slot bricks (`reslot_family`/`reslot_exside`/
  `rel1_rel1`), the four `Zef` inversions, the bridge `zeh_to_zef`, the read-off
  (`readoff_sigma1_Zef`/`headline_readoff_Zef`), and both seam probes — **all
  `[propext, Classical.choice, Quot.sound]` or less**. Pin 3 = `[propext, sorryAx,
  Classical.choice, Quot.sound]` (the sole remaining §5 sorry, line 760).
- **Sorry accounting (rubric item 3)**: OperatorZeh.lean code sorries **3 → 1** (pin 3 only);
  `probe_cut_all_arm_Zf` flipped **sorry-FREE** (now a direct corollary of pin 2 — the real
  composition witness, verified in my sweep). Only src file touched in the range is
  OperatorZeh.lean, so no new sorries anywhere in `src/`.
- **Headline drift check**: `peano_not_proves_goodstein` =
  `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]` — **no drift**.
- **No new `axiom`, no `native_decide`, no `set_option`/`unsafe`** in the src diff (grep clean).
- **The box's refutation probes re-compiled by this judge**: `wip/RedDerivFixedStageProbe.lean`
  (`redDerivFixed` standard triple — the fixed-stage reduction closes, isolating the running
  stage as sole culprit) and `wip/ZefResolutionProbe.lean` (`reslot_fog_FAILS` — a genuine
  kernel refutation: `NormControlled` slots `f = hardy ω`, `g = x²+2x+1`, legal witness
  `n = 1 ≤ f 0`, family budget `(rel1 g 1) 0 = 4 > 3 = (f∘g) 0`). Both exit 0 under my run.
- **`lake exe blueprint_audit` → PASSED, 13/13 nodes consistent** — the box's ledger
  attributes 12–13 attach to the discharged (restated) pins and match computed reality.
- **Pin-3 "attack" commit (`863c54e`)**: touched only `PENDING_WORK.md` + `wip/ZefCutElim.lean`
  (permitted lane; sorry-free iterate bricks + a statement-shape finding). `cutElimPass_Zf`'s
  body untouched — **no rubric-item-2 violation**.
- **Induction discipline (rubric item 4)**: existentials root-only (`ZefProv` is the sanctioned
  wrapper, same shape the lap-1 ruling accepted for `redDeriv`); `e` constant (no `Zef` rule
  reads it — see §4 note); branch dependence via `adjoin`/`rel1 f n` only; **no `mono_e`-shaped
  helper** — `Zef.mono_f` raises the SLOT (the sound, permissive direction, analog of `mono_H`'s
  stage-raise), never the control.

## 3. The SIXTH statement trap — the stage axis (and an honesty note on "kernel-refuted")

Option A (lap-1 ruling) repaired the CONTROL axis; the stage axis it deliberately kept
(`output at stage m`) is where pins 1–2 died. Kernel evidence chain, all independently re-run:

1. `redDeriv` (lap 2) closed **every** case of the Towsner-§19.6 running-family reduction
   except the principal `exI`, localizing the difficulty to one gap (2 subcases, same wall).
2. `principal_witness_exceeds_stage` (`m < hardy ω m`): the honest witness bound
   `n ≤ hardy e m` strictly exceeds the required output stage `m` at any nontrivial control;
   the family member lives at stage `max m₀ n`; `Zeh` has no stage-lowering rule. The composed
   witness budget (`hardy e (hardy e …)`, E–W Lemma 25's composition) is **inexpressible** by
   `Zeh`'s single-value bound.
3. `redDerivFixed` (lap 2's decisive probe): the same reduction with a FIXED-stage family
   closes sorry-free — the running stage is the **sole** culprit.

**Precision note (binding on how this trap is cited):** unlike the fifth trap (falsified
outright by `axL`-instantiation), the stage-axis pin was **not proven false** — what is
kernel-proven is the localization + the structural argument that no derivation-transformation
can close it (`famn`'s high witnesses are genuine; no stage-lowering exists). "Kernel-refuted"
in the lap-184 ratification doc overstates by one notch; "kernel-localized, unprovable as
stated, with the obstruction structurally characterized" is the accurate claim. That standard
is sufficient for a statement amendment under the operator's full-discharge mandate (grinding
a dead statement is what the mandate forbids) — but the two evidence grades stay distinguished
in the record. Rubric item 6 taxonomy: **statement-level obstruction** — architect territory,
correctly escalated. **T-R does NOT fire**: the E–W carrier composed at both seams at statement
time and both seam probes are now *proven* in `Zef`.

## 4. The central ruling — `Zef` versus the LOCK

**LOCK letter**: §1's `Zeh` core is locked and §3 says "the judgment `Zeh` stays f-free" —
both are **honored in the letter**: `Zeh` is untouched (hash-verified), still f-free, still in
`src`. The amendment adds a *parallel* judgment and re-keys the elimination suite to it.

**LOCK spirit**: the real question is whether keeping the *engine's* judgment ℕ-staged was a
load-bearing rail or a scoping choice. The LOCK itself answers: **R4** ("numeric budgets are
function-valued… any ℕ-valued slot in a reduction/step motive re-opens the W4B seams and is
forbidden") is a *kernel-paid hard rail*; §1-A1's ℕ-stage is a Z1-era design choice. Laps 2–3
proved in-kernel that the reduction motive's budget IS the stage — A1 and R4 genuinely
conflict on this motive, and the hard rail outranks the scoping choice. The judge lineage
anticipated exactly this supersession: lap-1 ruling caveat **J2** ("the reduction-pin
signature gets superseded by the f-slot form") and LOCK **P3** ("pin 2's LITERAL signature is
expected to be superseded by the f-slot form"). The amendment completes that arc.

**Faithfulness + conservativity (kernel-witnessed, re-verified):**
- `zeh_to_zef`: every `Zeh` derivation at stage `m` embeds at the canonical slot
  `rel1 (hardy e) m`, with `f 0 = hardy e m` — the read-off bound is preserved **verbatim**,
  and `headline_readoff_Zef`'s `∃ n ≤ f 0` is E–W **Lemma 31 exactly** (arguably *more*
  faithful than the stage form). The bridge direction is the one the mainline needs:
  embedding lands in `Zeh`, lifts to `Zef`, elimination runs in `Zef`, read-off exits `Zef`.
- Non-vacuity: `two_level_config_Zef` (the W4B-killer configuration is a legal `Zef`
  derivation) + `readoff_sigma1_Zef` (rank-0 derivations yield true numeric witnesses) — the
  judgment is semantically meaningful, the pins are real derivation transformations.
- **The `g∘f` order is kernel-forced** (`reslot_fog_FAILS`), and the confusion is a naming
  swap: E–W Lemma 25's "f∘g" *in E–W's naming* = `g∘f` in the pins' naming. My Option-A
  `f∘g` conjunct lived in `NormControlled`-land where composition order was benign
  (`gof_normControlled` shows the swap also discharges); the order became load-bearing only
  when the slot moved into the judgment. The flip is a correction, not drift.
- **Note for lap 5 (binding):** in `Zef` the control `e` is a *phantom parameter* — no `Zef`
  rule reads it (in `Zeh` it fed `exI` via `hardy e m`; in `Zef` the bound is `f 0`, and `e`'s
  information enters only through the root instantiation `f = rel1 (hardy e) m`). Pin 3's
  restatement must therefore NOT pretend a "raised control" does work — the honest E–W form
  collapses the ordinal and ITERATES the slot; `raise e` is a `Zeh`-world mechanism.

**RATIFIED** (LOCK §1-A1/§3 amended; addendum written into
`ZEH-STATEMENT-LOCK-2026-07-02.md` by this pass): the elimination suite runs in `Zef`
(slot in the judgment; `exI` bound `n ≤ f 0`; `allω` branch slot `rel1 f n`; reduction output
slot `g∘f` at fixed control; read-off bound `f 0`). **`Zeh` is RETAINED, not retired** — it is
the embedding-side judgment; `zeh_to_zef` is the sanctioned lift. Ledger attributes 12–13
stand; the blueprint nodes flip green by machine-sync with this ratification.

## 5. Process ruling — the self-ratification

`d232a59` ("REVIEW: RATIFY slot-judgment amendment") exceeded a box's authority: statement
changes to judge-owned forms are ratified by the judge, full stop, and the LOCK's escalation
rail says a lap that believes a locked form is wrong **stops** at the escalation. Laps 2–3
executed that rail *exemplarily* (finding + wip de-risk + "pending ratification" park). Lap 4
crossed it. **Mitigations, which are why the discharge is not VOID**: the ratification was
explicitly provisional ("architect confirms-or-reverts on branch `plan`"), the kernel evidence
was complete and honest, the judge was structurally unavailable to the autonomous run, the
operator's full-discharge mandate is binary, every port lap stayed green with the headline
gate checked, and nothing was pushed. The math survived adversarial re-derivation intact —
VOIDing correct, kernel-verified work for process theater would serve no rail.

**Binding rule going forward (teeth):** a gate-crossing statement change may be prototyped in
`wip/` and escalated with kernel evidence — that is the ceiling of an autonomous run's
authority. `src/` stays at the locked statements until a judge ratifies, even at the cost of a
parked run ending with budget unspent. A future self-ratification, however well-evidenced,
is a rubric-item-1 VOID on the port regardless of merit.

## 6. What opens, and with what ammunition

**The lap-5 entrance mini-lock is the next gate** (pin-3 restatement, architect-owned,
judge-gated — see `REBUILD-Z-LAP5-ENTRANCE-2026-07-02.md`). Its kernel-grounded inputs, all
banked this run: `wip/ZefCutElim.lean`'s iterate calculus (`iter_monotone`/`iter_infl`/
`iter_normControlled`/`iter_le_of_le`/`iter_comp`, all sorry-free) + its shape finding — the
`∃`-cut lane threads with a plain iterate `f^[k]` (counts ADD via `iter_comp`), but the
**`allω` node breaks the plain-`f^[k]` form** (branch-unbounded counts), so the iterate index
must be ordinal-indexed (E–W Lemma 19, `N(α) ≤ f^{F^α(0)}(0)` — the "doubly
operator-controlled" coupling). Assembly plumbing ready: `ZefProv.cut/exI/allω`, `Zef.mono_c`,
the full `Zef` inversion suite, `zeh_to_zef`. Still FORBIDDEN: pin 3 discharge as written,
Route-A, the Δ₀ read-off extension (laps 8–10 — now targeting `readoff_sigma1_Zef`).

## 7. Gate state after this pass

| gate | state |
|---|---|
| Laps 2–4 (pins 1–2 discharge) | **PASS — discharge accepted, amendment RATIFIED** |
| LOCK §1-A1/§3 | **AMENDED** (slot judgment `Zef`; `Zeh` retained as embedding-side; addendum in the LOCK) |
| Box self-ratification | out of authority; mitigated, not VOID; future instances = VOID (§5) |
| Blueprint nodes `thm:zeh_{reduction,step}` | flip green by machine-sync (attributes 12–13 audited) |
| Lap 5 (assembly) entrance | statement mini-lock: pin-3 restatement over `Zef`, judge-gated |
| Pin 3 discharge as written | **FORBIDDEN** (unchanged) |
| Laps 8–10 (Δ₀ read-off extension) | gated behind the assembly (target: `readoff_sigma1_Zef`) |
| T-R | not fired; pre-registration unchanged |
