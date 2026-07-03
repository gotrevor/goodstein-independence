# REBUILD-Z — SERIES-3 LEDGER (append-only; block per stage/lane-advance)

Order in force: `REBUILD-Z-SERIES-3-ORDER-2026-07-03.md`.  Baseline for judge diffs: `1e29f64`
(the HEAD the order was committed at).

---

## Block 1 — (N-0) T-S3 ENTRY GATE: **PASSES** (direct form; NO case-split dodge needed)

**Lap**: 198 · **Files**: `wip/NlogGateProbe.lean` (NEW, standalone probe, wip-only; `src`
untouched) · **Build**: 🟢 bare `lake build` (1342 jobs) · **Headline**: untouched (no src
delta; `lean-sorry src/` delta = 0).

**The gate demand** (order N-0): kernel-discharge the cut-node slack
`max (g 0) (f 0) + c ≤ g (f 0)` for `g = ewIter s βφ`, `f = ewIter s βψ`, `s` the threaded kit
slot (Monotone + inflationary + EwLow), `c = 1` (Nlog's absorbing constant), **including the
edges `βφ, βψ ∈ {0, 1}`** the judge flagged (`βψ = 0 ⇒ f 0 = 0 ⇒ hslack false as stated`).

**Result: the DIRECT form holds for ALL `βφ, βψ` — the flagged edge is vacuous and no
case-split dodge is required.**  Two structural facts:

1. **Edge vacuity** (`kit_f0_pos`, `ewIter_base_le`): the EwLow floor makes
   `f 0 = ewIter s βψ 0 ≥ s 0 ≥ 1` for every `βψ` — at the flagged edge `βψ = 0` we get
   `f 0 = s 0 ≥ 2·0+1 = 1`, never `0`.  The judge's degeneration presupposed a generic `f`
   with `f 0 = 0`, which the threaded kit never produces.
2. **The swap lemma** (`ewIter_swap`, the lap's structural insight — NEW, not in any prior
   probe): `s (ewIter s α x) ≤ ewIter s α (s x)` for every Monotone + inflationary `s` and
   EVERY `α`.  Proof: well-founded recursion on `α` through a new max-attainment primitive
   `ewIter_attained` (the `ewStep` max is realized on a gated branch `β < α`; extracted via
   `Finset.max'_mem`), chaining IH twice with `ewIter_monotone` and closing by `ewIter_lower`
   with the gate transported along `x ≤ s x`.  This converts the `g`-arm's needed strict gain
   into EwLow arithmetic **without strict monotonicity** — the trap-8 plateau obstruction (the
   reason `hg_base` was refuted for `ewIter` slots) dissolves because the argument bump
   `0 → f 0 ≥ s 0` is itself a slot application, and `ewIter` one-sidedly commutes with its
   own slot.

**hslack** (`hslack_kit`): `f`-arm by `ewIter_low` (`g (f 0) ≥ 2·f 0 + 1`); `g`-arm by
`g (f 0) ≥ g (s 0) ≥ s (g 0) ≥ 2·(g 0) + 1` (monotone + swap + EwLow).  Explicit edge
corollaries `hslack_kit_edge_00`, `_psi0`, `_11`.

**Also delivered (the rest of the N-0 bill)**:
- `Nlog_collapse` (= `Nlog α + 1`) and `Nlog_collapse_le` — the per-node pass gates over
  `Nlog`, exact analogs of `ewN_collapse`/`ewN_collapse_le` (same `f (f 0)` mechanism, only
  EwLow, `rel1`-surviving).
- `ewIterTower_infl/_monotone/_low` + `Nlog_collapseIter_le` — the Def-16 iterate/tower gate
  (rung R's per-pass node gate iterates down the rank).
- **Pins-1–2 miniature**: `Nlog_add_le_comp_kit` — the fresh-root gate
  `Nlog (α+γ) ≤ g (f 0)` at the ACTUAL kit slots, closed by `Nlog_add_le_max_succ` (the D-1
  absorbing theorem, copied verbatim — wip probes are standalone; N-1's src promotion is the
  dedup point) + `hslack_kit`, with **no `hg_base` anywhere**; `MiniZ.axL` + `mini_axL` +
  `mini_axL_fresh_root` — one axL and one rebuilt fresh-root case over the `Nlog` gate.

**Sweep** (`#print axioms`, all `[propext, Classical.choice, Quot.sound]`): `ewIter_swap`,
`hslack_kit`, `Nlog_add_le_comp_kit`, `Nlog_collapseIter_le`, `mini_axL_fresh_root`,
`Nlog_add_le_max_succ`.  No `native_decide`, no new `axiom`, no sorryAx.

**Consequence**: the Lane-N fallback (shift package {`rel1'`, `StepAdd`}) is NOT needed.
**N-1 (the in-place `ewN → Nlog` src swap) is UNBLOCKED.**

**N-1 design note surfaced by this block** (for the re-grind): the slot-lift plumbing
(`ewIter_slot_le`, `ewIter_comp_le`, the `allω` gate transfer in `passAux`) consumes
`ewN β ≤ f 0` gates from `Zef2.gate`.  After the norm swap the calculus hands back
`Nlog β ≤ f 0`, which does NOT bound `ewN β` (`Nlog ≤ ewN`, wrong direction).  So N-1 must
also swap `ewIter`'s internal ball/filter norm to `Nlog` (NF-restricted ball via
`Nlog_finite_fiber`.toFinset — `ewIter` is already noncomputable) and re-grind the `EwIter`
lemma suite on the same templates (`ewIter_lower` picks up an `NF β` hypothesis; all call
sites carry NF).  `ewIter_attained` + the swap lemma templates carry over unchanged.

---

## Block 2 — (N-1) THE NORM SWAP EXECUTED: `Zef2`'s gate norm `ewN → Nlog`, in place, suite re-ground

**Lap**: 198 · **Files**: `src/GoodsteinPA/EwIter.lean`, `src/GoodsteinPA/OperatorZef2.lean` ·
**Build**: 🟢 bare `lake build` (1342 jobs) · **`blueprint_audit`**: ✓ PASSED (16 nodes, 0
warnings) · **Headline**: `peano_not_proves_goodstein` = `[propext, Classical.choice,
goodstein_implies_consistency, Quot.sound]` — **UNDRIFTED** · **`lean-sorry src/` delta: 0**
(OperatorZef2 keeps exactly its 2: `passAux` top-rank cut :~750, `readoffD_trapped`).

**Promotions to src (EwIter.lean)** — all statements are the probe texts (ratified by
construction): `clog` + `clog_add_le`/`clog_pos`/`coe_lt_of_clog_le`, `Nlog` + simp lemmas,
`Nlog_finite_fiber` (NF form) + `NlogBall` (its `Finset`, via `.toFinset`) + `mem_NlogBall`,
`Nlog_add_le_max_succ`, `absorbing_closes_gate` (generic) + `Nlog_add_le_comp` (instance form),
`ewIter_attained`, `ewIter_swap`, `ewIter_base_le`, `hslack_kit`, **`hslack_kit_ge`** (NEW: the
`∀ k ≥ f 0` slot-threaded form — see design note below).

**The in-place swap**:
- `ewStep`'s branch ball: `ewBall`+`ewN` filter → `NlogBall`+`Nlog` filter (substitution image;
  the NF restriction is forced by `Nlog`'s fiber structure and is the population the calculus
  feeds anyway).  `ewIter`'s recursion/termination unchanged.
- `EwIter` suite re-ground on the same templates: `ewIter_lower`/`_le_of_lt`/`_slot_le`/
  `_lift(_of_mono_infl)`/`P1_ewIter_lift` gain an `NF β` hypothesis (Block-1's design note,
  realized); `_infl`/`_low`/`_monotone`/`_comp_le`/`_rel1_le` mechanical (`NF` for branch
  ordinals comes free from `mem_NlogBall`).
- `Zef2` constructor gates: `hαN : ewN α ≤ f 0` → `Nlog α ≤ f 0` (6 constructors), `gate`,
  `Zef2Prov`, `gate_rel1`, `allInv_Zef2` — mechanical.
- **The judged replacement at fresh roots**: `cutReduceAllAuxRunning_Zf2` drops
  `hg_base : ∀ k, g 0 + k ≤ g k` (the kernel-refuted base-additivity) and instead threads
  `hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k` INSIDE the induction statement (design forced:
  the slack is slot-dependent where `hg_base` was not; the `∀ k ≥ f 0` form transfers down the
  `allω` `rel1 f n` re-entries since slot bases only grow: `rel1 f n 0 = f n ≥ f 0`).  All ~15
  fresh-root gates now close by `Nlog_add_le_comp` (absorbing + slack); `stepAllω_Zf2`/`_bnd`
  restated with `hg_slack` in place of `hg_base`.
- `passAux`/`rankToZeroAux`: node gates `ewN_collapse_le` → `Nlog_collapse_le` (promoted next
  to `ewN_collapse_le`, which stays as frozen `ewN` evidence together with the whole
  `ewN`-arithmetic bank).

**Sweep** (all `[propext, Classical.choice, Quot.sound]` unless noted):
`cutReduceAllAuxRunning_Zf2` ✓, `stepAllω_Zf2` ✓, `stepAllω_Zf2_bnd` ✓,
`readoff_sigma1_Zef2` ✓, `headline_readoff_Zef2` ✓, `Nlog_collapse_le` ✓,
`Nlog_add_le_comp` ✓, `hslack_kit_ge` ✓, `ewIter_swap` ✓, `Nlog_add_le_max_succ` ✓,
`Nlog_finite_fiber` ✓; `rankToZero_Zef2`/`cutElimPass_exit_root_Zef2` = `+ sorryAx` (the named
`passAux` top-rank path, expected — that is N-2's target, now with its gate arithmetic REAL:
the kit discharges `hg_slack` via `hslack_kit_ge`).

**KEY consequence**: the reduction and both `stepAllω` wrappers no longer carry ANY unprovable
slot hypothesis — `hg_slack` is a THEOREM of the kit (`hslack_kit_ge` at `g = ewIter s βφ`,
`f = ewIter s βψ`).  The trilemma's escalated horn is dead in src, not just in probes.
**N-2 (the top-rank cut) is now purely assembly**: IH both premises, `stepAllω_Zf2_bnd`,
`collapse_add_lt`, `ewIter_comp_le`, + the `c = 0` atom-cut lemma.
