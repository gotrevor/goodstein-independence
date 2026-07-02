# E — JUDGE validation of REBUILD-Z lap 7 (Ren, 2026-07-02)

> Judge pass over the lap-7 statement lap (executed as a single external run; artifacts arrived
> UNCOMMITTED — committed with this ruling, provenance noted). Baseline for the src freeze:
> **`ed261d7`**. Entrance order in force: `REBUILD-Z-LAP7-ENTRANCE-2026-07-02.md`.
> Companion architect order issued with this ruling: `REBUILD-Z-LAP8-ENTRANCE-2026-07-02.md`.

## 1. Verdict: **PASS at statement level — trap 9 did NOT fire; the E–W ruling is kernel-verified**

The lap delivered every ordered item inside its authority: the Z3 implementability question was
resolved by the SANCTIONED fallback (with a kernel witness that the fallback was necessary), the
three kernel pre-probes all passed — **P1, the deciding probe, is a kernel-pure theorem** — and
the `Zef2` statement layer conforms to Z5/Z6 with the C3 exit consuming the iterate visibly.
`src/` diff vs `ed261d7` is EMPTY (the wip-only rail held). Two judge amendments land on the P4
embedding recipe (§5) — statement-level catches for the lap-8 order, not lap failures.

## 2. Independent re-verification (kernel-grounded, all run by this judge)

- **src freeze**: `git diff ed261d7 -- src/` empty. Working tree: exactly the three new
  untracked files. (The verdict's "dirty WainerRoute" note was stale — it observed this judge's
  own then-uncommitted ladder work, since committed as `ed261d7`.)
- **Compiles** (my own runs): `lake env lean wip/EwIter.lean` CLEAN;
  `LEAN_PATH=. lake env lean wip/Zef2Calculus.lean` = exactly **3** sorry warnings (the three
  disclosed pins). No `axiom` declarations in either file.
- **Axiom sweep** (own scratch): `P1_ewIter_lift`, `ewIter_lift_of_mono_infl`, `ewIter_lower`,
  `ewIter_infl`, `ewIter_monotone`, `ewIter_rel1_le`, `mem_ewBall_of_ewN_le` — ALL
  `[propext, Classical.choice, Quot.sound]` (kernel-pure; the lift engine carries no
  native_decide). `P2_trap8_instance_lift` / `P3_trap7_allomega_containment` — standard triple
  + exactly one `ofReduceBool` each, from `ewN` value anchors on the COMPUTABLE constructor norm
  (the noncomputable `ewIter` is never native_decided — correctly impossible and correctly
  avoided; the probes are inequality THEOREMS, not value anchors).

## 3. Ratified content

- **Z3 / T-Z7(i) fired and was handled as ordered.** The repo `norm` (CNF max-coefficient) has
  infinite fibers — kernel witness `cnf_norm_fiber_one_infinite` (every tower has norm 1). The
  lap adopted the constructor norm `ewN` (`ewN (oadd e n a) = ewN e + n + ewN a`; numerals sized
  `n`), with `ewBall : ℕ → Finset ONote` and the sorry-free completeness certificate
  `mem_ewBall_of_ewN_le` — the finite-fibers property is machine-certified, not assumed. `ewN`
  is not literally E–W's Def-13.3 `N` but satisfies its three load-bearing properties (finite
  fibers, numerals ~ n, the Lemma-19-class arithmetic provable); RATIFIED as the repo's gate norm.
- **`ewIter` is Def 16 verbatim**: base `f`; for `α ≠ 0` the max over
  `{β ∈ ewBall K | β < α ∧ ewN β ≤ K}`, `K = f (ewN α + m)`, of the DOUBLE application
  `ewIter f β (ewIter f β m)` — gate, double application, and max all faithful. Noncomputable
  (`Finset.max'` + classical decidability of `<` on ONote) — acceptable per the order.
- **P1 (the lift)**: `β < α → ewN β ≤ f 0 → ∀ x, ewIter f β x ≤ ewIter f α x` — proven
  kernel-pure, and from hypotheses WEAKER than ordered (Monotone + inflationary suffice; `EwF1`
  not needed). This is the exact proposition trap 8 refuted for `iterSlot`; it holding for
  `ewIter` is the deciding evidence for the whole E–W ruling.
- **P2**: the trap-8 instance (`f = ·+2`, `β = 2`, `α = ω`) — the lift PROVEN for all `x`
  (not just the argument-0 values). The dip is dead on the exact old counterexample.
- **P3**: the trap-7 reassembly containment
  `ewIter (rel1 f n) β ≤ rel1 (ewIter f α) n` at the `11 < 23` parameters — PROVEN for all `x`,
  riding the general engine `ewIter_rel1_le` (branch-slot iterate ≤ parent iterate at
  `max n x`), which is itself kernel-pure and general. Stronger than the ordered sanity check.
- **`Zef2` conforms to Z5**: per-node HYP `ewN α ≤ f 0` on every constructor; `exI` read stays
  `n ≤ f 0` (E3); `cut` gains the lh-shadow `φ.complexity ≤ f 0` (ratified as the PA-shadow of
  Def 23's `lh(C)` clause — `Form.complexity` is the repo's length proxy); `allω` branches stay
  `rel1 f n`, so each branch's own HYP reads `ewN (β n) ≤ f n` — the branch-indexed admissibility
  E–W's (⋀) prescribes. `e` phantom. `mono_f`/`change_H`/`mono_Hf` re-proven sorry-free.
- **`Zef2Prov`** slackens only the height (R2); the added `ewN α' ≤ f 0` conjunct mirrors what
  every root constructor already forces — self-certifying, not new strength.
- **Pass pin Z6-verbatim**: `Zef2 α e H f (c+1) Γ → EwF1 f → EwF2 f →
  Zef2Prov (collapse α) e H (ewIter f α) c Γ`. **C3 exit** `cutElimPass_exit_root_Zef2`
  typechecks as a real derivation from the pins with the bound
  `ewIter (ewRootSlot e m) α 0` VISIBLE and consumed.
- **`ewRootSlot e m x = 2(x + rel1 (hardy e) m x) + 3`** — the sanctioned Z4 fixed-base
  composition; `EwF1`/`EwF2` PROVEN for it; it dominates the canonical Zeh bound
  (`ewRootSlot e m 0 = 2·hardy e m + 3 ≥ hardy e m`), so the read-off is preserved up to the
  affine dressing.
- **Sorry ledger**: exactly 3, all disclosed statement pins. Discharge assignment (this ruling):
  `readoff_sigma1_Zef2` + `headline_readoff_Zef2` → **lap 8**, via the forgetful map (§4);
  `cutElimPass_Zef2` → the pass grind (laps 9+).

## 4. Judge note — the cheap discharge of both read-off pins

`Zef2` only ADDS hypotheses over the frozen `Zef`: a 6-case induction gives the forgetful
`Zef2.toZef : Zef2 α e H f c Γ → Zef α e H f c Γ` (drop `hαN`/`hcutRead`), after which both
read-off pins are the PROVEN `Zef` theorems composed with it. The lap-8 order MANDATES this
route — no re-proof, no drift risk, and it doubles as the conservativity witness
(`Zef2 ⊆ Zef`).

## 5. Judge AMENDMENTS on the P4 recipe (binding on the lap-8 order)

The written recipe (`zeh_to_zef2_budget`, verdict §P4) has two statement-level flaws — exactly
the class the pre-probe discipline exists to catch BEFORE they reach a port:

1. **The budget cannot be a function of the derivation.** `Zeh` is `Prop`-valued — there is no
   large elimination, so "define a recursive budget `B(d)`" is ill-typed. The pin must be
   EXISTENTIAL (`Zeh … → ∃ B, Zef2 … (budgeted slot B) …`), proven by induction
   (Prop-to-Prop is fine).
2. **"Finite Zeh derivation" is wrong, and arbitrary-`Zeh` transport is likely unprovable.**
   `Zeh.allω` is ω-branching — no max over branches exists. Branch obligations must ride the
   `rel1` relativization (branch `n` pays its HYP at `f n`), which requires the branch family's
   norms to be UNIFORMLY dominated (`ewN (β n) ≲ f n`-class). For an ARBITRARY `Zeh` derivation
   no such uniformity is available (`relOp` membership is information-free — K1), so a
   `zeh_to_zef2` theorem over all of `Zeh` is the wrong target and would likely have become the
   NINTH trap at the port. **Rung E's statement must target the PA-proof-sourced pipeline**
   (the W3-ratified K-hypothesis shape re-based onto `Zef2`), where the ω-branches are instances
   of one template with index-affine norms — exactly what E–W's Lemmas 32–36 provide.

Neither amendment touches lap-7's Lean artifacts (the recipe was prose); both are baked into
`REBUILD-Z-LAP8-ENTRANCE-2026-07-02.md`.

## 6. Process notes

- The lap ran OUTSIDE the treadmill (artifacts uncommitted, no `HANDOFF` baton, a codex-style
  summary instead) — content-wise fully conformant; the judge commits the artifacts with this
  ruling. If future statement laps run this way, have them commit — the freeze discipline wants
  hashes, not working-tree archaeology.
- Estimates: statement-lap cadence stays 1-session-accurate (this makes eight for eight at
  statement/judge time). Rung P consumed 1 of its ~4–7; lap 8 (port) estimated 1–2 sessions.

## 7. Gate state after this pass

- `src/` unchanged vs `ed261d7`: build 🟢 (1339), headline quadruple UNDRIFTED, OperatorZeh
  sorries = 1 (old pin 3, superseded-in-place, frozen), `blueprint_audit` 16/16.
- wip: `EwIter.lean` (kernel-pure engine + probes), `Zef2Calculus.lean` (3 disclosed pins) —
  both now committed evidence artifacts, read-only.
- Old `Zef`/`iterSlot`/pin-3 surfaces: FROZEN, untouched (retirement/supersession is lap-8
  business, judge-gated).
- Next fire: **lap 8 — the judged src port** per `REBUILD-Z-LAP8-ENTRANCE-2026-07-02.md`.
