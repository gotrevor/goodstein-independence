# REBUILD-Z — LAP-5 MINI-VERDICT: pin-3 restatement executed; STOP for the judge (2026-07-02)

> **Scope.** Executed the STATEMENT LAP mandated by `REBUILD-Z-LAP5-ENTRANCE-2026-07-02.md`
> (deliverables a–e). No pin-3 body grinding. Every commit green, headline undrifted. This file is
> the mini-verdict; the run STOPS here for the judge/architect pass (entrance-lock §2 lap-5, §5).
> Commit `435ed72` on branch `plan`.

## 0. Bottom line

The lap-5 statement deliverables all landed and kernel-check clean:

- Iterate bricks ported to `src` (sorry-free, axiom-clean).
- `collapse`, `iterCount`, `iterSlot` **defined explicitly against ONote** with the E–W paper open;
  the five C5 obligation lemmas are **PROVEN** (not sorried) and axiom-clean.
- Pin 3 `cutElimPass_Zf` **restated per C1–C2** (body `sorry`); the retired vacuous `∃ f'`/`raise e α'`
  form **deleted**.
- The C3 anti-vacuity composed-exit corollary `cutElimPass_exit_root` **typechecks at statement level**
  with the count-bearing bound `iterSlot (rel1 (hardy e) m) α 0` visible — the read-off DOES consume
  the count.

**No pre-registered trigger fired** in a blocking way. T-Z5(i) and T-Z5(ii) are cleared (the coupling
states without `∃`/branch-raise; the exit consumes the count). T-Z5(iii) is the sole live risk and is
by construction a GRIND-lap question (the `allω`-lane Lemma-19 arithmetic), deferred to laps 6–7.

**Requested of the judge:** ratify (or amend) the three definitions and the pin shape below, then
green-light laps 6–7 per entrance-lock §5.

## 1. The definitions (deliverable b) — grounded in the E–W paper

All three are explicit ONote-grounded definitions in `src/GoodsteinPA/OperatorZeh.lean` §5b, chosen
with `papers/eguchi-weiermann-2012-operator-controlled-id1.md` open:

| symbol | definition | E–W grounding |
|---|---|---|
| `collapse α` | `expTower α` = `ω^α` = `oadd α 1 0` | Lemma 27's Ω-free predicative shadow `φ 0 β = ω^β` for one rank step; iterated `c`× it is the rank-lowering tower `Ω_c(α) = Ω^{Ω_{c-1}(α)}` (paper §5, line 205) |
| `iterCount α` | `norm α + 1` | Lemma 19 count `N(α) ≤ f^{F^α(0)}(0)` — a ℕ readoff of the ordinal via the repo norm `N`; `+1` mirrors Lemma 30's `f^{F^α(0)+1}` and keeps `iterSlot f 0 = f` |
| `iterSlot f α` | `f^[iterCount α]` (`Function.iterate`) | Def 16's norm-gated iterate `f^α`, realized as a plain iterate at a count that **reads the ordinal** — NOT a fixed `f^[k]` |

**Why these satisfy C2's "no plain `f^[k]`.** At an `allω` node the branch slot is
`rel1 (iterSlot f (β n)) n = rel1 (f^[iterCount (β n)]) n`. Since `β n` is unbounded (e.g. the W4B
config's `β n = ω·(n+1)`, `iterCount (β n) = n + 2`), the per-branch iterate count grows with `n`: no
single `f^[k]` dominates the family — exactly the branch-unbounded demand the architect flagged (C2,
the same demand that killed the `(k,d)` calculus). The index reads the ordinal, so the family is an
ordinal-indexed iterate, not a fixed one.

**C5 obligations — all PROVEN (axiom-clean), not deferred:**

- `collapse_NF` — NF-preserving (`expTower_NF`).
- `collapse_strictMono` — `β < α → collapse β < collapse α` (`expTower_lt_expTower`): the descent the
  rank-lowering induction needs (`Zekd.add_osucc_descent`-class compatibility).
- `iterSlot_monotone` / `iterSlot_infl` — slot stays `Monotone` + inflationary through the pass
  (the `iter_monotone`/`iter_infl` bricks).
- `iterSlot_zero` — `iterSlot f 0 = f` (α = 0 = cut-free axiom, slot unchanged).

## 2. The restated pin (deliverable c)

```lean
theorem cutElimPass_Zf {α e : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Seq} (f : ℕ → ℕ)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef α e H f (c + 1) Γ) (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x) :
    ZefProv (collapse α) e H (iterSlot f α) c Γ := by
  sorry
```

Matches the entrance-lock C2 target shape verbatim in content:

- **C1** — control `e` untouched (no `raise e α` in the output); ordinal collapses, slot iterates.
- **C2** — output slot is the pinned ordinal-indexed iterate `iterSlot f α`; height `collapse α`,
  rank `c` (one predicative rank step `c+1 → c`); no `∃`, no plain `f^[k]`.
- **C4** — slots `Monotone` + inflationary hypotheses in; no new `axiom` (one disclosed `sorry` pin,
  named laps 6–7). Control `e` and `ZefProv`'s single ∃-ordinal wrapper are the only quantifiers.

The retired form (`∃ (α' f'), … ZehProv α' (raise e α') H m c Γ ∧ NormControlled f' (raise e α') m`)
is **deleted** — it belonged to the retired ℕ-stage `Zeh`/raised-control world (fifth-trap corpse per
C1) and had a kernel-vacuous `∃ f'` (`normControlled_exists_trivial`).

Deviation note (disclosed for the judge): the target shape in the lock elides the NF side conditions;
the concrete theorem carries `heNF`, `hαNF`, `hαH` (needed by the eventual proof; harmless to the
statement). No other divergence from the locked shape.

## 3. C3 anti-vacuity check (deliverable d) — the count IS consumed

```lean
theorem cutElimPass_exit_root {α e : ONote} {H : ONote → Prop} {m : ℕ}
    {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef α e H (rel1 (hardy e) m) (0 + 1) {(∃⁰ φ)}) :
    ∃ n ≤ iterSlot (rel1 (hardy e) m) α 0, atomTrue (φ/[nm n]) := by
  obtain ⟨α', _, _, _, D'⟩ :=
    cutElimPass_Zf (rel1 (hardy e) m) heNF hαNF hαH D
      (rel1_monotone (hardy_monotone e) m) (rel1_infl (le_hardy e) m)
  exact headline_readoff_Zef hφinst D'
```

- Composes ONE pass (rank `1 → 0`) with `headline_readoff_Zef`, at the canonical root slot
  `f = rel1 (hardy e) m` (the `zeh_to_zef` image, `f 0 = hardy e m`).
- **Bound `iterSlot (rel1 (hardy e) m) α 0 = (rel1 (hardy e) m)^[norm α + 1] 0` is VISIBLE in the
  statement and reads the count `iterCount α`.** A severed-slot (Q2) statement whose count the read-off
  never touched would not typecheck with the count in the bound; this one does.
- **Kernel footprint** = `[propext, sorryAx, Classical.choice, Quot.sound]`. The only non-clean axiom
  is `sorryAx`, and it enters solely through the pin body — proof that the corollary genuinely routes
  through the pin's iterate output (anti-vacuity PASSES). `iter_comp`, `iterSlot_monotone`, and the
  other carriers are all axiom-clean.

(This is the literal C3 shape `(iterSlot …) 0`. The general `c`-fold iterated exit is a grind-lap
composition — it needs slot-index tracking across `ZefProv`'s ordinal slack and is deferred.)

## 4. Pre-registered triggers (entrance-lock §3)

- **T-Z5(i)** — *coupling un-stateable without `∃`/branch-raise?* **NOT FIRED.** Stated cleanly as
  `f^[iterCount α]` with `iterCount : ONote → ℕ` a total function; no existential, no W4B branch-raise
  shape. The ordinal-indexing lives entirely in `iterCount α`.
- **T-Z5(ii)** — *composed exit fails to consume the count?* **NOT FIRED.** `cutElimPass_exit_root`
  typechecks with the count in the bound and `sorryAx` routing through the pin.
- **T-Z5(iii)** — *`allω`-lane Lemma-19 arithmetic kernel-obstructed on ONote?* **NOT TESTED this lap**
  (a grind-lap question by construction). This is the live risk: whether `iterCount := norm · + 1` is a
  count large enough that every cut-free witness norm is `≤ f^[iterCount α] 0` (the Lemma-19
  domination). If `norm` proves too weak in the `allω` lane, the entrance lock's prescribed response is
  architect-level (a different `collapse`/`iterCount` normal form), NOT a body grind. Flagged, not
  triggered.

## 5. Verification (all real `lake build` / `#print axioms`)

- `lake build` — **1333 jobs, green.** Sole `src` §5 `sorry` = pin 3 (`cutElimPass_Zf`, line 1761).
- `peano_not_proves_goodstein` — `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]`
  — **UNDRIFTED** (no `sorryAx` on the headline).
- `lake exe blueprint_audit` — **PASSES**, 13 nodes consistent, 0 warnings.
- C5 carriers `#print axioms`: `collapse_NF`/`collapse_strictMono` `[propext, choice, Quot.sound]`;
  `iterSlot_monotone` no axioms; `iterSlot_infl`/`iterSlot_zero` `[propext, Quot.sound]`; `iter_comp`
  no axioms.

## 6. The decision requested of the judge

1. **Ratify or amend** the three definitions (`collapse := ω^α`, `iterCount := norm · + 1`,
   `iterSlot f α := f^[iterCount α]`) and the pin shape §2. The one open design judgment is whether
   `iterCount := norm · + 1` is the right ℕ-count normal form, or whether the `allω`-lane arithmetic
   (T-Z5(iii)) demands a faster-growing/ordinal-native count now rather than after a grind probe.
2. If ratified, green-light **laps 6–7** (the pass grind) per entrance-lock §5: `--max-laps 3
   --max-duration 6h`, scoped to "discharge `cutElimPass_Zf` per the ratified lap-5 verdict; FORBIDDEN
   list §4", with the `∃`-cut lane via `iter_comp` and the `allω` lane carrying the Lemma-19/20
   arithmetic (the likely long pole).

**Nothing else is permitted this run** (entrance-lock §5: a second lap 5 has nothing to do). STOP.
