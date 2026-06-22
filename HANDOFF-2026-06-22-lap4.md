# HANDOFF — 2026-06-22 (lap 4)

> **NEXT LAP FIRST ACTION:** read this + `STATUS.md` lap-4 finding + `ON-LINE-REQUEST.md`. The
> project pivoted this lap on a **machine-checked architectural finding**: the completed M5
> cut-elimination is for a calculus that **cannot reach the headline**. Do **not** keep building M4
> on `src/Zinfty.lean` as-is. Priority is now `PENDING_WORK.md` **O0**.

Branch `plan`. Headline build **green** (`lake build GoodsteinPA`). Headline
`Statement.peano_not_proves_goodstein` is **still a literal `sorry`** (anti-fraud — correct; the
chain is not yet built). `Defs.lean`/`Bridge.lean` RHS/`goodsteinTerminates` LOCKED, untouched.

## What this lap did — found (and machine-checked) that the M5 calculus is off the headline path

The prior laps built an axiom-clean ε₀ cut-elimination for `Z_∞` in `src/GoodsteinPA/Zinfty.lean`.
**Ground-truthing it against Towsner §10–§19 this lap revealed it cannot close the headline:**

- Its `∃`-rule (`Deriv.exI`) puts **no bound on the witness numeral**; its ordinal measure `o` does
  **not** track Towsner's numeric index `k`. So its cut-free fragment *proves* the Goodstein
  sentence `∀x∃y g_y(x)=0` at ordinal **2** — making Towsner's lower bound (Thm 17.1) **false** for
  it. The three-theorem sandwich (16.7 ⟹ 19.9 ⟹ 17.1) only closes if all three track the
  witness/Hardy bound `value(t) ≤ h_α(k)`. M5 dropped it (correct *for cut-elim in isolation* — the
  prior "k not needed" claim — but a dead end for the chain).

All machine-checked + axiom-clean in **`wip/WitnessBound.lean`** (not in build target):
- `unbounded_proves_goodstein` — the witness-**unbounded** cut-free calculus derives `gAll` at `2`.
- `B` — the corrected **witness-bounded, Hardy-indexed `(α,k)`** calculus (Towsner §15).
- `lowerBound_existential` (+`_real`) — the `∀`-free existential-fragment lower bound: the
  witness-bounded calculus **cannot** derive `gEx n` once `h α k < G n`. The irreducible reason the
  bound bites. Grounded against the real Goodstein function `G n := sInf {m | goodsteinSeq n m = 0}`
  with `G_le_of_atomTrue` (HG) + `goodstein_zero_succ` (once-zero-stays-zero) proved concretely.
- `bounding` (disclosed `sorry`) + `lowerBound` — the **full** Towsner 17.1 as an honest
  decomposition: the contradiction-extraction (`lowerBound`, given Goodstein domination) is
  machine-checked; the single gap is the `bounding` lemma (= the `I∀`/accumulating-existentials
  invariant subtlety). `#print axioms lowerBound` = `[propext, sorryAx, choice, Quot.sound]` — the
  `sorryAx` enters *only* via `bounding`.

## The remaining frontier(s) — what's actually hard now

1. **The `bounding` lemma (M6 crux).** Towsner's stated 17.1 invariant (a,b,c) looks **insufficient**
   for the `I∀` case when *other* existentials are pending in the sequent (a cut-free derivation of
   `{gAll}` genuinely accumulates them by re-applying `I∀` before discharging an earlier `∃`): the
   old existential `gEx m` needs `G(m) > h_{βₙ}(n)` at the grown numeric bound `n`, which fails for
   the large `n` that domination forces. Verified by hand across ~4 attempts; this is *the* subtlety
   that makes 17.1 "the hardest theorem." **Do not confabulate it** (charter rule for infinitary
   proof theory). `ON-LINE-REQUEST.md` asks for the rigorous invariant (Schwichtenberg–Wainer
   boundedness lemma / Buchholz `H`-controlled derivations / Buss Handbook ch. II) — likely the clean
   route is a **single-ordinal `H`-controlled** reformulation rather than Towsner's two-index `(α,k)`.
2. **Architecture decision (gates everything downstream).** Towsner `(α,k)` vs Buchholz
   single-ordinal `H`-controlled. Resolve via the request **before** redoing cut-elimination, so the
   `k`-tracking redo targets the right system.
3. **Cut-elimination with `k`.** `src/Zinfty.lean`'s inversion/reduction *strategy* ports; only the
   bound bookkeeping changes. Needed so M5's cut-free output carries the `(α,k)` bound 17.1 refutes.
4. **PA↔PA⁺ language gap.** Our headline is real-`ℒₒᵣ` PA with an **opaque Σ₁** `goodsteinSentence`,
   not Towsner's extended-language `∀x∃y g_y(x)=0`. The arithmetization bridge Towsner *skips*
   (Remark 10.3) is a separate deep girder. Re-evaluate **Route A** (via `Con(PA)`, `Reduction.lean`)
   which stays entirely in real PA and sidesteps this — vs Route B's external-but-bridged path.
5. **Hardy hierarchy `h_α` + `τ` (architecture-independent, startable).** Discharges `Hmono`/`Hdom`.
   mathlib has `ONote.fundamentalSequence`/`fastGrowing` but **no** growth lemmas, no Hardy `h_α`, no
   Goodstein connection. Building it (+ Goodstein domination, Towsner §6–§9 = Part 1) is a large
   decoupled sub-project overlapping Track 1 `lean-formalizations Logic/FastGrowing`. Safe in any
   architecture. **Started** (`wip/FastGrowing.lean`): `fastGrowing_id_le` (`n ≤ fastGrowing o n`,
   axiom-clean) — the inflationary half is clean/separable. **Confirmed** the *monotonicity* half
   (`Hmono`/`Hmono_n`) genuinely needs the τ coefficient-control (Towsner §8) — its `fastGrowing`
   limit case reduces to ordinal-monotonicity at fixed `n`, false for small `n` without τ. Goodstein
   side started too (`G`, `goodstein_zero_succ`, `atomTrue_iff_G_le`).

## Recommended next-lap order (hardest-first, but unblock first)
1. Harvest any `ON-LINE-FINDINGS-*.md` for the `bounding` invariant + architecture; **decide** the
   calculus (likely `H`-controlled single-ordinal). Re-state `B`/`bounding` accordingly in `wip/`.
2. With the right invariant, **prove `bounding`** → `lowerBound` becomes real (the headline's teeth).
3. In parallel (architecture-independent): build the **Hardy hierarchy + monotonicity** to discharge
   `Hmono`, and start **Goodstein-dominates-Hardy** (Towsner §5–§9) to discharge `Hdom`.
4. Only then: cut-elimination-with-`k` redo, the M4 embedding (now witness-bounded), and the PA↔PA⁺
   bridge / Route-A re-evaluation.

## Build / file map
- `src/GoodsteinPA/{Defs,Encoding,Bridge,Statement}.lean` — Phase 0 (headline `sorry`). LOCKED bits.
- `src/GoodsteinPA/{Computability,Reduction}.lean` — M1 (axiom-clean) + M2 (Gödel II hook).
- `src/GoodsteinPA/Zinfty.lean` — `Z_∞` + COMPLETE `(α,c)` cut-elimination (M3+M5), axiom-clean —
  **a verified component, but OFF the headline path** until cut-elim tracks `k` (lap-4 finding).
- **`wip/WitnessBound.lean`** — lap-4: the witness-bound finding, the corrected calculus `B`, the
  existential lower bound (proved), and the full 17.1 decomposed to the `bounding` frontier.
- `wip/Zinfty.lean` — superseded `AForm` prototype (history; keep).
- `STATUS.md` (lap-4 finding), `PENDING_WORK.md` (**O0** top), `ON-LINE-REQUEST.md` (open).

No Aristotle job (offline). `ON-LINE-REQUEST.md` is OPEN (the `bounding` invariant + architecture).
