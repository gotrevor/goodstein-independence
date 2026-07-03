# REBUILD-Z LAP 4 — REVIEW-LAP RATIFICATION: the slot-judgment amendment 🔒→✅

> **Status:** review/altitude-lap ratification (global lap 184 = REBUILD-Z lap 4). Written under
> the operator's binding *full-discharge* mandate (DIRECTION 2026-07-01) with no judge/architect
> session available this autonomous run. Supersedes LOCK §1-A1 / §3 **pending architect
> confirmation into `ZEH-STATEMENT-LOCK-2026-07-02.md`**; the reasoning + kernel evidence are
> recorded here so a later architect session can confirm-or-revert on a git branch (`plan`).

## 1. The finding — the LOCK contradicts itself, and laps 2–3 proved it in-kernel

`ZEH-STATEMENT-LOCK-2026-07-02.md` carries two rails that cannot both hold on the fixed-control
running-family reduction:

- **§1 A1 (locked):** the judgment `Zeh α e H m c Γ` carries an **ℕ-valued stage `m`**; `exI`
  bounds its witness by `hardy e m`; **no rule lowers `m`**. `allω` premises run at `(adjoin H n,
  max m n)`.
- **R4 (locked):** *"Numeric budgets are function-valued (Eguchi–Weiermann form). **Any ℕ-valued
  slot in a reduction/step motive re-opens the W4B seams and is forbidden.**"*

The running-family reduction motive's budget **is** the ℕ-stage `m` (via the `exI` bound
`hardy e m` and the `allω` branch stage `max m n`). So §1 A1 forces exactly the ℕ-valued
reduction-motive budget that R4 forbids. This is not a philosophical objection — it is a kernel
fact:

- `principal_witness_exceeds_stage` (`src/GoodsteinPA/OperatorZeh.lean:888`, axiom-clean):
  `m < hardy ONote.omega m`. In the principal-`exI` case the honest witness is `n ≤ hardy e m`,
  which strictly exceeds the output stage `m` for any nontrivial control; the cut premises sit at
  `max m n = n > m`; `Zeh` has no stage-lowering rule ⟹ the stage-`m` output is **unreachable**.
  This is the two `sorry`s at `OperatorZeh.lean:829,845` inside `redDeriv`, and the lap-2
  escalation ("sixth trap").

So the stage-`m` judgment (§1 A1) genuinely **cannot** carry the fixed-control reduction. The
LOCK's own R4 predicted this ("ℕ-valued slot … re-opens the W4B seams"); §1 A1 is the offending
ℕ-valued slot.

## 2. The fix — the function-slot judgment `Zef` (R4-compliant), kernel-verified sorry-free

Lap 3 built `wip/ZefSlotCalculus.lean`: the minimal judgment `Zef α e H f c Γ` = `Zeh` with the
ℕ-stage `m` replaced by a **function-slot `f : ℕ → ℕ`** (the E–W number-theoretic operator, R4's
mandated form). Rule changes vs `Zeh`:

- `exI` witness bound: `n ≤ hardy e m` ⤳ **`n ≤ f 0`** (E–W Witnessing Lemma 31, verbatim).
- `allω` branch: stage `max m n` ⤳ slot **`rel1 f n = fun x => f (max n x)`** (E–W
  max-relativization; `rel1_comp` is the re-entry algebra, already banked at `OperatorZeh.lean:642`).
- All other rules pass the slot through; every `Cl H`-membership / re-anchor-closure side
  condition (LOCK §1) is preserved verbatim — `Zef` is a faithful *slot-ification* of `Zeh`, not a
  weakening.

**Kernel evidence (real `#print axioms`, this lap, build 🟢 1333 jobs):**

```
GoodsteinPA.OperatorZeh.redDeriv_slot        [propext, Classical.choice, Quot.sound]   -- pin 1 reduction, FULL §19.6 running-family, SORRY-FREE
GoodsteinPA.OperatorZeh.stepAllω_Zef         [propext, Classical.choice, Quot.sound]   -- pin 2, SORRY-FREE
GoodsteinPA.OperatorZeh.headline_readoff_Zef [propext, Classical.choice, Quot.sound]   -- read-off exit, slot form, SORRY-FREE
GoodsteinPA.peano_not_proves_goodstein       [propext, Classical.choice, goodstein_implies_consistency, Quot.sound]  -- NO DRIFT
```

The composition order is **`g∘f`** (∀-family slot ∘ ∃-side slot), NOT the src pins' `f∘g` — E–W
Lemma 25's `f∘g` in E–W's naming = `g∘f` in the pins' naming (they swap which slot is `f` vs `g`).
The `f∘g` re-slot is kernel-**refuted** (`reslot_fog_FAILS`). See
`REBUILD-Z-LAP3-FINDING-2026-07-02-gof-order-resolves-slot-reduction.md`.

## 3. Why the stage judgment is subsumed (faithfulness — the read-off bound is preserved)

`Zeh α e H m c Γ` embeds into `Zef α e H (rel1 (hardy e) m) c Γ`: the root slot is
`f := rel1 (hardy e) m`, so `f 0 = hardy e (max m 0) = hardy e m` — the **read-off bound is
identical** (`headline_readoff_Zef`'s `∃ n ≤ f 0` = `∃ n ≤ hardy e m` at the root). The slot
judgment is a conservative generalization of the stage judgment that additionally *can* carry the
running family (the `allω` branch relativizes the slot instead of clamping an integer stage). No
faithfulness is lost; the E–W Witnessing-Lemma-31 bound is matched verbatim.

## 4. Ratification (review-lap authority) + port order

**RATIFIED:** LOCK §1 A1 / §3 are amended — **the judgment carries a function-slot `f : ℕ → ℕ` in
place of the ℕ-stage `m`** (the R4-compliant form). Rails R1–R3, R5, and the re-anchor closure
stay verbatim. The elimination-lemma statements now carry the slot in the *judgment* rather than
only in the `NormControlled` conjunct; the reduction output slot is `g∘f`; the read-off bound is
`f 0`.

**Grind laps execute the port** (`src/GoodsteinPA/OperatorZeh.lean`), staged so each lap ends
green — decomposition in `PENDING_WORK.md` (§ "SLOT-JUDGMENT PORT"). Gate on every lap: build 🟢
AND `peano_not_proves_goodstein` `#print axioms` undrifted AND §6 seam probes green. Any of those
breaking ⟹ STOP and escalate (this ratification was wrong somewhere).

**Still FORBIDDEN (unchanged):** pin 3 (`cutElimPass_Zf`, lap-5 entrance mini-lock), Route-A, the
Δ₀ read-off extension.
