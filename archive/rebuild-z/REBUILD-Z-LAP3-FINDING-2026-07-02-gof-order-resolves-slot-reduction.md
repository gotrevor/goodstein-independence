# REBUILD-Z LAP 3 — FINDING: resolution (2) is VIABLE; the reduction closes with output slot `g∘f`, not `f∘g`

> Continues `REBUILD-Z-LAP2-FINDING-2026-07-02-fixed-stage-reduction-wall.md`.  Lap 2 localized
> pins 1–2 to ONE gap (the principal-`exI` running-family stage cannot be lowered) and named
> resolution (2) — a function-slot `exI` bound in the judgment (the faithful E–W shape) — as the
> fix, but flagged it "architect-level, reopens the judgment form, viability unverified."
> **This lap verifies resolution (2)'s crux in-kernel and corrects the composition order.**
> Work site: `wip/ZefResolutionProbe.lean` (diagnostic, off the live build), build 🟢, headline
> no drift.

## Verdict: resolution (2) DISCHARGES the reduction — provided the output slot is `g∘f` (E–W's `f∘g` under the pins' slot naming)

The lap-2 wall was: the `Zeh` judgment bounds `exI` witnesses by the FIXED value `hardy e m`, so
the running-family cut (family member `fam n` at stage `max m₀ n`, witnesses up to
`hardy e (max m₀ n)`) cannot land at the fixed output stage `m`.  Resolution (2) replaces the
fixed `hardy e m` bound by a CARRIED slot `f : ℕ → ℕ` (E–W's number-theoretic operator; witness
bound `≤ f 0`, ω-branch relativization `rel1 f n`).  In that calculus the principal-`exI` cut
re-slots BOTH premises to ONE output slot, and the reduction closes iff that output slot dominates
both.  This lap settles which slot works.

### The composition order was backwards in the pins

E–W Lemma 25 writes the cut-reduction update as **`f∘g`** for `f,F ⊢ Γ,¬C` & `g,F ⊢ Γ,C`, i.e.
`(¬C-slot)∘(C-slot)`.  In our reduction `¬C = ∀⁰χ` (the inverted-∀ family) and `C = ∃⁰∼χ` (the
∃-side).  The pins name the ∀-family slot `g` and the ∃-side slot `f`, so E–W's `f∘g` =
`(∀-slot)∘(∃-slot)` = **`g∘f` in pin naming**.  The pins' literal output `f∘g` is the WRONG order.

### Kernel evidence (`wip/ZefResolutionProbe.lean`, all `#print axioms`-clean)

1. **`reslot_fog_FAILS`** `[propext, choice, Quot.sound]` — the pins' `f∘g` output does NOT
   dominate the family member, even for slots that are monotone, inflationary, AND `NormControlled`
   at the SAME control.  Concrete: `f = hardy ω = 2x+1` (minimal), `g = x²+2x+1` (both
   `NormControlled` at `(ω, 0)`), legal witness `n = 1 ≤ f 0 = 1`.  Then the family member's own
   witness budget is `(rel1 g n) 0 = g 1 = 4`, but `(f∘g) 0 = f (g 0) = f 1 = 3 < 4` — the family
   witness overflows the `f∘g` bound.  Refuted.

2. **`reslot_gof_family`** `[propext]` + **`reslot_gof_exside`** — the corrected `g∘f` output
   dominates BOTH premises for ANY monotone + inflationary slots (every `NormControlled` slot is
   inflationary, `normControlled_infl`):
   - family member: `rel1 g n ≤ g∘f` pointwise, given `n ≤ f 0` (because `max n x ≤ f x`);
   - ∃-side reduct: `f ≤ g∘f` pointwise (because `g` is inflationary).

   So a slot calculus with output slot `g∘f` re-slots both cut premises by a plain `mono_f`
   (pointwise-`≤` slot weakening) — the exact move the fixed-`hardy e m` bound could not make.

3. **`gof_normControlled`** `[propext, choice, Quot.sound]` — the corrected conjunct
   `NormControlled (g∘f) e m` is still dischargeable: `normControlled_comp_running` with the roles
   swapped (outer = ∀-family slot `g`, inner = ∃-side slot `f`).

## Why the whole reduction (not just the principal cut) ports to the slot calculus

The lap-2 `redDeriv` already closes EVERY case but the principal `exI` in the STAGE calculus.
Those cases port to the slot calculus mechanically (the slot passes through exactly as the stage
did), and the two axis-critical points both hold:

- **principal `exI`** — closes via the `g∘f` re-slot above (this lap).
- **`allω` reassembly** — the branch outputs carry slot `g ∘ (rel1 f n)`, and
  `rel1_comp : rel1 (g∘f) n = g ∘ rel1 f n` (ALREADY in `OperatorZeh.lean:642`, the "reassembly
  algebra") re-expresses that as `rel1 (g∘f) n` — exactly the slot the output `allω` node's
  `n`-th branch must carry.  So the composed output slot threads through the ω-rule with no
  residue (E–W's Lemma-25 commutation, anticipated by the src lemma).

Hence: **resolution (2) makes pins 1–2 TRUE**, with arbitrary `NormControlled` slots — NO E–W
`(f.1)/(f.2)` growth class is needed for the REDUCTION step, only the composition ORDER `g∘f`.
(The growth class is still needed for `cutElimPass_Zf`/Lemma 30's ITERATE, pin 3 — untouched.)

## Concrete next step (for the architect / the LOCK §1 owner)

Resolution (2) is the adopt-recommendation, now de-risked:

- **Amend LOCK §1's `Zeh` judgment**: carry a slot `f : ℕ → ℕ`; `exI` bound `n ≤ f 0`; `allω`
  branch slot `rel1 f n`.  (The stage `m` is subsumed — `NormControlled f e m` becomes the
  root instantiation `f = hardy e (max m ·)`.)
- **Restate pins 1–2** with output slot **`g∘f`** (not `f∘g`).
- The reduction then discharges by porting lap-2's `redDeriv` (all cases already proven) with the
  slot substitution + the `g∘f` re-slot + `rel1_comp` reassembly.

Next grind lap (if the slot-judgment amendment is ratified, or as a `wip/` feasibility capstone):
build the minimal slot calculus `Zef` and port `redDeriv` to close the FULL reduction sorry-free —
the definitive proof that pins 1–2 are provable.

## What this does NOT change

- The CURRENT `src/GoodsteinPA/OperatorZeh.lean` pins stay as the lap-2 escalation left them
  (fixed-`hardy e m` bound; the gap is genuine in that calculus — resolution (2) is a JUDGMENT
  amendment, LOCK §1, not a grind-lap edit).
- Pin 3 (`cutElimPass_Zf`) stays FORBIDDEN as written.  Route-A / Δ₀ stay FORBIDDEN.
- Headline `peano_not_proves_goodstein` no drift.
