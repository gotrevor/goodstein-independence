# REBUILD-Z LAP 1 — VERDICT (Scope-A, statement lap)

> Deliverable of `REBUILD-Z-ORDER-2026-07-02.md` Scope-A (A1 + A2 + A3), executed under
> `ZEH-STATEMENT-LOCK-2026-07-02.md`.  Work site: `src/GoodsteinPA/OperatorZeh.lean` (wired
> into the `GoodsteinPABlueprint` build tree).  **STOP for the judge** before any reduction
> discharge (laps 2+ are gated on ratification of this verdict).

## Verdict: **PASS — the f-slot statements compose at both Z1 seams; T-R(i) does NOT fire.**

The calculus core seeded verbatim (A1), the first Z1 pin (`allInv_Zeh`) discharged to a real
axiom-clean proof (A3, a bonus — the order only asked for a grind attempt), and the E–W
function-slot elimination suite drafted with both W4B seams re-verified in the f-form (A2).
No FAIL / T-R criterion is met: neither seam needed a carrier the E–W function-slot cannot
supply, and every membership/algebra obligation at the seams is a real proof (no sorried
memberships, no sorried slots — the three `sorry`s are exactly the §5 statement pins).

## What was built (evidence)

`src/GoodsteinPA/OperatorZeh.lean` — full repo green (`lake build`, 1333 jobs), **exactly
three `sorry`s** (the §5 pins), **no new `axiom` declarations**.  Real `#print axioms`:

```
allInv_Zeh                          [propext, choice, Quot.sound]        (A3 — PIN 1 DISCHARGED)
Zeh.mono_H                          [propext, choice, Quot.sound]
readoff_sigma1 / headline_readoff   [propext, choice, Quot.sound]        (exit, verbatim, proven)
rel1_comp                           (no axioms)
seam1_bump_absorbed_by_composition  (no axioms)
seam2_function_slot_payable         [propext, choice, Quot.sound]
normControlled_root/_rel1           [propext, choice, Quot.sound]        (root + ω-node re-entry)
probe_allomega_reassembly_Zf        [propext, choice, Quot.sound]        (SEAM 2, sorry-FREE)
probe_cut_all_arm_Zf                [propext, sorryAx, choice, Quot.sound] (SEAM 1, pin-only sorry)
cutReduceAllAuxRunning_Zf           [propext, sorryAx, choice, Quot.sound] (PIN, lap 2–4)
stepAllω_Zf                         [propext, sorryAx, choice, Quot.sound] (PIN, lap 5–7)
cutElimPass_Zf                      [propext, sorryAx, choice, Quot.sound] (PIN, lap 5–7)
```

`sorryAx` appears ONLY on the three §5 pins and on the seam-1 arm probe, whose sole
sorry-dependence is the reduction pin — `allInv_Zeh` is now genuinely sorry-free, so the arm
no longer depends on it as a pin.

## A1 — the verbatim seed (LOCK §1)

`§0` transforms, `§1` operator layer (`IsOperator`/`Cl`/`adjoin`/`relOp` + K1–K3), `§2` the
`Zeh` inductive + `mono_H` + `ZehProv`, and `§3` the read-off exit
(`readoff_sigma1`/`headline_readoff`) are the spike forms verbatim (namespace change only,
`SpikeZ1 → OperatorZeh`).  The read-off is proven, per-instance, no evaluator, no `H`-data —
the fixed M2 exit.

## A3 — `allInv_Zeh` DISCHARGED (Z1 pin 1, was a statement pin)

`§4`.  A real six-case induction (`axL`/`wk`/`weak`/`allω`/`exI`/`cut`) mirroring the banked
`Zekd.allInv` (`OperatorZinfty.lean:484`).  The `Zekd` numeric bookkeeping (`max k n₀`,
`d`-inert) re-keys cleanly to the **stage axis** `max m n₀` and the **relativization axis**
`adjoin H n₀`.  The one genuinely new obligation: inverting under an `allω`/`exI`
sub-derivation adjoins `n₀` ON TOP of the branch relativization, giving nested
`adjoin (adjoin H n) n₀` / doubled `adjoin (adjoin H n₀) n₀`.  Three reassociation lemmas
absorb it — `adjoin_swap` (operator-side analog of `Zekd`'s `max (max k n₀) n = max (max k n) n₀`
reshuffle), `adjoin_idem`, `adjoin_base_mono` — each a two-line `rintro`.  `mono_H` carries the
derivation across the (provably equal, `≤`-both-ways) operator/stage endpoints.  Since the
minimal `Zeh` core has only the six mandated constructors, the induction is strictly SHORTER
than `Zekd`'s (no `andI`/`orI`/`verumR`/`trueRel`/`trueNrel`).

The A3 clause's **companion inversions** are also discharged (§7, all axiom-clean):
`orInv_Zeh`, `andInvL_Zeh`, `andInvR_Zeh` — the propositional inversions mirroring the
banked `Zekd` suite.  They keep the same `(α, e, H, m, c)` (no stage/relativization re-key),
and since the minimal core has no `andI`/`orI` intro rule, `φ ⋏ ψ`/`φ ⋎ ψ` is never
principal — every case threads past a passive side formula.  Reused by the cut-elimination
assembly (laps 5–7) for cuts on propositional formulas; independent of the §5 f-slot
statements.

## A2 — the f-slot elimination statements (LOCK §3/§6, NOT-LOCKED — the judge gate)

`§5`.  The E–W number-theoretic operator slot `f : ℕ → ℕ` (arXiv:1205.2879, Def. 23 +
Lemma 25) is threaded in the elimination STATEMENTS; the judgment `Zeh` stays f-free
(LOCK §3, held).  The carrier is `NormControlled f e m := ∀ x, hardy e (max m x) ≤ f x`:

* **root instantiation** — `normControlled_root : NormControlled (hardy e) e 0` (proven);
* **ω-node relativization** — `normControlled_rel1 : NormControlled f e m →
  NormControlled (rel1 f n) e (max m n)` (proven; `rel1 f n x = f (max n x)`), the semantic
  payload of `rel1_comp`;
* **composition at principal cuts** — the reduction/step pins output the COMPOSED slot
  `f ∘ g` at the raised control, carried as the `NormControlled (f ∘ g) (raise e …) m`
  conjunct.

The three pins (bodies `sorry`, named discharging laps):

| pin | shape | lap |
|-----|-------|-----|
| `cutReduceAllAuxRunning_Zf` | running-family §19.6 reduction; output `ZehProv (osucc (α+γ)) (raise e α)` ∧ `NormControlled (f∘g) …` | 2–4 |
| `stepAllω_Zf` | common-control (A2) principal ∀/∃ step; IHs at ONE control `E`; output `raise E δ`, `f∘g` | 5–7 |
| `cutElimPass_Zf` | one elimination pass `c+1 → c` at towered control; f-slot transfinitely iterated (`f ↦ f^{…}`, existential) | 5–7 |

### The two seams RE-EXPRESSED in the f-form (`§6`, real proofs — the deciding check)

* **Seam 1 (∀/∃ reduction's output-budget bump).**  `probe_cut_all_arm_Zf` runs the arm
  end-to-end: the now-PROVEN `allInv_Zeh` produces the running family in exactly
  `cutReduceAllAuxRunning_Zf`'s input shape (the handoff type-checks); the f-slot reduction
  pin fires; the emission carries NO output-side numeric slot (membership is closure-derived,
  `Cl.osucc (Cl.add …)`) AND its control rides the composed slot `f ∘ g`.  Real proof, sole
  sorry-dependence the reduction pin.  The W4B fatal slot `(d + norm e + 1) + norm αf + 1` is
  GONE; the algebraic residue it would have left is absorbed by composition
  (`seam1_bump_absorbed_by_composition`, axiom-free).
* **Seam 2 (ω-node's uniform-`d` re-assembly).**  `probe_allomega_reassembly_Zf` (sorry-FREE):
  the reduction-output family over the branch-unbounded two-level configuration re-enters
  `Zeh.allω`, with each branch's numeric control carried by the relativized f-slot
  `rel1 f n` (`normControlled_rel1`).  The branch-`n` demand that overflowed every `Zekd`
  `d`-slot (`SpikeW4B.seam2_no_uniform_slot`) is paid by ONE function slot through its own
  relativization (`seam2_function_slot_payable`, `rel1_comp`).

**T-R(i) does not fire:** the E–W carrier composes at both seams where the ℕ-slots failed;
no third carrier was needed.

## Rails audit (LOCK §2)

* R1 (no numeric fact through `H`-membership): held — the f-slot, not membership, carries all
  numeric data; memberships are closure bookkeeping only (K1 vacuity intact).
* R2 (existentials at the root only): held — `ZehProv`'s ∃-ordinal is the one wrapper; no
  someK-level existential inside any induction motive.
* R3 (`e` constant through a derivation; control changes at statement level): held —
  `Zeh` has no control-changing rule; the raise appears only in the §5 statement conclusions
  (`raise e α`), once per reduction/pass; no `mono_e`.
* R4 (numeric budgets function-valued): held — every numeric slot in §5 is `ℕ → ℕ`
  (`f`, `g`, `rel1 f n`); no ℕ-valued slot in any step/reduction motive.
* R5 (no new axioms; sorries only as disclosed pins): held — 3 sorries, all §5 pins with
  named laps; no `axiom`; `native_decide` unused.

## For the judge (what to gate)

The §5 f-slot signatures are the NOT-LOCKED lap-1 draft (LOCK §6).  Points the judge should
weigh before opening the reduction-discharge gate:

1. **The `NormControlled (f∘g) (raise e α) m` conjunct is the P1 obligation** — hardy
   domination under the once-per-pass raise.  It is stated, not proven (pin).  It is not
   obviously false (the open threading question); the pre-validated fallback if it stays hard
   is BW87 cut-free read-off (`readoff_sigma1`, proven).  Judge: is carrying it as a pin
   conjunct the right locus, or should it be a separate per-instance obligation at the
   headline (`e` concrete)?
2. **`cutElimPass_Zf` leaves the iterated slot `f'` existential** — faithful to E–W's
   `f ↦ f^{F^α(0)+1}` (the iteration index is the collapse's ordinal count).  Judge: is the
   existential the right abstraction for lap 1, or should the index be pinned now?
3. **`stepAllω_Zf` conflates the ∀ (allω) and ∃ (exI) principal cases** into one
   ∀/∃-principal step.  Faithful to the seam-1 arm shape; the judge may want them split.

## Bottom line

A1 seeded, A3 discharged pin 1 to a clean proof, A2 drafted the E–W function-slot suite and
re-verified both Z1 seams compose in the f-form.  The `Zᵉ` fork's numeric carrier is
validated at statement level; the reduction discharge (laps 2–4), cut-elimination assembly
(laps 5–7), and the Δ₀ read-off extension (laps 8–10) are judge-gated behind this verdict.
Scope-A exhausted — baton written, lap ends.
