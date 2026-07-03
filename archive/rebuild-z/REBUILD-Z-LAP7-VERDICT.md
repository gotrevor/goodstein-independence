# REBUILD-Z LAP 7 VERDICT

Date: 2026-07-02

Scope: statement lap, wip code only. No `src/` files were edited by this lap.

## Verdict

PASS at statement level. Trap 9 did not fire.

Artifacts:

- `wip/EwIter.lean`
- `wip/Zef2Calculus.lean`

## Z3: gated max implementability

The repo `norm` is the CNF max-coefficient norm and does not have finite fibers. Kernel witness:

- `cnf_norm_fiber_one_infinite : ∀ k, norm (GoodsteinPA.Dom.towerO k) = 1`

Per Z3, lap 7 adopts a constructor norm for the E-W gate:

- `ewN : ONote -> Nat`
- `ewBall : Nat -> Finset ONote`
- `mem_ewBall_of_ewN_le : ewN o <= K -> o ∈ ewBall K`

Thus the gated max is implemented over a finite listable carrier. This is the E-W-style constructor
norm decision; it intentionally does not use the repo CNF `norm` as the gate.

## P1-P3 kernel probes

P1 passed:

- `P1_ewIter_lift`
- statement: `β < α -> ewN β <= f 0 -> EwF1 f -> ∀ x, ewIter f β x <= ewIter f α x`

P2 passed:

- `P2_trap8_instance_lift`
- instance: `f n = n + 2`, `β = ONote.ofNat 2`, `α = ONote.omega`
- note: this reruns the trap-8 admissible side-condition instance; `n+2` is monotone/inflationary but is not a Z4 `(f.1)/(f.2)` operator.

P3 passed:

- `P3_trap7_allomega_containment`
- instance: `f = hardy ONote.omega`, branch `n = 2`, `β = ONote.ofNat 2`
- statement shape: `ewIter (rel1 f n) β <= rel1 (ewIter f α) n`

Supporting real theorems:

- `ewIter_lower`
- `ewIter_infl`
- `ewIter_monotone`
- `ewIter_rel1_le`

## Zef2 statement layer

`wip/Zef2Calculus.lean` defines `Zef2` alongside frozen `Zef`. Each constructor carries the
per-node HYP:

- `ewN α <= f 0`

Rule-local read clauses included:

- `exI`: keeps `n <= f 0`
- `cut`: adds the statement-level cut read shadow `φ.complexity <= f 0`
- `allω`: keeps branch slot `rel1 f n`

Plumbing ported far enough for statements:

- `Zef2.mono_f`
- `Zef2.change_H`
- `Zef2.mono_Hf`
- `Zef2Prov`

Pinned statements with `sorry` bodies, by lap order:

- `readoff_sigma1_Zef2`
- `headline_readoff_Zef2`
- `cutElimPass_Zef2`

C3 exit check type-checks:

- `cutElimPass_exit_root_Zef2`
- bound visible: `∃ n <= ewIter (ewRootSlot e m) α 0, atomTrue (φ/[nm n])`

The exit uses the sanctioned fixed-base composition route. The root operator is:

- `ewRootSlot e m x = 2 * (x + rel1 (hardy e) m x) + 3`

and the file proves:

- `ewRootSlot_f1 : EwF1 (ewRootSlot e m)`
- `ewRootSlot_f2 : EwF2 (ewRootSlot e m)`

## P4 embedding recipe

The `zeh_to_zef2` per-node HYP obligations should be supplied by a finite Zeh-tree budget in the
lap-8 port.

Named recipe: `zeh_to_zef2_budget`.

For a finite `Zeh` derivation `d`, define a recursive budget `B(d)` taking the maximum of:

- every node ordinal constructor norm `ewN α`
- every `exI` witness numeral
- every cut read shadow, represented in this repo statement layer by `φ.complexity`
- the branch-local formula/term numeric reads that enter through `rel1`

Embed at a budgeted fixed-base root slot, e.g.

`x |-> 2 * (x + B(d) + rel1 (hardy e) m x) + 3`.

Then root HYP and every subnode HYP are discharged by:

- finiteness of `d`
- monotonicity of the budgeted root slot
- the existing `rel1` branch widening at `allω`
- E-W's Lemma 32-34 pattern: formula/term norms enter through the `f[n]` relativization

This is a disclosed pin for the judged src port, not a lap-7 grind.

## Verification

Commands run:

- `lake env lean wip/EwIter.lean`
- `lake env lean -o wip/EwIter.olean wip/EwIter.lean`
- `LEAN_PATH=. lake env lean wip/Zef2Calculus.lean`

Result:

- `wip/EwIter.lean`: clean
- `wip/Zef2Calculus.lean`: type-checks with only the three expected `sorry` warnings for the pinned statement bodies

Worktree note: current dirty `src/GoodsteinPA/WainerRoute.lean` and blueprint/Wainer files were not edited by this lap.

STOP for judge.
