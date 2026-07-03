# M2 probe — lap-168 finding + DIRECTION reasonableness check

Grind lap 168. Probe-grind lap within the operator-ratified lap-167 M2 feasibility window
(laps 167–171, HARD GATE lap 171). This note is a **probe finding**, NOT the lap-171 verdict.

## Is the lap-167 DIRECTION reasonable? — YES (judged this lap, at the operator's request)

The directive scopes a bounded 5-lap M2 (Foundation→internal-Z bridge) feasibility spike in `wip/`,
with a concrete 4-step plan and a gate. It is a defensible, decision-oriented experiment for a
genuinely-needed girder component (M2/M4 is ~0% built), and this lap's investigation advances it
rather than refuting it. **I did not find the direction wrong.** One tension worth the review lap's
attention is recorded at the end.

## Finding A — the decisive case (induction leaf) is plausibly BOUNDED via the two-sided reformulation

Directive step 4 (THE decisive case) is `PAInductionAxiomShellSimulation` (`wip/M2Probe.lean:333`):
build a Z derivation of the translated sequent for the CLOSED PA induction axiom, given native `zInd`
only produces an INSTANCE `K(t)`.

Compiler-grounded facts established this lap:
- **Internal `ZDerivation` has exactly 9 rules** (`zDerivation_iff`): `zAtom`(0), `zIall`(1, ∀-intro),
  `zIneg`(2, the specific `(neg A)^⋎^⊥ = A→⊥` intro), `zInd`(3, induction), `zK`(4, cut),
  `zAxAll`(5), `zAxNeg`(6), `zAx1`(7, identity axiom), `zAxBot`(8, ⊥-left). There is **NO general
  `∧`-intro or `∨`-intro rule**, unlike the EXTERNAL `Provable` Tait calculus (which has
  `andI`/`orI`, used in the DONE M4 embedding `Embedding.lean`).
- Internal-Z formulas DO include `^⋏`/`^⋎` (full grammar; `irk_and`/`irk_or`), and
  `inegF A = (neg A) ^⋎ ^⊥` (Buchholz `¬A = A→⊥`). So internal Z is a **specialized ∀ / (A→⊥) / Ind
  / cut fragment**, not full Buchholz NNF.

Naively this looks like an obstruction (the induction axiom
`succInd φ = φ(0) → (∀x,φ(x)→φ(x+1)) → ∀x φ(x)` has `→`/`∧`/`∨` with no Z intro rule). **But the
two-sided sequent discipline dissolves it:** the one-sided→two-sided translation `toZ` loads the
`→`-hypotheses into the Z ANTECEDENT, so the target sequent is

    φ(0), ∀x(φ(x)→φ(x+1))  →  ∀x φ(x)

whose succedent is a plain `∀` (introduced by `zIall`), the induction discharged by native `zInd`
on the eigenvariable, and the base/step hypotheses cut in from the antecedent via `zAx1` (identity)
+ `zK` (cut). Every rule needed is present. So the shell is a BOUNDED construction, not a large new
formalization — **this LEANS M2-PLAUSIBLE for step 4**, provided the translation `toZ` correctly
peels the outer `→`s into antecedent members (a bounded syntactic decomposition, the real content of
`FoundationToZSequent`).

### Compiler-verified this lap (M2-PLAUSIBLE evidence)
`wip/M2Probe.lean` now proves `zDerivation_of_nativeZIndInstance_R` (typechecks, no `sorry`): the native
`zInd` step carries ALL THREE `ZDerivesEmptyR` invariants (`ZRegular ∧ ZFresh ∧ ZSeqAnt`) from the two
premise invariants plus three BOUNDED side-flags (`ltFlag (maxEigen d1) (π₁ at')` = eigenvariable
freshness, `freshFlag (π₁ at') ⊥ (seqAnt q)`, `seqAntSeqFlag q`) — via `zReg_zInd`/`zFresh_zInd`/
`zSeqAnt_zInd`, each a `max` of a flag and the premise invariants. So the invariants do NOT explode on
the induction rule; they are the standard eigenvariable side-condition. This is the first
compiler-grounded M2-PLAUSIBLE datapoint for the induction leaf.

### Concrete next probe (laps 169–171, toward the verdict)
Build, in `wip/M2Probe.lean`, the two-sided induction shell for a SIMPLE φ: a Z derivation of
`{φ(0)-code, step-code} → ∀-succedent` via `zIall` (peel the ∀) → `zInd` (native induction, eigen
`a`) → `zAx1`/`zK` to feed base+step from the antecedent. If this lands with bounded coding ⟹ strong
M2-PLAUSIBLE; if the `zIndWff` well-formedness or the antecedent-threading (`ZRegular/ZFresh/ZSeqAnt`
invariants) explodes ⟹ PIVOT-B signal. The `→`-peeling translation is the other half — define
`toZ` = "strip leading `→`s of the one-sided axiom into the two-sided antecedent."

## Tension for the review lap (lap 171 gate) — crux-2 is NOT clearly a "false summit"

The lap-167 directive's rationale for pivoting OFF crux-2 was partly "engine already tested to false
summits (18-lap test)". This lap's (initially off-directive, now-banked) work on the crux-2 `residual`
found the OPPOSITE for its hardest remaining sub-case: the C-exit R-intro replay is closable by a
**prefix sub-chain** reduct `zK s r (ds ↾ under (jstar+1))`, needing ONLY õ-descent (proven:
`iseqNaddIdgAux_lt_of_lt`, `InternalZ.lean`) + `idg`-≤ — **NO internal weakening / rank-drop** (the
formalized `iRedDescent` requires only iotil/idg descent). This overturns the STATUS "depth ≈ zAxBot"
framing for that obligation. See `PENDING_WORK.md` lap-168. The review lap should re-weigh A-vs-B with
BOTH signals: M2 induction leaf looks bounded (Finding A), AND crux-2 `residual` looks tractable —
i.e. Route A may be closer than the escalation assumed. (Recorded, not acted on — grind laps don't
edit `DIRECTION.md`.)
