# SPIKE Z1 — VERDICT

> Deciding experiment #4 (`SPIKE-Z1-SEAMS.md`), first session of the `Zᵉ` fork green-lit
> after T-W4B fired. One bounded session. Deliverable: kernel probe `wip/SpikeZ1Seams.lean`
> + this verdict.

## Verdict: **PASS — both seams close by closure, the read-off is PROVEN (not just
statable), T-Z1 does NOT fire — with three binding amendments and one major re-scoping
finding the rebuild must absorb before any re-threading.**

Q1: both W4B-refuted seams reverse in the `Zeh` form, as real kernel proofs with every
seam-crossing membership fact a real closure derivation (the anti-fake-PASS rail held: the
file's only two `sorry`s are the two §3 statement pins). Q2: the concrete `H` has proven
closure, and the bounding read-off is not merely statable — the Buchholz–Wainer
Bounding-Lemma analog is **proven outright** at the abstract level (`readoff_sigma1` /
`headline_readoff`, sorry-free), per-instance, with no universal evaluator and no truth
predicate. Neither FAIL criterion is met: no seam needed a missing closure operation, and
the read-off does not leave the per-instance Σ₁ discipline.

The honest core of the PASS, stated up front because a judge will (correctly) hunt for it:
**the seams close because set-membership at `ε₀` is information-free** — the overflow-
carrying numeric slots are deleted, not paid. Three kernel findings (K1–K3 below) prove
membership cannot carry the numeric data the calculus still needs elsewhere (the witness
axis), and the probe locates exactly where that data must now live (amendments A1/A2 + the
§6 function-slot form). This does not undermine the seam reversals — the W4B seams were
*statement-composition* failures of numeric slots, and those slots are genuinely gone — but
it re-scopes the rebuild non-trivially.

## What was built (evidence)

`wip/SpikeZ1Seams.lean` — elaborates green under the repo toolchain
(`lake env lean wip/SpikeZ1Seams.lean`), exactly **TWO `sorry`s** (`:423`, `:444` — the two
§3 statement pins, by design), **no new `axiom` declarations, no `src/` edits**. Real
`#print axioms`, in-file:

```
isOperator_Cl                        [propext]
Cl_of_NF                             [propext, Classical.choice, Quot.sound]   (K1)
finite_part_unbounded                [propext]                                 (K2a)
mono_e_membership_gate_refuted       [propext, Classical.choice, Quot.sound]   (K2b)
norm_ball_not_add_closed             [propext, Quot.sound]                     (K3)
Zeh.mono_H                           [propext, Classical.choice, Quot.sound]
allInv_Zeh                           [propext, sorryAx, Classical.choice, Quot.sound]  (pin)
cutReduceAllAuxRunning_Zeh           [propext, sorryAx, Classical.choice, Quot.sound]  (pin)
seam1_membership_absorbed            [propext]
wmul_mem                             [propext]
two_level_config_Zeh                 [propext, Classical.choice, Quot.sound]
probe_cut_all_arm_Zeh                [propext, sorryAx, Classical.choice, Quot.sound]  (via the pins ONLY)
probe_allomega_reassembly_Zeh        [propext, Classical.choice, Quot.sound]
readoff_sigma1                       [propext, Classical.choice, Quot.sound]
headline_readoff                     [propext, Classical.choice, Quot.sound]
concrete_readoff_instance            [propext, Classical.choice, Quot.sound]
rel1_comp                            (no axioms)
seam2_function_slot_payable          [propext, Classical.choice, Quot.sound]
seam1_bump_absorbed_by_composition   (no axioms)
```

`sorryAx` appears ONLY on the two pins and on `probe_cut_all_arm_Zeh`, whose sole possible
source is the pins — there are literally two sorries in the file. The seam-2 probe
(`probe_allomega_reassembly_Zeh`), the configuration, and the ENTIRE Q2 read-off are
sorry-free.

## The pinned `Zeh` rule forms (binding for the rebuild, with amendments)

`Zeh α e H m c Γ` — inductive, in-file §2:

* judgment slots: derivation ordinal `α`; control `e` (constant through a derivation);
  operator **generator** slot `H : ONote → Prop` (side conditions are `Cl H`-membership,
  where `Cl` is the inductive closure under the pin's four operations `+`/`expTower`/
  `osucc`/`ofNat`; `IsOperator (Cl S)` proven for every `S`); **stage `m : ℕ`
  (amendment A1)**; cut rank `c`; sequent `Γ`.
* rules: exactly the mandated `axL`, `allω` (premises at the relativization `adjoin H n` =
  generation from `gen ∪ {ofNat n}`, running stage `max m n`, branch ordinals
  `∈ relOp H n`), `exI` (witness bound `n ≤ hardy e m` — the designated argument is the
  STAGE), `cut`, `weak` (source ordinal `∈ Cl H` — the judge's re-anchor closure holds:
  every rule demands its ordinals in the operator), plus `weak`'s same-ordinal companion
  `wk` (sequent weakening; `Zekd` carries both and the probes' cleanup needs it).
* structural layer: `mono_H` (generators + stage raised together; `hardy_monotone` pays the
  `exI` bound — REAL proof) replaces `mono_k`/`mono_d`, per the pin.
* the `ZekdProv` NORM-wrapper has no twin — its norm clause is deleted as the pin promised;
  the `≤`-slack/NF bookkeeping survives as `ZehProv` with the ordinal's membership carried
  ("the judgment carries `α ∈ H` directly").

**Amendment A1 (stage designation, kernel-forced).** The pin's `exI` form "`n ≤ hardy e m`
for some `m ∈ H ∩ ℕ`" designates nothing: `finite_part_unbounded` proves every closure's
finite part is ALL of ℕ. The designated argument must be a judgment-carried stage,
threaded `max m n` at ω-premises — which is also exactly Buchholz–Wainer's Bounding-Lemma
form (bound = fast-growing function at the sequent's numeric parameters) and, it turns
out, the literature's own PA-level operator mechanism (§6 below: Eguchi–Weiermann's
number-theoretic operators relativize by max-adjunction — `Zekd`'s `k`-axis was never the
diseased axis and returns here in operator dress).

**Amendment A2 (common-control motive, kernel-forced).** The pin's "`mono_e`'s numeric
gate `norm e ≤ k + d` becomes `e ∈ H`" is **kernel-refuted**
(`mono_e_membership_gate_refuted`): there are `e < e' = raise e 1`, both NF, both in every
closure, with `hardy e' 0 = 1 < 5 = hardy e 0` (`raise (ofNat 5) 1 = ω` by computation —
CNF absorption). So no rule package of (NF, `<`, membership) facts can re-establish the
`exI` bound after a control raise; `Zekd`'s gate was genuinely paid by the numeric `hτ`
(premise-norm) conditions that `Zeh` deletes. Consequence: SPIKE-W4's `step_allω`
mechanism (per-branch raise, then `mono_e`-unify) does NOT carry over verbatim — the
carries-over list of the W4B verdict is wrong on this one point. A workable `Zeh` step
motive must hold its IHs at ONE control through the recursion (root-parameter control,
with the raise applied once per elimination pass at statement level, its
hardy-domination discharged per-instance — the `prwoInstance` discipline extended to the
control axis), or carry the witness data on the §6 function slot. The arm probe is stated
at a common control accordingly.

## Q1 — both seams close (the deciding question, answered YES)

**Seam 1 (the ∀/∃ reduction's output-budget bump).** `probe_cut_all_arm_Zeh` — a REAL
proof whose only sorry-dependence is the two pins — runs the arm end-to-end:
`allInv_Zeh` applied to the ∀-side IH produces the running family in EXACTLY the reduction
pin's input shape (the handoff type-checks — the kernel-verified analog of W4B's
`allInv`-feeds-the-pin check); the reduction fires at the ∃-side; the sequent cleans up;
and the emission's only output-side obligation is `Cl (adjoin H nBr) (osucc (αf + γf))` —
derived by `seam1_membership_absorbed` (TWO constructor steps, `[propext]` only) from the
IHs' carried memberships. Contrast W4B: the arm there emitted slot
`(d + norm e + 1) + norm αf + 1` against a motive demanding `d + norm e + 1`, with
`seam1_uniform_slot_unpayable` killing every re-entry. Here the emission's membership IS
the motive's demanded form, derivable for every branch. **The splice ordinal lies in
`H[n]` by closure, exactly as the pin claimed; there is no bump because there is no slot.**

**Seam 2 (the ω-node's uniform-`d` re-assembly).** `probe_allomega_reassembly_Zeh`
(sorry-free): the branch family in the reduction-output class over W4B's own two-level
family — ordinals `osucc (ω·(n+1) + ω·(n+1))`, whose `Zekd` slots grew like `n`
(`seam2_no_uniform_slot`) — re-enters `Zeh.allω` directly: "every branch's output is
`H[n]`-controlled" IS the ω-rule's premise form. Each branch's membership is a real
per-branch closure tree (`wmul_mem`, an `n`-sized tree of kernel-computed equal-exponent
merges): the previously branch-unbounded quantity is a *member*, not a *bound* — the pin's
exact claim, realized. Non-vacuity: `two_level_config_Zeh` (sorry-free) rebuilds W4B §3's
configuration — ONE `allω` at `ω^ω`, every branch a rank-`c` principal ∀/∃ cut at premise
ordinals `ω·(n+1)` — as a legal `Zeh` derivation.

**Anti-fake-PASS rail (held).** Every membership discharged at the seams is a constructor
derivation from `IsOperator`'s conditions (`Cl.add`/`Cl.osucc`/`Cl.expTower`/`Cl.ofNat` +
the kernel-computed merge equalities); none is sorried; the two pins' bodies are the only
sorries and are statement-level by design. Disclosed pin caveat carried from W4B verbatim:
the reduction's output control `raise e α` may be witness-insufficient when `ω^α < e`
(hardy-of-hardy) — statement-level, unresolved here, on the rebuild's plate.

## The kernel findings (what the closure conditions actually are, at `ε₀`)

* **(K1) `Cl_of_NF` — vacuity.** Every normal-form `ONote` is in `Cl S` for EVERY `S`:
  all of `ε₀` is hereditarily generated from numerals by `+` and `ω^·`. So the pinned
  membership side conditions are uniformly dischargeable — which is WHY no seam can
  overflow — and carry zero numeric information. This matches the literature: Buchholz
  operators constrain genuinely only at impredicative levels, through the collapsing
  clauses of `C_γ(δ)` (Freund, *Second course*, Def. 3.10/5.4); at the `ε₀`/PA level the
  numeric content of BW87 lives in the Bounding Lemma's parameters, never in membership.
* **(K2) `finite_part_unbounded` + `mono_e_membership_gate_refuted`** — see A1/A2.
* **(K3) `norm_ball_not_add_closed`.** No norm-ball is `+`-closed (head-coefficient
  merges are additive — W4B's rail brick reused). So K1 is not a representation artifact:
  NO concrete `H` can satisfy the pinned closure conditions and certify norms. The hoped
  division of labor ("membership certifies what norms certified") is structurally
  impossible; the numeric data must ride a different slot.

## §6 — where the numeric data goes: the literature's actual PA-level operator form

Mid-spike, the operator landed Eguchi–Weiermann, *A simplified characterisation of
provably computable functions of `ID₁`* (arXiv:1205.2879, 2012; now on disk as
`papers/eguchi-weiermann-2012-operator-controlled-id1.{pdf,md}` with a full-mechanics
tracked summary, host commit `f411cf4`), which settles what "Buchholz operator control"
concretely is at the PA/witness level (Def. 23 + Lemma 25; doubly-controlled sequents
`f, F ⊢^α_ρ Γ` — the ordinal operator `F` does the K_Ω/collapsing control, the
**number-theoretic operator `f : ℕ → ℕ`** the norm control; their conclusion states the
split: `F` analyzes Π¹₁-consequences, `f` the Π⁰₂-consequences — cf. Weiermann
JSL 61 (1996), Blankertz–Weiermann 1996): every norm side condition is `N(·) ≤ f 0`, and
the **Witnessing Lemma bounds every existential witness by `f 0`** — the exact shape of
the W5 read-off (`wainer_bound_of_pa_proves_goodstein`); the ω-rule relativizes by
max-adjunction (`f[N(ι)] x := f (max (N ι) x)` — `Zekd`'s `max k n` axis in operator
dress, = amendment A1, family-uniform exactly per SPIKE-W4's "never branch-indexed"
doctrine); **cut-reduction outputs the COMPOSITION `f ∘ g`** of the premises' operators,
and collapse transfinitely iterates (`f ↦ f^{F^α(0)+1}`, norm-gated). That is the
standing doctrine — budgets are functions of structure — with the slot itself
function-valued and structurally NON-AFFINE: no numeric budget exists to overflow because
super-affine demand is absorbed by climbing a function hierarchy rather than incrementing
a `(k,d)` counter — precisely the "recursion restructuring that abandons per-statement
numeric budgets" which the W4B verdict could not probe and explicitly deferred to this
fork. Kernel-checked here:

* `rel1_comp` (axiom-free, definitional): max-relativization commutes with composition —
  a cut-reduced (composed) slot re-enters the ω-rule's premise form with no residue.
  This is the algebra Eguchi–Weiermann's Lemma 25 runs on, and the function-slot answer
  to seam 2's re-entry.
* `seam2_function_slot_payable`: the exact branch-demand family that refuted every ℕ-slot
  (`seam2_no_uniform_slot`) is paid by ONE function slot through its relativization.
* `seam1_bump_absorbed_by_composition`: the reduction's `+ norm α + 1`-class bump, fatal
  against a fixed input slot (`seam1_uniform_slot_unpayable`), is absorbed exactly by a
  composing factor.

**Binding recommendation for the rebuild:** the `Zeh` core's numeric side is the pair
`(e, m)` with the `exI` bound `hardy e m` (as pinned here, A1), and the cut-elimination
statements carry their budget as a number-theoretic operator in the Eguchi–Weiermann
sense — concretely, the reduction/step statements should thread `f`-slots composed at
principal cuts and max-relativized at ω-nodes, with `hardy e` as the root instantiation.
Flagged wants for that lap (per the paper's references, noted in the tracked summary):
Weiermann BSL 12(2) 2006 (the PA case proper) and Buchholz MLQ 47 (2001), *Finitary
Treatment of Operator Controlled Derivations* — the finitary shape an in-kernel Lean
formalization actually wants. The
`H`-membership layer stays as pinned (it is the ordinal-side bookkeeping, harmless and
literature-shaped, and the seams' absence of slots is real) — but no numeric fact may be
routed through it (K1–K3).

## Q2 — the concrete `H` and the read-off (PASS, and the headline risk dissolves)

* **Representation + closure:** the concrete `H` is `Cl gen` (inductive closure of a
  finite generator list; membership witnesses are finite trees); `IsOperator (Cl S)` is
  proven for every `S` (`isOperator_Cl`). Concrete explicit-tree check in-file (the
  branch-3 splice ordinal `osucc (ω·4 + ω·4)` by a 10-node tree).
* **The bounding read-off, PROVEN (the work order asked only for a small case):**
  `readoff_sigma1` — the BW87 Bounding-Lemma analog — by induction on `Zeh`: a rank-0
  derivation of a ∀-free Σ₁-shaped sequent (target `∃⁰ φ` with atomic instances +
  literals) yields a witness `n ≤ hardy e m` with `φ/[nm n]` true (`atomTrue`), or a true
  literal in the sequent. `headline_readoff` specializes to the W5/M2-exit shape
  (`Zeh α e H m 0 {∃⁰ φ} → ∃ n ≤ hardy e m, atomTrue (φ/[nm n])`). Concrete kernel
  instance: a two-node `exI`/`axL` derivation at control `ω`, stage `1`, witness `3`,
  with `hardy ω 1 = 3` kernel-computed.
* **What BW87 actually licenses (the work order's explicit question):** the bound is a
  Hardy-class function of the judgment's control at the judgment's numeric parameter —
  NOT anything membership-derived (their Bounding Lemma's `F_α(k)`, `k` = the sequent's
  numeric parameters; ∀-free positive Σ₁ only). The proven lemma is exactly that form.
  Scope caveat, disclosed: Σ₁ matrices with bounded-∀ (real `Δ₀`) introduce `allω` nodes
  the ∀-free lemma excludes; the Towsner-5.4-style extension is rebuild scope, not spike
  scope.
* **The "new headline risk" (Σ₁-definability of the concrete `H`) dissolves:** the
  read-off consumes NO `H`-data — `H` does not occur in the conclusion, and the proof
  uses no membership fact. Σ₁-definability of `H` would matter only if `Zeh` itself must
  be arithmetized for the M2 bridge, which the read-off does not require; and by K1 the
  membership predicate is extensionally trivial on NF notations in any case. The
  per-instance discipline is preserved throughout (parametric `φ`, `atomTrue`, no
  evaluator, no truth predicate, no non-arithmetic quantification) — FAIL criterion (ii)
  is not met.

## T-Z1 assessment (does not fire)

* Criterion (i): both seams CLOSE under the pinned closure conditions — no missing
  closure operation, hence not even an `IsOperator` amendment was needed for Q1. The two
  judgment-shape amendments (A1, A2) are statement-level, precedented (SPIKE-W4's
  mandatory `d`-budget amendment), and kernel-forced by in-file refutations.
* Criterion (ii): the read-off is proven per-instance with no universal evaluator.

## Re-scoping the ~7–11-lap estimate (what the probes surfaced)

1. **The rebuild's first lap must pin the function-slot statements** (§6): the reduction
   and step motives re-keyed to `f`-slots (composition at principal cuts,
   max-relativization at ω-nodes, `hardy e` at the root), with A1/A2 folded in. This
   replaces, not adds to, the "calculus core" lap already budgeted.
2. **The `mono_e` mechanism is redesigned, not re-threaded** (A2): once-per-pass raise at
   statement level, hardy-domination discharged per-instance at the headline (`e` is
   chosen there; `hardy (raise e α₀)`-domination is an instance fact, not a rule) — or
   witness data carried wholly on the `f`-slot, BW87-style. The W4B caveat (ii)
   (raise-insufficiency when `ω^α < e`) lands on the same desk.
3. **The witness-threading fallback is already kernel-validated:** if threading witness
   bounds through cut-elimination stays hard, BW87's discipline — don't thread; read off
   the CUT-FREE derivation, whose ordinal may tower — is available, and `readoff_sigma1`
   is that read-off, proven. This is a genuine de-risking: the fork no longer has a
   single-point-of-failure on the threading design.
4. Net: estimate stays ~7–11 laps (spike-calibrated; the grind-lap 2–4× optimism note
   from the judge's calibration stands). Risk moved OFF "Σ₁-definability of `H`"
   (dissolved) and ONTO "witness-threading design through cut-elim" (bounded by the
   validated fallback in 3).

## Bottom line

The `Zᵉ` fork is real: the two kernel-confirmed W4B seams do not exist in the `Zeh` form
(proven at the seams, rail-clean), the read-off the M2 exit needs is proven in the
literature's exact licensed shape, and the one place the pin was wrong (`e ∈ H` as the
`mono_e` gate; `H ∩ ℕ` as the `exI` designator) is kernel-refuted with the amendment
pinned. The rebuild proceeds on the amended rule forms, function-valued numeric slots per
§6, and the sorry-free read-off as its fixed exit.
