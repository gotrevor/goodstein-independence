# REBUILD-Z — SERIES-2 LEDGER (append-only, one block per stage)

Order: `REBUILD-Z-SERIES-2-ORDER-2026-07-03.md`. Discipline: bare `lake build` (1342-job full
gate) per stage; hygiene claims diff-verified (Series-1 §5.2); self-ratification VOID; wip-only
for everything probe-shaped.

---

## Stage A — Series-1 Stage-1 debt (src, pre-ratified, mechanical) — ✅ LANDED (lap 196)

**Build**: 🟢 `lake build` (1342 jobs, fresh full rebuild). **Headline**:
`GoodsteinPA.peano_not_proves_goodstein` footprint = `{propext, Classical.choice,
GoodsteinPA.goodstein_implies_consistency, Quot.sound}` — UNDRIFTED (re-checked via
`blueprint_audit`). **`blueprint_audit`**: ✓ PASSED, 16 nodes consistent, 0 warnings.

Diff-verified changes (git diff, not asserted from memory):

- **(A-1) `src/GoodsteinPA/WainerLadder.lean` CREATED.** Imports `GoodsteinPA.OperatorZef2` +
  `GoodsteinPA.WainerRoute` (the translation apparatus: `EventuallyLE`, `goodsteinSentence`,
  `GoodsteinPA.Dom.goodsteinLength`, `fastGrowing`). Namespace `GoodsteinPA.WainerLadder`.
  Wired into the blueprint lib root (`src/GoodsteinPABlueprint.lean` +1 import line). This is
  the L-E-direction home (ruling §4) where the top rungs can bind the concrete goodstein
  translation without the `OperatorZef2`-level cross-import obstruction.
- **(A-2) `wainer_splice_Zef2` MOVED + RESTATED VERBATIM** at the R-5 shape:
  ```lean
  theorem wainer_splice_Zef2 :
      (𝗣𝗔 ⊢ ↑goodsteinSentence) →
        ∃ o : ONote, o.NF ∧
          EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n) := by sorry
  ```
  This is EXACTLY the statement of the `wainer_bound_of_pa_proves_goodstein` axiom (the rung
  that flips it `axiom → theorem`). The OLD parametric form
  (`(e B α …) : … ewIter (ewRootSlot e B) α 0 ≤ …`, the lap-8-ruling L-W VOIDed-as-trivial
  shape) DELETED from `OperatorZef2.lean`.
- **(A-3) `embedding_Zef2` DELETED** from `OperatorZef2.lean` (lap-8 ruling §4 VOIDed
  placeholder, R-6 debt). A `TODO(rung E, Stage-B statement lap)` naming its faithful
  statement now lives in `WainerLadder.lean`'s module docstring. No src theorem for rung E
  (its statement is the Stage-B ratification target — wip-first).
- **(A-4) Blueprint tex** (`blueprint/src/content.tex`): `thm:zeh_rank_zero` `\notready`
  DROPPED (proven modulo the pass; kept OFF `\leanok` — no `@[goodstein_blueprint]` site since
  sorry-pins can't be tagged, so the reconciler leaves this hand-status alone);
  `thm:wainer_splice` bound `\lean{GoodsteinPA.WainerLadder.wainer_splice_Zef2}` (kept
  `\notready`, still a sorry). `blueprint_audit` PASSES.
  ⚠️ **Web HTML regeneration (`annotate_depgraph.py --web`) DEFERRED to host**: `leanblueprint`
  is not installed on this box (`which leanblueprint` → absent). The tex SOURCE is updated and
  the machine gate (`blueprint_audit`) passes; the generated `blueprint/web/*.html` +
  `blueprint/lean_decls` (both untracked artifacts) refresh needs the host's leanblueprint
  toolchain. `checkdecls` will resolve the new `\lean{}` binding (the decl compiles in the
  blueprint lib).
- **(A-5) `wip/Lap13ReadoffDeltaProbe.lean` DELETED** (`git rm`) — stale name-clash with the
  now-promoted `src` `sound0` (`OperatorZef2.lean:897`).

**Sorry-declaration delta** (build `declaration uses \`sorry\`` warnings, fresh full rebuild):
15 → **14** = net −1, matching the mandated {−2 voided (A-2 old form + A-3 embedding), +1
restated}. (The order's absolute "17 expected" uses a `lean-sorry` tool not present on this
box; the verifiable delta is the mandated −1.)

Gate summary: 🟢 build · headline undrifted · no new `src` axiom · no `native_decide` in new
files · wip freeze refs untouched · `blueprint_audit` ✓. Stage A CLOSED.

---

## Stage D-1 — absorbing-norm existence (wip probe) — ✅ POSITIVE RESULT (lap 196)

**File**: `wip/AbsorbingNormProbe.lean` (compiles standalone via `lake env lean`; NOT imported
by any lib, so `src`/`lake build` UNCHANGED — pure ruling input). No `native_decide`.

**FINDING — the lap-192 conjecture "finite fibers force additivity-like growth (T-Z7(i))" is
REFUTED.** A finite-fibered ABSORBING norm on `ONote` exists: the **max-over-terms norm with a
logarithmic coefficient charge**

  `Nlog (oadd e n a) = max (Nlog e + clog n) (Nlog a)`,  `clog n = ⌊log₂ (n+1)⌋`.

Two design moves defeat the two obstructions to `ewN` being absorbing:
- **max-over-terms** (not `ewN`'s SUM) tames CONCATENATION (`α+γ` with disjoint exponents):
  the max of two maxes is a max — absorbing with `c = 0`;
- **log coefficient charge** tames the MERGE `ω^β·n + ω^β·m = ω^β·(n+m)` (`ONote.addAux`
  `Ordering.eq` arm, where coefficients ADD): `clog_add_le` proves
  `clog (n+m) ≤ max (clog n)(clog m) + 1` (pure ℕ, kernel-clean), vs `ewN`'s linear charge
  which costs the unbounded `min(n,m)`.

**Kernel-checked (`decide`, no `native_decide`):**
- `nlog_absorbs_merge_small/_big`, `nlog_absorbs_concat`, `nlog_absorbs_drop` — `Nlog` satisfies
  `Nlog (α+γ) ≤ max (Nlog α)(Nlog γ) + 1` on the adversarial merge/concat/drop pairs;
- `ewN_not_absorbing`, `ewN_not_absorbing_const_30` — the CONTRAST family `ω·k + ω·k` where
  `ewN` violates absorption for EVERY fixed constant (gap grows as `k`);
- `Nlog_spine : Nlog (spine k) = k+1` — `Nlog` GROWS on the tower spine `ω, ω^ω, …`, i.e. it
  does NOT share the E–W max-coefficient source norm's infinite-fiber failure mode (constant `1`
  on the spine — the exact reason `src` needed `ewN`);
- `clog_le_self`, `Nlog_le_ewN` — `Nlog ≤ ewN` (recorded to flag it is the WRONG direction to
  transfer finite fibers).

**Node-gate consequence (kernel-clean): `absorbing_closes_gate`** — ANY absorbing norm with
constant `c` closes the top-rank-cut node gate `N (α+γ) ≤ g (f 0)` from `N α ≤ g 0`, `N γ ≤ f 0`
needing ONLY `max (g 0)(f 0) + c ≤ g (f 0)` — vastly weaker than the refuted base-additivity
`hg_base : ∀ k, g 0 + k ≤ g k`. With `f 0 ≥ 1` (the EwF1 `2m+1` floor) this needs essentially
just `g 0 + c < g (f 0)`, i.e. `g` non-constant across `[0, f 0]` — the trap-8 plateau at a
SINGLE point no longer blocks it.

**General absorbing theorem — PROVEN (lap 196 P3 deepening, kernel-clean
`[propext, Classical.choice, Quot.sound]`):** `Nlog_add_le_max_succ : ∀ NF α γ,
Nlog (α+γ) ≤ max (Nlog α)(Nlog γ) + 1`. Proof: induct on α, `lt_trichotomy` on the two leading
exponents `repr e`, `repr eg`; each case pins the SYNTACTIC form of `α+γ` via `repr_inj` +
ordinal absorption (`add_of_omega0_opow_le`, `isPrincipal_add_omega0_opow`): `lt`→ `α+γ = γ`
(α absorbed); `gt`→ `α+γ = oadd e n (a+γ)` (prepend, IH on `a`); `eq`→ `a+γ = γ` collapses the
merge so `α+γ = oadd e (n+ng) ag`, coefficient tamed by `clog_add_le`. The single merge boundary
means the two `+1`s never compound. Helper `add_eq_right_of_repr` banked. So absorption is now a
THEOREM, not just evidenced on adversaries — the D-1 disposition is DISPOSITIVE for property (ii).

**Finite fibers — PROVEN (lap 197, D-1 CLOSED; probe now sorry-free, kernel-clean
`[propext, Classical.choice, Quot.sound]`):**
- `Nlog_finite_fiber : ∀ K, {α : ONote | NF α ∧ Nlog α ≤ K}.Finite` — property (i) fully
  mechanized. Proof: induction on `K`; at `K+1` an inner **well-founded induction on the
  `NFBelow` bound ordinal** `b`: any `oadd e n a` in the `NFBelow · b` fiber has exponent `e`
  in the finite (outer-IH) `Nlog ≤ K` NF-fiber with `repr e < b`, coefficient `< 2^(K+2)`
  (`coe_lt_of_clog_le`), and tail in the `NFBelow · (repr e)` fiber (inner IH, `repr e < b`) —
  a finite union of images. No `nlogBallBelow` Finset construction needed.
- **The NF restriction is NECESSARY** (`Nlog_fiber_infinite_without_NF`, kernel-clean): the
  lap-196 unrestricted statement `{α : ONote | Nlog α ≤ K}.Finite` is FALSE — the non-NF flat
  chains `oadd 0 1 (oadd 0 1 (…))` are pairwise distinct with `Nlog = 1` (infinite `≤ 1` ball).
  NF is exactly the population the calculus feeds the norm (`ewBall` clients are all NF), so
  the ruling candidate reads: finite fibers **on NF notations**. The NF strict exponent descent
  is precisely what the inner ordinal induction consumes.

**DISPOSITION for the reserved top-rank-cut ruling:** the TRILEMMA's prime amendment candidate
(finite-fibered ABSORBING norm) is now KERNEL-EVIDENCED to EXIST — the judge can dissolve the
node gate by swapping `ewN → Nlog` (an absorbing norm) with a trivial non-constancy slack, WITHOUT
touching `rel1` or the additive output ordinal. This is the strongest of the three trilemma horns
and was the one the lap-192 review believed impossible.

---

## Stage C-1 — lane-D Option-B splice feasibility (wip probe) — ✅ YES, structurally FREE (lap 197)

**File**: `wip/OptionBSpliceProbe.lean` (compiles standalone; NOT in any lib — `src` untouched).

**QUESTION**: does the splice consumer close if rung D concludes at the ACHIEVABLE bound
`∃ n ≤ ewIter f α 0` instead of the ratified-but-(Ax2)-gated `∃ n ≤ f 0`?

**ANSWER: YES — the cost is exactly ONE tower level, i.e. nothing.** Kernel facts:
- `optionB_tower_step` (**`rfl`**, axiom-clean): the Option-B exit bound at the rank-0 pair,
  `ewIter (ewIterTower f d α) (collapseIter d α)`, IS `ewIterTower f (d+1) α` BY DEFINITION.
  The splice's final-bound functional shape is unchanged; whatever Hardy-bracket domination
  handles depth `d` handles depth `d+1` (both fixed per PA proof).
- `ewIterTower_mono_infl` (axiom-clean): the slot tower preserves Monotone + inflationary.
- `optionB_splice_exit`: the generic composition — from ANY Option-B-shaped read-off
  (`readoffB : Zef2 α' e H f' 0 {∃⁰ φ} → ∃ n ≤ ewIter f' α' 0, …`) and a rank-`d` derivation,
  `rankToZeroAux` composes to `∃ n ≤ ewIterTower f (d+1) α 0`; the `Zef2Prov` ordinal slack is
  absorbed by gated ordinal-monotonicity (`ewIter_le_of_lt`, gate from the Prov norm bound).
  NO hypotheses beyond the EwLow triple rung R already threads. ⚠️ Inherits rung R's disclosed
  `sorryAx` (`passAux` top-rank cut = the escalated crux); the composition itself adds none.

**R-4′ restatement draft (ruling input, text only, in the probe docstring)**: R-4 with exit
bound `f 0 → ewIter f α 0`. Consequence: with `readoffD_trapped_of_mono` covering the
monotone-matrix fragment, **(Ax2) would be needed by NEITHER the read-off NOR the splice on the
headline path** — it stays solely a rung-E calculus-faithfulness question (Stage B).

**Honest caveat recorded**: this verifies the CONSUMER side. The PRODUCER side (that
`readoff_delta0_Zef2'` itself closes structurally at the `allω` trapped case under the
`ewIter f α` budget) is post-ruling Series-3 grind; feasibility evidence = lap-195's diagnosis
(the trap is exactly an `f 0`-vs-`rel1`-growth budget mismatch, covered by construction).

**Ruling (2) input status**: Stage C now provides the missing feasibility evidence for the
"restate rung D" horn of ruling (2) [Ax2 vs restatement]. Stage B (Ax2-adequacy) remains the
other horn's evidence.

---

## Stage C-2 — goodstein matrix vs the mono guard (wip probe) — ❌ guard REFUTED (lap 197)

**File**: `wip/GuardMonoProbe.lean` (standalone; `src` untouched). Kernel-clean
`[propext, Classical.choice, Quot.sound]`, no `native_decide`.

**FINDING — the `readoffD_trapped_of_mono` guard `atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)` does
NOT hold for the goodstein matrix's bounded-∀ step-clause shape.** `guardShape_not_mono`:
on the minimal representative `χ = (x < 2 → x = 0)` of the guarded-implication class (the
`igoodsteinDef`/`resultDef` β-coding certifies runs by `∀ i (i < N → step-i-equation)` clauses),
the `0`-instance is TRUE while `∀⁰ χ` is FALSE (`1`-instance fails inside the guard) — the
run-miscoded-at-step-1 adversary. Evaluated via `Evalm ℕ` simp in the kernel.

**Consequence (ruling-(2) input): Option B is LOAD-BEARING.** The mono fragment does NOT cover
the concrete goodstein translation, so the lane-D residue on the headline path needs one of the
two judged amendments. Combined with Stage C-1 (Option-B splice cost = one definitional tower
level), Stage C's evidence points at the **R-4′ restatement** (bound `f 0 → ewIter f α 0`) as
the ruling-(2) recommendation; (Ax2) remains solely the rung-E faithfulness question (Stage B).

**Scope honesty (recorded in-file)**: this is the SHAPE-CLASS refutation (what any generic
`hmono` instantiation would need), not a computation inside the machine-generated `resultDef`
blob; but the run-miscoding adversary is a semantic counterexample family for the specific
coding too.

---

## Stage B — rung-E (Ax2)-adequacy probe (`Zef2T` clone) — ✅ ANSWERED (lap 197)

**File**: `wip/Ax2AdequacyProbe.lean` (standalone; `src` untouched). All headline probe
theorems kernel-clean `[propext, Classical.choice, Quot.sound]`, no `native_decide`.

**The clone**: `Zef2T` = `Zef2`'s six constructors VERBATIM (gates included) + E–W (Ax2) as
`trueRel`/`trueNrel` (the `Zekd` shape with the `ewN` gate threaded). `Zef2T.gate` and the
inclusion `Zef2T.ofZef2 : Zef2 → Zef2T` proven.

**(i) `toZef` does NOT extend — (Ax2) is a STRICT extension at rank 0 (kernel-proven).**
`zef2T_derives_true_literal`: `Zef2T 0 e H id 0 {0=0}` (one trueRel leaf).
`zef_rank0_literal_pair`: every rank-0 `Zef` derivation of an all-literal sequent carries a
complementary PAIR (allω/exI conclusions are non-literals; cut impossible at rank 0) ⇒
`zef_not_derives_true_literal_singleton`. CONSEQUENCE: the lap-8 "discharge read-offs via
`toZef`" route is unavailable for `Zef2T`; read-offs must be re-proven natively.

**(ii) Pins 1–2 extend MECHANICALLY on the new leaves (kernel-proven case).**
`reduction_trueLit_case` = the exact new constructor case `cutReduceAllAuxRunning_Zf2` would
acquire: the true literal survives `Δ.erase (∃⁰ ∼φ)` (`ne_of_ne_complexity`) and one `trueRel`
leaf at `α + γ` closes with the SAME `ewN_add_le_comp` gate arithmetic as `axL`. No new
mathematics; (f.1)-class hypotheses untouched.

**(iii) Falsity-invariant read-offs treat (Ax2) leaves VACUOUSLY (kernel-proven case).**
`readoffD_trueLit_vacuous`/`readoffD_trueNlit_vacuous`: under the lane-D invariant, a true
literal in Γ is contradictory — the `readoffD_aux` induction extends with two vacuous cases.
⚠️ HONEST LIMIT (lap-195's caution, kernel-grounded): (Ax2) does NOT dissolve the `allω`
trapped-contraction residue PER-DERIVATION (that case is unchanged in `Zef2T`); its value is
derivation EXISTENCE — an embedding can close true Δ₀ leaves without forcing the goal
existential into the shared `allω` context (E–W Lemma 31's separation). That is a
rung-E/embedding property.

**Combined Stage B+C ruling input**: (Ax2) is cheap on the calculus side ((ii),(iii)) but
BREAKS the toZef read-off route ((i)) and is NOT needed by lane D (Stage C: R-4′ restatement +
guard-refutation). Recommendation shape: adopt (Ax2) if-and-only-if rung E's embedding needs
it (its Lemma-31 separation suggests it does); lane D takes R-4′ regardless.

---

## Stage D-2 — shift-relativization `rel1'` cost assessment (wip probe) — ✅ ANSWERED (lap 197)

**File**: `wip/Rel1ShiftProbe.lean` (standalone; `src` untouched). Kernel-clean, no
`native_decide`. `rel1' f n = f (n + ·)` (E–W Def 23 literal) vs ratified `rel1 f n = f (max n ·)`.

**Kernel findings:**
- `rel1'` preserves the EwLow triple (`rel1'_monotone/_infl/_low`) — pass-threading unaffected.
- **`rel1'` does NOT preserve `hg_base`** (`rel1'_not_base`, concrete `fBad` satisfying ALL FOUR
  ratified hypotheses whose shift-by-1 violates base-additivity at `k=2`). So the naive
  "max→+ and keep `hg_base`" amendment is POINTLESS — kernel-sharpens the lap-192 parenthetical
  (insufficient even before the `ewIter` plateau enters).
- The property that survives is **uniform step-additivity** `StepAdd f = ∀ m k, f m + k ≤ f (m+k)`:
  implies `hg_base` (`stepAdd_base`); **closed under `rel1'`** (`stepAdd_rel1'`, axiom-FREE —
  self-reproducing through nested ω-contexts); **NOT closed under `rel1`** (`stepAdd_not_rel1`,
  `f = id`, `rel1 f 5` at `m=0,k=1`) — consistent with the banked refutation; and the CONCRETE
  root slot has it (`ewRootSlot_stepAdd`), so the pins' upgrade `hg_base → StepAdd` is free at
  the root.
- **Blast radius (measured)**: `rel1` occurs 88×/68×/13× in OperatorZeh/OperatorZef2/EwIter;
  the `allω` constructors BIND `rel1` structurally → swap = NEW INDUCTIVE + full lemma-suite
  re-proof. Branch-0 mechanism carries over (`rel1' f 0 = f` by `zero_add`, propositional like
  `max 0 x = x`).

**Amendment cost verdict**: the viable shift package is {`rel1 → rel1'`, `hg_base → StepAdd`}
at new-inductive + full-suite cost; the D-1 absorbing norm (`ewN → Nlog`) dissolves the SAME
node gate with NO constructor change and NO slot property. **Stage D ranks: absorbing norm ≫
shift+StepAdd.**

---

# SERIES-2 END — all stages closed (A, B, C-1, C-2, D-1, D-2). STOP for the judge per the order.

**The two amendment rulings' evidence packages:**
- **Ruling (1) [top-rank cut trilemma]**: D-1 (absorbing `Nlog`: BOTH properties proven, NF
  finite fibers + absorption theorems; unrestricted statement kernel-refuted) vs D-2 (shift
  package viable but strictly dominated on cost). → prime candidate: `ewN → Nlog`.
- **Ruling (2) [lane-D residue: Ax2 vs restatement]**: C-1 (Option-B/R-4′ restatement is
  structurally FREE for the splice — one definitional tower level) + C-2 (the mono-guard
  fragment does NOT cover the concrete goodstein matrix — kernel-refuted) + B ((Ax2) strict at
  rank 0, breaks the toZef route, mechanical elsewhere, does NOT dissolve the allω trap
  per-derivation; its value is embedding-side existence). → lane D: R-4′ restatement; (Ax2):
  iff rung E's embedding needs it (Lemma-31 separation suggests yes).
