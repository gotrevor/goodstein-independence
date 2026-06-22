# Pending work — open obligations & attack paths

State after lap 2026-06-22. Build green (`lake build GoodsteinPA`, 1204 jobs). Phase 0 (encoding +
faithfulness bridge) axiom-clean. Phase 1 (Gödel II hook) landed. The headline stays a literal
`sorry` (anti-fraud). See `PHASE2-DECOMPOSITION.md` for the full girder ladder.

## ⚠️ TOP PRIORITY (lap 4) — O0: re-architect on the witness-bounded calculus
**Finding (machine-checked, axiom-clean, `wip/WitnessBound.lean`):** the completed M5 cut-elimination
in `src/Zinfty.lean` is for a calculus with an **unbounded `∃`-witness** and **no numeric index `k`**.
That calculus cannot reach the headline — `unbounded_proves_goodstein` derives the Goodstein sentence
cut-free at ordinal 2, so Towsner's lower bound (17.1) is FALSE for it. The headline needs the
**witness-bounded, Hardy-indexed `(α,k)` calculus** (Towsner §15), where `∃` carries `v ≤ h α k`,
`True` carries `τ α < k`, and `∀`'s premises use `max k n`. See `STATUS.md` lap-4 finding.

Attack paths (hardest-first; the crux is now the lower bound + the `k`-tracking cut-elim):
1. **Finish the lower bound (M6 / Thm 17.1).** `wip/WitnessBound.lean` has the calculus `B` and the
   `∀`-free fragment proved (`lowerBound_existential`). The remaining frontier is the `gAll`/`I∀`
   case with *accumulating* existentials — Towsner's stated invariant looks insufficient there
   (see `ON-LINE-REQUEST.md`). Either crack the refined invariant (likely a single-ordinal
   `H`-controlled measure, Buchholz style) or get it from the literature, then discharge the abstract
   Hardy hypotheses `Hmono`/`Hdom`/`HG` from a real `h_α`/`τ`/`G` (mathlib `ONote.fastGrowing`?).
2. **Retrofit `k` into cut-elimination.** Redo `src/Zinfty.lean`'s inversions/reductions tracking the
   numeric bound `k` (the *strategy* ports; only the bookkeeping changes). Needed so the cut-free
   output of M5 still carries the `(α,k)` bound that 17.1 refutes.
3. **Decide architecture:** Towsner two-index `(α,k)` vs. Buchholz single-ordinal `H`-controlled
   derivations. The latter may formalize more cleanly (one well-founded measure, standard boundedness
   theorem). Resolve via `ON-LINE-REQUEST.md` before sinking the cut-elim redo.

Plus the **PA↔PA⁺ language gap**: our headline is real-`ℒₒᵣ` PA with an opaque Σ₁ `goodsteinSentence`,
not Towsner's extended-language `∀x∃y g_y(x)=0`; the arithmetization bridge Towsner skips (Remark
10.3) is a separate deep girder (M7-adjacent). Route A (via `Con(PA)`, O1) stays entirely in real PA
and sidesteps this — re-evaluate Route A vs Route B in light of the language gap.

## Open obligations (toward a clean headline)

### O1 — `Reduction.goodstein_implies_consistency` (Route A girder) — `sorry`
`𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. The deep ordinal-analysis content via Con(PA).
Attack paths:
1. **Gentzen `TI(ε₀) ⊢ Con(𝗣𝗔)` + `γ ⟹ TI(ε₀)`** — the classic route; needs `PA_∞`
   cut-elimination (same `Z_∞` machinery as Route B) plus the Con(PA) lower bound. Reuses
   Foundation's Gödel II downstream. (Buchholz `on-gentzens-first-consistency-proof`.)
2. **Drop Route A entirely for Route B** (recommended) — Towsner shows `𝗣𝗔 ⊬ γ` directly without
   Con(PA); then `goodstein_implies_consistency` becomes unnecessary (leave it as a documented,
   never-used alternative). The headline is discharged via O2's chain instead.
3. Partial: keep the lemma but prove the *easier* converse direction / a weaker reflection
   principle first as warmup, to exercise Foundation's provability API (`⊢`, `Con`, D1–D3).

### O2 — the Phase-2 girder (Route B, Towsner) — milestones M3…M7 in `PHASE2-DECOMPOSITION.md`

**✅ M3 (Z_∞ calculus) + M5 (cut-elimination) COMPLETE & axiom-clean** in
`src/GoodsteinPA/Zinfty.lean` (promoted from `wip/`, 0 sorries, `#print axioms` = trust base only,
2026-06-22 lap 3). The whole Towsner §19 is machine-checked: inversions 19.2–19.4, cut reductions
19.5 (`cutReduceConj/Disj`) + 19.6 (`cutReduceAll`), atomic/⊥ cuts (`atomCut`/`removeFalsum`, **no
truth layer needed** — set sequents dissolve them), `cutElimStep` (19.7), `cutElim` (19.9). Key
findings: `Ordinal.nadd` ABSENT in mathlib v4.31.0 → ordinary `+` with `+1` slack (bounded below
`ω^(·+1)` by additive principality); the Hardy `k` index was NOT needed for cut-elim (pure Schütte
`(α,c)` suffices — it's a §17 device); `exI` restricted to numeral witnesses.

**NEXT (hardest-first): M4 — the embedding `PA⁺ ↪ Z_∞`** (Towsner §16 Thm 16.7 / §18 Thm 18.1). A
`PA⁺` proof of `φ` yields `∃ α<ε₀, ∃ k c, Z_∞ ⊢^{α}_c φ`, finite `c` (finitely many induction
instances ⇒ finitely many finite-rank cuts — the hinge of the whole argument). Sub-targets:
M4.1 (Lemma 16.1, true universal sentences derivable at finite bound), M4.2 (Lemma 16.5/Cor 16.6,
induction axioms at bound `ω·4 # 2rk(φ) # 8`), M4.3 (Thm 16.7, induct over a Hilbert-style proof;
reuse Foundation's finitary `Derivation`, map `∀`→ω-rule). M6 (Hardy lower bound, §17) is
**independent and parallelizable** (M6.1–M6.3 overlap Track 1 `Logic/FastGrowing`; M6.4 = Thm 17.1
is new and likely DOES need the Hardy `k` threaded through a cut-free `Provable₀`).

<details><summary>Superseded lap-2 status (M5 was one open leaf `cutElimStep`)</summary>
Done and **machine-checked** (`lake env lean wip/ZinftyF.lean`, only `cutElimStep` sorry):
- The `Z_∞` calculus `inductive Deriv` over `SyntacticFormula ℒₒᵣ`, **Finset sequents** (set-based,
  per Towsner ⇒ contraction is FREE, no `contr` rule), ω-rule `allω`, ordinal bound `o`, `ℕ∞`
  cut rank `cr`. The `ℕ∞/⊤` blocker is **gone**: `complexity : Form → ℕ` is finite.
- Full predicate-level inference API: `axL/verumR/andI/orI/exI/allω/cut/mono/weakening/cast`,
  contraction free.
- **All three inversion lemmas PROVED** (the syntactic content of cut-elimination):
  `orInvAux`/`Provable.orInv` (§19.2 ∨), `andInvAux`/`Provable.andInvL`/`.andInvR` (§19.3 ∧),
  `allInvAux`/`Provable.allInv` (§19.4 ω/∀). Each by structural induction on `Deriv`, all 8 cases,
  preserving ordinal bound and cut rank.
- `cutElim` (Thm 19.9) reduced to the single open leaf `cutElimStep` (Thm 19.7).

**NEXT (hardest-first): the cut-REDUCTION lemma (Towsner §19.5–19.7), the ordinal-arithmetic
heart of `cutElimStep`.** With all inversions in hand, the reduction lemma is: a top-level cut on a
formula of complexity `= c` between two `Provable _ c` derivations can be replaced by a cut-free-at-
rank-`c` derivation with the ordinal bounds *added* (not `max+1`). The principal-formula reduction
uses the inversions to push the cut to the immediate subformulas (∨/∧ → smaller-complexity cut;
ω/∀ → instantiate at the ∃-witness numeral). Then `cutElimStep` does the transfinite induction over
the derivation eliminating all rank-`c` cuts, raising `α ↦ ω^α`. Likely needs a numeric/Hardy `k`
parameter re-added to `Provable` (Towsner threads `h_{ω^α}(k)` through 19.6/19.7) — assess whether
the `(α,c)` indexing suffices first.

Attack paths:
1. **Continue the `wip/Zinfty.lean` prototype** (E2 encoding — *compiles*). Next: (a) connect
   `AForm` to a faithful arithmetic formula with a real free-variable/substitution layer (replace
   the `ℕ → AForm` family with a single body + numeral substitution), so `rk` is genuinely
   finite; (b) state M3.3 bound-monotonicity lemmas; (c) state M4 embedding + M5 cut-elimination
   theorems as disclosed `sorry`s. Bank each as it typechecks; promote to `src/` when green.
2. **Develop M6 (Hardy domination) via Track 1.** `~/src/lean-formalizations` `Logic/FastGrowing`
   is building `h_α`, monotonicity, and Goodstein-length domination on mathlib's
   `ONote.fastGrowing`. Reuse those for M6.1–M6.3; only M6.4 (Thm 17.1, the cut-free lower bound)
   is new here. (Does NOT block M3–M5 — parallelizable.)
3. **Tackle cut-elimination (M5) on the prototype first**, before the embedding — it is the
   self-contained heart (Towsner §19). **STATUS: M5 is now structured down to ONE leaf.**
   `wip/Zinfty.lean` has `Provable.cutElim` (Thm 19.9, full elimination) *proved* by induction on
   cut rank, reducing entirely to the single open lemma **`Provable.cutElimStep`** (Thm 19.7, one
   level). So the next concrete target is exactly `cutElimStep` = §19 inversions 19.2–19.4 +
   reductions 19.5–19.6 + the principal-`Cut`-on-rank-`c` case. Proving it makes the whole
   cut-elimination machine-checked (mod the embedding M4 and lower bound M6.4). NOTE: `cutElimStep`
   likely needs the numeric/Hardy `k` bound that `Provable` currently elides — re-add a `k : ℕ`
   index to `Provable`/`Deriv.o` first (it threads the `h_{ω^α}(k)` bound through 19.6/19.7).
   *(Resolved lap 3: the `k` index turned out NOT to be needed for cut-elimination.)*
</details>

### O2′ — M4 DESIGN DECISION (scouted lap 3, execute lap 4) ⭐
The embedding needs Z_∞ to derive PA's **true defining axioms** (e.g. `n+(m+1)=(n+m)+1`), which the
current calculus CANNOT: `axL` is the clash-based identity (`rel r v ∧ nrel r v ∈ Γ`) and `verumR`
is only `⊤`. Towsner's "True" rule is a **truth-based atomic axiom**. So M4 requires extending the
calculus. Concrete plan:
1. **Atomic truth predicate** — reuse Foundation `Semiformula.Evalm ℕ` (the `standardModel`
   instance for `ℒₒᵣ` over `ℕ`; `=`/`<` decidable). For embedding-substituted formulas (free vars
   replaced by numerals) truth is assignment-independent. **VALIDATED (lap 3)** — this typechecks
   (imports `Foundation.FirstOrder.Arithmetic.Basic.Model`):
   ```
   noncomputable def atomTrue (φ : SyntacticFormula ℒₒᵣ) : Prop :=
     Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ
   ```
   (`Foundation/.../Semantics/Semantics.lean:241`, `Arithmetic/Basic/Model.lean:25`.)
2. **Add `trueAtom` constructor** to `Deriv`: `(φ : Form) → (φ atomic) → Evalm ℕ … φ → φ ∈ Γ →
   Deriv Γ`, with `o = 0`, `cr = 0`. ⚠️ **This touches the completed cut-elimination**: every
   induction (`orInvAux`, `allInvAux`, `andInvAux`, `cutReduceAllAux`, `atomCutAux`,
   `removeFalsumAux`, `cutElimStepAux`) gains one new leaf case — mostly trivial (like `verumR`),
   EXCEPT `atomCutAux`: a `trueAtom` on the cut atom `rel r v` means `rel r v` is true ⇒ `nrel r v`
   is false ⇒ must remove it from the other premise. So `atomCut` needs a **truth-based false-atomic
   removal** (the genuine §19.2 content, now unavoidable, but only for atomics — decidable ℕ
   arithmetic). Do this extension on a `wip/` copy first; re-green; re-promote.
3. **ε₀** is `ε_ 0` in `Mathlib.SetTheory.Ordinal.Veblen` (first fixed point of `ω^·`); `omegaTower
   c α < ε₀` for `α < ε₀` is the closure fact M5.4/M7 need (ε₀ closed under `ω^·`).
4. Then M4.1 (Lemma 16.1) → M4.2 (Cor 16.6) → M4.3 (Thm 16.7), inducting over a `Peano`-proof
   (`𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`), reusing Foundation's finitary `Derivation`.

**Caveat on the clean state:** cut-elimination is currently truth-free and axiom-clean precisely
because of clash-`axL`. Adding `trueAtom` re-introduces a (decidable, atomic-only) truth layer.
This is the standard Schütte setup and is correct; just do it carefully so the §19 proofs stay green.

### O3 — `PA_delta1Definable : 𝗣𝗔.Δ₁` (Foundation axiom) — only on Route A
Needed to *state* Gödel II for `𝗣𝗔`; Foundation axiomatizes it (TODO in
`Incompleteness/Examples.lean`). Route B avoids it. Attack paths:
1. **Avoid** — go Route B (O1 path 2); the axiom never enters the headline profile.
2. Discharge it: construct the Δ₁-definition of PA's axiom set (PA⁻ + induction scheme) in
   Foundation's `Theory.Δ₁` framework and prove `isDelta1`. Deep arithmetization; multi-lap.
3. Upstream: check whether a newer Foundation rev proves it (the TODO may get filled upstream);
   file an `ON-LINE-REQUEST.md` to check the latest Foundation `Incompleteness/Examples.lean`.

## Done — lap 4 (2026-06-22)
- **Witness-bound architectural finding** (machine-checked, axiom-clean, `wip/WitnessBound.lean`):
  the `src/Zinfty.lean` `(α,c)` cut-elimination is OFF the headline path (its unbounded `∃` makes the
  lower bound false). Built the corrected witness-bounded calculus `B`; proved the existential-fragment
  lower bound (`lowerBound_existential[_real]`) grounded against the real `G`; decomposed the full
  Thm 17.1 to the single `bounding` frontier (`True`/`W`/`I∃` cases machine-verified via `sat_mono_ord`,
  `I∀` case the literature-gated frontier; `lowerBound` contradiction-extraction real). Goodstein-side
  grounded: `G`, `goodstein_zero_succ`/`_mono`, `atomTrue_iff_G_le`. Filed `ON-LINE-REQUEST.md` for the
  rigorous `bounding` invariant + architecture (Towsner `(α,k)` vs Buchholz `H`-controlled).
- Next deep brick (architecture-independent, but gated on the notation/architecture decision):
  the **Hardy / fast-growing hierarchy + τ-controlled monotonicity** to discharge `Hmono`/`Hmono_n`,
  and **Goodstein domination** (Towsner §5–§9) to discharge `Hdom`. mathlib `ONote.fastGrowing`
  exists but has NO growth lemmas (deliberately minimal).
  - **STARTED** (`wip/FastGrowing.lean`, axiom-clean): `fastGrowing_id_le` — `n ≤ fastGrowing o n`
    (the inflationary half, which IS separable from ordinal-monotonicity: successor case via
    iterating a `≥id` map, limit case via the smaller-ordinal IH).
  - **Confirmed entangled:** *numeric* monotonicity (`Hmono_n` analogue) of `fastGrowing` — its
    limit case `fastGrowing (f m) m ≤ fastGrowing (f m') m` needs *ordinal* monotonicity at fixed `n`,
    which is the τ-subtle one (false for small `n` without the coefficient control — Towsner §8). So
    `Hmono`/`Hmono_n` for the real hierarchy genuinely need the τ machinery; not a quick brick.

## Done — lap 1
- M1: `Encoding.goodsteinTerminates_re` proved (`Computability.lean`: `primrec_natLog`,
  `primrec_bump`, `primrec_goodsteinSeq`). Phase 0 axiom-clean.
- M2: `Reduction.lean` — Gödel II hook + meta-reduction (axiom-clean mod `PA_delta1Definable`).
- Phase 2: `PHASE2-DECOMPOSITION.md` (Towsner-grounded ladder) + `wip/Zinfty.lean` (E2 encoding
  prototype — compiles: ω-rule inductive, ordinal/cut-rank measures, bound-domination lemma,
  `Provable.mono`/`.weakening`, and the **proved predicate-level inference API** `Provable.orI`,
  `.exI`, `.allI` — the ω-rule with the supremum ordinal bound, machine-checked against the
  `Deriv` measures via `Classical.choice`).

## ⭐ KEY FINDING (2026-06-22, end of lap) — build `Z_∞` ON Foundation's Tait calculus
Foundation **already has a finitary Tait one-sided FO sequent calculus**:
`FirstOrder/Basic/Calculus.lean` — `inductive Derivation (𝓢 : Schema L) : Sequent L → Type`
with constructors `axL, verum, or, and, all, exs, wk, cut` and a `height` measure, over the *real*
`SyntacticFormula ℒₒᵣ` (which already carries free variables, substitution, negation, rank).
Plus `FirstOrder/Hauptsatz.lean` (finitary cut-elimination). **There is NO infinitary calculus /
ω-rule / `PA_∞`** (confirmed by grep — only finitary Tait + Hauptsatz).

**Consequence — revise M3.1:** do NOT continue the standalone `wip/Zinfty.lean` `AForm`. Instead
define `Z_∞` as a new inductive **over Foundation's `SyntacticFormula ℒₒᵣ`/`Sequent`**, replacing
the finitary `all` (eigenvariable, one premise, `ℕ` height) with the **ω-rule** (`all` taking an
`ℕ`-indexed family `n ↦ φ[x ↦ numeral n]`, `Ordinal` height). This:
- **kills the `AForm` substitution-layer prerequisite** — Foundation's formula substitution +
  `rk` are reused, so `rk φ` is already finite and `cut`/`cutElimStep` become directly stateable;
- **shrinks M4 (embedding):** a PA proof already yields a Foundation *finitary* `Derivation`
  (via Hauptsatz machinery); M4 becomes "finitary `Derivation` ↪ `Z_∞`" (map each rule across,
  ∀→ω-rule) instead of re-deriving from `True`/`Lemma 16.1` by hand;
- **makes M7 natural:** everything is over real `ℒₒᵣ` formulas, so connecting to our
  `goodsteinSentence` is a formula-level statement, not a re-encoding.
The `wip/Zinfty.lean` prototype keeps its value as the *proof that the ordinal/ω-rule measures
work* (the encoding-feasibility result) — port its `o`/`cr`/`allI`/`cutElim` skeleton onto
Foundation's `Derivation`-shaped inductive. **This is the recommended first action next lap**
(read `FirstOrder/Basic/Calculus.lean` + `Hauptsatz.lean` first).

## Design note — `Provable.cut` + the `ℕ∞` cut-rank (next lap, read before refactoring)
`cr : Deriv Γ → ℕ∞` (cut rank can be `⊤` for pathological infinite families). A predicate-level
`Provable.cut` is the one rule still missing: from `Provable α c (φ ::ₘ Γ)` and
`Provable β c (φ.neg ::ₘ Γ)` it should give `Provable (max α β + 1) c' (Γ)` where
`c' ≥ rk φ + 1`. But `rk φ : ℕ∞` may be `⊤`, so you can't pick a finite `c' : ℕ` in general —
`Provable`'s `c : ℕ`. **Fix:** when `AForm` gets the real free-variable + numeral-substitution
layer (the M3.1 refinement), `rk φ` becomes provably finite (`rk φ ≠ ⊤`) for genuine formulas, so
`Provable.cut` and the Hardy-bounded `cutElimStep` both become stateable with finite `c`. So the
substitution-layer refactor is a prerequisite for *both* `cut` and `cutElimStep` — do it first.

## Gotcha noted (for the corpus)
For `Ordinal`, `add_le_add_right h c` elaborates to `c + a ≤ c + b` (adds on the *left*) — use
`add_le_add h le_rfl` to get `a + 1 ≤ b + 1` from `a ≤ b`. `gcongr` on `⨆`-bounds spawns a
`BddAbove (Set.range …)` side-goal (discharge with `Ordinal.bddAbove_range`).
