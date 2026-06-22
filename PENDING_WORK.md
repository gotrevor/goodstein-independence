# Pending work — open obligations & attack paths

State after lap 6 (2026-06-22). Build green (`lake build GoodsteinPA`, 1257 jobs). Phase 0 + Phase 1
clean; **M5 (cut-elim) and M6 (Hardy lower bound) both DONE**. Headline stays a literal `sorry`
(anti-fraud). See `PHASE2-DECOMPOSITION.md` for the girder ladder; `ANALYSIS-…-bounding-resolution.md`
§"M4 scoping" for the 5-step connecting spine.

## ✅ LAP-6 — M6 DONE (lower bound self-contained); TOP PRIORITY now = step 1, the `Zᵏ` calculus
`src/GoodsteinPA/LowerBound.lean` (`lowerBound_hardy_selfcontained`) is the full Towsner Thm 17.1 with
no hypotheses beyond `α.NF`, axiom-clean modulo the 🟢 `native_decide` Goodstein base-cases. M5 + M6
are now both complete but **disconnected** (M5 = unbounded `(α,c)` over real `ℒₒᵣ`; M6 = bounded
`(α,k)` over the `GForm` fragment). The connecting spine (hardest-first):

### Step 1 — `Zᵏ`: witness-bounded ω-calculus over real `SyntacticFormula ℒₒᵣ` (Towsner §15)
**DEFINED + §19.2–19.5 DONE** (`wip/BoundedZinfty.lean`, lap 6, all axiom-clean). Chosen design:
**ONote-indexed, B-style (bound-as-parameter, no `⨆`-suprema)** over real `ℒₒᵣ` formulas, with both
`(α,k)` side conditions the lower bound needs (lap-4 finding — cannot be dropped): truth-atom rules
`trueRel`/`trueNrel` (`norm α < k`) + `∃`-witness bound (`exI` carries `n ≤ hardy α k`). Plus a
height-preserving `wk`, a β<α `weak` (raises ordinals in principal inversion cases), `∧`/`∨`/`cut`.
Built: `mono_k`, `mono_c`, `wk`/`weakening`; the **full inversion suite** `orInv`/`andInvL`/`andInvR`/
`allInv` (reshuffle helpers `invPush`/`invPull`/`invPush2`/`inv1Push`/… kept standalone so
`DecidableEq Form` doesn't blow the heartbeat limit inside the big inductions); the **§19.5** ∧/∨
cut-reductions `cutReduceConj`/`cutReduceDisj` (`lt_osucc` + caller-supplied NF upper bound `δ`, result
at `osucc δ` — no natural sum needed).

**NEXT — §19.6 ∀/∃ cut-reduction `cutReduceAllAux`** (the hard, non-invertible one; the witness-bound
survival crux). Port `src/Zinfty.lean`'s measure-style version to parameter-style:
- **Bound framing:** the family `fam : ∀ n, Zk α k c (insert (φ/[nm n]) Γ)`; induct on the ∃-side
  `d : Zk γ k c Δ` with running conclusion bound **`α + γ`** (`ONote.add`; `add_nf` instance gives NF,
  `repr_add` + `Ordinal.add_lt_add_left` give strict monotonicity in `γ` for the premise-`<` conditions).
- **Principal `exI` case** (∃-side introduces `∃⁰∼φ` at witness `n`): cut `fam n` (∀-instance) against
  the ∃-premise on `φ/[nm n]` (complexity `< c`). This is the witness cut.
- The non-principal cases mirror the inversions (reuse the union-reshuffle pattern; src frames the
  running sequent as `Δ.erase (∃⁰∼φ) ∪ Γ`).

**Then `cutElimStep` (§19.7, `c+1→c`, bound `ω^α = oadd α 1 0`) + `cutElim` (§19.9).**

⚠️ **KEY FINDING (lap 6) — the `norm<k` budget does NOT survive ordinal addition; it grows.** `norm`
is `max` over CNF coefficients (`Hardy.lean:637`), and addition MERGES coefficients when leading
exponents coincide: machine-checked `norm ω = 1` but `norm (ω+ω) = norm (ω·2) = 2`. So the naive
"`norm(α+γ) ≤ max`" is **false**; the true bound is additive (`norm(α+γ) ≤ norm α + norm γ`, to verify).
Consequences for the cut-elim design:
- **§19.7 `ω^α` blow-up is SAFE:** `norm (oadd α 1 0) = max (norm α) 1` (machine-checked, `norm_omegaPow`),
  coefficient stays `1` — a pure ω-tower never bumps `norm` beyond `max(norm α, 1)`. So iterating the
  rank-reduction keeps the budget (for `k ≥ 2`).
- **§19.6 within-rank addition is where `norm` grows.** The ω-rule combines premises by *supremum*
  (bound-as-parameter, no sum), NOT addition — so it doesn't bump `norm`. Only the §19.6 cut-combination
  (∀-family `α` + ∃-side `γ`) is an addition, and cut-elim performs finitely many such reductions (cut
  rank `c` finite), so `norm` grows by a *bounded* amount ⇒ choosing `k` large enough at embedding (M4)
  absorbs it. **The precise bookkeeping (how Towsner threads `τ`/`k` through §19; the exact growth bound)
  needs the paper — see `ON-LINE-REQUEST.md`.** Do NOT claim cut-elim closed until this is pinned down.
- Helpers banked this lap: `lt_osucc`, `add_lt_add_left_NF`, `le_add_left_NF`, `norm_omegaPow`. Still
  need (build with §19.6): `norm (α+γ) ≤ norm α + norm γ`, `norm (osucc δ) ≤ norm δ + 1`.
(`Ordinal.nadd`/`♯` absent in mathlib v4.31.0; ordinary `+`/`osucc` with slack, as `src/Zinfty.lean` did
— note natural sum would NOT help here, it merges coefficients the same way.)

### Step 2 — M4 embedding `PA ⊢ φ ⟹ Zᵏ ⊢^{α,k}_c φ`  (UNBLOCKED — independent of the §19.6 τ/k question)
α<ε₀, finite c (Towsner §16/§18). **Reconnaissance done (lap 6).** Foundation's proof object is
`Derivation (𝓢 : Schema L) : Sequent L → Type` in `Foundation/FirstOrder/Basic/Calculus.lean:20`
(`Sequent L = List (SyntacticFormula L)`, one-sided/Tait). Constructors + their `Zᵏ` image (the
embedding inducts on this `Derivation`):
- `axm : φ ∈ 𝓢` — **the PA-axiom case, the crux.** `Zᵏ` must derive each PA axiom at a bounded `(α,k)`:
  Lemma 16.1 (true Δ₀/atomic axioms via the `trueRel`/`trueNrel` rules, low bound) + Cor 16.6 (the
  **induction-scheme** instances at bound `ω·4 # 2rk(φ) # 8` — the real work; `∀`-closure via the
  ω-rule). This is the bulk of M4.
- `axL r v`→`Zk.axL`; `verum`→`Zk.verumR`; `or`→`Zk.orI`; `and`→`Zk.andI`; `wk`→`Zk.wk`;
  `cut`→`Zk.cut` (finitely many cut formulas of bounded complexity ⇒ finite cut rank `c`).
- `all` (eigenvariable `φ.free`) → **`Zk.allω`** (finitary ∀ becomes the ω-rule: derive `φ/[nm n]` for
  every `n`). 2nd deep case: needs **derivation-substitution** — specialize the single eigenvariable
  premise (`φ.free :: Γ⁺`, fresh free var) to each numeral `n` (Foundation `Rew`/free-var substitution
  on a whole `Derivation`). The uniform eigenvariable proof instantiates to all `ℕ`-many ω-rule premises.
- `exs t` (witness *term* `t`) → **`Zk.exI`** with numeral `⟦t⟧ℕ`, needing the **witness bound**
  `⟦t⟧ℕ ≤ hardy α k` (Towsner picks `k` large enough — where the bound is established).
Two wrinkles: (a) Foundation sequents are **`List`**, `Zᵏ` uses **`Finset`** — need a list→finset bridge.
(b) Confirm how `𝗣𝗔 ⊢ ↑goodsteinSentence` (the headline's `LO.Entailment`) connects to `Derivation
𝗣𝗔-schema` (the `OneSided` instance at `Calculus.lean:31` is `Derivation`). The structural map is
clean — the depth is all in `axm`. Foundation-heavy; not Aristotle-friendly.

### Step 3 — cut-elim with `k`
Redo `src/Zinfty.lean` §19 tracking the witness bound. The inversions/reductions *strategy* ports; the
new content is threading `h_{ω^α}(k)` through §19.6 (∀/∃ reduction) and confirming `ω^α < ε₀` keeps the
final cut-free bound `< ε₀` (so domination still bites). No deep math doubt (literature-standard,
host-verified) — formalization labor.

### Step 4 — subformula bridge (the clean small connector)
A cut-free `Zᵏ`-derivation of `{gAll}` contains only subformulas of `gAll` closed under numeral
substitution = exactly `{gAll, gEx n, atom m n}` = the `GForm` fragment, so it **is** a `B`-derivation
⇒ `lowerBound_hardy_selfcontained` refutes it. Needs: a subformula-closure lemma for the ω-calculus
(structural induction over `Deriv`, ω-rule = closure under numeral substitution) + the `GForm ↪ ℒₒᵣ`
encoding identification. Reuses M6 as-is.

### M7a — the language gap (the other hard girder; Towsner Remark 10.3)
`goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is an **opaque Σ₁ blob**, NOT the
transparent `∀x∃y g_y(x)=0` that step 4 needs. Build a transparent Π₂ `gAllReal` (arithmetize
`goodsteinSeq` as a real `ℒₒᵣ` formula — Foundation's Σ₁/representability tools) and prove
`𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`'s spec so faithfulness can't regress.
Then the subformula bridge runs on `gAllReal`.

## ✅ LAP-5 — O0 done + the I∀ frontier RESOLVED; TOP PRIORITY is now O0′ (port `Hdom`)
The witness-bounded calculus `B` is now built over `ONote` with the **concrete** Hardy hierarchy
(`src/GoodsteinPA/Hardy.lean`, ported from Track-1). `wip/LowerBoundHardy.lean` proves, axiom-clean:
the ∃-fragment lower bound (`lowerBound_existential_hardy`, zero abstract hyps), `k`-monotonicity,
**∀-inversion** (`B.allInv`), and the **full Thm 17.1 modulo domination** (`lowerBound_hardy`). The
lap-4 "accumulating existentials" wall is resolved by inverting `gAll` away rather than carrying it
(see `ANALYSIS-2026-06-22-bounding-resolution.md`).

### O0′ (TOP) — discharge `Hdom : ∃ x, hardy α (max k x) < G x`
`G = goodsteinLength`; Goodstein defs (`bump`/`base`/`goodsteinSeq`) are **byte-identical** to Track-1.
Port `~/src/lean-formalizations Logic/Goodstein/{Length,Domination,DominationOmega,TowerDomination,
GrowthStatement,DominationCorollary,GoodsteinLike,DominationBaseCases}.lean` →
`goodsteinLength_dominates_fastGrowing {o}(ho:o.NF) : ∃ N, ∀ m≥N, fastGrowing o m ≤ goodsteinLength m+2`.
Chain `hardy α m ≤ fastGrowing α m` (`hardy_le_fastGrowing`) + identify `G = goodsteinLength`. **Bridge
the `+2` to strict `<`** (the one genuinely-open bit; fastGrowing's gap over hardy swallows +2 for
large m — good Aristotle target). Then `lowerBound_hardy` becomes a self-contained Thm 17.1. NB the
port carries documented `native_decide` finite-base-case axioms.

<details><summary>Superseded lap-4 O0 (re-architect on the witness-bounded calculus) — DONE</summary>

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
</details>

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

**UPDATE (lap 6, cross-session news):** a separate session (`~/src/Foundation-delta1-burndown`,
branch `feat/induction-scheme-delta1`) is **actively discharging** both `PA_delta1Definable` and
`ISigma1_delta1Definable` (proving them in `InductionSchemeDelta1.lean`; reduced `PA.Δ₁` to 3 isolated
obligations, build green, ~1–2 laps to PA-complete per that session). So path 3 is in progress
**upstream** — do NOT duplicate it here. When it lands and our Foundation pin bumps to include it,
Route A's `not_proves_of_implies_consistency` becomes axiom-clean (no `PA_delta1Definable`). This is a
**fallback de-risk only**: our headline stays on **Route B** (Towsner direct, avoids `Con(PA)` and this
axiom). `goodstein_implies_consistency` (the `TI(ε₀)⊢Con(PA)`-inside-PA girder of Route A) remains
deeply blocked regardless, so the Δ₁ news doesn't make Route A the preferred path.

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
