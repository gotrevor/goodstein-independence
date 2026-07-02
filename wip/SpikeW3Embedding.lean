/-
# SPIKE W3 — the global budgeted-embedding STATEMENT skeleton (operator-commissioned, 2026-07-01)

Deciding experiment #1 of `MASTERPLAN-2026-07-01-ZERO-AXIOMS.md` §5 (W3).  This file is a **typed
skeleton**, NOT a proof campaign: the master statement `budgetedEmbedding` is assembled from one
named `sorry`ed lemma per `Derivation2` rule case by a REAL (non-`sorry`) induction, so that any
rule whose budget cannot survive the global embedding induction surfaces as a typing mismatch (none
did — the skeleton elaborates) and every genuine obstruction is exposed at the case-lemma level for
the verdict.  Sorries here are expected and correct.  See `SPIKE-W3-VERDICT.md`.

Template: `src/GoodsteinPA/Embedding.lean:525` (`embedC`, the complete UNBOUNDED embedding — 10
`Derivation2` cases).  Target calculus: the witness-bounded operator calculus `ZekdSomeK`
(`src/GoodsteinPA/OperatorZinfty.lean:1991`).

Budget discipline (Towsner §16, as stated in the candidate signature): the cut-rank `c` and the
additive norm budget `d₀` are structural (derivation-only, chosen OUTSIDE `∀ env`); the numeral
witness budget `K` lives inside `ZekdSomeK`'s `∃ K` and may depend on `env`; the ordinals `α`, `e`
are chosen per node.  (The verdict documents the ONE amendment the ω-rule forces on this candidate:
`e` — and the ordinal family's uniform `< ε₀` bound — must be structural too, i.e. hoisted OUTSIDE
`∀ env`, exactly as `EmbeddingBound.embedC_LX_bdd` does for the ordinal-only half.)
-/
import GoodsteinPA.Embedding
import GoodsteinPA.OperatorZinfty

namespace GoodsteinPA.SpikeW3

open LO LO.FirstOrder ONote GoodsteinPA.OperatorZinfty

/-- **The master statement's body**, as a reusable predicate.  A `Derivation2`-sequent `Γ` is
*budgeted-embeddable* iff there are structural budgets `c`, `d₀` such that, at every numeral
assignment `env` of the free variables, the closed image `Γ.image (asg env ▹ ·)` has a
witness-bounded operator derivation `ZekdSomeK α e d₀ c` for some node ordinals `α`, `e` (both NF,
hence `< ε₀`).  This is exactly the candidate master signature of `SPIKE-W3-STATEMENT.md`. -/
def BudgetedEmbeds (Γ : Finset (SyntacticFormula ℒₒᵣ)) : Prop :=
  ∃ c d₀ : ℕ, ∀ env : ℕ → ℕ, ∃ α e : ONote, α.NF ∧ e.NF ∧
    ZekdSomeK α e d₀ c (Γ.image (fun φ => Embedding.asg env ▹ φ))

/-! ## One named case lemma per `Derivation2` rule (mirrors `embedC`'s split exactly).

Each is stated with the SAME budget discipline (conclusion `BudgetedEmbeds`, IHs `BudgetedEmbeds`).
The docstrings record the probe-consistency check (`SPIKE-W3-STATEMENT.md` objective #3): which
banked `OperatorZinfty` probe discharges the case, and whether the case looks mechanical or hard. -/

/-- **`closed` — identity / excluded-middle leaf** (`φ, ∼φ ∈ Γ`).
Consistency: `ZekdSomeK.axL` for the atomic base; general `φ` via the banked EM probe
`embedding_valueCongruentEM_probe` (the `ZekdSomeK`-level analogue of `embedC`'s `provable_em`).
Verdict: **mechanical** (banked). -/
theorem budgetedEmbedding_closed {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (φ : SyntacticFormula ℒₒᵣ) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    BudgetedEmbeds Γ := by
  sorry

/-- **`axm` — PA axiom leaf** (`φ ∈ 𝗣𝗔`).  THE structurally hard case.  In the *unbounded* `embedC`
this is discharged for free (`provable_true`, ω-completeness — a PA axiom is a true closed formula);
the witness-bounded calculus must PAY for it, and it dispatches by the shape of `σ`:
 * finite `𝗣𝗔⁻` + equality axioms → `ZekdSomeK.ofBoundedTruth` (masterplan reified capstone #1,
   `boundedAxiomLeaves`; the lone existential-witness sub-case `addEqOfLt` uses the closed-term
   `exI` probes);
 * the **induction schema** (arbitrary matrix) → the bounded cut-tower
   `inductionLeaf_cutTowerStepWithTerm_someK_probe` packaged by
   `inductionLeaf_allOmegaFromStep_someK_probe` (masterplan reified capstone #2, `boundedInduction`).
Verdict: **hard** — this case IS masterplan phases W1+W2; it is a leaf here only because W1/W2 feed W3. -/
theorem budgetedEmbedding_axm {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (φ : SyntacticFormula ℒₒᵣ) (hφ : φ ∈ (𝗣𝗔 : Schema ℒₒᵣ)) (hΓ : φ ∈ Γ) :
    BudgetedEmbeds Γ := by
  sorry

/-- **`verum`** (`⊤ ∈ Γ`).  Consistency: `ZekdSomeK.verumR`.  Verdict: **mechanical**. -/
theorem budgetedEmbedding_verum {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (h : (⊤ : SyntacticFormula ℒₒᵣ) ∈ Γ) :
    BudgetedEmbeds Γ := by
  sorry

/-- **`and`.**  Consistency: `ZekdSomeK.andI`, after aligning the two IH budgets `(c, d₀)` by `max`
(`ZekdSomeK.mono_c`/`mono_d`) and unifying the per-node control ordinals `e` (`ZekdSomeK.mono_e`).
Verdict: **mechanical** given `e` structural (see verdict); the `e`-unification is the only bookkeeping. -/
theorem budgetedEmbedding_and {Γ : Finset (SyntacticFormula ℒₒᵣ)} {φ ψ : SyntacticFormula ℒₒᵣ}
    (h : φ ⋏ ψ ∈ Γ)
    (ihp : BudgetedEmbeds (insert φ Γ)) (ihq : BudgetedEmbeds (insert ψ Γ)) :
    BudgetedEmbeds Γ := by
  sorry

/-- **`or`.**  Consistency: `ZekdSomeK.orI`.  Verdict: **mechanical**. -/
theorem budgetedEmbedding_or {Γ : Finset (SyntacticFormula ℒₒᵣ)} {φ ψ : SyntacticFormula ℒₒᵣ}
    (h : φ ⋎ ψ ∈ Γ)
    (ih : BudgetedEmbeds (insert φ (insert ψ Γ))) :
    BudgetedEmbeds Γ := by
  sorry

/-- **`all` — the ω-rule.**  THE tight case for the budget discipline.  `embedC` instantiates the IH
at the shifted assignment `n :>ₙ env` for each branch `n` and closes with the *unbounded*
`Provable.allω`, which `⨆`-sups an arbitrary family over full `Ordinal.{0}` and carries NO witness
index.  The witness-bounded `ZekdSomeK.allω` instead demands (i) a family `β : ℕ → ONote` uniformly
`< α` for a single NF `α` (`EmbeddingBound`'s uniform-ω-family discipline — finite branches sup to
`ω`, nested-∀ handled by `allClosure`), (ii) a SINGLE control ordinal `e` across all branches, and
(iii) the running-index `max K n`.  (i)+(iii) are absorbed by `∃ K`; (ii) is the amendment finding
— see verdict.  Consistency: `ZekdSomeK.allω` + `inductionLeaf_allOmegaFromStep_someK_probe`.
Verdict: **hard** (needs the `EmbeddingBound` port into the witness-bounded calculus + the `e`
hoist). -/
theorem budgetedEmbedding_all {Γ : Finset (SyntacticFormula ℒₒᵣ)} {φ : SyntacticSemiformula ℒₒᵣ 1}
    (h : ∀⁰ φ ∈ Γ)
    (ih : BudgetedEmbeds (insert (Rewriting.free φ) (Γ.image Rewriting.shift))) :
    BudgetedEmbeds Γ := by
  sorry

/-- **`exs`** — explicit witness term `t`.  Consistency: `embedding_closedTermExI_someK_probe`
(the closed-term collapse: `asg env t` is closed, value `stdClosedVal (asg env t)`, absorbed into
the finite index `K` inside `∃ K`).  Verdict: **mechanical** (banked) — this is the objective-#3
probe check for the `ex` case, and it holds: the probe's signature is exactly this obligation. -/
theorem budgetedEmbedding_exs {Γ : Finset (SyntacticFormula ℒₒᵣ)} {φ : SyntacticSemiformula ℒₒᵣ 1}
    (h : ∃⁰ φ ∈ Γ) (t : SyntacticTerm ℒₒᵣ)
    (ih : BudgetedEmbeds (insert (φ/[t]) Γ)) :
    BudgetedEmbeds Γ := by
  sorry

/-- **`wk`** (weakening).  Consistency: `ZekdSomeK.wk` + `Finset.image_subset_image`.
Verdict: **mechanical**. -/
theorem budgetedEmbedding_wk {Δ Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (hsub : Δ ⊆ Γ) (ih : BudgetedEmbeds Δ) :
    BudgetedEmbeds Γ := by
  sorry

/-- **`shift`** (eigenvariable re-indexing).  Consistency: as in `embedC`,
`asg env ∘ Rew.shift = asg (env ∘ succ)`, so the image is unchanged up to re-indexing the
assignment; the budgets and derivation carry over unchanged.  Verdict: **mechanical**. -/
theorem budgetedEmbedding_shift {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (ih : BudgetedEmbeds Γ) :
    BudgetedEmbeds (Γ.image Rewriting.shift) := by
  sorry

/-- **`cut`.**  Consistency: `ZekdSomeK.cut`, after aligning budgets by `max`; the structural
cut-rank `c` must dominate `φ.complexity` (env-independent — substitution preserves complexity),
which is why `c` is safely OUTSIDE `∀ env`.  Verdict: **mechanical** given `e` structural. -/
theorem budgetedEmbedding_cut {Γ : Finset (SyntacticFormula ℒₒᵣ)} {φ : SyntacticFormula ℒₒᵣ}
    (ihp : BudgetedEmbeds (insert φ Γ)) (ihn : BudgetedEmbeds (insert (∼φ) Γ)) :
    BudgetedEmbeds Γ := by
  sorry

/-! ## The master theorem — assembled by a REAL (non-`sorry`) induction.

The signature is the candidate of `SPIKE-W3-STATEMENT.md` verbatim; its body is `BudgetedEmbeds Γ`
(`show` unfolds the `def`).  The induction mirrors `embedC`'s 10-case split exactly; each arm is a
single `exact` into the corresponding case lemma, so the whole global embedding induction is
STRUCTURALLY closed — only the leaf lemmas are `sorry`.  That the assembly elaborates is the spike's
positive result: the candidate budget survives the global induction (modulo the documented `e`
amendment). -/
theorem budgetedEmbedding {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) :
    ∃ c d₀ : ℕ, ∀ env : ℕ → ℕ, ∃ α e : ONote, α.NF ∧ e.NF ∧
      ZekdSomeK α e d₀ c (Γ.image (fun φ => Embedding.asg env ▹ φ)) := by
  show BudgetedEmbeds Γ
  induction d with
  | closed Γ φ hp hn => exact budgetedEmbedding_closed φ hp hn
  | axm φ hφ hΓ => exact budgetedEmbedding_axm φ hφ hΓ
  | verum h => exact budgetedEmbedding_verum h
  | @and Γ φ ψ h _dp _dq ihp ihq => exact budgetedEmbedding_and h ihp ihq
  | @or Γ φ ψ h _d ih => exact budgetedEmbedding_or h ih
  | @all Γ φ h _d ih => exact budgetedEmbedding_all h ih
  | @exs Γ φ h t _d ih => exact budgetedEmbedding_exs h t ih
  | @wk Δ Γ _d hsub ih => exact budgetedEmbedding_wk hsub ih
  | @shift Γ _d ih => exact budgetedEmbedding_shift ih
  | @cut Γ φ _dp _dn ihp ihn => exact budgetedEmbedding_cut ihp ihn

end GoodsteinPA.SpikeW3

-- Real axiom footprint of the assembled master (expect `sorryAx` + the 3 canonical; NO new
-- `axiom` declarations anywhere in this file):
--   [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms GoodsteinPA.SpikeW3.budgetedEmbedding
