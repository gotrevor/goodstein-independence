/-
# `InternalBump.lean` — E-core(b) brick 4: the hereditary base-change `bump` inside `V`

Brick 4 (`DESCENT-PLAN.md §3`). `Defs.bump b n` is course-of-values recursion (it recurses at
`e = log_b n` and `r = n mod b^e`, both `< n`). To realize it inside `V ⊧ₘ* 𝗜𝚺₁` we use the standard
table reduction of strong recursion to primitive recursion (`HFS/PRF.lean`'s `PR.Construction`):

* `bumpNext b M s` — the value `bump b M` computed from the **table** `s = ⟨bump b 0,…,bump b (M-1)⟩`
  (length `M`): peel the top base-`b` power of `M` and read the two recursive sub-results out of `s`.

This file establishes `bumpNext` and its `𝚺₁`-definability (the artifact the table's `PR.Blueprint`
references). Brick 4b will assemble the table itself via `PR.Construction`, brick 4c will read off
`ibump b n := (table b n).[n]` and prove it satisfies `Defs.bump`'s recursion.
-/
import GoodsteinPA.InternalLog

namespace GoodsteinPA.InternalPow

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Table step of `bump`.** Given the table `s = ⟨bump b 0,…,bump b (M-1)⟩`, compute `bump b M` by
peeling the top base-`b` power: `e = ilog b M`, top coefficient `M / b^e`, exponent result `s.[e]`,
remainder result `s.[M % b^e]`. (For `M ≥ 1` with a correct table this equals `Defs.bump b M`.) -/
noncomputable def bumpNext (b M s : V) : V :=
  M / ipow b (ilog b M) * ipow (b + 1) (znth s (ilog b M)) + znth s (M % ipow b (ilog b M))

/-- The `𝚺₁` graph-definition of `bumpNext`, composing `ilog`, `ipow`, `znth`, `div`, `rem`. -/
def _root_.LO.FirstOrder.Arithmetic.bumpNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b M s.
    ∃ e, !ilogDef e b M ∧ ∃ pe, !ipowDef pe b e ∧ ∃ te, !znthDef te s e ∧
      ∃ pte, !ipowDef pte (b + 1) te ∧ ∃ q, !divDef q M pe ∧ ∃ r, !remDef r M pe ∧
        ∃ tr, !znthDef tr s r ∧ y = q * pte + tr”

instance bumpNext_defined : 𝚺₁-Function₃ (bumpNext : V → V → V → V) via bumpNextDef := .mk fun v ↦ by
  simp [bumpNextDef, bumpNext, ilog_defined.iff, ipow_defined.iff, znth_defined.iff,
    div_defined.iff, rem_defined.iff]

instance bumpNext_definable : 𝚺₁-Function₃ (bumpNext : V → V → V → V) := bumpNext_defined.to_definable

/-! ### The `bump` table via primitive recursion -/

/-- Blueprint for the `bump` table: `bumpTable b 0 = ⟨0⟩`, `bumpTable b (n+1)` appends
`bumpNext b (n+1) (bumpTable b n)`. -/
def bumpTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n x. ∃ v, !bumpNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def bumpTable.construction : PR.Construction V bumpTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun x n ih ↦ seqCons ih (bumpNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [bumpTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [bumpTable.blueprint, bumpNext_defined.iff, seqCons_defined.iff]

/-- **The `bump` table** inside `V`: `ibumpTable b n = ⟨bump b 0,…,bump b n⟩` (length `n+1`). -/
noncomputable def ibumpTable (b n : V) : V := bumpTable.construction.result ![b] n

@[simp] lemma ibumpTable_zero (b : V) : ibumpTable b 0 = !⟦0⟧ := by
  simp [ibumpTable, bumpTable.construction]

@[simp] lemma ibumpTable_succ (b n : V) :
    ibumpTable b (n + 1) = seqCons (ibumpTable b n) (bumpNext b (n + 1) (ibumpTable b n)) := by
  simp [ibumpTable, bumpTable.construction]

/-- **Internalized hereditary base-change** `bump b n` in `V`: the `n`-th entry of the table. -/
noncomputable def ibump (b n : V) : V := znth (ibumpTable b n) n

section

def _root_.LO.FirstOrder.Arithmetic.ibumpTableDef : 𝚺₁.Semisentence 3 :=
  bumpTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance ibumpTable_defined : 𝚺₁-Function₂ (ibumpTable : V → V → V) via ibumpTableDef := .mk
  fun v ↦ by simp [bumpTable.construction.result_defined_iff, ibumpTableDef]; rfl

instance ibumpTable_definable : 𝚺₁-Function₂ (ibumpTable : V → V → V) := ibumpTable_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.ibumpDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y b n. ∃ t, !ibumpTableDef t b n ∧ !znthDef y t n”

instance ibump_defined : 𝚺₁-Function₂ (ibump : V → V → V) via ibumpDef := .mk fun v ↦ by
  simp [ibumpDef, ibump, ibumpTable_defined.iff, znth_defined.iff]

instance ibump_definable : 𝚺₁-Function₂ (ibump : V → V → V) := ibump_defined.to_definable

end

end GoodsteinPA.InternalPow
