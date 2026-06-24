/-
# `StdCor34F.lean` — Crux 1: the internal Cor-3.4 run over a width FUNCTION

**Status: COMPLETE (axiom-clean, in the build). The lap-57 width-code-wall fix, step 2.**

`StdCor34.crux1_internal_run_of_width_dom` drives the internal Goodstein run through `BlkRec.blk wseq`
(a finite code) — which `ANALYSIS-2026-06-23-lap57-width-code-wall.md` shows cannot carry a genuine
infinite descent. This file re-runs the same assembly through `BlkRecF.blkF` (a width FUNCTION
`W := fun t => iC (β (t+1))`, the internal `Grz.corW`), so the elapsed width grows without a code-length
ceiling and the slowness C-bound `iC (β (blkF j)) ≤ iC (β 0) + j` holds for **all** `j` — discharged
internally (no `hβC` hypothesis), via the internal `C_le_wsum_corW` analog `iC_le_wsumcF`.

Result `crux1_internal_run_F`: from a `𝚺₁`-definable `≺`-descending NF-nonzero `β` whose **width**
`iC (β (n+1))` is `iF l₀`-dominated, the internal Goodstein run is non-terminating. No finite code, no
`Cβ`/`wseq` to supply — the entire remaining crux-1 width gap is closed.
-/
import GoodsteinPA.StdCor34
import GoodsteinPA.BlkRecF

namespace GoodsteinPA.StdCor34F

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.InternalONote GoodsteinPA.IIter GoodsteinPA.InternalIg
open GoodsteinPA.InternalPow GoodsteinPA.StdCor34

set_option maxHeartbeats 400000

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **`iC` positivity**: a nonzero normal-form code has `iC ≥ 1` (its leading coefficient is `≥ 1` and
`iC` reads `≥` that coefficient). -/
theorem one_le_iC_of_ne_zero {c : V} (h : isNF c) (hc : c ≠ 0) : 1 ≤ iC c := by
  have hco : ocCoeff c ≠ 0 :=
    ((isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)).1
  rw [← ocOadd_destruct hc, iC_ocOadd]
  exact le_trans (pos_iff_one_le.mp (pos_of_ne_zero hco)) (le_max_of_le_left (le_max_right _ _))

/-! ## The width function `W t = iC (β (t+1))` and its `𝚺₁` graph -/

/-- The internal Cor-3.4 width function (the internal `Grz.corW`). -/
noncomputable def corWF (β : V → V) (t : V) : V := iC (β (t + 1))

variable {β : V → V} {βDef : 𝚺₁.Semisentence 2}

def _root_.LO.FirstOrder.Arithmetic.corWFDef (βDef : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 2 :=
  .mkSigma “y t. ∃ b, !βDef b (t + 1) ∧ !iCDef y b”

theorem corWF_defined (hβ : 𝚺₁.DefinedFunction₁ β βDef) :
    𝚺₁.DefinedFunction₁ (corWF β : V → V) (corWFDef βDef) := .mk fun v ↦ by
  simp [corWFDef, corWF, hβ.iff, iC_defined.iff]

/-- **The internal `C_le_wsum_corW`**: for `n ≥ 1`, `iC (β n) ≤ wsumcF (corWF β) n` — `iC (β n)`
is one summand (`corWF β (n-1)`) of the cumulative width. -/
theorem iC_le_wsumcF (hβ : 𝚺₁.DefinedFunction₁ β βDef) {n : V} (hn : 1 ≤ n) :
    iC (β n) ≤ BlkRecF.wsumcF (corWFDef βDef) (corWF β) (corWF_defined hβ) n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by rw [sub_add_self_of_le hn]⟩
  rw [BlkRecF.wsumcF_succ]
  show iC (β (n' + 1)) ≤ _ + corWF β n'
  rw [corWF]
  exact le_add_self

/-! ## The crux-1 internal run over the width function -/

/-- **Crux-1 internal run, width-FUNCTION form (the width-code-wall fix).** From a `𝚺₁`-definable
`≺`-descending NF-nonzero `β` whose width `iC (β (n+1))` is `iF l₀`-dominated, the internal Goodstein
run is non-terminating. The slowness C-bound and the within-block domination are discharged INTERNALLY
(`iC_le_wsumcF` + `BlkRecF.wsumcF_blkF_le`; `BlkRecF.offF_succ_lt_width_of_blkF_eq` + `hwdom`); no
finite `wseq`, no `Cβ` to supply. This replaces `StdCor34.crux1_internal_run_of_width_dom`. -/
theorem crux1_internal_run_F (l₀ : ℕ) (hl₀ : 0 < l₀)
    (hβNF : ∀ n, isNF (β n)) (hβ0 : ∀ n, β n ≠ 0)
    (hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0)
    (hβdef : 𝚺₁.DefinedFunction₁ β βDef)
    (hwdom : ∀ n, iC (β (n + 1)) ≤ iF l₀ n) :
    ∃ m₀ : V, ∀ k : V, 0 < igoodstein m₀ k := by
  -- the width function and its block bookkeeping
  set W := corWF β with hWdef
  set WDef := corWFDef βDef with hWDefdef
  have hW : 𝚺₁.DefinedFunction₁ W WDef := corWF_defined hβdef
  have hWpos : ∀ b, 1 ≤ W b := fun b => one_le_iC_of_ne_zero (hβNF (b + 1)) (hβ0 (b + 1))
  set blk := BlkRecF.blkF WDef W hW with hblkdef
  set off := BlkRecF.offF WDef W hW with hoffdef
  -- (a) the slowness C-bound `iC (β (blk j)) ≤ iC (β 0) + j`, discharged internally
  have hβC : ∀ j, iC (β (blk j)) ≤ iC (β 0) + j := by
    intro j
    rcases eq_or_ne (blk j) 0 with h0 | hpos
    · rw [h0]; exact le_self_add
    · have h1 : 1 ≤ blk j := pos_iff_one_le.mp (pos_of_ne_zero hpos)
      calc iC (β (blk j)) ≤ BlkRecF.wsumcF WDef W hW (blk j) := iC_le_wsumcF hβdef h1
        _ ≤ j := BlkRecF.wsumcF_blkF_le hWpos j
        _ ≤ iC (β 0) + j := le_add_self
  -- (b) the within-block domination `off j + 1 < iF l₀ (blk j)` from width domination
  have hdom : ∀ j, blk (j + 1) = blk j → off j + 1 < iF l₀ (blk j) := by
    intro j hb
    exact lt_of_lt_of_le (BlkRecF.offF_succ_lt_width_of_blkF_eq j hb) (hwdom (blk j))
  -- (c) feed the abstract Cor-3.4 → Thm-3.5 assembly with `blk`/`off` from `BlkRecF`
  obtain ⟨K, s, _, hNF, hC, hdesc⟩ :=
    bbeta_of_igtTot l₀ hl₀ (β := β) (blk := blk) (off := off) (Cβ := iC (β 0))
      hβNF hβ0 hβdesc hβC
      (BlkRecF.blkF_succ_dich) (BlkRecF.offF_succ_of_blkF_eq) (BlkRecF.blkF_add_offF_le) hdom
  -- (d) definability of the slowed sequence and the Lemma-3.6 engine
  have hbdef : 𝚺₁-Function₁ (bbeta K s (salpha (l₀ : V) β blk off (igtTot l₀)) : V → V) := by
    haveI : 𝚺₁-Function₁ (blk : V → V) := BlkRecF.blkF_definable 𝚺
    haveI : 𝚺₁-Function₁ (off : V → V) := BlkRecF.offF_definable 𝚺
    exact bbeta_definable K s
      (salpha_definable (l₀ : V) hβdef.to_definable inferInstance inferInstance (igtTot_definable l₀ 𝚺))
  exact nonterminating_of_bbeta_facts hbdef hNF hC hdesc

end GoodsteinPA.StdCor34F
