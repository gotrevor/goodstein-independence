/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import OrdinalAnalysis.Gentzen.NotationBridge

/-!
# Internal fundamental sequences on Wu's ordinal-notation codes

`OrdinalAnalysis.Gentzen.InternalONote` arithmetizes the Cantor-normal-form *codes* of `ONote`
inside every model of `𝗜𝚺₁`, together with comparison (`icmp`), normal-form recognition (`isNF`)
and addition (`iadd`).  The lower half of Wainer's classification additionally needs the
**fundamental sequence** — that is what the fast-growing recursion recurses along — so this file
adds it, in the same course-of-values table idiom.

`ifd c n` packs mathlib's `ONote.fundamentalSequence c` at index `n` into one code
`⟪kind, value⟫`:

| `kind` | meaning              | `value`                    |
| ------ | -------------------- | -------------------------- |
| `0`    | `c = 0`              | `0`                        |
| `1`    | `c` is a successor   | the predecessor of `c`     |
| `2`    | `c` is a limit       | `c[n]`                     |

Both recursive calls (into the tail `ocTail c` and into the exponent `ocExp c`) are at *smaller
codes*, so one table indexed by `c` with `n` as a parameter suffices.
-/

open scoped FFL.FirstOrder.Bounding

set_option autoImplicit false

namespace GoodsteinWu.InternalFund

open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
  OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The table step -/

/-- Table step of `ifd` at code `c` (parameter `n`, table `s` of `ifd · n` below `c`).

Mirrors `ONote.fundamentalSequence` clause by clause; `i.succPNat` there is `n + 1` here. -/
noncomputable def ifdNext (n c s : V) : V :=
  if c = 0 then ⟪0, 0⟫
  else
    let e := ocExp c
    let k := ocCoeff c
    let r := ocTail c
    if r ≠ 0 then ⟪π₁ (znth s r), ocOadd e k (π₂ (znth s r))⟫
    else
      let u := znth s e
      if π₁ u = 0 then
        ⟪1, if k = 1 then 0 else ocOadd 0 (k - 1) 0⟫
      else if π₁ u = 1 then
        ⟪2, if k = 1 then ocOadd (π₂ u) (n + 1) 0
            else ocOadd e (k - 1) (ocOadd (π₂ u) (n + 1) 0)⟫
      else
        ⟪2, if k = 1 then ocOadd (π₂ u) 1 0
            else ocOadd e (k - 1) (ocOadd (π₂ u) 1 0)⟫

def _root_.FFL.FirstOrder.Arithmetic.ifdNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y n c s.
    (c = 0 ∧ !pairDef y 0 0)
  ∨ (c ≠ 0 ∧ ∃ e, !ocExpDef e c ∧ ∃ k, !ocCoeffDef k c ∧ ∃ r, !sndIdxDef r c ∧
      ( (r ≠ 0 ∧ ∃ t, !znthDef t s r ∧ ∃ tk, !pi₁Def tk t ∧ ∃ tv, !pi₂Def tv t ∧
            ∃ w, !ocOaddDef w e k tv ∧ !pairDef y tk w)
      ∨ (r = 0 ∧ ∃ u, !znthDef u s e ∧ ∃ uk, !pi₁Def uk u ∧ ∃ uv, !pi₂Def uv u ∧
          ∃ km, !subDef km k 1 ∧
          ( (uk = 0 ∧ ( (k = 1 ∧ !pairDef y 1 0)
                      ∨ (k ≠ 1 ∧ ∃ w, !ocOaddDef w 0 km 0 ∧ !pairDef y 1 w) ))
          ∨ (uk = 1 ∧ ∃ b, !ocOaddDef b uv (n + 1) 0 ∧
                      ( (k = 1 ∧ !pairDef y 2 b)
                      ∨ (k ≠ 1 ∧ ∃ w, !ocOaddDef w e km b ∧ !pairDef y 2 w) ))
          ∨ (uk ≠ 0 ∧ uk ≠ 1 ∧ ∃ b, !ocOaddDef b uv 1 0 ∧
                      ( (k = 1 ∧ !pairDef y 2 b)
                      ∨ (k ≠ 1 ∧ ∃ w, !ocOaddDef w e km b ∧ !pairDef y 2 w) )) )) ))”

instance ifdNext_defined : 𝚺₁-Function₃ (ifdNext : V → V → V → V) via ifdNextDef := .mk fun v ↦ by
  simp only [ifdNextDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [ifdNext, ocExp_defined.iff, ocCoeff_defined.iff, ocTail, sndIdx_defined.iff,
    znth_defined.iff, ocOadd_defined.iff, pair_defined.iff, pi₁_defined.iff, pi₂_defined.iff,
    sub_defined.iff]
  by_cases hc : v 2 = 0
  · simp [hc]
  · by_cases hr : sndIdx (v 2) = 0
    · by_cases h0 : π₁ (znth (v 3) (ocExp (v 2))) = 0
      · by_cases hk : ocCoeff (v 2) = 1 <;> simp [hc, hr, h0, hk]
      · by_cases h1 : π₁ (znth (v 3) (ocExp (v 2))) = 1 <;>
          by_cases hk : ocCoeff (v 2) = 1 <;> simp [hc, hr, h0, h1, hk]
    · simp [hc, hr]

instance ifdNext_definable : 𝚺₁-Function₃ (ifdNext : V → V → V → V) := ifdNext_defined.to_definable

/-! ### The table -/

def ifdTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. ∃ p, !pairDef p 0 0 ∧ !mkSeq₁Def y p”
  succ := .mkSigma “y ih n x. ∃ v, !ifdNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def ifdTable.construction : PR.Construction V ifdTable.blueprint where
  zero := fun _ ↦ !⟦(⟪0, 0⟫ : V)⟧
  succ := fun x n ih ↦ seqCons ih (ifdNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [ifdTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def, pair_defined.iff]
  succ_defined := .mk fun v ↦ by
    simp [ifdTable.blueprint, ifdNext_defined.iff, seqCons_defined.iff]

/-- **The `ifd` table**: `ifdTable n N = ⟨ifd 0 n, …, ifd N n⟩`. -/
noncomputable def ifdTable (n N : V) : V := ifdTable.construction.result ![n] N

@[simp] lemma ifdTable_zero (n : V) : ifdTable n 0 = !⟦(⟪0, 0⟫ : V)⟧ := by
  simp [ifdTable, ifdTable.construction]

@[simp] lemma ifdTable_succ (n N : V) :
    ifdTable n (N + 1) = seqCons (ifdTable n N) (ifdNext n (N + 1) (ifdTable n N)) := by
  simp [ifdTable, ifdTable.construction]

/-- **The internal fundamental-sequence datum** `⟪kind, value⟫` of the code `c` at index `n`. -/
noncomputable def ifd (c n : V) : V := znth (ifdTable n c) c

def _root_.FFL.FirstOrder.Arithmetic.ifdTableDef : 𝚺₁.Semisentence 3 :=
  ifdTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance ifdTable_defined : 𝚺₁-Function₂ (ifdTable : V → V → V) via ifdTableDef := .mk
  fun v ↦ by simp [ifdTable.construction.result_defined_iff, ifdTableDef]; rfl

instance ifdTable_definable : 𝚺₁-Function₂ (ifdTable : V → V → V) := ifdTable_defined.to_definable
instance ifdTable_definable' (Γ) (m : ℕ) :
    Γᴬ-[m + 1]-Function₂ (ifdTable : V → V → V) := ifdTable_definable.of_sigmaOne

def _root_.FFL.FirstOrder.Arithmetic.ifdDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c n. ∃ t, !ifdTableDef t n c ∧ !znthDef y t c”

instance ifd_defined : 𝚺₁-Function₂ (ifd : V → V → V) via ifdDef := .mk fun v ↦ by
  simp only [ifdDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [ifd, ifdTable_defined.iff, znth_defined.iff]

instance ifd_definable : 𝚺₁-Function₂ (ifd : V → V → V) := ifd_defined.to_definable
instance ifd_definable' (Γ) (m : ℕ) :
    Γᴬ-[m + 1]-Function₂ (ifd : V → V → V) := ifd_definable.of_sigmaOne

/-- The kind tag of `c`: `0` zero, `1` successor, `2` limit. -/
noncomputable def ifdKind (c : V) : V := π₁ (ifd c 0)

/-- The predecessor (kind `1`) or `n`-th fundamental-sequence member (kind `2`) of `c`. -/
noncomputable def ifdVal (c n : V) : V := π₂ (ifd c n)

/-! ### Structural correctness -/

private lemma def_ifdTable {k} (n : V) (i : Fin k) :
    𝚺ᴬ-[1].DefinableFunction (fun v : Fin k → V ↦ ifdTable n (v i)) :=
  DefinableFunction₂.comp (F := ifdTable) (DefinableFunction.const n) (DefinableFunction.var i)

private lemma def_ifd {k} (n : V) (i : Fin k) :
    𝚺ᴬ-[1].DefinableFunction (fun v : Fin k → V ↦ ifd (v i) n) :=
  DefinableFunction₂.comp (F := ifd) (DefinableFunction.var i) (DefinableFunction.const n)

@[simp] lemma ifdTable_seq (n N : V) : Seq (ifdTable n N) := by
  induction N using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_ifdTable n 0)
  case zero => simp
  case succ N ih => rw [ifdTable_succ]; exact ih.seqCons _

@[simp] lemma ifdTable_lh (n N : V) : lh (ifdTable n N) = N + 1 := by
  induction N using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_ifdTable n 0)) (by definability)
  case zero => simp
  case succ N ih => rw [ifdTable_succ, Seq.lh_seqCons _ (ifdTable_seq n N), ih]

lemma znth_ifdTable_succ {n N k : V} (hk : k < N + 1) :
    znth (ifdTable n (N + 1)) k = znth (ifdTable n N) k := by
  rw [ifdTable_succ]
  exact znth_seqCons_of_lt (ifdTable_seq n N) _ (by rw [ifdTable_lh]; exact hk)

lemma znth_ifdTable_eq_ifd (n : V) : ∀ N : V, ∀ k ≤ N, znth (ifdTable n N) k = ifd k n := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.arithmetic_ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_ifdTable n 1) (DefinableFunction.var 0))
      (def_ifd n 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_ifdTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma ifd_zero (n : V) : ifd 0 n = ⟪0, 0⟫ := by
  simp only [ifd, ifdTable_zero]
  exact (singleton_seq _).znth_eq_of_mem ((mem_singleton_seq_iff _ _).mpr rfl)

/-- **The internal fundamental-sequence recursion.** -/
lemma ifd_ocOadd (e k r n : V) :
    ifd (ocOadd e k r) n =
      (if r ≠ 0 then ⟪π₁ (ifd r n), ocOadd e k (π₂ (ifd r n))⟫
       else
        if π₁ (ifd e n) = 0 then ⟪1, if k = 1 then 0 else ocOadd 0 (k - 1) 0⟫
        else if π₁ (ifd e n) = 1 then
          ⟪2, if k = 1 then ocOadd (π₂ (ifd e n)) (n + 1) 0
              else ocOadd e (k - 1) (ocOadd (π₂ (ifd e n)) (n + 1) 0)⟫
        else
          ⟪2, if k = 1 then ocOadd (π₂ (ifd e n)) 1 0
              else ocOadd e (k - 1) (ocOadd (π₂ (ifd e n)) 1 0)⟫) := by
  set c := ocOadd e k r with hc
  have hpos : 0 < c := ocOadd_pos e k r
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (ifdTable n c) c = ifdNext n c (ifdTable n M) := by
    rw [hM, ifdTable_succ]
    have := znth_seqCons_self (ifdTable_seq n M) (ifdNext n (M + 1) (ifdTable n M))
    rwa [ifdTable_lh] at this
  have htail : ocTail c ≤ M := by
    have h := ocTail_lt e k r; rw [← hc] at h; exact le_iff_lt_succ.mpr (hM ▸ h)
  have hexp : ocExp c ≤ M := by
    have h := ocExp_lt e k r; rw [← hc] at h; exact le_iff_lt_succ.mpr (hM ▸ h)
  rw [ifd, key, ifdNext, if_neg hpos.ne']
  simp only [hc, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd] at htail hexp ⊢
  rw [znth_ifdTable_eq_ifd n M r htail, znth_ifdTable_eq_ifd n M e hexp]

/-! ### The order laws

The fast-growing recursion descends along `≺`, and that is what makes progressiveness of
"`f_c` is total" a *one-step* argument.  The two facts below are what carries it.
-/

private lemma exp_lt_of_le {e k r w : V} (h : ocOadd e k r ≤ w) : e < w :=
  lt_of_lt_of_le (by have h' := ocExp_lt e k r; rwa [ocExp_ocOadd] at h') h

private lemma tail_lt_of_le {e k r w : V} (h : ocOadd e k r ≤ w) : r < w :=
  lt_of_lt_of_le (by have h' := ocTail_lt e k r; rwa [ocTail_ocOadd] at h') h

private lemma sub_one_lt {k : V} (hk : k ≠ 0) : k - 1 < k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 :=
    ⟨k - 1, (sub_add_self_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hk))).symm⟩
  simp

/-- **Only the zero code has kind `0`.** -/
lemma ifd_kind_ne_zero (n : V) : ∀ w : V, ∀ c ≤ w, c ≠ 0 → π₁ (ifd c n) ≠ 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro c hcw hc
    obtain ⟨e, k, r, rfl⟩ : ∃ e k r, c = ocOadd e k r :=
      ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
    rw [ifd_ocOadd]
    by_cases hr : r = 0
    · subst hr
      by_cases h0 : π₁ (ifd e n) = 0 <;> by_cases h1 : π₁ (ifd e n) = 1 <;>
        simp [h0, h1]
    · rw [if_pos hr, pi₁_pair]
      exact ih r (tail_lt_of_le hcw) r le_rfl hr

/-- **The kind tag is one of `0`, `1`, `2`.** -/
lemma ifd_kind_cases (n : V) : ∀ w : V, ∀ c ≤ w,
    π₁ (ifd c n) = 0 ∨ π₁ (ifd c n) = 1 ∨ π₁ (ifd c n) = 2 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro c hcw
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    obtain ⟨e, k, r, rfl⟩ : ∃ e k r, c = ocOadd e k r :=
      ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
    rw [ifd_ocOadd]
    by_cases hr : r = 0
    · subst hr
      by_cases h0 : π₁ (ifd e n) = 0 <;> by_cases h1 : π₁ (ifd e n) = 1 <;>
        simp [h0, h1]
    · rw [if_pos hr, pi₁_pair]
      exact ih r (tail_lt_of_le hcw) r le_rfl

/-- **The kind tag does not depend on the index.**  `ifd c n` is `⟪kind, value⟫` and the kind
is determined by `c` alone; only the value of a *limit* code depends on `n`. -/
lemma ifd_kind_indep (m n : V) : ∀ w : V, ∀ c ≤ w, π₁ (ifd c m) = π₁ (ifd c n) := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro c hcw
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    obtain ⟨e, k, r, rfl⟩ : ∃ e k r, c = ocOadd e k r :=
      ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
    rw [ifd_ocOadd, ifd_ocOadd]
    by_cases hr : r = 0
    · subst hr
      have he : π₁ (ifd e m) = π₁ (ifd e n) := ih e (exp_lt_of_le hcw) e le_rfl
      simp only [ne_eq, not_true_eq_false, if_false, he]
      by_cases h0 : π₁ (ifd e n) = 0 <;> by_cases h1 : π₁ (ifd e n) = 1 <;>
        simp [h0, h1]
    · have hrr : π₁ (ifd r m) = π₁ (ifd r n) := ih r (tail_lt_of_le hcw) r le_rfl
      rw [if_pos hr, if_pos hr, pi₁_pair, pi₁_pair, hrr]

lemma ifd_kind_eq_zero_of {c n : V} (h : π₁ (ifd c n) = 0) (w : V) (hcw : c ≤ w) : c = 0 := by
  by_contra hc
  exact ifd_kind_ne_zero n w c hcw hc h

/-- **The fundamental-sequence value of a nonzero normal code precedes it.**

This is the internal descent fact: `ifdVal c n ≺ c`, uniformly in `n`, and it is what turns
the successor and limit cases of progressiveness into single steps. -/
theorem icmp_ifdVal_lt (n : V) : ∀ w : V, ∀ c ≤ w, isNF c → c ≠ 0 →
    icmp (π₂ (ifd c n)) c = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro c hcw hnf hc
    obtain ⟨e, k, r, rfl⟩ : ∃ e k r, c = ocOadd e k r :=
      ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
    obtain ⟨hk0, hnfe, hnfr, -⟩ := (isNF_ocOadd e k r).mp hnf
    have helt : e < w := exp_lt_of_le hcw
    have hrlt : r < w := tail_lt_of_le hcw
    rw [ifd_ocOadd]
    by_cases hr : r = 0
    · subst hr
      simp only [ne_eq, not_true_eq_false, if_false]
      by_cases h0 : π₁ (ifd e n) = 0
      · have he0 : e = 0 := ifd_kind_eq_zero_of h0 e le_rfl
        subst he0
        rw [if_pos h0]
        by_cases hk1 : k = 1
        · simp only [pi₂_pair, hk1, if_true]
          exact icmp_zero_ocOadd 0 1 0
        · simp only [if_neg hk1, pi₂_pair]
          rw [icmp_ocOadd, icmp_self 0 0 le_rfl]
          have : cmpV (k - 1) k = 0 := by simp [cmpV, sub_one_lt hk0]
          rw [this]
          simp [thenV]
      · have hene : e ≠ 0 := by
          rintro rfl; exact h0 (by simp)
        have ihe : icmp (π₂ (ifd e n)) e = 0 := ih e helt e le_rfl hnfe hene
        by_cases h1 : π₁ (ifd e n) = 1
        · rw [if_neg h0, if_pos h1]
          by_cases hk1 : k = 1
          · simp only [pi₂_pair, hk1, if_true]
            rw [icmp_ocOadd, ihe]
            simp [thenV]
          · simp only [if_neg hk1, pi₂_pair]
            rw [icmp_ocOadd, icmp_self e e le_rfl]
            have : cmpV (k - 1) k = 0 := by simp [cmpV, sub_one_lt hk0]
            rw [this]
            simp [thenV]
        · rw [if_neg h0, if_neg h1]
          by_cases hk1 : k = 1
          · simp only [pi₂_pair, hk1, if_true]
            rw [icmp_ocOadd, ihe]
            simp [thenV]
          · simp only [if_neg hk1, pi₂_pair]
            rw [icmp_ocOadd, icmp_self e e le_rfl]
            have : cmpV (k - 1) k = 0 := by simp [cmpV, sub_one_lt hk0]
            rw [this]
            simp [thenV]
    · rw [if_pos hr, pi₂_pair]
      have ihr : icmp (π₂ (ifd r n)) r = 0 := ih r hrlt r le_rfl hnfr hr
      rw [icmp_ocOadd, icmp_self e e le_rfl, cmpV_self, ihr]
      simp [thenV]

private lemma sub_one_ne_zero {k : V} (hk0 : k ≠ 0) (hk1 : k ≠ 1) : k - 1 ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 :=
    ⟨k - 1, (sub_add_self_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hk0))).symm⟩
  intro h
  rw [hj] at h hk1
  simp at h
  exact hk1 (by rw [h]; simp)

/-- **Normal forms are closed under the fundamental sequence**, together with the invariant that
makes the induction go through: the leading exponent never increases. -/
theorem isNF_ifdVal (n : V) : ∀ w : V, ∀ c ≤ w, isNF c →
    isNF (π₂ (ifd c n)) ∧
      (π₂ (ifd c n) = 0 ∨ icmp (ocExp (π₂ (ifd c n))) (ocExp c) ≠ 2) := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro c hcw hnf
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    obtain ⟨e, k, r, rfl⟩ : ∃ e k r, c = ocOadd e k r :=
      ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
    obtain ⟨hk0, hnfe, hnfr, htc⟩ := (isNF_ocOadd e k r).mp hnf
    have helt : e < w := exp_lt_of_le hcw
    have hrlt : r < w := tail_lt_of_le hcw
    rw [ifd_ocOadd]
    by_cases hr : r = 0
    · subst hr
      simp only [ne_eq, not_true_eq_false, if_false]
      by_cases h0 : π₁ (ifd e n) = 0
      · have he0 : e = 0 := ifd_kind_eq_zero_of h0 e le_rfl
        subst he0
        rw [if_pos h0]
        by_cases hk1 : k = 1
        · simp [hk1]
        · simp only [if_neg hk1, pi₂_pair]
          refine ⟨(isNF_ocOadd 0 (k - 1) 0).mpr ⟨sub_one_ne_zero hk0 hk1, isNF_zero,
            isNF_zero, Or.inl rfl⟩, Or.inr ?_⟩
          simp only [ocExp_ocOadd]
          rw [icmp_self (V := V) 0 0 le_rfl]
          exact one_lt_two.ne
      · have hene : e ≠ 0 := by rintro rfl; exact h0 (by simp)
        obtain ⟨hnfve, -⟩ := ih e helt e le_rfl hnfe
        have hvelt : icmp (π₂ (ifd e n)) e = 0 := icmp_ifdVal_lt n e e le_rfl hnfe hene
        have hinner : ∀ j : V, j ≠ 0 →
            isNF (ocOadd (π₂ (ifd e n)) j 0) := fun j hj =>
          (isNF_ocOadd _ _ _).mpr ⟨hj, hnfve, isNF_zero, Or.inl rfl⟩
        have houter : ∀ j : V, j ≠ 0 → k ≠ 1 →
            isNF (ocOadd e (k - 1) (ocOadd (π₂ (ifd e n)) j 0)) := fun j hj hk1 =>
          (isNF_ocOadd _ _ _).mpr ⟨sub_one_ne_zero hk0 hk1, hnfe, hinner j hj,
            Or.inr (by rw [ocExp_ocOadd]; exact hvelt)⟩
        by_cases h1 : π₁ (ifd e n) = 1
        · rw [if_neg h0, if_pos h1]
          by_cases hk1 : k = 1
          · simp only [pi₂_pair, hk1, if_true]
            exact ⟨hinner (n + 1) (by simp), Or.inr (by
              simp only [ocExp_ocOadd]; rw [hvelt]; exact (_root_.two_pos).ne)⟩
          · simp only [if_neg hk1, pi₂_pair]
            exact ⟨houter (n + 1) (by simp) hk1, Or.inr (by
              simp only [ocExp_ocOadd]; rw [icmp_self e e le_rfl]; exact one_lt_two.ne)⟩
        · rw [if_neg h0, if_neg h1]
          by_cases hk1 : k = 1
          · simp only [pi₂_pair, hk1, if_true]
            exact ⟨hinner 1 _root_.one_ne_zero, Or.inr (by
              simp only [ocExp_ocOadd]; rw [hvelt]; exact (_root_.two_pos).ne)⟩
          · simp only [if_neg hk1, pi₂_pair]
            exact ⟨houter 1 _root_.one_ne_zero hk1, Or.inr (by
              simp only [ocExp_ocOadd]; rw [icmp_self e e le_rfl]; exact one_lt_two.ne)⟩
    · rw [if_pos hr, pi₂_pair]
      obtain ⟨hnfvr, hexpr⟩ := ih r hrlt r le_rfl hnfr
      have hre : icmp (ocExp r) e = 0 := htc.resolve_left hr
      have htail : π₂ (ifd r n) = 0 ∨ icmp (ocExp (π₂ (ifd r n))) e = 0 := by
        rcases hexpr with h | h
        · exact Or.inl h
        · right
          rcases eq_or_ne (icmp (ocExp (π₂ (ifd r n))) (ocExp r)) 1 with h1 | h1
          · have := icmp_eq_imp_eq (max (ocExp (π₂ (ifd r n))) (ocExp r))
              _ (le_max_left _ _) _ (le_max_right _ _) h1
            rw [this]; exact hre
          · have h0 : icmp (ocExp (π₂ (ifd r n))) (ocExp r) = 0 :=
              icmp_eq_zero_of_ne h1 h
            exact icmp_trans (max (ocExp (π₂ (ifd r n))) (max (ocExp r) e))
              _ (le_max_left _ _) _ (le_trans (le_max_left _ _) (le_max_right _ _))
              _ (le_trans (le_max_right _ _) (le_max_right _ _)) h0 hre
      refine ⟨(isNF_ocOadd _ _ _).mpr ⟨hk0, hnfe, hnfvr, htail⟩, Or.inr ?_⟩
      simp only [ocExp_ocOadd]
      rw [icmp_self e e le_rfl]
      exact one_lt_two.ne

end GoodsteinWu.InternalFund
