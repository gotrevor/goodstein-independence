/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinWu.FastGrowingGraph

/-!
# Totality of the fast-growing hierarchy is progressive

`fgTotal c` says "`f_c` is total": `isNF c → ∀ n, ∃ y, fgGraph c n y`.  The main theorem here,
`fgTotal_progressive`, is that this predicate is progressive along Wu's coded ordering `≺`
(`isNF d ∧ isNF c ∧ icmp d c = 0`), inside every model of `𝗜𝚺₁`.

That is the hypothesis of `TIupto`, so feeding it to `gentzen_upper_bound` at `o + 1` gives
`f_o` total in `𝗣𝗔`.

The three cases follow the kind tag of `ifd c`:

* kind `0`: `c = 0`, one singleton witness `{⟪⟪0,n⟫,⟪n+1,0⟫⟫}`;
* kind `2` (limit): `c[n] ≺ c`, so one step off the inductive hypothesis;
* kind `1` (successor): the only case needing induction — a `𝚺₁` induction on `j ≤ n` building
  the iteration sequence `u` with `u₀ = n` and `u_{j+1} = f_{pred c}(u_j)`.
-/

open scoped FFL.FirstOrder.Bounding

set_option autoImplicit false

namespace GoodsteinWu.Progressive

open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
  OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote GoodsteinWu.InternalFund
  GoodsteinWu.FastGrowingGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- "`f_c` is total". -/
def fgTotal (c : V) : Prop := isNF c → ∀ n : V, ∃ y, fgGraph c n y

/-! ### Witness plumbing -/

lemma fgWit_insert {w e : V} (hw : fgWit w) (hj : fgJust (insert e w) e) :
    fgWit (insert e w) := by
  intro ent hent
  rcases mem_bitInsert_iff.mp hent with rfl | hent
  · exact hj
  · exact fgJust_mono (fun x hx => mem_bitInsert_iff.mpr (Or.inr hx)) (hw ent hent)

/-- The entry just inserted is itself a step of the enlarged witness. -/
lemma fgStepIn_self (w c n y u : V) :
    fgStepIn (insert ⟪⟪c, n⟫, ⟪y, u⟫⟫ w) c n y := by
  refine ⟨u, ?_, mem_bitInsert_iff.mpr (Or.inl rfl)⟩
  refine lt_of_le_of_lt (le_trans (le_pair_right y u) (le_pair_right ⟪c, n⟫ ⟪y, u⟫)) ?_
  exact lt_of_mem (mem_bitInsert_iff.mpr (Or.inl rfl))

lemma subset_insert_self (e w : V) : w ⊆ insert e w :=
  fun _ hx => mem_bitInsert_iff.mpr (Or.inr hx)

/-! ### The three cases -/

lemma fgTotal_zero : fgTotal (0 : V) := by
  intro _ n
  refine ⟨n + 1, ({⟪⟪(0 : V), n⟫, ⟪n + 1, 0⟫⟫} : V), ?_, ?_⟩
  · intro ent hent
    rcases mem_singleton_iff.mp hent with rfl
    simp [fgJust]
  · exact ⟨0, pos_of_nonempty (mem_singleton_iff.mpr rfl), mem_singleton_iff.mpr rfl⟩

/-- `c ≠ 0` whenever `ifd c` has a nonzero kind tag. -/
lemma ne_zero_of_kind {c n : V} (h : π₁ (ifd c n) ≠ 0) : c ≠ 0 := by
  rintro rfl; exact h (by simp)

lemma fgTotal_limit {c : V} (hnf : isNF c) (n₀ : V) (hk : π₁ (ifd c n₀) = 2)
    (ih : ∀ d : V, isNF d → icmp d c = 0 → fgTotal d) :
    ∃ y : V, fgGraph c n₀ y := by
  have hc0 : c ≠ 0 := ne_zero_of_kind (n := n₀) (by rw [hk]; simp)
  have hlt : icmp (π₂ (ifd c n₀)) c = 0 := icmp_ifdVal_lt n₀ c c le_rfl hnf hc0
  have hnfd : isNF (π₂ (ifd c n₀)) := (isNF_ifdVal n₀ c c le_rfl hnf).1
  obtain ⟨y, w, hw, hstep⟩ := ih _ hnfd hlt hnfd n₀
  refine ⟨y, insert ⟪⟪c, n₀⟫, ⟪y, (0 : V)⟫⟫ w, ?_, fgStepIn_self _ _ _ _ _⟩
  refine fgWit_insert hw ?_
  simp only [fgJust, pi₁_pair, pi₂_pair]
  exact Or.inr (Or.inr ⟨hk, fgStepIn_mono (subset_insert_self _ _) hstep⟩)

/-- The `𝚺₁` induction of the successor case: an iteration sequence of length `j + 1`
starting at `n`, each step justified by a single witness set. -/
lemma fgIter {p : V} (hnfp : isNF p) (hp : fgTotal p) (n : V) : ∀ j : V,
    ∃ w u : V, fgWit w ∧ Seq u ∧ lh u = j + 1 ∧ znth u 0 = n ∧
      ∀ i < j, fgStepIn w p (znth u i) (znth u (i + 1)) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    refine ⟨∅, !⟦n⟧, ?_, by simp, ?_, ?_, by simp⟩
    · intro ent hent; simp at hent
    · simp
    · exact (singleton_seq n).znth_eq_of_mem ((mem_singleton_seq_iff _ _).mpr rfl)
  case succ j IH =>
    obtain ⟨w, u, hw, hu, hlh, h0, hsteps⟩ := IH
    obtain ⟨y, w₂, hw₂, hstep⟩ := hp hnfp (znth u j)
    have hlhc : lh (u ⁀' y) = j + 1 + 1 := by rw [Seq.lh_seqCons y hu, hlh]
    have hold : ∀ i : V, i < j + 1 → znth (u ⁀' y) i = znth u i := by
      intro i hi; exact znth_seqCons_of_lt hu y (by rw [hlh]; exact hi)
    have hnew : znth (u ⁀' y) (j + 1) = y := by
      have := znth_seqCons_self hu y; rwa [hlh] at this
    refine ⟨w ∪ w₂, u ⁀' y, fgWit_union hw hw₂, hu.seqCons y, hlhc, ?_, ?_⟩
    · rw [hold 0 (by simp)]; exact h0
    · intro i hi
      rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hi) with hij | rfl
      · have h1 : i < j + 1 := lt_trans hij (by simp)
        rw [hold i h1, hold (i + 1) (by simpa using hij)]
        exact fgStepIn_mono (union_succ_union_left w w₂) (hsteps i hij)
      · rw [hold i (by simp), hnew]
        exact fgStepIn_mono (union_succ_union_right w w₂) hstep

lemma fgTotal_succ {c : V} (hnf : isNF c) (hk : π₁ (ifd c 0) = 1)
    (ih : ∀ d : V, isNF d → icmp d c = 0 → fgTotal d) (n : V) :
    ∃ y : V, fgGraph c n y := by
  have hc0 : c ≠ 0 := ne_zero_of_kind (n := 0) (by rw [hk]; simp)
  have hlt : icmp (π₂ (ifd c 0)) c = 0 := icmp_ifdVal_lt 0 c c le_rfl hnf hc0
  have hnfp : isNF (π₂ (ifd c 0)) := (isNF_ifdVal 0 c c le_rfl hnf).1
  obtain ⟨w, u, hw, hu, hlh, h0, hsteps⟩ :=
    fgIter hnfp (ih _ hnfp hlt) n n
  refine ⟨znth u n, insert ⟪⟪c, n⟫, ⟪znth u n, u⟫⟫ w, ?_, fgStepIn_self _ _ _ _ _⟩
  refine fgWit_insert hw ?_
  simp only [fgJust, pi₁_pair, pi₂_pair]
  refine Or.inr (Or.inl ⟨hk, hu, hlh, h0, trivial, fun i hi => ?_⟩)
  exact fgStepIn_mono (subset_insert_self _ _) (hsteps i hi)

/-- **Totality of the fast-growing hierarchy is progressive along `≺`.** -/
theorem fgTotal_progressive (c : V)
    (ih : ∀ d : V, isNF d → isNF c → icmp d c = 0 → fgTotal d) : fgTotal c := by
  intro hnf n
  have ih' : ∀ d : V, isNF d → icmp d c = 0 → fgTotal d := fun d h1 h2 => ih d h1 hnf h2
  rcases eq_or_ne (π₁ (ifd c 0)) 0 with h0 | h0
  · have : c = 0 := ifd_kind_eq_zero_of h0 c le_rfl
    subst this; exact fgTotal_zero hnf n
  rcases eq_or_ne (π₁ (ifd c 0)) 1 with h1 | h1
  · exact fgTotal_succ hnf h1 ih' n
  · have hk : π₁ (ifd c n) = 2 := by
      rw [← ifd_kind_indep 0 n c c le_rfl]
      rcases ifd_kind_cases (0 : V) c c le_rfl with h | h | h
      · exact absurd h h0
      · exact absurd h h1
      · exact h
    exact fgTotal_limit hnf n hk ih'

end GoodsteinWu.Progressive
