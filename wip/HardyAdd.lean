/-
# Hardy additive composition law (development scratch)

Goal: the general non-absorbing Hardy additivity `H_{γ+δ} = H_γ ∘ H_δ`, generalizing the
already-banked `hardy_oadd_tail` (single leading term) to a full left summand `γ`.

This is the load-bearing infra (B) for the §19.6 control-ordinal operator calculus: the
cut-elim control collapse `hardy e (hardy α x) = hardy (e + α) x` is the instance with `α`
below `e`'s least term.
-/
import GoodsteinPA.Hardy

namespace GoodsteinPA.FastGrowing

open ONote Ordinal

/-- The least (trailing) exponent of a notation's Cantor normal form (`0` for `0`). -/
def lastExp : ONote → ONote
  | 0 => 0
  | oadd e _ a => match a with
    | 0 => e
    | oadd _ _ _ => lastExp a

@[simp] theorem lastExp_zero : lastExp 0 = 0 := rfl
@[simp] theorem lastExp_oadd_zero (e n) : lastExp (oadd e n 0) = e := rfl

theorem lastExp_oadd_ne {e : ONote} {n : ℕ+} {a : ONote} (h : a ≠ 0) :
    lastExp (oadd e n a) = lastExp a := by
  cases a with
  | zero => exact absurd rfl h
  | oadd e' n' a' => rfl

/-- `addAux` concatenates (no merge/absorb) when the right operand's leading exponent is
strictly below `e`. -/
theorem addAux_concat {e : ONote} (he : e.NF) {n : ℕ+} {o : ONote} (ho : o.NF)
    (h : o = 0 ∨ ∀ e' n' a', o = oadd e' n' a' → e'.repr < e.repr) :
    addAux e n o = oadd e n o := by
  match o, ho, h with
  | 0, _, _ => rfl
  | oadd e' n' a', ho', h' =>
    have hlt : e'.repr < e.repr := by
      rcases h' with h0 | hf
      · exact absurd h0 (by simp)
      · exact hf e' n' a' rfl
    have hee' : ONote.cmp e e' = Ordering.gt :=
      (@ONote.cmp_compares e e' he ho'.fst).eq_gt.2 hlt
    simp only [addAux, hee']

/-- The least exponent of a nonzero notation lies below any bound it is `NFBelow`. -/
theorem lastExp_repr_lt : ∀ {o : ONote} {b : Ordinal}, NFBelow o b → o ≠ 0 →
    (lastExp o).repr < b := by
  intro o
  induction o with
  | zero => intro b _ h; exact absurd rfl h
  | oadd e n a _ iha =>
    intro b hb _
    rcases eq_or_ne a 0 with ha | ha
    · subst ha; rw [lastExp_oadd_zero]; exact hb.lt
    · rw [lastExp_oadd_ne ha]
      exact lt_trans (iha hb.snd ha) hb.lt

/-- Convert an `NFBelow` fact into the leading-exponent bound `addAux_concat` consumes. -/
theorem nfBelow_concat {o : ONote} {b : Ordinal} (h : NFBelow o b) :
    o = 0 ∨ ∀ e' n' a', o = oadd e' n' a' → e'.repr < b := by
  cases o with
  | zero => left; rfl
  | oadd e' n' a' => right; intro e'' n'' a'' heq; cases heq; exact h.lt

/-- **The general non-absorbing Hardy additive composition law.** For normal-form `γ`, `δ`
with `δ` lying strictly below `γ`'s least exponent (so `γ + δ` is genuine Cantor-normal-form
concatenation, no coefficient merge / absorption), the Hardy hierarchy composes:
`H_{γ+δ}(x) = H_γ(H_δ(x))`. Generalizes `hardy_oadd_tail` (single leading term) by induction
on `γ`. -/
theorem hardy_add_comp : ∀ (γ : ONote), γ.NF → ∀ (δ : ONote), δ.NF →
    (δ = 0 ∨ δ.repr < ω ^ (lastExp γ).repr) → ∀ x,
    hardy (γ + δ) x = hardy γ (hardy δ x) := by
  intro γ
  induction γ with
  | zero =>
    intro _ δ _ _ x
    show hardy ((0 : ONote) + δ) x = hardy (0 : ONote) (hardy δ x)
    rw [ONote.zero_add, hardy_zero]; rfl
  | oadd e n a _ iha =>
    intro hγ δ hδ hcond x
    haveI := hγ
    -- δ = 0 is trivial (γ + 0 = γ, hardy 0 = id)
    rcases eq_or_ne δ 0 with hδ0 | hδ0
    · subst hδ0
      have hadd : oadd e n a + 0 = oadd e n a :=
        repr_inj.mp (by rw [repr_add, repr_zero, add_zero])
      rw [hadd, hardy_zero]; rfl
    -- δ ≠ 0: genuine concatenation
    have he : e.NF := hγ.fst
    have hba : NFBelow a e.repr := hγ.snd'
    have ha : a.NF := ⟨⟨e.repr, hba⟩⟩
    -- δ lies below e: δ.repr < ω ^ e.repr
    have hle : (lastExp (oadd e n a)).repr ≤ e.repr := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst ha0; rw [lastExp_oadd_zero]
      · rw [lastExp_oadd_ne ha0]; exact le_of_lt (lastExp_repr_lt hba ha0)
    have hδlt_e : δ.repr < ω ^ e.repr := by
      rcases hcond with h0 | hlt
      · exact absurd h0 hδ0
      · exact lt_of_lt_of_le hlt (opow_le_opow_right omega0_pos hle)
    have hbδ : NFBelow δ e.repr := NF.below_of_lt' hδlt_e hδ
    -- a + δ stays below e, so the top-level addAux is a clean concatenation
    have hbaδ : NFBelow (a + δ) e.repr := add_nfBelow hba hbδ
    have hcc : addAux e n (a + δ) = oadd e n (a + δ) :=
      addAux_concat he (⟨⟨_, hbaδ⟩⟩) (nfBelow_concat hbaδ)
    rw [oadd_add, hcc, hardy_oadd_tail e n (a + δ) x]
    -- recurse into the tail
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0; rw [ONote.zero_add]
    · have ihcond : δ = 0 ∨ δ.repr < ω ^ (lastExp a).repr := by
        right
        rcases hcond with h0 | hlt
        · exact absurd h0 hδ0
        · rwa [lastExp_oadd_ne ha0] at hlt
      rw [iha ha δ hδ ihcond x, hardy_oadd_tail e n a (hardy δ x)]

end GoodsteinPA.FastGrowing

-- axiom check
#print axioms GoodsteinPA.FastGrowing.hardy_add_comp
