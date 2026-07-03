import GoodsteinPA.WainerLadder

/-!
# SERIES-2 Stage B probe — (Ax2) adequacy: `Zef2T` = `Zef2` + the E–W true-literal rule

**Question (`REBUILD-Z-SERIES-2-ORDER-2026-07-03.md` Stage B).**  E–W Def 23 has **(Ax2)**:
a sequent containing a TRUE closed PA-literal closes.  `Zekd` has `trueRel`/`trueNrel`; `Zef2`
has only the complementary-pair leaf `axL`.  Rung E (the embedding) and the lane-D residue both
flagged this as the shared calculus-faithfulness decision.  This probe clones `Zef2` as
**`Zef2T`** (= `Zef2` + `trueRel` + `trueNrel`, gates threaded) and kernel-answers the three
Stage-B questions:

**(i) `toZef` does NOT extend — (Ax2) is a STRICT extension at rank 0** (kernel-proven).
`zef2T_derives_true_literal`: `Zef2T` derives the singleton `{0 = 0}` at rank 0 (one `trueRel`
leaf).  `zef_rank0_literal_pair`: every rank-0 `Zef` derivation of an all-literal sequent
carries a complementary literal PAIR in the sequent (induction: `allω`/`exI` conclusions are
not literals, `cut` is impossible at rank 0) — so `Zef` canNOT derive `{0 = 0}`
(`zef_not_derives_true_literal_singleton`: a one-element sequent holds no pair).
CONSEQUENCE: the lap-8 read-off route "discharge через `toZef`" is NOT available for `Zef2T`;
read-offs must be re-proven natively (see (iii) — the falsity-invariant ones extend trivially).

**(ii) The pins-1–2 reduction extends MECHANICALLY on the new leaves** (kernel-proven case).
`reduction_trueLit_case` proves exactly the new constructor case that
`cutReduceAllAuxRunning_Zf2`'s induction would acquire: a `trueRel` leaf of `Δ` rebuilds at the
fresh root `α + γ` deriving `Δ.erase (∃⁰ ∼φ) ∪ Γ` — the literal survives the erase
(`ne_of_ne_complexity`) and the gate is the SAME `ewN_add_le_comp` arithmetic as the `axL`
case.  No new mathematics; the (f.1)-class hypotheses are untouched.

**(iii) Falsity-invariant read-offs treat (Ax2) leaves VACUOUSLY** (kernel-proven case).
`readoffD_trueLit_vacuous`: under the lane-D invariant "every member is the goal `∃⁰ φ` or
standard-model FALSE", a `trueRel`/`trueNrel` leaf is CONTRADICTORY (its true literal is
neither) — so the `readoffD_aux` induction extends to `Zef2T` with two vacuous cases.
⚠️ HONEST LIMIT (= lap-195's caution, now kernel-grounded): (Ax2) does NOT dissolve the
`allω` trapped-contraction residue per-derivation — the trap case of the read-off induction is
UNCHANGED in `Zef2T`.  What (Ax2) changes is derivation EXISTENCE: an embedding may close true
Δ₀ leaves by `trueRel` WITHOUT forcing the goal existential into the shared `allω` context
(E–W Lemma 31's separation).  That is a rung-E/embedding property, not a read-off property —
exactly why the ruling should treat (Ax2) as the RUNG-E faithfulness question while lane D
takes the R-4′ restatement (Stage C's combined verdict).

wip-only ruling input (SERIES-2 order Stage B / ladder P2).  `src` untouched; no `native_decide`.
-/

namespace GoodsteinPA.Ax2AdequacyProbe

open LO LO.FirstOrder ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## The clone: `Zef2T` = `Zef2` + (Ax2) -/

/-- **`Zef2T`** — `Zef2` (verbatim constructors, gates included) + E–W's (Ax2) as the two
true-literal leaves `trueRel`/`trueNrel` (the `Zekd` shape, with the `ewN` gate threaded). -/
inductive Zef2T : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Seq → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : ewN α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef2T α e H f c Γ
  | trueRel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : ewN α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hmem : Semiformula.rel r v ∈ Γ) : Zef2T α e H f c Γ
  | trueNrel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : ewN α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hmem : Semiformula.nrel r v ∈ Γ) : Zef2T α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : ewN α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2T α e H f c Δ) :
      Zef2T α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : ewN α ≤ f 0)
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef2T β e H f c Δ) : Zef2T α e H f c Γ
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : ewN α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef2T (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef2T α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : ewN α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef2T β e H f c (insert (φ/[nm n]) Γ)) : Zef2T α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : ewN α ≤ f 0)
      (φ : Form) (hcompl : φ.complexity < c) (hcutRead : φ.complexity ≤ f 0)
      (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef2T βφ e H f c (insert φ Γ)) (d₂ : Zef2T βψ e H f c (insert (∼φ) Γ)) :
      Zef2T α e H f c Γ

namespace Zef2T

/-- Gate projection (as for `Zef2`). -/
theorem gate {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (dd : Zef2T α e H f c Γ) : ewN α ≤ f 0 := by
  cases dd <;> assumption

/-- `Zef2 ⊆ Zef2T` — the clone is conservative-over-nothing in this direction (every `Zef2`
derivation is a `Zef2T` derivation verbatim). -/
theorem ofZef2 : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → Zef2T α e H f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => exact Zef2T.axL hαN r v hp hn
  | wk hαN hsub _ ih => exact Zef2T.wk hαN hsub ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih => exact Zef2T.weak hαN hβ hβNF hαNF hβH hsub ih
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      exact Zef2T.allω hαN φ β hβ hβNF hαNF hβH (fun n => ih n)
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      exact Zef2T.exI hαN φ n hβ hβNF hαNF hβH hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zef2T.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ih₁ ih₂

end Zef2T

/-! ## (i) Strictness: `Zef2T` derives `{0 = 0}` at rank 0; `Zef` cannot -/

/-- The concrete true literal `0 = 0`. -/
noncomputable def eqLit : Form :=
  Semiformula.rel (Language.Eq.eq : (ℒₒᵣ).Rel 2) ![nm 0, nm 0]

theorem eqLit_true : atomTrue eqLit := by
  simp [eqLit, atomTrue, nm]

/-- `Zef2T` derives the singleton `{0 = 0}` at rank 0 (one (Ax2) leaf; root ordinal `0`). -/
theorem zef2T_derives_true_literal (e : ONote) (H : ONote → Prop) :
    Zef2T 0 e H id 0 {eqLit} :=
  Zef2T.trueRel (by simp) _ _ eqLit_true (Finset.mem_singleton_self _)

/-- A literal (positive or negative). -/
def IsLit (ψ : Form) : Prop :=
  ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v,
    ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v

/-- **Rank-0 `Zef` derivations of all-literal sequents carry a complementary PAIR.**  The
kernel invariant behind strictness: at rank 0 the only leaf is `axL` (a pair), `wk`/`weak`
preserve all-literal downward, `allω`/`exI` conclusions contain a quantified member (not a
literal), and `cut` needs `complexity < 0`. -/
theorem zef_rank0_literal_pair :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef α e H f c Γ → c = 0 → (∀ ψ ∈ Γ, IsLit ψ) →
      ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v,
        Semiformula.rel r v ∈ Γ ∧ Semiformula.nrel r v ∈ Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL r v hp hn => intro _ _; exact ⟨_, r, v, hp, hn⟩
  | wk hsub _ ih =>
      intro hc hyp
      obtain ⟨ar, r, v, hp, hn⟩ := ih hc (fun ψ hψ => hyp ψ (hsub hψ))
      exact ⟨ar, r, v, hsub hp, hsub hn⟩
  | weak hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hyp
      obtain ⟨ar, r, v, hp, hn⟩ := ih hc (fun ψ hψ => hyp ψ (hsub hψ))
      exact ⟨ar, r, v, hsub hp, hsub hn⟩
  | allω φ β hβ hβNF hαNF hβH _ _ =>
      intro _ hyp
      obtain ⟨ar, r, v, h | h⟩ := hyp (∀⁰ φ) (Finset.mem_insert_self _ _)
      · exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
  | exI φ n hβ hβNF hαNF hβH hbound _ _ =>
      intro _ hyp
      obtain ⟨ar, r, v, h | h⟩ := hyp (∃⁰ φ) (Finset.mem_insert_self _ _)
      · exact absurd h (by simp [ExsQuantifier.exs])
      · exact absurd h (by simp [ExsQuantifier.exs])
  | cut φ hcompl _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      intro hc _; omega

/-- **`Zef` canNOT derive `{0 = 0}` at rank 0** — the one-element sequent has no complementary
pair (its sole member is a positive literal).  With `zef2T_derives_true_literal`, (Ax2) is a
STRICT extension at rank 0, so `toZef` does NOT extend to `Zef2T`. -/
theorem zef_not_derives_true_literal_singleton (α e : ONote) (H : ONote → Prop) (f : ℕ → ℕ) :
    ¬ Zef α e H f 0 {eqLit} := by
  intro D
  obtain ⟨ar, r, v, hp, hn⟩ := zef_rank0_literal_pair D rfl
    (fun ψ hψ => by
      rw [Finset.mem_singleton] at hψ
      exact ⟨2, Language.Eq.eq, ![nm 0, nm 0], Or.inl (by rw [hψ, eqLit])⟩)
  rw [Finset.mem_singleton] at hn
  simp [eqLit] at hn

/-! ## (ii) The reduction's new leaf case is mechanical -/

/-- **The `trueRel` case of `cutReduceAllAuxRunning_Zf2`'s induction, in isolation.**  Mirrors
the proven `axL` case verbatim: the true literal of `Δ` is not the erased existential
(`ne_of_ne_complexity`), so it survives into `Δ.erase (∃⁰ ∼φ) ∪ Γ` and one `trueRel` leaf at
the fresh root `α + γ` closes — gate by the SAME `ewN_add_le_comp` arithmetic.  (The `hg_base`
hypothesis is what `ewN_add_le_comp` consumes, exactly as in `axL`; nothing (f.1)-shaped is
touched by the new leaf.) -/
theorem reduction_trueLit_case {φ : SyntacticSemiformula ℒₒᵣ 1} {α γ e : ONote}
    {H : ONote → Prop} {f g : ℕ → ℕ} {Γ Δ : Seq} {ar : ℕ}
    (_hαNF : α.NF) (_hγNF : γ.NF)
    (hg_base : ∀ k, g 0 + k ≤ g k)
    (hg0 : ewN α ≤ g 0) (hγN : ewN γ ≤ f 0)
    (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
    (hmem : Semiformula.rel r v ∈ Δ) :
    Zef2T (α + γ) e H (g ∘ f) 0 (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
  Zef2T.trueRel (ewN_add_le_comp hg0 hγN hg_base) r v htrue
    (Finset.mem_union_left _
      (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))

/-! ## (iii) Falsity-invariant read-offs: the (Ax2) leaves are VACUOUS -/

/-- **The `trueRel` case of the lane-D `readoffD_aux` induction, in isolation** — vacuous:
under the falsity invariant "every member is `∃⁰ φ` or FALSE", a true literal in `Γ` is
contradictory (a literal is not the goal existential, and it is true). -/
theorem readoffD_trueLit_vacuous {φ : SyntacticSemiformula ℒₒᵣ 1} {Γ : Seq} {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
    (hmem : Semiformula.rel r v ∈ Γ)
    (hyp : ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ) :
    False := by
  rcases hyp _ hmem with h | h
  · exact absurd h (by simp [ExsQuantifier.exs])
  · exact h htrue

/-- Dual: the `trueNrel` case is vacuous the same way. -/
theorem readoffD_trueNlit_vacuous {φ : SyntacticSemiformula ℒₒᵣ 1} {Γ : Seq} {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
    (hmem : Semiformula.nrel r v ∈ Γ)
    (hyp : ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ) :
    False := by
  rcases hyp _ hmem with h | h
  · exact absurd h (by simp [ExsQuantifier.exs])
  · exact h htrue

end GoodsteinPA.Ax2AdequacyProbe
