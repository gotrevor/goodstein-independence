import GoodsteinPA.OperatorZef2

/-!
# Route-(c) value gate — the hereditary `Gated` predicate (lap 206, step (2))

Mandated by the DIRECTION lap-206 block, step (2), after the step-(1) gadget probe PASSED
(`wip/ReadoffValueGadgetProbe.lean`).  Design (PENDING_WORK lap-206 top): instead of threading a
SYNTACTIC subformula-closure through the read-off's derivation induction, the invariant tracks a
SEMANTIC hereditary predicate `Gated P V ψ` —

* at a false `∀⁰ χ` member the trap descent needs a **value-gated false branch**
  `∃ k ≤ P V, ¬ atomTrue (χ/[nm k])` (E–W's rule-side branch gate, reconstructed semantically);
* every quantifier instance stays `Gated` at the bumped budget `max V k` (so the invariant
  survives `allω`/vacuous-`exI` insertions), and connective constituents stay `Gated` at the
  same budget (`andI`/`orI` insertions).

The syntactic work (φ's `Hierarchy 𝚺` ball-shapes + the subterm value bound `P_φ`) then
discharges `Gated` ONCE, at the pipeline root, for the concrete `goodsteinBodyE` instances —
NOT inside the derivation induction.  This file defines `Gated` and banks its two derivation-side
laws: budget monotonicity (`Gated_mono`) and the accessor lemmas the induction's cases consume.

Wip-only ruling input; `Gated` is internal proof machinery (no ratified-statement contact).
-/

namespace GoodsteinPA.ReadoffValueGate

open LO LO.FirstOrder
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-- **The hereditary value gate.**  `Gated P V ψ` says: along any refutation descent through
`ψ`'s quantifier/connective structure, false `∀⁰`-heads admit a false branch of index `≤ P` of
the running budget, where the budget starts at `V` and absorbs every instantiation index.
Atoms/⊤/⊥ are vacuously gated (the read-off's leaf cases never descend). -/
def Gated (P : ℕ → ℕ) : ℕ → Form → Prop
  | _, Semiformula.rel _ _ => True
  | _, Semiformula.nrel _ _ => True
  | _, Semiformula.verum => True
  | _, Semiformula.falsum => True
  | V, Semiformula.and χ₁ χ₂ => Gated P V χ₁ ∧ Gated P V χ₂
  | V, Semiformula.or χ₁ χ₂ => Gated P V χ₁ ∧ Gated P V χ₂
  | V, Semiformula.all χ =>
      (¬ atomTrue (Semiformula.all χ) → ∃ k, k ≤ P V ∧ ¬ atomTrue (χ/[nm k])) ∧
      ∀ k, Gated P (max V k) (χ/[nm k])
  | V, Semiformula.exs χ => ∀ n, Gated P (max V n) (χ/[nm n])
termination_by _ φ => φ.complexity
decreasing_by
  all_goals simp [Semiformula.complexity_rew]

/-! ## Accessors — the shapes the read-off induction's cases consume -/

theorem Gated_and_iff {P : ℕ → ℕ} {V : ℕ} {χ₁ χ₂ : Form} :
    Gated P V (χ₁ ⋏ χ₂) ↔ Gated P V χ₁ ∧ Gated P V χ₂ := by
  rw [show (χ₁ ⋏ χ₂) = Semiformula.and χ₁ χ₂ from rfl, Gated]

theorem Gated_or_iff {P : ℕ → ℕ} {V : ℕ} {χ₁ χ₂ : Form} :
    Gated P V (χ₁ ⋎ χ₂) ↔ Gated P V χ₁ ∧ Gated P V χ₂ := by
  rw [show (χ₁ ⋎ χ₂) = Semiformula.or χ₁ χ₂ from rfl, Gated]

theorem Gated_all_iff {P : ℕ → ℕ} {V : ℕ} {χ : SyntacticSemiformula ℒₒᵣ 1} :
    Gated P V (∀⁰ χ) ↔
      ((¬ atomTrue (∀⁰ χ) → ∃ k, k ≤ P V ∧ ¬ atomTrue (χ/[nm k])) ∧
        ∀ k, Gated P (max V k) (χ/[nm k])) := by
  rw [show (∀⁰ χ) = Semiformula.all χ from rfl, Gated]

theorem Gated_exs_iff {P : ℕ → ℕ} {V : ℕ} {χ : SyntacticSemiformula ℒₒᵣ 1} :
    Gated P V (∃⁰ χ) ↔ ∀ n, Gated P (max V n) (χ/[nm n]) := by
  rw [show (∃⁰ χ) = Semiformula.exs χ from rfl, Gated]

/-! ## Budget monotonicity — old members stay gated when the budget bumps -/

theorem Gated_mono {P : ℕ → ℕ} (hP : Monotone P) :
    ∀ (φ : Form) (V V' : ℕ), V ≤ V' → Gated P V φ → Gated P V' φ
  | Semiformula.rel _ _, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.nrel _ _, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.verum, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.falsum, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.and χ₁ χ₂, V, V', h, hg => by
      rw [Gated] at hg ⊢
      exact ⟨Gated_mono hP χ₁ V V' h hg.1, Gated_mono hP χ₂ V V' h hg.2⟩
  | Semiformula.or χ₁ χ₂, V, V', h, hg => by
      rw [Gated] at hg ⊢
      exact ⟨Gated_mono hP χ₁ V V' h hg.1, Gated_mono hP χ₂ V V' h hg.2⟩
  | Semiformula.all χ, V, V', h, hg => by
      rw [Gated] at hg ⊢
      refine ⟨fun hf => ?_, fun k => ?_⟩
      · obtain ⟨k, hk, hkf⟩ := hg.1 hf
        exact ⟨k, le_trans hk (hP h), hkf⟩
      · exact Gated_mono hP (χ/[nm k]) (max V k) (max V' k)
          (max_le_max h le_rfl) (hg.2 k)
  | Semiformula.exs χ, V, V', h, hg => by
      rw [Gated] at hg ⊢
      intro n
      exact Gated_mono hP (χ/[nm n]) (max V n) (max V' n)
        (max_le_max h le_rfl) (hg n)
termination_by φ _ _ _ _ => φ.complexity
decreasing_by
  all_goals simp [Semiformula.complexity_rew]

/-! ## The term-value frame `tvB` — standard-model values with all variables at `B`

The root discharge's `P_φ` is built from `tvB` over φ's guard terms.  `tvB t B` dominates the
value of every numeral instance of `t` whose numerals are `≤ B` (monotonicity + `val_rew`). -/

/-- Standard-model `ℒₒᵣ` term values are monotone in both environments (0/1/+/· are monotone). -/
theorem valm_mono : ∀ {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) {e e' : Fin m → ℕ} {ε ε' : ℕ → ℕ},
    (∀ i, e i ≤ e' i) → (∀ x, ε x ≤ ε' x) →
    Semiterm.valm ℕ e ε t ≤ Semiterm.valm ℕ e' ε' t := by
  intro m t
  induction t with
  | bvar x => intro e e' ε ε' he _; simpa using he x
  | fvar x => intro e e' ε ε' _ hε; simpa using hε x
  | func f v ih =>
      intro e e' ε ε' he hε
      cases f with
      | zero =>
          show Semiterm.valm ℕ e ε (Semiterm.func Language.Zero.zero v)
            ≤ Semiterm.valm ℕ e' ε' (Semiterm.func Language.Zero.zero v)
          simp
      | one =>
          show Semiterm.valm ℕ e ε (Semiterm.func Language.One.one v)
            ≤ Semiterm.valm ℕ e' ε' (Semiterm.func Language.One.one v)
          simp
      | add =>
          show Semiterm.valm ℕ e ε (Semiterm.func Language.Add.add v)
            ≤ Semiterm.valm ℕ e' ε' (Semiterm.func Language.Add.add v)
          simp only [Semiterm.val_func, Structure.add_eq_of_lang]
          have h0 := ih 0 he hε
          have h1 := ih 1 he hε
          exact Nat.add_le_add h0 h1
      | mul =>
          show Semiterm.valm ℕ e ε (Semiterm.func Language.Mul.mul v)
            ≤ Semiterm.valm ℕ e' ε' (Semiterm.func Language.Mul.mul v)
          simp only [Semiterm.val_func, Structure.mul_eq_of_lang]
          have h0 := ih 0 he hε
          have h1 := ih 1 he hε
          exact Nat.mul_le_mul h0 h1

/-- `tvB t B` — the value of `t` with every bounded variable at `B` and every free name at `0`. -/
noncomputable def tvB {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) (B : ℕ) : ℕ :=
  Semiterm.valm ℕ (fun _ => B) (fun _ => 0) t

theorem tvB_mono {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) : Monotone (tvB t) :=
  fun _ _ h => valm_mono t (fun _ => h) (fun _ => le_rfl)

/-- `bShift` does not change `tvB` (the constant environment absorbs the shift). -/
theorem tvB_bShift {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) (B : ℕ) :
    tvB (Rew.bShift t) B = tvB t B := by
  simp [tvB, Semiterm.val_bShift']

/-! ## The guard-value bound `gvb` — the root discharge's `P_φ` shape

`gvb ψ B` = the max standard-model value of any argument term of any atomic subformula of `ψ`,
with every bounded variable at `B` (names at `0`).  Ball guards `x < t` are atoms, so `gvb`
dominates every guard value; it is monotone in `B` and contracts under numeral substitution
(`gvb (χ/[nm k]) B ≤ gvb χ (max B k)`), which is exactly what the master induction threads. -/

noncomputable def gvb : ∀ {m : ℕ}, SyntacticSemiformula ℒₒᵣ m → ℕ → ℕ
  | _, Semiformula.rel _ v, B => Finset.univ.sup fun i => tvB (v i) B
  | _, Semiformula.nrel _ v, B => Finset.univ.sup fun i => tvB (v i) B
  | _, Semiformula.verum, _ => 0
  | _, Semiformula.falsum, _ => 0
  | _, Semiformula.and χ₁ χ₂, B => max (gvb χ₁ B) (gvb χ₂ B)
  | _, Semiformula.or χ₁ χ₂, B => max (gvb χ₁ B) (gvb χ₂ B)
  | _, Semiformula.all χ, B => gvb χ B
  | _, Semiformula.exs χ, B => gvb χ B

theorem gvb_mono : ∀ {m : ℕ} (ψ : SyntacticSemiformula ℒₒᵣ m), Monotone (gvb ψ) := by
  intro m ψ
  induction ψ with
  | rel r v => exact fun B B' h => Finset.sup_mono_fun fun i _ => tvB_mono (v i) h
  | nrel r v => exact fun B B' h => Finset.sup_mono_fun fun i _ => tvB_mono (v i) h
  | verum => exact fun _ _ _ => le_rfl
  | falsum => exact fun _ _ _ => le_rfl
  | and χ₁ χ₂ ih₁ ih₂ => exact fun B B' h => max_le_max (ih₁ h) (ih₂ h)
  | or χ₁ χ₂ ih₁ ih₂ => exact fun B B' h => max_le_max (ih₁ h) (ih₂ h)
  | all χ ih => exact ih
  | exs χ ih => exact ih

/-- Terms contract under a numeral-or-variable rewrite: if `ω` maps every bounded variable to a
term of frame value `≤ max B K` and fixes names, then `tvB (ω t) B ≤ tvB t (max B K)`. -/
theorem tvB_rew_le {K : ℕ} {n₁ n₂ : ℕ} (t : Semiterm ℒₒᵣ ℕ n₁) (ω : Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (hb : ∀ i B, tvB (ω #i) B ≤ max B K) (hf : ∀ x, ω &x = &x) (B : ℕ) :
    tvB (ω t) B ≤ tvB t (max B K) := by
  have h1 : tvB (ω t) B
      = Semiterm.valm ℕ (fun i => tvB (ω #i) B) (fun x => tvB (ω &x) B) t :=
    Semiterm.val_rew ω t
  rw [h1]
  apply valm_mono t
  · intro i
    exact hb i B
  · intro x
    rw [hf x]
    simp [tvB]

/-- The rewrite class is stable under the binder lift `ω.q`. -/
theorem q_class {K : ℕ} {n₁ n₂ : ℕ} (ω : Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (hb : ∀ i B, tvB (ω #i) B ≤ max B K) (hf : ∀ x, ω &x = &x) :
    (∀ i B, tvB (ω.q #i) B ≤ max B K) ∧ (∀ x, ω.q &x = &x) := by
  constructor
  · intro i B
    cases i using Fin.cases with
    | zero => simp [tvB]
    | succ j => rw [Rew.q_bvar_succ, tvB_bShift]; exact hb j B
  · intro x
    rw [Rew.q_fvar, hf x]
    rfl

/-- **The substitution law**: `gvb` contracts under a numeral-or-variable rewrite. -/
theorem gvb_rew_le {K : ℕ} :
    ∀ {n₁ : ℕ} (χ : SyntacticSemiformula ℒₒᵣ n₁) {n₂ : ℕ} (ω : Rew ℒₒᵣ ℕ n₁ ℕ n₂),
      (∀ i B, tvB (ω #i) B ≤ max B K) → (∀ x, ω &x = &x) →
      ∀ B, gvb (ω ▹ χ) B ≤ gvb χ (max B K) := by
  intro n₁ χ
  induction χ with
  | rel r v =>
      intro n₂ ω hb hf B
      rw [Semiformula.rew_rel]
      simp only [gvb]
      exact Finset.sup_le fun i _ =>
        le_trans (tvB_rew_le (v i) ω hb hf B)
          (Finset.le_sup (f := fun i => tvB (v i) (max B K)) (Finset.mem_univ i))
  | nrel r v =>
      intro n₂ ω hb hf B
      rw [Semiformula.rew_nrel]
      simp only [gvb]
      exact Finset.sup_le fun i _ =>
        le_trans (tvB_rew_le (v i) ω hb hf B)
          (Finset.le_sup (f := fun i => tvB (v i) (max B K)) (Finset.mem_univ i))
  | verum =>
      intro n₂ ω _ _ B
      rw [show (ω ▹ (Semiformula.verum : SyntacticSemiformula ℒₒᵣ _))
        = Semiformula.verum from rfl]
      simp [gvb]
  | falsum =>
      intro n₂ ω _ _ B
      rw [show (ω ▹ (Semiformula.falsum : SyntacticSemiformula ℒₒᵣ _))
        = Semiformula.falsum from rfl]
      simp [gvb]
  | and χ₁ χ₂ ih₁ ih₂ =>
      intro n₂ ω hb hf B
      rw [show (ω ▹ Semiformula.and χ₁ χ₂)
        = Semiformula.and (ω ▹ χ₁) (ω ▹ χ₂) from rfl]
      simp only [gvb]
      exact max_le_max (ih₁ ω hb hf B) (ih₂ ω hb hf B)
  | or χ₁ χ₂ ih₁ ih₂ =>
      intro n₂ ω hb hf B
      rw [show (ω ▹ Semiformula.or χ₁ χ₂)
        = Semiformula.or (ω ▹ χ₁) (ω ▹ χ₂) from rfl]
      simp only [gvb]
      exact max_le_max (ih₁ ω hb hf B) (ih₂ ω hb hf B)
  | all χ ih =>
      intro n₂ ω hb hf B
      rw [show (ω ▹ Semiformula.all χ) = Semiformula.all (ω.q ▹ χ) from rfl]
      simp only [gvb]
      obtain ⟨hb', hf'⟩ := q_class ω hb hf
      exact ih ω.q hb' hf' B
  | exs χ ih =>
      intro n₂ ω hb hf B
      rw [show (ω ▹ Semiformula.exs χ) = Semiformula.exs (ω.q ▹ χ) from rfl]
      simp only [gvb]
      obtain ⟨hb', hf'⟩ := q_class ω hb hf
      exact ih ω.q hb' hf' B

/-- Numerals sit inside the frame: `tvB (nm k) B = k`. -/
theorem tvB_nm (k B : ℕ) : tvB (nm k) B = k := by
  have he : (fun _ => B : Fin 0 → ℕ) = ![] := by funext i; exact i.elim0
  simp only [tvB, he]
  exact valm_nm k (fun _ => 0)

/-- **The numeral-instance law** — the exact shape the master induction threads at `allω`/`exs`
descents: instantiating the head variable by `nm k` contracts `gvb` into the `max B k` frame. -/
theorem gvb_substs_le {χ : SyntacticSemiformula ℒₒᵣ 1} (k B : ℕ) :
    gvb (χ/[nm k]) B ≤ gvb χ (max B k) := by
  have hb : ∀ (i : Fin 1) B', tvB ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) #i) B' ≤ max B' k := by
    intro i B'
    have h0 : (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) #i = nm k := by
      simp
    rw [h0, tvB_nm]
    exact le_max_right _ _
  have hf : ∀ x, (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) &x = &x := by
    intro x; simp
  exact gvb_rew_le (K := k) χ (Rew.subst ![nm k]) hb hf B

#print axioms GoodsteinPA.ReadoffValueGate.Gated_mono
#print axioms GoodsteinPA.ReadoffValueGate.Gated_all_iff
#print axioms GoodsteinPA.ReadoffValueGate.gvb_mono
#print axioms GoodsteinPA.ReadoffValueGate.gvb_rew_le
#print axioms GoodsteinPA.ReadoffValueGate.gvb_substs_le

end GoodsteinPA.ReadoffValueGate
