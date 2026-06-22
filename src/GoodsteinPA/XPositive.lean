/-
# `wip/XPositive.lean` — X-positivity + monotonicity of `⊨^γ` in `γ` (lap-13, Boundedness ingredient)

Buchholz's Boundedness uses, in cases 2/3/4: for an **X-positive** sequent `Γ` and `β₀ ≤ β`,
`⊨^{α+2^{β₀}} Γ ⟹ ⊨^{α+2^β} Γ`. The semantic content is monotonicity of truth in the `X`-set for
formulas where `X` occurs only positively, together with `U^γ ⊆ U^δ` for `γ ≤ δ`. This file proves
that monotonicity.
-/
import GoodsteinPA.TruthSem

namespace GoodsteinPA.XPositive

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.TruthSem

/-- **X-positive**: no `¬X t` subformula — i.e. every negative atom is an `ℒₒᵣ`-relation
(`Sum.isLeft`), never the set variable `X`. -/
def XPos : {n : ℕ} → Semiformula LX ℕ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel _ _ => True
  | _, .nrel r _ => Sum.isLeft r = true
  | _, .and φ ψ => XPos φ ∧ XPos ψ
  | _, .or φ ψ => XPos φ ∧ XPos ψ
  | _, .all φ => XPos φ
  | _, .exs φ => XPos φ

/-- Term values are independent of the `X`-interpretation (terms never mention `X`; `structLX`'s
function interpretation does not depend on `S`). -/
theorem val_structLX_eq (S S' : ℕ → Prop) {n} (e : Fin n → ℕ) (ε : ℕ → ℕ) (t : Semiterm LX ℕ n) :
    Semiterm.val (structLX S) e ε t = Semiterm.val (structLX S') e ε t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f w ih => simp only [Semiterm.val_func]; congr 1; funext i; exact ih i

/-- **X-positive monotonicity of truth in the X-set.** If `X`-positive `A` is true with `X := S` and
`S ⊆ S'` (pointwise), then `A` is true with `X := S'`. -/
theorem eval_mono {S S' : ℕ → Prop} (hSS : ∀ n, S n → S' n) :
    ∀ {n} (A : Semiformula LX ℕ n), XPos A → ∀ (e : Fin n → ℕ) (ε : ℕ → ℕ),
      Semiformula.Eval (structLX S) e ε A → Semiformula.Eval (structLX S') e ε A := by
  intro n A
  induction A using Semiformula.rec' with
  | hverum => intro _ e ε h; exact h
  | hfalsum => intro _ e ε h; exact h
  | hrel r v =>
    intro _ e ε h
    simp only [Semiformula.eval_rel] at h ⊢
    -- align the (S'-)term-values in the goal with the (S-)term-values in `h`
    have hv : (fun i => Semiterm.val (structLX S') e ε (v i))
        = (fun i => Semiterm.val (structLX S) e ε (v i)) :=
      funext fun i => val_structLX_eq S' S e ε (v i)
    rw [hv]
    rcases r with r₀ | rx
    · -- `ℒₒᵣ`-relation: `(structLX S).rel (Sum.inl ·) = (structLX S').rel (Sum.inl ·)` (defeq)
      exact h
    · -- positive `X`-atom: `S (v 0) → S' (v 0)`
      cases rx
      rw [structLX_rel_X] at h ⊢
      exact hSS _ h
  | hnrel r v =>
    intro hpos e ε h
    simp only [Semiformula.eval_nrel] at h ⊢
    have hv : (fun i => Semiterm.val (structLX S') e ε (v i))
        = (fun i => Semiterm.val (structLX S) e ε (v i)) :=
      funext fun i => val_structLX_eq S' S e ε (v i)
    rw [hv]
    rcases r with r₀ | rx
    · exact h
    · exact absurd hpos (by simp [XPos])
  | hand φ ψ ihφ ihψ =>
    intro hpos e ε h
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq] at h ⊢
    exact ⟨ihφ hpos.1 e ε h.1, ihψ hpos.2 e ε h.2⟩
  | hor φ ψ ihφ ihψ =>
    intro hpos e ε h
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq] at h ⊢
    exact h.imp (ihφ hpos.1 e ε) (ihψ hpos.2 e ε)
  | hall φ ih =>
    intro hpos e ε h
    simp only [Semiformula.eval_all] at h ⊢
    exact fun x => ih hpos (x :> e) ε (h x)
  | hexs φ ih =>
    intro hpos e ε h
    simp only [Semiformula.eval_ex] at h ⊢
    obtain ⟨x, hx⟩ := h
    exact ⟨x, ih hpos (x :> e) ε hx⟩

/-- `U^γ ⊆ U^δ` for `γ ≤ δ`. -/
theorem levelSet_mono (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt] {γ δ : Ordinal.{0}} (h : γ ≤ δ) :
    ∀ n, levelSet lt γ n → levelSet lt δ n := fun _ hn => lt_of_lt_of_le hn h

/-- **`⊨^γ` is monotone in `γ` on X-positive formulas** (Buchholz, cases 2/3/4). -/
theorem models_mono (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt] {γ δ : Ordinal.{0}}
    (h : γ ≤ δ) {A : Form LX} (hpos : XPos A) : models lt γ A → models lt δ A :=
  eval_mono (levelSet_mono lt h) A hpos ![] id

end GoodsteinPA.XPositive
