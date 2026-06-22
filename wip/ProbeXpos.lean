import GoodsteinPA.XPositive
open LO LO.FirstOrder GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.XPositive
theorem xpos_rew : ∀ {n₁} (χ : Semiformula LX ℕ n₁) {n₂} (ω : Rew LX ℕ n₁ ℕ n₂),
    XPos χ → XPos (ω ▹ χ) := by
  intro n₁ χ
  induction χ using Semiformula.rec' with
  | hverum => intro n₂ ω h; simp [XPos]
  | hfalsum => intro n₂ ω h; simp [XPos]
  | hrel r v => intro n₂ ω h; rw [Semiformula.rew_rel]; simp [XPos]
  | hnrel r v => intro n₂ ω h; rw [Semiformula.rew_nrel]; simpa [XPos] using h
  | hand φ ψ ihφ ihψ =>
      intro n₂ ω h
      simp only [LogicalConnective.HomClass.map_and, XPos] at *
      exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hor φ ψ ihφ ihψ =>
      intro n₂ ω h
      simp only [LogicalConnective.HomClass.map_or, XPos] at *
      exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hall φ ih => intro n₂ ω h; rw [Rewriting.app_all]; exact ih ω.q h
  | hexs φ ih => intro n₂ ω h; rw [Rewriting.app_exs]; exact ih ω.q h
