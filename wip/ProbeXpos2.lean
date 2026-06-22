import GoodsteinPA.XPositive
open LO LO.FirstOrder GoodsteinPA.ZinftyGen GoodsteinPA.LangX
example {n₁ n₂} (ω : Rew LX ℕ n₁ ℕ n₂) (φ : Semiformula LX ℕ (n₁+1)) :
    ω ▹ (∀⁰ φ) = ∀⁰ (ω.q ▹ φ) := by exact?
