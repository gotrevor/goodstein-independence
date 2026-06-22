/-
# `EmbeddingBound.lean` — D': the embedded ordinal is `< ε₀`

The headline-route theorem `Thm56.peano_not_proves_TI` is axiom-clean modulo F-φ **and** the disclosed
`Thm56.embed_TI_bounded` (D'): a **finite** PA-proof embeds to a `Z∞`-proof of ordinal height `< ε₀`.
This is *the* Gentzen content (PA cannot certify heights up to ε₀ itself); `embedC_LX` forgets the
bound (`∃ α` with no `< ε₀`). This file re-runs the embedding tracking a **uniform** ordinal bound.

## Strategy

The ω-rule (`PXFc.allω`) maps a family `{α(n)}ₙ` to `(⨆ₙ α(n)) + 1`. For the result to stay `< ε₀` the
family must be **uniformly** bounded below ε₀ — and a plain existential `∃ α(n) < ε₀` is NOT enough (the
α(n) could climb to ε₀). The fix everywhere: carry a bound determined by *complexity / structure*, not
by the instantiation, so the family is **constant** in `n`.

- **`provable_em_x_bdd`** (this file): the `Z∞` excluded middle for `φ` has ordinal `≤ 2·complexity φ`,
  a **finite** ordinal. Its own ω-rule case (nested quantifiers) closes because the sub-family is at the
  constant complexity-bound `2·(k-1)+1`, so `⨆ₙ const = const`.

Downstream chips (next laps): `provable_true_x_bdd`, `exI_closed_bdd`, `metaInduction_cong_bdd`,
`PXFc_allClosure_bdd`, then `embedC_LX_gen_bdd` (10 cases) + `hax_paLX_bdd`, then discharge
`embed_TI_bounded`.
-/
import GoodsteinPA.XFreeCutElim
import GoodsteinPA.EmbeddingX

namespace GoodsteinPA.EmbeddingBound

open scoped Ordinal
open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.XFreeCutElim GoodsteinPA.EmbeddingX

/-- `⨆ₙ c = c` over `ℕ` (constant family), specialised to `Ordinal`. -/
private theorem iSup_const_ord (c : Ordinal.{0}) : (⨆ _ : ℕ, c) = c := ciSup_const

/-- **Bounded `Z∞` excluded middle over `LX`.** The cut-free `XFreeAx` derivation of `{φ, ∼φ}` has
**finite** ordinal `≤ 2·complexity φ`. The bound is complexity-determined (not instantiation-determined),
so the ω-rule case's numeral-family is constant — `⨆ₙ const = const` — and the ordinal stays finite.
Strengthens `XFreeCutElim.provable_em_x` (which forgot the bound). -/
theorem provable_em_x_bdd : ∀ (k : ℕ) (φ : Form LX), φ.complexity ≤ k →
    ∀ {Γ : Seq LX}, φ ∈ Γ → ∼φ ∈ Γ → PXFc ((2 * k : ℕ) : Ordinal) 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro φ hk Γ hp hn
    have h0 : ((2 * 0 : ℕ) : Ordinal) = 0 := by norm_num
    rw [h0]
    cases φ using Semiformula.cases' with
    | hverum => exact PXFc.verumR hp
    | hfalsum => exact PXFc.verumR (by simpa using hn)
    | hrel r v => exact PXFc.axL r v hp (by simpa using hn)
    | hnrel r v => exact PXFc.axL r v (by simpa using hn) hp
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro φ hk Γ hp hn
    -- target ordinal `↑(2*(k+1)) = ↑(2*k) + 1 + 1`
    have hk2 : (2 * (k + 1) : ℕ) = (2 * k + 1) + 1 := by omega
    have hcast : ((2 * (k + 1) : ℕ) : Ordinal) = ((2 * k : ℕ) : Ordinal) + 1 + 1 := by
      rw [hk2]; simp only [Nat.cast_add, Nat.cast_one]
    cases φ using Semiformula.cases' with
    | hverum => exact (PXFc.verumR hp).mono (by simp) (le_refl 0)
    | hfalsum => exact (PXFc.verumR (by simpa using hn)).mono (by simp) (le_refl 0)
    | hrel r v => exact (PXFc.axL r v hp (by simpa using hn)).mono (by simp) (le_refl 0)
    | hnrel r v => exact (PXFc.axL r v (by simpa using hn) hp).mono (by simp) (le_refl 0)
    | hand φ ψ =>
      have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have h1 := ih φ hφk (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ))) (by simp) (by simp)
      have h2 := ih ψ hψk (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ))) (by simp) (by simp)
      have hand := PXFc.andI φ ψ h1 h2
      rw [Finset.insert_eq_self.mpr
        (show (φ ⋏ ψ) ∈ insert (∼φ) (insert (∼ψ) Γ) by simp [hp])] at hand
      have hor := PXFc.orI (∼φ) (∼ψ) hand
      rw [Finset.insert_eq_self.mpr (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn)] at hor
      -- hor : PXFc (max (↑(2k)) (↑(2k)) + 1 + 1) 0 Γ ; max=↑(2k); target ↑(2k)+1+1
      rw [hcast]
      simpa only [max_self] using hor
    | hor φ ψ =>
      have hn' : (∼φ ⋏ ∼ψ) ∈ Γ := by simpa using hn
      have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have h1 := ih φ hφk (Γ := insert (∼φ) (insert φ (insert ψ Γ))) (by simp) (by simp)
      have h2 := ih ψ hψk (Γ := insert (∼ψ) (insert φ (insert ψ Γ))) (by simp) (by simp)
      have hand := PXFc.andI (∼φ) (∼ψ) h1 h2
      rw [Finset.insert_eq_self.mpr
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
      have hor := PXFc.orI φ ψ hand
      rw [Finset.insert_eq_self.mpr (show (φ ⋎ ψ) ∈ Γ by simp [hp])] at hor
      rw [hcast]
      simpa only [max_self] using hor
    | hall ψ =>
      have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hex : (∃⁰ ∼ψ) ∈ Γ := by simpa using hn
      -- constant family: each member is `PXFc (↑(2k) + 1) 0 (insert (ψ/[nm n]) Γ)`
      have fam : ∀ n, PXFc (((2 * k : ℕ) : Ordinal) + 1) 0 (insert (ψ/[nm n]) Γ) := by
        intro n
        have hcomp : (ψ/[nm n]).complexity ≤ k := by
          have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
          rw [he]; exact hψk
        have ha := ih (ψ/[nm n]) hcomp
          (Γ := insert (∼(ψ/[nm n])) (insert (ψ/[nm n]) Γ)) (by simp) (by simp)
        have hexI := PXFc.exI (∼ψ) n (Γ := insert (ψ/[nm n]) Γ)
          (by have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
              rw [heq]; exact ha)
        rwa [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hex)] at hexI
      have hall := PXFc.allω (β := fun _ => ((2 * k : ℕ) : Ordinal) + 1) ψ (Γ := Γ) fam
      rw [Finset.insert_eq_self.mpr hp, iSup_const_ord] at hall
      rw [hcast]; exact hall
    | hexs ψ =>
      have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hall' : (∀⁰ ∼ψ) ∈ Γ := by simpa using hn
      have fam : ∀ n, PXFc (((2 * k : ℕ) : Ordinal) + 1) 0 (insert ((∼ψ)/[nm n]) Γ) := by
        intro n
        have hcomp : (ψ/[nm n]).complexity ≤ k := by
          have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
          rw [he]; exact hψk
        have ha := ih (ψ/[nm n]) hcomp
          (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) Γ)) (by simp) (by simp)
        have hexI := PXFc.exI ψ n (Γ := insert (∼(ψ/[nm n])) Γ) ha
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp)] at hexI
        have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
        rw [heq]; exact hexI
      have hall := PXFc.allω (β := fun _ => ((2 * k : ℕ) : Ordinal) + 1) (∼ψ) (Γ := Γ) fam
      rw [Finset.insert_eq_self.mpr hall', iSup_const_ord] at hall
      rw [hcast]; exact hall

end GoodsteinPA.EmbeddingBound
