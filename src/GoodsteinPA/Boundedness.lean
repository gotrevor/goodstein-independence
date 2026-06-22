/-
# `Boundedness.lean` — the `Prog_≺(X)` / `TI_≺(X)` formulas + corollary bridges (lap-13)

The transfinite-induction formula scaffolding the Boundedness theorem (Buchholz Thm 5.4) inverts,
plus the corollary bridges connecting `⊨^γ`-truth of `X`-atoms to the ≺-rank.
The order `≺` is given by a depth-2 `LX`-formula `prec` (`#0 ≺ #1`); for the headline `prec` is the
ℒₒᵣ-definable CNF-ε₀ order. `X t` is the set-variable atom `Xat t`.

  `Prog_≺(X) := ∀x ((∀y (y ≺ x → X y)) → X x)`
  `TI_≺(X)   := Prog_≺(X) → ∀x X x`

The de-Bruijn shapes are pinned so the Boundedness induction's inversion cases line up; the proof of
Boundedness itself is the next target. The corollary step (`‖≺‖ ≤ 2^β` from `⊨^{2^β} Xn ∀n`) is here.
-/
import GoodsteinPA.ZinftyGen
import GoodsteinPA.LangX
import GoodsteinPA.TruthSem

namespace GoodsteinPA.Boundedness

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.TruthSem

/-- The set-variable atom `X t`. -/
def Xat {n} (t : Semiterm LX ℕ n) : Semiformula LX ℕ n := Semiformula.rel Xsym ![t]

variable (prec : Semiformula LX ℕ 2)

/-- `∀y (y ≺ x → X y)` as a depth-1 formula (free `x = #0`). At depth 2, `prec` reads `#0 ≺ #1`
with `#0 = y`, `#1 = x`. -/
def hyp : Semiformula LX ℕ 1 := ∀⁰ (prec 🡒 Xat (#0))

/-- `Prog_≺(X) := ∀x ((∀y (y ≺ x → X y)) → X x)`. -/
def Prog : Semiformula LX ℕ 0 := ∀⁰ (hyp prec 🡒 Xat (#0))

/-- `TI_≺(X) := Prog_≺(X) → ∀x X x`. -/
def TI : Semiformula LX ℕ 0 := Prog prec 🡒 ∀⁰ (Xat (#0))

-- Probes: the formulas typecheck and their negations have the expected `∃`/`∀` shape for inversion.
example : Form LX := Prog prec
example : Form LX := TI prec
example : ∼(Prog prec) = ∃⁰ ∼(hyp prec 🡒 Xat (#0)) := by simp [Prog]
example : ∼(TI prec) = (Prog prec) ⋏ ∼(∀⁰ (Xat (#0))) := by simp [TI, Semiformula.imp_eq]

/-! ## Corollary bridges: `⊨^γ`-truth of `X`-atoms ↔ the ≺-rank

These connect the Boundedness conclusion (`⊨^{2^β} Xn` for all `n`) to `‖≺‖ ≤ 2^β` — the corollary
`Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`. -/

section Corollary
variable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]

/-- The numeral `nm n` denotes `n` in the `structLX` carrier (its `ℒₒᵣ`-fragment is the standard
model). -/
theorem val_nm_structLX (S : ℕ → Prop) (n : ℕ) :
    Semiterm.val (structLX S) ![] (id : ℕ → ℕ) (nm n) = n := by
  letI inst : Structure LX ℕ := structLX S
  haveI : Structure.Zero LX ℕ := ⟨rfl⟩
  haveI : Structure.One LX ℕ := ⟨rfl⟩
  haveI : Structure.Add LX ℕ := ⟨fun _ _ => rfl⟩
  simp [nm]

/-- `⊨^γ (X (numeral n)) ↔ |n|_≺ < γ` — the carrier reads the `X`-atom on a numeral as the level-set
membership, i.e. as the ≺-rank bound. -/
theorem models_Xat_nm (γ : Ordinal.{0}) (n : ℕ) :
    models lt γ (Xat (nm n)) ↔ rk lt n < γ := by
  unfold models Xat
  rw [Semiformula.eval_rel₁, structLX_rel_Xsym]
  simp only [Matrix.cons_val_zero, val_nm_structLX]
  rfl

/-- **The corollary's order-type step.** If `⊨^γ (X (numeral n))` for every `n`, then `‖≺‖ ≤ γ`.
With `γ := 2^β` this is `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β` once Boundedness supplies the hypothesis. -/
theorem orderType_le_of_models_Xat {γ : Ordinal.{0}}
    (h : ∀ n, models lt γ (Xat (nm n))) : orderType lt ≤ γ :=
  orderType_le_of_forall lt (fun n => (models_Xat_nm lt γ n).mp (h n))

end Corollary

end GoodsteinPA.Boundedness
