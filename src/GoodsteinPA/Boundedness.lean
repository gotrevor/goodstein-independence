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
import GoodsteinPA.XPositive

namespace GoodsteinPA.Boundedness

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.TruthSem GoodsteinPA.XPositive

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

/-! ## Boundedness (Buchholz Thm 5.4) — the 8→5-case induction

Buchholz: for X-positive `Γ`, `Z∞ ⊢^β_1 ¬Prog_≺(X), ¬Xs₁,…,¬Xs_k, Γ` with `|sᵢ|_≺ ≤ α`
⟹ `⊨^{α+2^β} Γ`. We prove the **cut-free** specialisation (`cr d = 0`): the three `Cut` cases
(Buchholz 6/7/8) are then vacuous (a `cut` node has `cr ≥ 1`), leaving 5 cases.

The induction is **nested**: an outer strong induction on the ordinal height `o d` (the `¬Prog`
inversion case shrinks it strictly) wrapping an inner structural induction on the derivation `d`
(the height-preserving `weak`/`andI`/`orI`/`allω` cases). See
`papers/buchholz-beweistheorie-lecture-notes.pdf` p.29 + `ANALYSIS-2026-06-22-lap13-boundedness-design.md`.

**Faithfulness of the X-atom leaf.** Our generic `axTrue` is more permissive than Buchholz's `Z∞`
at `LX`: it admits a *lone* true X-literal, which Buchholz forbids (his only X-axiom is the *pair*
`{Xs,¬Xt}`). Boundedness is false for lone-X leaves, so we carry `XFreeAx d` (every `axTrue` leaf
uses an `ℒₒᵣ`-relation); the X-pair axiom enters via `axL` (a genuine complementary pair, handled in
case 1.2). The embedding `embedC` over `LX` discharges `XFreeAx` by routing X-atom identity axioms
through `axL` rather than `axTrue`. -/

section Main

/-- The ambient ℕ-model for the Boundedness derivations: `X := ∅`. The choice is immaterial — every
X-free leaf is `S`-independent and `XFreeAx` forbids X-literal leaves — but fixing it lets `LitTrue`
(under this instance) connect to `models` (under the level-set instance). -/
noncomputable instance ambient : Structure LX ℕ := structLX (fun _ => False)

variable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]

/-- `tval lt t = |tᴺ|_≺` — the ≺-rank of the ℕ-value of a closed `LX`-term (X-free, so the carrier
is immaterial). -/
noncomputable def tval (t : Semiterm LX ℕ 0) : Ordinal.{0} :=
  rk lt (Semiterm.val (structLX (fun _ => False)) ![] id t)

/-- **The X-atom on a closed term reads the ≺-rank bound.** -/
theorem models_Xat' (γ : Ordinal.{0}) (t : Semiterm LX ℕ 0) :
    models lt γ (Xat t) ↔ tval lt t < γ := by
  unfold models Xat tval
  rw [Semiformula.eval_rel₁, structLX_rel_Xsym]
  simp only [Matrix.cons_val_zero, levelSet]
  rw [val_structLX_eq (levelSet lt γ) (fun _ => False)]

/-- **The negated X-atom is true at `γ` iff the rank is `≥ γ`.** -/
theorem models_negXat (γ : Ordinal.{0}) (t : Semiterm LX ℕ 0) :
    models lt γ (∼(Xat t)) ↔ γ ≤ tval lt t := by
  have : ∼(Xat t) = Semiformula.nrel Xsym ![t] := rfl
  rw [this]
  unfold models tval
  rw [Semiformula.eval_nrel₁, structLX_rel_Xsym]
  simp only [Matrix.cons_val_zero, levelSet]
  rw [val_structLX_eq (levelSet lt γ) (fun _ => False)]
  exact not_lt

/-- A true **X-free** literal is `models`-true at every level (its truth is carrier-independent). -/
theorem models_inl_lit (γ : Ordinal.{0}) (b : Bool) {k} (r₀ : (ℒₒᵣ).Rel k)
    (v : Fin k → Semiterm LX ℕ 0) (htrue : LitTrue (signedLit b (Sum.inl r₀) v)) :
    models lt γ (signedLit b (Sum.inl r₀) v) := by
  have hv : (fun i => Semiterm.val (structLX (levelSet lt γ)) ![] id (v i))
      = (fun i => Semiterm.val (structLX (fun _ => False)) ![] id (v i)) :=
    funext fun i => val_structLX_eq _ _ _ _ (v i)
  cases b <;>
    · simp only [signedLit, models, LitTrue, Semiformula.eval_rel, Semiformula.eval_nrel,
        Semiformula.Evalm] at htrue ⊢
      rw [hv]; exact htrue

/-- **X-free axTrue leaves only** (Buchholz-faithfulness; see the section header). -/
def XFreeAx : {Δ : Seq LX} → Deriv Δ → Prop
  | _, .axL _ _ _ _ => True
  | _, .axTrue _ r _ _ _ => Sum.isLeft r = true
  | _, .verumR _ => True
  | _, .weak d _ => XFreeAx d
  | _, .andI _ _ dφ dψ => XFreeAx dφ ∧ XFreeAx dψ
  | _, .orI _ _ d => XFreeAx d
  | _, .allω _ d => ∀ n, XFreeAx (d n)
  | _, .exI _ _ d => XFreeAx d
  | _, .cut _ d₁ d₂ => XFreeAx d₁ ∧ XFreeAx d₂

variable (prec : Semiformula LX ℕ 2)

/-- A formula's **role** in a Boundedness sequent: the negated progressiveness `¬Prog`, a bounded
negative X-atom `¬Xt` (`|tᴺ|_≺ ≤ α`), or an X-positive formula. -/
def PartItem (α : Ordinal.{0}) (A : Form LX) : Prop :=
  A = ∼(Prog prec) ∨
  (∃ t : Semiterm LX ℕ 0, A = ∼(Xat t) ∧ tval lt t ≤ α) ∨
  XPos A

/-- The Boundedness sequent invariant: every member has a valid role. -/
def Partition (α : Ordinal.{0}) (Δ : Seq LX) : Prop := ∀ A ∈ Δ, PartItem lt prec α A

/-- The Boundedness conclusion: some **X-positive** member is `⊨^γ`-true. -/
def SatPos (γ : Ordinal.{0}) (Δ : Seq LX) : Prop := ∃ A ∈ Δ, XPos A ∧ models lt γ A

/-- **Boundedness (Buchholz Thm 5.4), cut-free.** For an X-positive-decomposed sequent `Δ` (every
member is `¬Prog`, a bounded `¬Xt`, or X-positive), a cut-free `XFreeAx` derivation of `Δ` at height
`o d` yields `⊨^{α+2^{o d}}` of some X-positive member. The corollary `‖≺‖ ≤ 2^β` follows. -/
theorem boundedness (β : Ordinal.{0}) :
    ∀ {Δ : Seq LX} (α : Ordinal.{0}) (d : Deriv Δ),
      d.o ≤ β → d.cr = 0 → XFreeAx d → Partition lt prec α Δ →
      SatPos lt (α + 2 ^ d.o) Δ := by
  induction β using Ordinal.induction with
  | _ β outerIH =>
  intro Δ α d
  induction d generalizing α with
  | axL r v hp hn =>
    intro hob hcr hxf hpart
    cases r with
    | inl r₀ =>
      rcases litTrue_or_neg (Semiformula.rel (Sum.inl r₀) v) with ht | ht
      · exact ⟨Semiformula.rel (Sum.inl r₀) v, hp, by simp [XPos],
          models_inl_lit lt _ true r₀ v ht⟩
      · exact ⟨Semiformula.nrel (Sum.inl r₀) v, hn, by simp [XPos],
          models_inl_lit lt _ false r₀ v ht⟩
    | inr rx =>
      cases rx
      have hv1 : v = ![v 0] := by funext i; refine Fin.cases ?_ (fun j => j.elim0) i; rfl
      have hbound : tval lt (v 0) ≤ α := by
        rcases hpart (Semiformula.nrel Xsym v) hn with h | ⟨t', heq, hb⟩ | hpos
        · rw [Prog] at h; simp [Xat, Xsym] at h
        · simp only [Xat, Xsym] at heq
          injection heq with e1 e2 e3 e4
          rw [show v = ![t'] from e4]; simpa using hb
        · simp [XPos, Xsym] at hpos
      refine ⟨Xat (v 0), hv1 ▸ hp, by simp [Xat, XPos], ?_⟩
      rw [models_Xat']
      simp only [Deriv.o, Ordinal.opow_zero]
      exact lt_of_le_of_lt hbound (lt_add_of_pos_right α one_pos)
  | axTrue b r v htrue hmem =>
    intro hob hcr hxf hpart
    cases r with
    | inr rx => simp [XFreeAx] at hxf
    | inl r₀ =>
      exact ⟨signedLit b (Sum.inl r₀) v, hmem, by cases b <;> simp [signedLit, XPos],
        models_inl_lit lt _ b r₀ v htrue⟩
  | verumR h =>
    intro hob hcr hxf hpart
    exact ⟨⊤, h, by simp [XPos], by simp [models]⟩
  | weak d' hsub ih =>
    intro hob hcr hxf hpart
    obtain ⟨A, hA, hposA, hmodA⟩ := ih α hob hcr hxf (fun B hB => hpart B (hsub hB))
    exact ⟨A, hsub hA, hposA, hmodA⟩
  | andI φ ψ dφ dψ ihφ ihψ => intro hob hcr hxf hpart; sorry
  | orI φ ψ d' ih => intro hob hcr hxf hpart; sorry
  | allω χ d' ih => intro hob hcr hxf hpart; sorry
  | exI χ n d' ih => intro hob hcr hxf hpart; sorry
  | cut φ d₁ d₂ ih₁ ih₂ =>
    intro hob hcr hxf hpart
    exfalso
    have h1 : (↑φ.complexity + 1 : ℕ∞) ≤ 0 := hcr ▸ le_max_left _ _
    simp at h1

end Main

end GoodsteinPA.Boundedness
