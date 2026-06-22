/-
# M4 — the embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` (Towsner §16 / Buchholz §5.5)

**The universal bottleneck of the whole expedition** (required on every route to the headline;
see `REFLECTION-2026-06-22.md`). This file is the lap-9 feasibility scaffold: it sets the embedding
up over Foundation's **`Derivation2`** (the Finset-sequent variant, `Calculus2.lean`), which lives
over the *same* `Finset (SyntacticFormula ℒₒᵣ)` substrate as M5's `ZinftyF.Seq` — so the embedding is
a pure rule-by-rule map with **no language translation**.

## API anchors (verified lap 9)
- `Schema ℒₒᵣ := Set (SyntacticFormula ℒₒᵣ)`; `(𝗣𝗔 : Theory) ↦ (𝗣𝗔 : Schema) = Rewriting.emb '' 𝗣𝗔`.
- `provable_def : T ⊢ σ ↔ (T : Schema) ⊢ ↑σ` (rfl) · `provable_iff_derivable2 : 𝓢 ⊢ φ ↔ 𝓢 ⊢!₂! φ`.
  ⟹ `𝗣𝗔 ⊢ goodsteinSentence` unfolds to `Nonempty (Derivation2 (𝗣𝗔:Schema) {↑goodsteinSentence})`.
- M5 target: `GoodsteinPA.ZinftyF.Deriv.Provable α c Γ` with constructors `axL/verumR/andI/orI/exI/
  allω/cut/weakening/mono/cast` (`src/Zinfty.lean:116–208`).

## Status of the cases (lap 10 — compiles, `lake env lean wip/Embedding.lean`)
- **`provable_em` (Z∞ excluded-middle): FULLY PROVED, axiom-clean** (`[propext, choice, Quot.sound]`).
  `∀ φ Γ, φ∈Γ → ∼φ∈Γ → ∃ a, Provable a 0 Γ`, incl. the ∀/∃ numeral ω-family. Promotable to `src/`.
- **`provable_rew` (renaming-invariance enabler): PROVED across ALL 8 `Deriv` cases**
  (axL/verumR/weak/andI/orI/allω/exI/cut) — cut-rank-preserving so `allω`'s ℕ-many premises share one
  `c`. **Sole residue = `rew_subst_nm`** (`ω ▹ (φ/[nm n]) = (ω.q ▹ φ)/[nm n]`, a `Rew`-substs algebra
  fact). **`rew_subst_nm` discharged (lap 10) ⟹ `provable_rew`/`ZProvable.rew` axiom-clean.**
- **`embed`: 8/10 cases DONE** (closed/verum/and/or/wk/cut/**shift/all**). `shift` = `ZProvable.rew
  Rew.shift`; `all` = `provable_rew` substitutes the freed var by each `nm n` (undoing the `shift` on
  `Γ` via `rewrite_comp_shift_eq_id`) then the ω-rule `allω` (lap 10). Remaining: `axm`, `exs`.
- No `axiom` declarations; open obligations are honest `sorry`s (`embed`'s 2 cases: `axm`, `exs`).
- **DISCLOSED `sorry` (the real content), hardest-first:**
  - `axm` — each PA axiom Z∞-derivable. `𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`: PeanoMinus is a
    finite set of true ∀-sentences (finite ordinal); `univCl (succInd ψ)` is derived **via the ω-rule**
    (`allω`) — THE deep case (Buchholz §5.5).
  - `exs` — witness term `t` → its standard numeral value, then `exI`. **OBSTRUCTION (lap 10):** `t`
    may be OPEN (free vars from an `all` closer to the root). The naive statement `Derivation2 𝗣𝗔 Γ →
    ZProvable Γ` cannot close an open existential with M5's numeral-only `exI`. The fix is the
    **assignment-carrying reformulation** `∀ e : ℕ → ℕ, ZProvable (Γ.image (ρ e ▹))`, `ρ e :=
    Rew.rewrite (nm ∘ e)` closing all free vars to numerals; then `ρe▹t` is closed and `exI` reads its
    value. That also needs a Z∞ closed-term→numeral collapse (`ρe▹t = nm m` is arithmetic, not
    syntactic — built from the PeanoMinus eqns ⟹ intertwined with `axm`). Multi-lap.
-/
import GoodsteinPA.Zinfty
import Foundation.FirstOrder.Basic.Calculus2
import Foundation.FirstOrder.Arithmetic.Schemata

namespace GoodsteinPA.Embedding

open LO LO.FirstOrder GoodsteinPA.ZinftyF GoodsteinPA.ZinftyF.Deriv

/-- A `Z_∞`-derivable sequent, existentially quantified over the ordinal bound and cut rank
(Towsner states the whole embedding/cut-elim chain existentially in `(α, c)` — see
`ANALYSIS-…-cutelim-k-threading.md`). -/
def ZProvable (Γ : ZinftyF.Seq) : Prop := ∃ α c, Provable α c Γ

namespace ZProvable

theorem mono {Γ : ZinftyF.Seq} : ZProvable Γ → ZProvable Γ := id

/-- Weaken the sequent (Foundation `wk`). -/
theorem weakening {Γ Δ : ZinftyF.Seq} (h : Γ ⊆ Δ) : ZProvable Γ → ZProvable Δ := by
  rintro ⟨α, c, hd⟩; exact ⟨α, c, hd.weakening h⟩

/-- Drop a sequent element that already occurs (`insert X Γ = Γ` when `X ∈ Γ`). -/
theorem of_insert_mem {Γ : ZinftyF.Seq} {X : ZinftyF.Form} (h : X ∈ Γ) :
    ZProvable (insert X Γ) → ZProvable Γ := by
  rw [Finset.insert_eq_self.mpr h]; exact id

end ZProvable

/-- **Identity / law of excluded middle for `Z_∞`** (the `closed` case). For any `φ`, a sequent
containing both `φ` and `∼φ` is `Z_∞`-derivable cut-free. Proved by induction on a `complexity`
bound (the standard Tait `em`, cf. Foundation `Derivation.em`, `Calculus.lean:164`). The atomic /
propositional cases are discharged here; the **∀/∃ cases** need M5's numeral ω-family (`allω` over
all `nm n`, each premise closed by `exI` + the IH at the substitution instance `φ/[nm n]`, whose
`complexity` equals `φ`'s) — disclosed `sorry`, the next chip. -/
theorem provable_em (φ : ZinftyF.Form) {Γ : ZinftyF.Seq} (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    ∃ a, Provable a 0 Γ := by
  have key : ∀ (k : ℕ) (φ : ZinftyF.Form), φ.complexity ≤ k →
      ∀ {Γ : ZinftyF.Seq}, φ ∈ Γ → ∼φ ∈ Γ → ∃ a, Provable a 0 Γ := by
    intro k
    induction k with
    | zero =>
      intro φ hk Γ hp hn
      cases φ using Semiformula.cases' with
      | hverum => exact ⟨0, Provable.verumR hp⟩
      | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
      | hrel r v => exact ⟨0, Provable.axL r v hp (by simpa using hn)⟩
      | hnrel r v => exact ⟨0, Provable.axL r v (by simpa using hn) hp⟩
      | hand φ ψ => simp at hk
      | hor φ ψ => simp at hk
      | hall φ => simp at hk
      | hexs φ => simp at hk
    | succ k ih =>
      intro φ hk Γ hp hn
      cases φ using Semiformula.cases' with
      | hverum => exact ⟨0, Provable.verumR hp⟩
      | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
      | hrel r v => exact ⟨0, Provable.axL r v hp (by simpa using hn)⟩
      | hnrel r v => exact ⟨0, Provable.axL r v (by simpa using hn) hp⟩
      | hand φ ψ =>
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        obtain ⟨a1, h1⟩ := ih φ hφk (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ)))
          (by simp) (by simp)
        obtain ⟨a2, h2⟩ := ih ψ hψk (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ)))
          (by simp) (by simp)
        have hand := Provable.andI φ ψ h1 h2
        rw [Finset.insert_eq_self.mpr
          (show (φ ⋏ ψ) ∈ insert (∼φ) (insert (∼ψ) Γ) by simp [hp])] at hand
        have hor := Provable.orI (∼φ) (∼ψ) hand
        rw [Finset.insert_eq_self.mpr (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn)] at hor
        exact ⟨_, hor⟩
      | hor φ ψ =>
        have hn' : (∼φ ⋏ ∼ψ) ∈ Γ := by simpa using hn
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        obtain ⟨a1, h1⟩ := ih φ hφk (Γ := insert (∼φ) (insert φ (insert ψ Γ)))
          (by simp) (by simp)
        obtain ⟨a2, h2⟩ := ih ψ hψk (Γ := insert (∼ψ) (insert φ (insert ψ Γ)))
          (by simp) (by simp)
        have hand := Provable.andI (∼φ) (∼ψ) h1 h2
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
        have hor := Provable.orI φ ψ hand
        rw [Finset.insert_eq_self.mpr (show (φ ⋎ ψ) ∈ Γ by simp [hp])] at hor
        exact ⟨_, hor⟩
      | hall ψ =>
        -- φ = ∀⁰ψ, ∼φ = ∃⁰∼ψ. Introduce ∀⁰ψ by the ω-rule; each premise closed by `exI (∼ψ) n`
        -- over the IH at `ψ/[nm n]` (same complexity as ψ < (∀⁰ψ)'s).
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
        have hex : (∃⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, ∃ a, Provable a 0 (insert (ψ/[nm n]) Γ) := by
          intro n
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
            rw [he]; exact hψk
          obtain ⟨a, ha⟩ := ih (ψ/[nm n]) hcomp
            (Γ := insert (∼(ψ/[nm n])) (insert (ψ/[nm n]) Γ)) (by simp) (by simp)
          have hexI := Provable.exI (∼ψ) n (Γ := insert (ψ/[nm n]) Γ)
            (by have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
                rw [heq]; exact ha)
          rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hex)] at hexI
          exact ⟨a + 1, hexI⟩
        choose β hβ using fam
        have hall := Provable.allω ψ (Γ := Γ) hβ
        rw [Finset.insert_eq_self.mpr hp] at hall
        exact ⟨_, hall⟩
      | hexs ψ =>
        -- φ = ∃⁰ψ, ∼φ = ∀⁰∼ψ. Dual: introduce ∀⁰∼ψ by the ω-rule; each premise closed by `exI ψ n`.
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
        have hall' : (∀⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, ∃ a, Provable a 0 (insert ((∼ψ)/[nm n]) Γ) := by
          intro n
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
            rw [he]; exact hψk
          obtain ⟨a, ha⟩ := ih (ψ/[nm n]) hcomp
            (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) Γ)) (by simp) (by simp)
          have hexI := Provable.exI ψ n (Γ := insert (∼(ψ/[nm n])) Γ) ha
          rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp)] at hexI
          have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
          rw [heq]; exact ⟨a + 1, hexI⟩
        choose β hβ using fam
        have hall := Provable.allω (∼ψ) (Γ := Γ) hβ
        rw [Finset.insert_eq_self.mpr hall'] at hall
        exact ⟨_, hall⟩
  exact key φ.complexity φ le_rfl hp hn

/-- **(enabler helper, DISCLOSED)** Numeral substitution commutes with rewriting: since `nm n` is a
closed term (fixed by any `Rew`), `ω ▹ (φ/[nm n]) = (ω.q ▹ φ)/[nm n]`. The one substitution-algebra
fact the `allω`/`exI` cases of the renaming enabler need. Proof = `Rew`-substs composition law
(`Rewriting.subst` ∘ `ω` = `ω.q` ∘ `Rewriting.subst`) + `ω ▹ nm n = nm n`. -/
private lemma rew_subst_nm (ω : Rew ℒₒᵣ ℕ 0 ℕ 0) (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) :
    ω ▹ (φ/[nm n]) = (ω.q ▹ φ)/[nm n] := by
  -- `φ/[nm n] = Rew.subst ![nm n] ▹ φ`; push `ω` through and collapse the two `▹` into a
  -- single composed `Rew`, reducing to a pointwise `Rew` identity.
  show ω ▹ (Rew.subst ![nm n] ▹ φ) = Rew.subst ![nm n] ▹ (ω.q ▹ φ)
  have heq : ω.comp (Rew.subst ![nm n]) = (Rew.subst ![nm n]).comp ω.q := by
    ext x
    · -- bound variable: only `#0`, sent to the closed numeral `nm n` (fixed by `ω`).
      cases x using Fin.cases with
      | zero => simp [Rew.comp_app, nm]
      | succ i => exact Fin.elim0 i
    · -- free variable: `ω.q &x = bShift (ω &x)`, killed by `subst_bShift_app`.
      simp [Rew.comp_app]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, heq]

/-- **General substitution–rewriting commutation** (the `exs`/`axm` version of `rew_subst_nm`, for an
arbitrary witness term `t`): `ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t]`. In the assignment embedding `ω = asg e`
closes `t`, so `ω t = asg e ▹ t` is a closed term whose numeral value feeds `Provable.exI`. -/
lemma rew_subst_term (ω : Rew ℒₒᵣ ℕ 0 ℕ 0) (φ : SyntacticSemiformula ℒₒᵣ 1)
    (t : SyntacticTerm ℒₒᵣ) : ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t] := by
  show ω ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![ω t] ▹ (ω.q ▹ φ)
  have heq : ω.comp (Rew.subst ![t]) = (Rew.subst ![ω t]).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact Fin.elim0 i
    · simp [Rew.comp_app]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, heq]

/-- **(enabler, M4) Renaming invariance for `Z_∞`**, **cut-rank-preserving** (the ordinal may grow;
existential `α`). The shared prerequisite for the embedding's `shift`/`all`/`exs` cases (the analogue
of Foundation's `Derivation.rewrite`, `Calculus.lean:255`). Preserving the cut rank `c` exactly is
what makes the `allω` case work — its ℕ-many premises all sit at the *same* `c`. Proved by induction
on the derivation via the M5 smart constructors; the only residue is `rew_subst_nm` (used in
`allω`/`exI`). -/
theorem provable_rew (c : ℕ) : ∀ {Γ : ZinftyF.Seq} (d : Deriv Γ), cr d ≤ (c : ℕ∞) →
    ∀ (ω : Rew ℒₒᵣ ℕ 0 ℕ 0), ∃ α, Provable α c (Γ.image (fun φ => ω ▹ φ)) := by
  intro Γ d
  induction d with
  | axL r v hp hn =>
    intro _ ω
    exact ⟨0, (Provable.axL r (fun i => ω (v i))
      (Finset.mem_image_of_mem (fun φ => ω ▹ φ) hp)
      (Finset.mem_image_of_mem (fun φ => ω ▹ φ) hn)).mono le_rfl (Nat.zero_le c)⟩
  | @axTrue Γ k b r v htrue hmem =>
    intro _ ω
    -- **DESIGN PIVOT (lap 10):** `provable_rew` (renaming invariance) is NOT valid for the new
    -- `axTrue` leaf when the literal is OPEN: `ω ▹ (signedLit b r v)` is true-under-`id` iff the
    -- literal is true under the `ω`-composed assignment, which renaming need not preserve. The fix
    -- is the **assignment-carrying embedding** (`∀ e, ZProvable (Γ.image (ρe ▹))`, `ρe := Rew.rewrite
    -- (nm∘e)`): there ALL sequents are CLOSED, `ω ▹ (closed lit) = lit` and truth is preserved, so
    -- this case is trivial (re-apply `axTrue`) — AND `provable_rew` is then only ever needed for
    -- closed renamings (mostly identity). The naive (open) `embed`/`provable_rew`/`shift`/`all` of
    -- lap 9–10 are SUPERSEDED by the closed form. See HANDOFF/PENDING (M4 next thread).
    sorry
  | verumR h =>
    intro _ ω
    exact ⟨0, (Provable.verumR
      (by have := Finset.mem_image_of_mem (fun φ => ω ▹ φ) h; simpa using this)).mono le_rfl (Nat.zero_le c)⟩
  | @weak Δ Γ d hsub ih =>
    intro hcr ω
    obtain ⟨α, h⟩ := ih (by simpa [cr] using hcr) ω
    exact ⟨α, h.weakening (Finset.image_subset_image hsub)⟩
  | @andI Γ φ ψ dφ dψ ihφ ihψ =>
    intro hcr ω
    simp only [cr] at hcr
    obtain ⟨a1, h1⟩ := ihφ (le_trans (le_max_left _ _) hcr) ω
    obtain ⟨a2, h2⟩ := ihψ (le_trans (le_max_right _ _) hcr) ω
    rw [Finset.image_insert] at h1 h2
    refine ⟨max a1 a2 + 1, ?_⟩
    have := Provable.andI (ω ▹ φ) (ω ▹ ψ) h1 h2
    rw [Finset.image_insert]; simpa using this
  | @orI Γ φ ψ d ih =>
    intro hcr ω
    obtain ⟨a, h⟩ := ih (by simpa [cr] using hcr) ω
    rw [Finset.image_insert, Finset.image_insert] at h
    refine ⟨a + 1, ?_⟩
    have := Provable.orI (ω ▹ φ) (ω ▹ ψ) h
    rw [Finset.image_insert]; simpa using this
  | @allω Γ φ d ih =>
    intro hcr ω
    simp only [cr] at hcr
    have hfam : ∀ n, ∃ a, Provable a c (insert ((ω.q ▹ φ)/[nm n]) (Γ.image (fun ψ => ω ▹ ψ))) := by
      intro n
      obtain ⟨a, ha⟩ := ih n (le_trans (le_iSup (fun m => cr (d m)) n) hcr) ω
      rw [Finset.image_insert, rew_subst_nm ω φ n] at ha
      exact ⟨a, ha⟩
    choose β hβ using hfam
    refine ⟨(⨆ n, β n) + 1, ?_⟩
    have := Provable.allω (ω.q ▹ φ) (Γ := Γ.image (fun ψ => ω ▹ ψ)) hβ
    rw [Finset.image_insert]; simpa [Rewriting.app_all] using this
  | @exI Γ φ n d ih =>
    intro hcr ω
    obtain ⟨a, h⟩ := ih (by simpa [cr] using hcr) ω
    rw [Finset.image_insert, rew_subst_nm ω φ n] at h
    refine ⟨a + 1, ?_⟩
    have := Provable.exI (ω.q ▹ φ) n h
    rw [Finset.image_insert]; simpa [Rewriting.app_exs] using this
  | @cut Γ φ d₁ d₂ ih₁ ih₂ =>
    intro hcr ω
    simp only [cr] at hcr
    obtain ⟨a1, h1⟩ := ih₁ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hcr)) ω
    obtain ⟨a2, h2⟩ := ih₂ (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hcr)) ω
    rw [Finset.image_insert] at h1 h2
    refine ⟨max a1 a2 + 1, ?_⟩
    have hcω : ((ω ▹ φ).complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := by
      rw [Semiformula.complexity_rew]; exact le_trans (le_max_left _ _) hcr
    have := Provable.cut (ω ▹ φ) hcω h1 (by simpa using h2)
    exact this

/-- **`Provable`-level renaming invariance** (existential bounds), the form the embedding consumes.
`shift` is the special case `ω = Rew.shift`. -/
theorem ZProvable.rew (ω : Rew ℒₒᵣ ℕ 0 ℕ 0) {Γ : ZinftyF.Seq} :
    ZProvable Γ → ZProvable (Γ.image (fun φ => ω ▹ φ)) := by
  rintro ⟨α, c, d, _, hcr⟩
  obtain ⟨α', h⟩ := provable_rew c d hcr ω
  exact ⟨α', c, h⟩

/-- **The embedding (M4), Finset form.** Every Foundation `Derivation2` from the `𝗣𝗔` schema embeds
into the infinitary `Z_∞` calculus. Structural rules are mapped; the four remaining non-structural
cases (`axm`/`all`/`exs`/`shift`) are the disclosed deep obligations (see header). -/
theorem embed {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) : ZProvable Γ := by
  induction d with
  | closed Γ φ hp hn =>
    obtain ⟨a, hd⟩ := provable_em φ hp hn
    exact ⟨a, 0, hd⟩
  | axm φ hφ hΓ =>
    -- `φ ∈ (𝗣𝗔 : Schema)`, i.e. `φ = ↑σ`, `σ ∈ 𝗣𝗔⁻ + InductionScheme`. Each Z∞-derivable:
    --   PeanoMinus = finite true ∀-sentences; `univCl (succInd ψ)` via the ω-rule. THE deep case.
    sorry
  | verum hΓ =>
    exact ⟨0, 0, Provable.verumR hΓ⟩
  | @and Γ φ ψ h _dp _dq ihp ihq =>
    obtain ⟨a1, c1, h1⟩ := ihp
    obtain ⟨a2, c2, h2⟩ := ihq
    refine ⟨max a1 a2 + 1, max c1 c2, ?_⟩
    have h1' := h1.mono (le_refl a1) (le_max_left c1 c2)
    have h2' := h2.mono (le_refl a2) (le_max_right c1 c2)
    have hand := Provable.andI φ ψ h1' h2'
    rwa [Finset.insert_eq_self.mpr h] at hand
  | @or Γ φ ψ h _d ih =>
    obtain ⟨a, c, hd⟩ := ih
    refine ⟨a + 1, c, ?_⟩
    have hor := Provable.orI φ ψ hd
    rwa [Finset.insert_eq_self.mpr h] at hor
  | @all Γ φ h _d ih =>
    -- The IH derives `insert (free φ) (Γ.image shift)`. For each numeral `n`, the renaming
    -- enabler `provable_rew` substitutes the freed variable `&0` by `nm n` — which simultaneously
    -- undoes the `shift` on `Γ` (`rewrite_comp_shift_eq_id`) — producing `insert (φ/[nm n]) Γ`.
    -- The ω-rule `allω` collects this ℕ-family into `insert (∀⁰φ) Γ = Γ`.
    obtain ⟨_, c, d, _ho, hcr⟩ := ih
    have hfam : ∀ n, ∃ a, Provable a c (insert (φ/[nm n]) Γ) := by
      intro n
      obtain ⟨a, ha⟩ := provable_rew c d hcr (Rew.rewrite (nm n :>ₙ fun x => &x))
      refine ⟨a, ?_⟩
      have key : (insert (Rewriting.free φ) (Γ.image Rewriting.shift)).image
            (fun ψ => (Rew.rewrite (nm n :>ₙ fun x => &x)) ▹ ψ) = insert (φ/[nm n]) Γ := by
        rw [Finset.image_insert, LawfulSyntacticRewriting.rewrite_free_eq_subst,
          Finset.image_image]
        congr 1
        refine Eq.trans (Finset.image_congr (fun ψ _ => ?_) ) Finset.image_id
        show (Rew.rewrite (nm n :>ₙ fun x => &x)) ▹ (Rew.shift ▹ ψ) = id ψ
        rw [← TransitiveRewriting.comp_app, Rew.rewrite_comp_shift_eq_id,
          ReflectiveRewriting.id_app, id_eq]
      rwa [key] at ha
    choose β hβ using hfam
    have hall := Provable.allω φ hβ
    rw [Finset.insert_eq_self.mpr h] at hall
    exact ⟨_, c, hall⟩
  | @exs Γ φ h t _d _ih =>
    -- witness term `t` → numeral (term-model eval), then `exI`. DEEP.
    sorry
  | @wk Δ Γ _d h ih =>
    exact ih.weakening h
  | @shift Γ _d ih =>
    -- `Rewriting.shift φ = Rew.shift ▹ φ`, so this is exactly the renaming enabler at `ω = shift`.
    have h := ZProvable.rew Rew.shift ih
    simpa [Rewriting.shift] using h
  | @cut Γ φ _d _dn ihd ihdn =>
    obtain ⟨a1, c1, h1⟩ := ihd
    obtain ⟨a2, c2, h2⟩ := ihdn
    refine ⟨max a1 a2 + 1, max (φ.complexity + 1) (max c1 c2), ?_⟩
    have h1' := h1.mono (le_refl a1)
      (show c1 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_left c1 c2) (le_max_right _ _))
    have h2' := h2.mono (le_refl a2)
      (show c2 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_right c1 c2) (le_max_right _ _))
    have hc : ((φ.complexity + 1 : ℕ) : ℕ∞) ≤ ((max (φ.complexity + 1) (max c1 c2) : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.le_max_left _ _
    exact Provable.cut φ hc h1' h2'


/-! ## Closed-term existential introduction (ported from wip/ScratchEmCong.lean, lap 11)
    The shared chip for `embedC`'s `exs`/`axm`: a value-congruent law of excluded middle
    (`provable_em_cong_gen`) ⟹ closed-term `∃`-intro `Provable.exI_closed`. -/

/-- Substitution-composition: substituting the freed (q) variable by `nm m` after a renaming
`Rew.subst w` is the same as substituting by the extended vector `nm m :> w`. -/
lemma subst_q_cons (w : Fin n → SyntacticTerm ℒₒᵣ) (m : ℕ) :
    (Rew.subst ![nm m]).comp (Rew.subst w).q = Rew.subst (nm m :> w) := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ i => simp [Rew.comp_app]
  · simp [Rew.comp_app]

/-- Formula form: `((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ`. -/
lemma subst_q_cons_app (w : Fin n → SyntacticTerm ℒₒᵣ) (m : ℕ)
    (ψ : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    ((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ := by
  show Rew.subst ![nm m] ▹ ((Rew.subst w).q ▹ ψ) = Rew.subst (nm m :> w) ▹ ψ
  rw [← TransitiveRewriting.comp_app, subst_q_cons]

/-- Value of a renamed term depends only on the values of the substituted terms. -/
lemma valm_subst_congr {n} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
                = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i))
    (t : SyntacticSemiterm ℒₒᵣ n) :
    Semiterm.valm ℕ ![] (id : ℕ → ℕ) (Rew.subst w t)
      = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (Rew.subst w' t) := by
  simp only [Semiterm.valm, Semiterm.val_substs]
  congr 1
  funext x; exact hval x

/-- Literal-truth congruence under value-equal substitutions. -/
lemma litTrue_subst_congr {n} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
                = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i))
    (b : Bool) {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticSemiterm ℒₒᵣ n) :
    LitTrue (signedLit b r (fun i => Rew.subst w (v i)))
      ↔ LitTrue (signedLit b r (fun i => Rew.subst w' (v i))) := by
  have hv : (fun i => Semiterm.valm ℕ ![] (id : ℕ → ℕ) (Rew.subst w (v i)))
          = (fun i => Semiterm.valm ℕ ![] (id : ℕ → ℕ) (Rew.subst w' (v i))) := by
    funext i; exact valm_subst_congr w w' hval (v i)
  cases b <;>
    simp only [signedLit, LitTrue, Semiformula.eval_rel, Semiformula.eval_nrel, hv]

/-- The numeral `nm m` evaluates to `m` in the standard ℕ-model (any free assignment). -/
lemma valm_nm (m : ℕ) (f : ℕ → ℕ) : Semiterm.valm ℕ ![] f (nm m) = m := by
  simp [nm]

/-- **Value-congruent excluded middle (arity-general).** -/
theorem provable_em_cong_gen : ∀ (k : ℕ) {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (ψ : SyntacticSemiformula ℒₒᵣ n), ψ.complexity ≤ k →
    (∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
        = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i)) →
    ∀ {Γ : Seq}, (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ → ∃ a, Provable a 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro n w w' ψ hk hval Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
    | hrel r v => exact atomic_close w w' hval r v hp hn
    | hnrel r v => exact atomic_close_neg w w' hval r v hp hn
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro n w w' ψ hk hval Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
    | hrel r v => exact atomic_close w w' hval r v hp hn
    | hnrel r v => exact atomic_close_neg w w' hval r v hp hn
    | hand a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
      have hn' : (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
      obtain ⟨a1, h1⟩ := ih (n := n) w w' a hak hval
        (Γ := insert (Rew.subst w ▹ a)
          (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
        (by simp) (by simp)
      obtain ⟨a2, h2⟩ := ih (n := n) w w' b hbk hval
        (Γ := insert (Rew.subst w ▹ b)
          (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
        (by simp) (by simp)
      have hand := Provable.andI (Rew.subst w ▹ a) (Rew.subst w ▹ b) h1 h2
      rw [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b))
        ∈ insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ) by simp [hp'])] at hand
      have hor := Provable.orI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) hand
      rw [Finset.insert_eq_self.mpr hn'] at hor
      exact ⟨_, hor⟩
    | hor a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
      have hn' : (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
      obtain ⟨a1, h1⟩ := ih (n := n) w w' a hak hval
        (Γ := insert (∼(Rew.subst w' ▹ a))
          (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
        (by simp) (by simp)
      obtain ⟨a2, h2⟩ := ih (n := n) w w' b hbk hval
        (Γ := insert (∼(Rew.subst w' ▹ b))
          (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
        (by simp) (by simp)
      have hand := Provable.andI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) h1 h2
      rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))]
        at hand
      have hor := Provable.orI (Rew.subst w ▹ a) (Rew.subst w ▹ b) hand
      rw [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ
        by simp [hp'])] at hor
      exact ⟨_, hor⟩
    | hall a =>
      -- ψ = ∀⁰a ; positive side ∀⁰((subst w).q ▹ a), negative side ∃⁰((subst w').q ▹ ∼a)
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, ∃ x, Provable x 0 (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ) := by
        intro m
        have hvalm : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w) i)
            = Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w') i) := by
          intro i; cases i using Fin.cases with
          | zero => rfl
          | succ j => simpa using hval j
        obtain ⟨x, hx⟩ := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        -- reconstruct ∃⁰((subst w').q ▹ ∼a) via exI with witness m
        have hexI := Provable.exI ((Rew.subst w').q ▹ ∼a) m
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)
          (by
            have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
            rw [heq, Finset.insert_comm]; exact hx)
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hn')] at hexI
        exact ⟨_, hexI⟩
      choose β hβ using fam
      have hallω := Provable.allω ((Rew.subst w).q ▹ a) hβ
      rw [Finset.insert_eq_self.mpr hp'] at hallω
      exact ⟨_, hallω⟩
    | hexs a =>
      -- ψ = ∃⁰a ; positive side ∃⁰((subst w).q ▹ a), negative side ∀⁰((subst w').q ▹ ∼a)
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, ∃ x, Provable x 0 (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ) := by
        intro m
        have hvalm : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w) i)
            = Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w') i) := by
          intro i; cases i using Fin.cases with
          | zero => rfl
          | succ j => simpa using hval j
        obtain ⟨x, hx⟩ := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        -- reconstruct ∃⁰((subst w).q ▹ a) via exI with witness m
        have hexI := Provable.exI ((Rew.subst w).q ▹ a) m
          (Γ := insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ) hx
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp')] at hexI
        have heq : (((Rew.subst w').q ▹ ∼a)/[nm m]) = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
        rw [heq]; exact ⟨_, hexI⟩
      choose β hβ using fam
      have hallω := Provable.allω ((Rew.subst w').q ▹ ∼a) hβ
      rw [Finset.insert_eq_self.mpr hn'] at hallω
      exact ⟨_, hallω⟩
where
  atomic_close {n} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
      (hval : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
                = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i))
      {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticSemiterm ℒₒᵣ n)
      {Γ : Seq} (hp : (Rew.subst w ▹ Semiformula.rel r v) ∈ Γ)
      (hn : (∼(Rew.subst w' ▹ Semiformula.rel r v)) ∈ Γ) : ∃ a, Provable a 0 Γ := by
    have hp' : signedLit true r (fun i => Rew.subst w (v i)) ∈ Γ := by
      simpa [signedLit, Semiformula.rew_rel] using hp
    have hn' : signedLit false r (fun i => Rew.subst w' (v i)) ∈ Γ := by
      simpa [signedLit, Semiformula.rew_rel] using hn
    rcases litTrue_or_neg (signedLit true r (fun i => Rew.subst w (v i))) with htt | htf
    · exact ⟨0, Provable.axTrue true r _ htt hp'⟩
    · rw [neg_lit] at htf
      have htf' : LitTrue (signedLit false r (fun i => Rew.subst w' (v i))) :=
        (litTrue_subst_congr w w' hval false r v).mp htf
      exact ⟨0, Provable.axTrue false r _ htf' hn'⟩
  atomic_close_neg {n} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
      (hval : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
                = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i))
      {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticSemiterm ℒₒᵣ n)
      {Γ : Seq} (hp : (Rew.subst w ▹ Semiformula.nrel r v) ∈ Γ)
      (hn : (∼(Rew.subst w' ▹ Semiformula.nrel r v)) ∈ Γ) : ∃ a, Provable a 0 Γ := by
    have hp' : signedLit false r (fun i => Rew.subst w (v i)) ∈ Γ := by
      simpa [signedLit, Semiformula.rew_nrel] using hp
    have hn' : signedLit true r (fun i => Rew.subst w' (v i)) ∈ Γ := by
      simpa [signedLit, Semiformula.rew_nrel] using hn
    rcases litTrue_or_neg (signedLit false r (fun i => Rew.subst w (v i))) with htt | htf
    · exact ⟨0, Provable.axTrue false r _ htt hp'⟩
    · rw [neg_lit] at htf
      have htf' : LitTrue (signedLit true r (fun i => Rew.subst w' (v i))) :=
        (litTrue_subst_congr w w' hval true r v).mp htf
      exact ⟨0, Provable.axTrue true r _ htf' hn'⟩

/-- **Value-congruent excluded middle (single-term form).** For closed terms `s, s'` of equal
standard value, a sequent containing `ψ/[s]` and `∼(ψ/[s'])` is `Z∞`-derivable cut-free. -/
theorem provable_em_cong (s s' : SyntacticTerm ℒₒᵣ)
    (hval : Semiterm.valm ℕ ![] (id : ℕ → ℕ) s = Semiterm.valm ℕ ![] (id : ℕ → ℕ) s')
    (ψ : SyntacticSemiformula ℒₒᵣ 1) {Γ : Seq}
    (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) : ∃ a, Provable a 0 Γ := by
  refine provable_em_cong_gen ψ.complexity ![s] ![s'] ψ le_rfl ?_ ?_ ?_
  · intro i; cases i using Fin.cases with
    | zero => simpa using hval
    | succ j => exact j.elim0
  · exact hp
  · exact hn

/-- **Closed-term existential introduction.** From a derivation of `insert (ψ/[s]) Γ` for ANY
(closed) witness term `s`, conclude `insert (∃⁰ψ) Γ`. The witness need not be a numeral: `s` is
collapsed to its standard value `m` via `provable_em_cong` + `cut`, then the numeral-witness rule
`Provable.exI` applies. (The cut raises the cut-rank bound to `max c (ψ.complexity + 1)`.) -/
theorem Provable.exI_closed {α : Ordinal.{0}} {c : ℕ} {Γ : Seq}
    (ψ : SyntacticSemiformula ℒₒᵣ 1) (s : SyntacticTerm ℒₒᵣ)
    (h : Provable α c (insert (ψ/[s]) Γ)) :
    ∃ β, Provable β (max c (ψ.complexity + 1)) (insert (∃⁰ ψ) Γ) := by
  set m : ℕ := Semiterm.valm ℕ ![] (id : ℕ → ℕ) s with hm
  set c' : ℕ := max c (ψ.complexity + 1) with hc'
  have hsval : Semiterm.valm ℕ ![] (id : ℕ → ℕ) (nm m)
             = Semiterm.valm ℕ ![] (id : ℕ → ℕ) s := by rw [valm_nm]
  -- left cut premise: ψ/[s] available (from h, weakened to add ψ/[nm m])
  have h₁ : Provable α c' (insert (ψ/[s]) (insert (ψ/[nm m]) Γ)) :=
    (h.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))).mono le_rfl
      (le_max_left _ _)
  -- right cut premise: ∼(ψ/[s]) and ψ/[nm m] — value-congruent em (nm m vs s, equal values)
  obtain ⟨b, h₂⟩ := provable_em_cong (nm m) s hsval ψ
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[nm m]) Γ)) (by simp) (by simp)
  -- cut on χ = ψ/[s]
  have hcc : (((ψ/[s]).complexity : ℕ) + 1 : ℕ∞) ≤ (c' : ℕ∞) := by
    have : (ψ/[s]).complexity = ψ.complexity := by simp
    rw [this]; exact_mod_cast le_max_right _ _
  have hcut := Provable.cut (ψ/[s]) hcc h₁ (h₂.mono le_rfl (le_max_left _ _))
  -- hcut : Provable _ c' (insert (ψ/[nm m]) Γ); introduce ∃ by exI with numeral m
  exact ⟨_, Provable.exI ψ m hcut⟩



/-- **ω-completeness for true closed formulas.** Any closed (`SyntacticFormula ℒₒᵣ`) formula that is
TRUE in the standard model `ℕ` (`LitTrue`) is `Z∞`-derivable, cut-free. Proof by induction on
`complexity`: atomic via `axTrue`, `∀` via the ω-rule `allω`, `∃` by choosing a true witness. -/
theorem provable_true : ∀ (k : ℕ) (φ : Form), φ.complexity ≤ k → LitTrue φ →
    ∀ {Γ : Seq}, φ ∈ Γ → ∃ a, Provable a 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro φ hk htrue Γ hmem
    cases φ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR hmem⟩
    | hfalsum => simp [LitTrue] at htrue
    | hrel r v => exact ⟨0, Provable.axTrue true r v htrue hmem⟩
    | hnrel r v => exact ⟨0, Provable.axTrue false r v htrue hmem⟩
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro φ hk htrue Γ hmem
    cases φ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR hmem⟩
    | hfalsum => simp [LitTrue] at htrue
    | hrel r v => exact ⟨0, Provable.axTrue true r v htrue hmem⟩
    | hnrel r v => exact ⟨0, Provable.axTrue false r v htrue hmem⟩
    | hand a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have htab : LitTrue a ∧ LitTrue b := by simpa [LitTrue] using htrue
      obtain ⟨hta, htb⟩ := htab
      obtain ⟨a1, h1⟩ := ih a hak hta (Γ := insert a Γ) (by simp)
      obtain ⟨a2, h2⟩ := ih b hbk htb (Γ := insert b Γ) (by simp)
      have hand := Provable.andI a b h1 h2
      rw [Finset.insert_eq_self.mpr hmem] at hand
      exact ⟨_, hand⟩
    | hor a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have htor : LitTrue a ∨ LitTrue b := by simpa [LitTrue] using htrue
      rcases htor with hta | htb
      · obtain ⟨a1, h1⟩ := ih a hak hta (Γ := insert a (insert b Γ)) (by simp)
        have hor := Provable.orI a b h1
        rw [Finset.insert_eq_self.mpr hmem] at hor
        exact ⟨_, hor⟩
      · obtain ⟨a1, h1⟩ := ih b hbk htb (Γ := insert a (insert b Γ)) (by simp)
        have hor := Provable.orI a b h1
        rw [Finset.insert_eq_self.mpr hmem] at hor
        exact ⟨_, hor⟩
    | hall a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hfam : ∀ n, LitTrue (a/[nm n]) := by
        intro n
        have := htrue
        simp only [LitTrue, Semiformula.eval_all] at this
        simpa [LitTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton]
          using this n
      have fam : ∀ n, ∃ x, Provable x 0 (insert (a/[nm n]) Γ) := by
        intro n
        have hcomp : (a/[nm n]).complexity ≤ k := by
          have : (a/[nm n]).complexity = a.complexity := by simp
          rw [this]; exact hak
        exact ih (a/[nm n]) hcomp (hfam n) (by simp)
      choose β hβ using fam
      have hallω := Provable.allω a hβ
      rw [Finset.insert_eq_self.mpr hmem] at hallω
      exact ⟨_, hallω⟩
    | hexs a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hex : ∃ n, LitTrue (a/[nm n]) := by
        have := htrue
        simp only [LitTrue, Semiformula.eval_ex] at this
        obtain ⟨x, hx⟩ := this
        exact ⟨x, by simpa [LitTrue, Semiformula.eval_substs, valm_nm,
          Matrix.constant_eq_singleton] using hx⟩
      obtain ⟨n, hn⟩ := hex
      have hcomp : (a/[nm n]).complexity ≤ k := by
        have : (a/[nm n]).complexity = a.complexity := by simp
        rw [this]; exact hak
      obtain ⟨x, hx⟩ := ih (a/[nm n]) hcomp hn (Γ := insert (a/[nm n]) Γ) (by simp)
      have hexI := Provable.exI a n hx
      rw [Finset.insert_eq_self.mpr hmem] at hexI
      exact ⟨_, hexI⟩



/-! ## The assignment-carrying (all-closed) embedding `embedC` — the correct frame (lap 10)

The naive `embed` above cannot finish (`exs` with an open witness; `provable_rew` invalid for the new
`axTrue` leaf). The fix is to carry a **numeral assignment** `e : ℕ → ℕ` of the free variables, so
every sequent in the image is CLOSED. `asg e` substitutes every free variable `&x` by the numeral
`nm (e x)`. The headline consumes `embedC d (fun _ => 0)` on the closed `↑goodsteinSentence`. -/

/-- The closing substitution: free variable `&x ↦ nm (e x)`. Sends every `SyntacticFormula` to a
closed formula (sentence image). -/
noncomputable def asg (e : ℕ → ℕ) : Rew ℒₒᵣ ℕ 0 ℕ 0 := Rew.rewrite (fun x => nm (e x))

/-- **The embedding, assignment-carrying form.** Every `Derivation2` from `𝗣𝗔` embeds into `Z_∞`
*at every numeral assignment of its free variables* (all sequents closed). Structural cases done;
`all`/`exs`/`axm` are the disclosed deep obligations (the latter two now unblocked by `axTrue`). -/
theorem embedC {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) :
    ∃ c : ℕ, ∀ e : ℕ → ℕ, ∃ α, Provable α c (Γ.image (fun φ => asg e ▹ φ)) := by
  induction d with
  | closed Γ φ hp hn =>
    exact ⟨0, fun e => provable_em (asg e ▹ φ) (Finset.mem_image_of_mem _ hp)
      (by have := Finset.mem_image_of_mem (fun φ => asg e ▹ φ) hn; simpa using this)⟩
  | axm φ hφ hΓ =>
    -- closed PA axiom `φ = ↑σ`, `σ ∈ 𝗣𝗔`. Since `ℕ ⊧ₘ* 𝗣𝗔`, `↑σ` is a TRUE closed formula, so
    -- (even after the closing substitution `asg e`, which fixes it) `provable_true` (ω-completeness)
    -- derives it directly — no Buchholz meta-induction needed; the ω-rule subsumes it.
    obtain ⟨σ, hσ, rfl⟩ := hφ
    refine ⟨0, fun e => ?_⟩
    have htrue : LitTrue (asg e ▹ (↑σ : SyntacticFormula ℒₒᵣ)) := by
      have hmod : ℕ ⊧ₘ σ := ModelsTheory.models ℕ hσ
      simp only [LitTrue, asg, Semiformula.eval_rewrite, Semiformula.eval_emb]
      rw [models_iff] at hmod
      simpa using hmod
    exact provable_true _ _ le_rfl htrue (Finset.mem_image_of_mem _ hΓ)
  | verum hΓ =>
    exact ⟨0, fun e => ⟨0, Provable.verumR
      (by have := Finset.mem_image_of_mem (fun φ => asg e ▹ φ) hΓ; simpa using this)⟩⟩
  | @and Γ φ ψ h _dp _dq ihp ihq =>
    obtain ⟨c1, ihp⟩ := ihp; obtain ⟨c2, ihq⟩ := ihq
    refine ⟨max c1 c2, fun e => ?_⟩
    obtain ⟨a1, h1⟩ := ihp e; obtain ⟨a2, h2⟩ := ihq e
    rw [Finset.image_insert] at h1 h2
    have h1' := h1.mono (le_refl a1) (le_max_left c1 c2)
    have h2' := h2.mono (le_refl a2) (le_max_right c1 c2)
    have hand := Provable.andI (asg e ▹ φ) (asg e ▹ ψ) h1' h2'
    have hmem : (asg e ▹ φ ⋏ asg e ▹ ψ) ∈ Γ.image (fun φ => asg e ▹ φ) := by
      have := Finset.mem_image_of_mem (fun φ => asg e ▹ φ) h; simpa using this
    rw [Finset.insert_eq_self.mpr hmem] at hand
    exact ⟨_, hand⟩
  | @or Γ φ ψ h _d ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    obtain ⟨a, hd⟩ := ih e
    rw [Finset.image_insert, Finset.image_insert] at hd
    have hor := Provable.orI (asg e ▹ φ) (asg e ▹ ψ) hd
    have hmem : (asg e ▹ φ ⋎ asg e ▹ ψ) ∈ Γ.image (fun φ => asg e ▹ φ) := by
      have := Finset.mem_image_of_mem (fun φ => asg e ▹ φ) h; simpa using this
    rw [Finset.insert_eq_self.mpr hmem] at hor
    exact ⟨_, hor⟩
  | @all Γ φ h _d ih =>
    -- `∀⁰φ ∈ Γ`. Introduce by `allω`: for each `n`, use `ih (n :>ₙ e)` — the freed var `&0 ↦ nm n`
    -- (A), the shifted `Γ` collapses to the `asg e` image (B). The clean ω-rule case (uniform `c`).
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    have hfam : ∀ n, ∃ a, Provable a c
        (insert (((asg e).q ▹ φ)/[nm n]) (Γ.image (fun ψ => asg e ▹ ψ))) := by
      intro n
      obtain ⟨a, hd⟩ := ih (n :>ₙ e)
      rw [Finset.image_insert] at hd
      have hA : asg (n :>ₙ e) ▹ (Rewriting.free φ) = ((asg e).q ▹ φ)/[nm n] := by
        have hRew : (asg (n :>ₙ e)).comp Rew.free = (Rew.subst ![nm n]).comp (asg e).q := by
          ext x
          · refine Fin.cases ?_ (fun i => Fin.elim0 i) x
            simp [asg, Rew.comp_app]
          · simp [asg, Rew.comp_app]
        show asg (n :>ₙ e) ▹ (Rew.free ▹ φ) = Rew.subst ![nm n] ▹ ((asg e).q ▹ φ)
        rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hRew]
      have hB : (Γ.image Rewriting.shift).image (fun ψ => asg (n :>ₙ e) ▹ ψ)
          = Γ.image (fun ψ => asg e ▹ ψ) := by
        have hcompB : (asg (n :>ₙ e)).comp Rew.shift = asg e := by
          ext x
          · exact Fin.elim0 x
          · simp [asg, Rew.comp_app]
        rw [Finset.image_image]
        refine Finset.image_congr (fun ψ _ => ?_)
        show asg (n :>ₙ e) ▹ (Rew.shift ▹ ψ) = asg e ▹ ψ
        rw [← TransitiveRewriting.comp_app, hcompB]
      rw [hA, hB] at hd
      exact ⟨a, hd⟩
    choose β hβ using hfam
    have hall := Provable.allω ((asg e).q ▹ φ) hβ
    have hmem : (asg e ▹ (∀⁰ φ)) ∈ Γ.image (fun ψ => asg e ▹ ψ) := Finset.mem_image_of_mem _ h
    rw [show (asg e ▹ (∀⁰ φ)) = ∀⁰ ((asg e).q ▹ φ) by simp] at hmem
    rw [Finset.insert_eq_self.mpr hmem] at hall
    exact ⟨_, hall⟩
  | @exs Γ φ h t _d ih =>
    -- `∃⁰φ ∈ Γ`, witness `t`. `rew_subst_term` turns the IH's `asg e ▹ (φ/[t])` into
    -- `((asg e).q ▹ φ)/[asg e t]` with `asg e t` CLOSED. The remaining `sorry` is the **closed-term
    -- collapse** `Provable (insert (ψ/[s]) Γ) → Provable (insert (∃⁰ψ) Γ)` for closed `s` (value `m`):
    -- a `Provable.exI_closed` derived from `Provable.exI` + Z∞ equality-congruence (`s = nm m` via
    -- `axTrue`, then Leibniz). The term-evaluation content — next chip.
    obtain ⟨c, ih⟩ := ih
    refine ⟨max c (φ.complexity + 1), fun e => ?_⟩
    obtain ⟨a, hd⟩ := ih e
    rw [Finset.image_insert, rew_subst_term (asg e) φ t] at hd
    -- hd : Provable a c (insert (((asg e).q ▹ φ)/[asg e t]) (Γ.image (asg e ▹)))
    obtain ⟨β, hβ⟩ := Provable.exI_closed ((asg e).q ▹ φ) (asg e t) hd
    -- hβ : Provable β (max c (((asg e).q▹φ).complexity+1)) (insert (∃⁰((asg e).q▹φ)) (Γ.image (asg e▹)))
    have hcomp : (((asg e).q ▹ φ).complexity + 1) = (φ.complexity + 1) := by simp
    rw [hcomp] at hβ
    have hmem : (asg e ▹ (∃⁰ φ)) ∈ Γ.image (fun ψ => asg e ▹ ψ) := Finset.mem_image_of_mem _ h
    rw [show (asg e ▹ (∃⁰ φ)) = ∃⁰ ((asg e).q ▹ φ) by simp] at hmem
    rw [Finset.insert_eq_self.mpr hmem] at hβ
    exact ⟨_, hβ⟩
  | @wk Δ Γ _d h ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    obtain ⟨α, hα⟩ := ih e
    exact ⟨α, hα.weakening (Finset.image_subset_image h)⟩
  | @shift Γ _d ih =>
    -- re-index the assignment: `asg e ∘ Rew.shift = asg (e ∘ succ)`.
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    have hcomp : (asg e).comp Rew.shift = asg (e ∘ Nat.succ) := by
      ext x
      · exact Fin.elim0 x
      · simp [asg, Rew.comp_app]
    have key : (Γ.image Rewriting.shift).image (fun φ => asg e ▹ φ)
        = Γ.image (fun φ => asg (e ∘ Nat.succ) ▹ φ) := by
      rw [Finset.image_image]
      refine Finset.image_congr (fun ψ _ => ?_)
      show asg e ▹ (Rew.shift ▹ ψ) = asg (e ∘ Nat.succ) ▹ ψ
      rw [← TransitiveRewriting.comp_app, hcomp]
    rw [key]; exact ih (e ∘ Nat.succ)
  | @cut Γ φ _d _dn ihd ihdn =>
    obtain ⟨c1, ihd⟩ := ihd; obtain ⟨c2, ihdn⟩ := ihdn
    refine ⟨max (φ.complexity + 1) (max c1 c2), fun e => ?_⟩
    obtain ⟨a1, h1⟩ := ihd e; obtain ⟨a2, h2⟩ := ihdn e
    rw [Finset.image_insert] at h1 h2
    rw [show (asg e ▹ (∼φ)) = ∼(asg e ▹ φ) by simp] at h2
    have h1' := h1.mono (le_refl a1)
      (show c1 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_left c1 c2) (le_max_right _ _))
    have h2' := h2.mono (le_refl a2)
      (show c2 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_right c1 c2) (le_max_right _ _))
    have hc : (((asg e ▹ φ).complexity + 1 : ℕ) : ℕ∞)
        ≤ ((max (φ.complexity + 1) (max c1 c2) : ℕ) : ℕ∞) := by
      rw [Semiformula.complexity_rew]; exact_mod_cast Nat.le_max_left _ _
    exact ⟨_, Provable.cut (asg e ▹ φ) hc h1' h2'⟩

end GoodsteinPA.Embedding
