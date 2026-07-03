import GoodsteinPA.OperatorZef2
import GoodsteinPA.WainerRoute
import GoodsteinPA.Embedding

/-!
# E-1 grind (Series-3) — `Zef2TC` (full E–W Def-23 rule set) + the budgeted EM lemma

Per the E-1 block-1 finding (`wip/E0Ax2NeedProbe.lean` § E-1 seam probe): `Zef2T` lacks the
connective rules the PA-proof embedding needs (`{⊤}` kernel-underivable even with (Ax2)).  This
file erects the AMENDED target calculus — **`Zef2TC` = `Zef2` + (Ax2) `trueRel`/`trueNrel` +
the finite `verumR`/`andI`/`orI`** (the `Zekd` shapes with the `Nlog` gate + `Cl`-operator
side conditions threaded, mirroring `weak`/`exI`) — and banks the first E–W Lemma-32 mechanism:

* `em_Zef2TC` — the **budgeted excluded middle** (the W3 `closed` case engine): any sequent
  containing `φ, ∼φ` is `Zef2TC`-derivable cut-free at the DETERMINISTIC ordinal
  `ofNat (2·complexity + 1)`, any slot `f` that is monotone + inflationary with
  `clog (2·complexity+1) ≤ f 0`.  Mirrors `Embedding.lean`'s `provable_em` with the full
  gate/ordinal bookkeeping; the ∀/∃ cases pair `allω` branches with `exI` at witness `n`
  (bound `n ≤ rel1 f n 0 = f n` — inflationarity), the finite cases ride `andI`/`orI`.

Everything here is wip-only ruling input (the `Zef2TC` amendment is flagged for the judge in
ledger block 6, NOT self-ratified); statements are new-machinery lemmas, not rung texts.  The
amended DRAFT `embedding_Zef2TC_DRAFT` re-bases the E-0 draft verbatim onto `Zef2TC`.
-/

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## `Zef2TC` — the full-rule-set target calculus -/

/-- **`Zef2TC`** — `Zef2` (verbatim, `Nlog` gates) + E–W (Ax2) (`trueRel`/`trueNrel`) + the
finite connective rules `verumR`/`andI`/`orI` (`Zekd` shapes; ordinal-descending premises with
the `weak`-style NF/`Cl` side conditions; slot UNCHANGED — E–W relativizes only the ω-rule). -/
inductive Zef2TC : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Seq → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef2TC α e H f c Γ
  | trueRel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hmem : Semiformula.rel r v ∈ Γ) : Zef2TC α e H f c Γ
  | trueNrel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hmem : Semiformula.nrel r v ∈ Γ) : Zef2TC α e H f c Γ
  | verumR {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0) (h : (⊤ : Form) ∈ Γ) : Zef2TC α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : Nlog α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2TC α e H f c Δ) :
      Zef2TC α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef2TC β e H f c Δ) : Zef2TC α e H f c Γ
  | andI {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (dφ : Zef2TC βφ e H f c (insert φ Γ)) (dψ : Zef2TC βψ e H f c (insert ψ Γ)) :
      Zef2TC α e H f c (insert (φ ⋏ ψ) Γ)
  | orI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (dd : Zef2TC β e H f c (insert φ (insert ψ Γ))) :
      Zef2TC α e H f c (insert (φ ⋎ ψ) Γ)
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef2TC (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef2TC α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef2TC β e H f c (insert (φ/[nm n]) Γ)) : Zef2TC α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : Form) (hcompl : φ.complexity < c) (hcutRead : φ.complexity ≤ f 0)
      (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef2TC βφ e H f c (insert φ Γ)) (d₂ : Zef2TC βψ e H f c (insert (∼φ) Γ)) :
      Zef2TC α e H f c Γ

namespace Zef2TC

theorem gate {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (dd : Zef2TC α e H f c Γ) : Nlog α ≤ f 0 := by
  cases dd <;> assumption

/-- `Zef2 ⊆ Zef2TC`. -/
theorem ofZef2 : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → Zef2TC α e H f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => exact Zef2TC.axL hαN r v hp hn
  | wk hαN hsub _ ih => exact Zef2TC.wk hαN hsub ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih => exact Zef2TC.weak hαN hβ hβNF hαNF hβH hsub ih
  | allω hαN φ β hβ hβNF hαNF hβH _ ih => exact Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ih
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      exact Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ih₁ ih₂

end Zef2TC

/-! ## Ordinal-ladder toolkit (`ofNat` rungs) -/

theorem ofNat_lt_ofNat {a b : ℕ} (h : a < b) : ONote.ofNat a < ONote.ofNat b := by
  rw [ONote.lt_def, ONote.repr_ofNat, ONote.repr_ofNat]
  exact_mod_cast h

theorem Nlog_ofNat_le (m : ℕ) : Nlog (ONote.ofNat m) ≤ clog m := by
  cases m with
  | zero => simp
  | succ k =>
      rw [show ONote.ofNat (k + 1) = ONote.oadd 0 k.succPNat 0 from rfl]
      simp [Nat.succPNat]

theorem clog_mono {a b : ℕ} (h : a ≤ b) : clog a ≤ clog b :=
  Nat.log_mono_right (by omega)

/-! ## The budgeted excluded middle (E–W Lemma 32 / the W3 `closed`-case engine) -/

/-- **Budgeted EM**: a sequent containing `φ, ∼φ` is cut-free `Zef2TC`-derivable at the
deterministic ordinal rung `ofNat (2k+1)` (`k ≥ complexity φ`), for ANY slot `f` monotone +
inflationary with `clog (2k+1) ≤ f 0`.  All hypotheses are `rel1`-stable, so the ω-cases
recurse at the relativized slots.  Mirrors `provable_em` (`Embedding.lean:71`). -/
theorem em_Zef2TC (k : ℕ) :
    ∀ (φ : Form), φ.complexity ≤ k →
    ∀ {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq},
      Monotone f → (∀ m, m ≤ f m) → clog (2 * k + 1) ≤ f 0 →
      φ ∈ Γ → ∼φ ∈ Γ → Zef2TC (ONote.ofNat (2 * k + 1)) e H f 0 Γ := by
  induction k with
  | zero =>
    intro φ hk e H f Γ hmono hinfl hgate hp hn
    have hgate' : Nlog (ONote.ofNat 1) ≤ f 0 := le_trans (Nlog_ofNat_le 1) hgate
    cases φ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hgate' hp
    | hfalsum => exact Zef2TC.verumR hgate' (by simpa using hn)
    | hrel r v => exact Zef2TC.axL hgate' r v hp (by simpa using hn)
    | hnrel r v => exact Zef2TC.axL hgate' r v (by simpa using hn) hp
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro φ hk e H f Γ hmono hinfl hgate hp hn
    -- rungs: IH at `ofNat (2k+1)`, connective/witness node at `ofNat (2k+2)`,
    -- root at `ofNat (2k+3) = ofNat (2·(k+1)+1)`
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at hgate ⊢
    have hNF : ∀ m : ℕ, (ONote.ofNat m).NF := fun m => ONote.nf_ofNat m
    have hlt12 : ONote.ofNat (2 * k + 1) < ONote.ofNat (2 * k + 2) := ofNat_lt_ofNat (by omega)
    have hlt23 : ONote.ofNat (2 * k + 2) < ONote.ofNat (2 * k + 3) := ofNat_lt_ofNat (by omega)
    have hlt13 : ONote.ofNat (2 * k + 1) < ONote.ofNat (2 * k + 3) := ofNat_lt_ofNat (by omega)
    have hroot : Nlog (ONote.ofNat (2 * k + 3)) ≤ f 0 := le_trans (Nlog_ofNat_le _) hgate
    have hg2 : Nlog (ONote.ofNat (2 * k + 2)) ≤ f 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (clog_mono (by omega)) hgate)
    have hg1 : clog (2 * k + 1) ≤ f 0 := le_trans (clog_mono (by omega)) hgate
    cases φ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hroot hp
    | hfalsum => exact Zef2TC.verumR hroot (by simpa using hn)
    | hrel r v => exact Zef2TC.axL hroot r v hp (by simpa using hn)
    | hnrel r v => exact Zef2TC.axL hroot r v (by simpa using hn) hp
    | hand φ ψ =>
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have h1 := ih φ hφk (e := e) (H := H) (f := f)
          (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ))) hmono hinfl hg1 (by simp) (by simp)
        have h2 := ih ψ hψk (e := e) (H := H) (f := f)
          (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ))) hmono hinfl hg1 (by simp) (by simp)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 2)) hg2 φ ψ hlt12 hlt12
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rw [Finset.insert_eq_self.mpr
          (show (φ ⋏ ψ) ∈ insert (∼φ) (insert (∼ψ) Γ) by simp [hp])] at hand
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot (∼φ) (∼ψ) hlt23
          (hNF _) (hNF _) (Cl.ofNat _) hand
        rwa [Finset.insert_eq_self.mpr (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn)] at hor
    | hor φ ψ =>
        have hn' : (∼φ ⋏ ∼ψ) ∈ Γ := by simpa using hn
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have h1 := ih φ hφk (e := e) (H := H) (f := f)
          (Γ := insert (∼φ) (insert φ (insert ψ Γ))) hmono hinfl hg1 (by simp) (by simp)
        have h2 := ih ψ hψk (e := e) (H := H) (f := f)
          (Γ := insert (∼ψ) (insert φ (insert ψ Γ))) hmono hinfl hg1 (by simp) (by simp)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 2)) hg2 (∼φ) (∼ψ) hlt12 hlt12
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot φ ψ hlt23
          (hNF _) (hNF _) (Cl.ofNat _) hand
        rwa [Finset.insert_eq_self.mpr (show (φ ⋎ ψ) ∈ Γ by simp [hp])] at hor
    | hall ψ =>
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
        have hex : (∃⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, Zef2TC (ONote.ofNat (2 * k + 2)) e (adjoin H n) (rel1 f n) 0
            (insert (ψ/[nm n]) Γ) := by
          intro n
          have hf0n : f 0 ≤ rel1 f n 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max n 0))
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            simpa using hψk
          have h0 := ih (ψ/[nm n]) hcomp (e := e) (H := adjoin H n) (f := rel1 f n)
            (Γ := insert (∼(ψ/[nm n])) (insert (ψ/[nm n]) Γ))
            (rel1_monotone hmono n) (rel1_infl hinfl n)
            (le_trans hg1 hf0n) (by simp) (by simp)
          have hbound : n ≤ rel1 f n 0 := by
            simpa [rel1] using hinfl n
          have hexI := Zef2TC.exI (α := ONote.ofNat (2 * k + 2))
            (le_trans hg2 hf0n)
            (∼ψ) n hlt12 (hNF _) (hNF _) (Cl.ofNat _) hbound
            (by have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
                rw [heq]; exact h0)
          rwa [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hex)] at hexI
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot ψ
          (fun _ => ONote.ofNat (2 * k + 2)) (fun _ => hlt23) (fun _ => hNF _) (hNF _)
          (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hp] at hall
    | hexs ψ =>
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
        have hall' : (∀⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, Zef2TC (ONote.ofNat (2 * k + 2)) e (adjoin H n) (rel1 f n) 0
            (insert ((∼ψ)/[nm n]) Γ) := by
          intro n
          have hf0n : f 0 ≤ rel1 f n 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max n 0))
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            simpa using hψk
          have h0 := ih (ψ/[nm n]) hcomp (e := e) (H := adjoin H n) (f := rel1 f n)
            (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) Γ))
            (rel1_monotone hmono n) (rel1_infl hinfl n)
            (le_trans hg1 hf0n) (by simp) (by simp)
          have hbound : n ≤ rel1 f n 0 := by
            simpa [rel1] using hinfl n
          have hexI := Zef2TC.exI (α := ONote.ofNat (2 * k + 2))
            (le_trans hg2 hf0n)
            ψ n hlt12 (hNF _) (hNF _) (Cl.ofNat _) hbound h0
          rw [Finset.insert_eq_self.mpr
            (Finset.mem_insert_of_mem hp)] at hexI
          have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
          rw [heq]
          exact hexI
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot (∼ψ)
          (fun _ => ONote.ofNat (2 * k + 2)) (fun _ => hlt23) (fun _ => hNF _) (hNF _)
          (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hall'] at hall


/-- Non-`k`-indexed corollary: EM at the formula's own complexity rung. -/
theorem em_Zef2TC' (φ : Form) {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq}
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hgate : clog (2 * φ.complexity + 1) ≤ f 0)
    (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    Zef2TC (ONote.ofNat (2 * φ.complexity + 1)) e H f 0 Γ :=
  em_Zef2TC φ.complexity φ le_rfl hmono hinfl hgate hp hn

/-! ## The AMENDED rung-E statement DRAFT (block-6 amendment applied) -/

/-- The goodstein Π₂ body (as in `wip/E0Ax2NeedProbe.lean`). -/
noncomputable def goodsteinBody : Semisentence ℒₒᵣ 1 :=
  “∃ N, !LO.FirstOrder.Arithmetic.igoodsteinDef 0 #1 N”

theorem goodsteinSentence_eq_all_body :
    GoodsteinPA.goodsteinSentence = ∀⁰ goodsteinBody := rfl

noncomputable def goodsteinBodyE : SyntacticSemiformula ℒₒᵣ 1 :=
  Rewriting.emb goodsteinBody

/-- **DRAFT (E-1 amendment of the E-0 draft; NOT ratified — DO NOT port to src).**  Identical
to `embedding_Zef2T_DRAFT` (`wip/E0Ax2NeedProbe.lean`) with the sole change `Zef2T → Zef2TC`
(the connective-rule amendment, forced by `zef2T_not_derives_verum`). -/
theorem embedding_Zef2TC_DRAFT :
    (𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) →
      ∃ B d : ℕ, ∃ e : ONote, e.NF ∧ ∀ m : ℕ, ∃ α : ONote, α.NF ∧ ∃ H : ONote → Prop,
        Cl H α ∧ Zef2TC α e H (ewRootSlot e B) d {(goodsteinBodyE/[nm m])} := by
  sorry

/-! ## E-1 block 3 — monotonicity ports, the slot toolkit, and the case ladder

### The block-3 STATEMENT discovery (amendment input for the judge)

The E-0/E-1 DRAFT's **fixed root slot cannot pay the `exI` gate**: `Zef2TC.exI` demands the
witness numeral `n ≤ f 0`, and in the `Derivation2` `exs` case the witness value
`(asg env) t` is **env-dependent and unbounded** while `f = ewRootSlot e B` is structural
(chosen before `∀ env`).  Concretely, at the root the DRAFT's conclusion sequent
`{goodsteinBodyE/[nm m]}` is a Σ₁ instance whose only introduction rule is `exI` at the true
goodstein witness `N(m)` — unbounded in `m` — so the fixed-slot DRAFT is unprovable as stated
(and morally false).  This is exactly the seam the W3 verdict solved in `ZekdSomeK` with the
env-local `∃ K` witness budget; the fix here is the same discipline transplanted to the slot:
the master predicate carries an **env-local relativization index `K`** and runs the derivation
at slot `rel1 (ewRootSlot e B) K`.  `rel1`-slots compose with the ω-rule
(`rel1_rel1 : rel1 (rel1 f m) n = rel1 f (max m n)`) and keep `EwF1`/`EwF2` (`rel1_low`), so
the downstream pass/read-off pipeline is undisturbed.  `embedding_Zef2TC_DRAFT2` below is the
so-amended rung-E statement (the DRAFT above is retained verbatim as the flagged judge input).
-/

namespace Zef2TC

/-- Slot monotonicity (port of `Zef2.mono_f` over the full rule set). -/
theorem mono_f : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → ∀ {f' : ℕ → ℕ}, (∀ x, f x ≤ f' x) → Zef2TC α e H f' c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn =>
      intro f' hff'; exact .axL (le_trans hαN (hff' 0)) r v hp hn
  | trueRel hαN r v htrue hmem =>
      intro f' hff'; exact .trueRel (le_trans hαN (hff' 0)) r v htrue hmem
  | trueNrel hαN r v htrue hmem =>
      intro f' hff'; exact .trueNrel (le_trans hαN (hff' 0)) r v htrue hmem
  | verumR hαN h => intro f' hff'; exact .verumR (le_trans hαN (hff' 0)) h
  | wk hαN hsub _ ih => intro f' hff'; exact .wk (le_trans hαN (hff' 0)) hsub (ih hff')
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro f' hff'; exact .weak (le_trans hαN (hff' 0)) hβ hβNF hαNF hβH hsub (ih hff')
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact .andI (le_trans hαN (hff' 0)) φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH
        (ih₁ hff') (ih₂ hff')
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro f' hff'; exact .orI (le_trans hαN (hff' 0)) φ ψ hβ hβNF hαNF hβH (ih hff')
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro f' hff'
      exact .allω (le_trans hαN (hff' 0)) φ β hβ hβNF hαNF hβH
        (fun n => ih n (rel1_mono hff' n))
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro f' hff'
      exact .exI (le_trans hαN (hff' 0)) φ n hβ hβNF hαNF hβH
        (le_trans hbound (hff' 0)) (ih hff')
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact .cut (le_trans hαN (hff' 0)) φ hcompl (le_trans hcutRead (hff' 0))
        hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hff') (ih₂ hff')

/-- Cut-rank monotonicity (only `cut` mentions `c`). -/
theorem mono_c : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → ∀ {c' : ℕ}, c ≤ c' → Zef2TC α e H f c' Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => intro c' _; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro c' _; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro c' _; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro c' _; exact .verumR hαN h
  | wk hαN hsub _ ih => intro c' hcc; exact .wk hαN hsub (ih hcc)
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro c' hcc; exact .weak hαN hβ hβNF hαNF hβH hsub (ih hcc)
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro c' hcc
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hcc) (ih₂ hcc)
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro c' hcc; exact .orI hαN φ ψ hβ hβNF hαNF hβH (ih hcc)
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro c' hcc; exact .allω hαN φ β hβ hβNF hαNF hβH (fun n => ih n hcc)
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro c' hcc; exact .exI hαN φ n hβ hβNF hαNF hβH hbound (ih hcc)
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro c' hcc
      exact .cut hαN φ (lt_of_lt_of_le hcompl hcc) hcutRead hβφ hβψ hβφNF hβψNF hαNF
        hβφH hβψH (ih₁ hcc) (ih₂ hcc)

/-- Operator swap (port of `Zef2.change_H`; `Cl_of_NF` supplies every `Cl` obligation). -/
theorem change_H : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → ∀ {H' : ONote → Prop}, Zef2TC α e H' f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => intro H'; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro H'; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro H'; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro H'; exact .verumR hαN h
  | wk hαN hsub _ ih => intro H'; exact .wk hαN hsub ih
  | weak hαN hβ hβNF hαNF _ hsub _ ih =>
      intro H'; exact .weak hαN hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂
  | orI hαN φ ψ hβ hβNF hαNF _ _ ih =>
      intro H'; exact .orI hαN φ ψ hβ hβNF hαNF (Cl_of_NF hβNF) ih
  | allω hαN φ β hβ hβNF hαNF _ _ ih =>
      intro H'
      exact .allω hαN φ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI hαN φ n hβ hβNF hαNF _ hbound _ ih =>
      intro H'; exact .exI hαN φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'
      exact .cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

/-- Control-ordinal swap: `e` is a phantom index of the derivation relation (no rule inspects
it), so a derivation transports to ANY control ordinal.  (The control ordinal only acquires
meaning in the cut-elimination pass, where it drives the `ewIter`/`hardy` slot arithmetic.) -/
theorem change_e : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → ∀ (e' : ONote), Zef2TC α e' H f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => intro e'; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro e'; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro e'; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro e'; exact .verumR hαN h
  | wk hαN hsub _ ih => intro e'; exact .wk hαN hsub (ih e')
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro e'; exact .weak hαN hβ hβNF hαNF hβH hsub (ih e')
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro e'
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ e') (ih₂ e')
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro e'; exact .orI hαN φ ψ hβ hβNF hαNF hβH (ih e')
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro e'; exact .allω hαN φ β hβ hβNF hαNF hβH (fun n => ih n e')
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro e'; exact .exI hαN φ n hβ hβNF hαNF hβH hbound (ih e')
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro e'
      exact .cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ e') (ih₂ e')

end Zef2TC

/-! ### `Nlog`/slot toolkit for the ordinal joins -/

/-- `Nlog` is near-stable under `osucc` (mirror of `ewN_osucc_le`). -/
theorem Nlog_osucc_le : ∀ {o : ONote}, o.NF → Nlog (osucc o) ≤ Nlog o + 1
  | 0, _ => by
      show Nlog (oadd 0 1 0) ≤ Nlog 0 + 1
      simp only [Nlog_oadd, Nlog_zero, PNat.one_coe]
      have : clog 1 = 1 := by decide
      omega
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [ONote.repr_zero, Ordinal.opow_zero] at hlt
        exact (@ONote.repr_inj a 0 h.snd ONote.NF.zero).1
          (by rw [ONote.repr_zero]; exact Order.lt_one_iff.1 hlt)
      subst ha0
      show Nlog (oadd 0 (n + 1) 0) ≤ Nlog (oadd 0 n 0) + 1
      have hadd := clog_add_le (n : ℕ) 1
      have hpos := clog_pos n
      have h1 : clog 1 = 1 := by decide
      simp only [Nlog_oadd, Nlog_zero, PNat.add_coe, PNat.one_coe, Nat.zero_add]
      omega
  | oadd (oadd e' n' a') m b, h => by
      show Nlog (oadd (oadd e' n' a') m (osucc b)) ≤ Nlog (oadd (oadd e' n' a') m b) + 1
      have hIH := Nlog_osucc_le h.snd
      simp only [Nlog_oadd] at hIH ⊢
      omega

/-- The `K`-relativized root slot dominates a smaller-budget one: `e₁ < e` (with
`norm e₁ ≤ B`), `B₁ ≤ B`, `K₁ ≤ K` give pointwise domination.  The `norm e₁ ≤ B`
side condition is exactly `hardy_le_of_lt`'s budget gate, absorbed into the structural `B`. -/
theorem relSlot_le {e₁ e : ONote} (he₁ : e₁.NF) (he : e.NF) (hlt : e₁ < e)
    {B₁ B K₁ K : ℕ} (hB : B₁ ≤ B) (hK : K₁ ≤ K) (hnorm : norm e₁ ≤ B) (x : ℕ) :
    rel1 (ewRootSlot e₁ B₁) K₁ x ≤ rel1 (ewRootSlot e B) K x := by
  simp only [rel1, ewRootSlot]
  have harg : max B₁ (max K₁ x) ≤ max B (max K x) :=
    max_le_max hB (max_le_max hK le_rfl)
  have h1 : hardy e₁ (max B₁ (max K₁ x)) ≤ hardy e₁ (max B (max K x)) :=
    hardy_monotone e₁ harg
  have h2 : hardy e₁ (max B (max K x)) ≤ hardy e (max B (max K x)) :=
    hardy_le_of_lt he₁ he hlt (le_trans hnorm (le_max_left _ _))
  have h3 : max K₁ x ≤ max K x := max_le_max hK le_rfl
  omega

/-- Same-`e` slot monotonicity in `(B, K)`. -/
theorem relSlot_mono {e : ONote} {B₁ B K₁ K : ℕ} (hB : B₁ ≤ B) (hK : K₁ ≤ K) (x : ℕ) :
    rel1 (ewRootSlot e B₁) K₁ x ≤ rel1 (ewRootSlot e B) K x := by
  simp only [rel1, ewRootSlot]
  have h1 : hardy e (max B₁ (max K₁ x)) ≤ hardy e (max B (max K x)) :=
    hardy_monotone e (max_le_max hB (max_le_max hK le_rfl))
  have h3 : max K₁ x ≤ max K x := max_le_max hK le_rfl
  omega

/-- One `K`-rung buys `+2` of root-gate slack (the `2·(x + …)` slot shape). -/
theorem relSlot_succ_gap (e : ONote) (B M : ℕ) :
    rel1 (ewRootSlot e B) M 0 + 2 ≤ rel1 (ewRootSlot e B) (M + 1) 0 := by
  simp only [rel1, ewRootSlot]
  have h1 : hardy e (max B (max M 0)) ≤ hardy e (max B (max (M + 1) 0)) :=
    hardy_monotone e (max_le_max le_rfl (max_le_max (Nat.le_succ M) le_rfl))
  have h2 : max M 0 + 1 ≤ max (M + 1) 0 := by omega
  omega

/-- The structural budget `B` is readable off the slot at `0`. -/
theorem le_relSlot_zero (e : ONote) (B K : ℕ) : B ≤ rel1 (ewRootSlot e B) K 0 := by
  simp only [rel1, ewRootSlot]
  have h1 := le_hardy e (max B (max K 0))
  have h2 : B ≤ max B (max K 0) := le_max_left _ _
  omega

/-! ### The master predicate and the `Derivation2` case ladder -/

/-- **The rung-E master predicate** (block-3 amendment of the W3 shape): structural budgets
`B` (slot), `d` (cut rank), `e` (control tower) OUTSIDE `∀ env`; per-assignment an env-local
relativization index `K` (the `SomeK` witness-budget discipline — see the block-3 discovery
note) and a node ordinal `α`; operator fixed at the full closure `Cl (⊤)` (every `Cl`
obligation is `Cl.base trivial`, and `∃ H, Cl H α ∧ …` follows). -/
def BudgetedEmbedsTC (Γ : Finset (SyntacticFormula ℒₒᵣ)) : Prop :=
  ∃ B d : ℕ, ∃ e : ONote, e.NF ∧ ∀ env : ℕ → ℕ, ∃ K : ℕ, ∃ α : ONote, α.NF ∧
    Zef2TC α e (fun _ => True) (rel1 (ewRootSlot e B) K) d
      (Γ.image (fun φ => Embedding.asg env ▹ φ))

/-- Every `Cl (⊤)` obligation is free. -/
theorem clT (β : ONote) : Cl (fun _ : ONote => True) β := Cl.base trivial

/-- **`closed`** — consume `em_Zef2TC'`; the ordinal is the deterministic complexity rung
(env-independent since rewriting preserves `complexity`), the budget is its `clog` gate. -/
theorem budgetedEmbedsTC_closed {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (φ : SyntacticFormula ℒₒᵣ) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    BudgetedEmbedsTC Γ := by
  refine ⟨clog (2 * φ.complexity + 1), 0, 0, ONote.NF.zero, fun env => ?_⟩
  refine ⟨0, ONote.ofNat (2 * (Embedding.asg env ▹ φ).complexity + 1), ONote.nf_ofNat _, ?_⟩
  have hf1 := ewRootSlot_f1 0 (clog (2 * φ.complexity + 1))
  have hmono : Monotone (rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0) :=
    rel1_monotone hf1.1.monotone 0
  have hinfl : ∀ m, m ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0 m :=
    rel1_infl (fun m => by have := hf1.2 m; omega) 0
  have hgate : clog (2 * (Embedding.asg env ▹ φ).complexity + 1)
      ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0 0 := by
    simp only [Semiformula.complexity_rew]
    exact le_relSlot_zero 0 _ 0
  exact em_Zef2TC' (Embedding.asg env ▹ φ) hmono hinfl hgate
    (Finset.mem_image_of_mem _ hp)
    (by simpa using Finset.mem_image_of_mem (fun ψ => Embedding.asg env ▹ ψ) hn)

/-- **`verum`** — `verumR` at ordinal `0`. -/
theorem budgetedEmbedsTC_verum {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (h : (⊤ : SyntacticFormula ℒₒᵣ) ∈ Γ) :
    BudgetedEmbedsTC Γ := by
  refine ⟨0, 0, 0, ONote.NF.zero, fun env => ⟨0, 0, ONote.NF.zero, ?_⟩⟩
  have hmem : (⊤ : SyntacticFormula ℒₒᵣ) ∈ Γ.image (fun ψ => Embedding.asg env ▹ ψ) := by
    have := Finset.mem_image_of_mem (fun ψ => Embedding.asg env ▹ ψ) h
    simpa using this
  exact Zef2TC.verumR (by simp) hmem

/-- **`wk`** — image weakening; all budgets carried. -/
theorem budgetedEmbedsTC_wk {Δ Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (hsub : Δ ⊆ Γ) (ih : BudgetedEmbedsTC Δ) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih env
  exact ⟨K, α, hαNF, D.wk D.gate (Finset.image_subset_image hsub)⟩

/-- **`shift`** — the image collapses under the shifted assignment (`embedC`'s `hB`
computation, verbatim); budgets and derivation carried unchanged. -/
theorem budgetedEmbedsTC_shift {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (ih : BudgetedEmbedsTC Γ) :
    BudgetedEmbedsTC (Γ.image Rewriting.shift) := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih (fun x => env (x + 1))
  refine ⟨K, α, hαNF, ?_⟩
  have himg : (Γ.image (Rewriting.shift : SyntacticFormula ℒₒᵣ → SyntacticFormula ℒₒᵣ)).image
        (fun φ => Embedding.asg env ▹ φ)
      = Γ.image (fun φ => Embedding.asg (fun x => env (x + 1)) ▹ φ) := by
    have hcompB : (Embedding.asg env).comp Rew.shift
        = Embedding.asg (fun x => env (x + 1)) := by
      ext x
      · exact Fin.elim0 x
      · simp [Embedding.asg, Rew.comp_app]
    rw [Finset.image_image]
    refine Finset.image_congr (fun ψ _ => ?_)
    show Embedding.asg env ▹ (Rew.shift ▹ ψ) = Embedding.asg (fun x => env (x + 1)) ▹ ψ
    rw [← TransitiveRewriting.comp_app, hcompB]
  rwa [himg]

/-- **`or`** — single premise; `osucc` root, one `K`-rung pays the `Nlog` gate. -/
theorem budgetedEmbedsTC_or {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ ψ : SyntacticFormula ℒₒᵣ} (h : φ ⋎ ψ ∈ Γ)
    (ih : BudgetedEmbedsTC (insert φ (insert ψ Γ))) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih env
  refine ⟨K + 1, osucc α, osucc_NF hαNF, ?_⟩
  have hgate := D.gate
  rw [Finset.image_insert, Finset.image_insert] at D
  have D' := D.mono_f (relSlot_mono (le_refl B) (Nat.le_succ K))
  have hg : Nlog (osucc α) ≤ rel1 (ewRootSlot e B) (K + 1) 0 := by
    have hs := Nlog_osucc_le hαNF
    have hgap := relSlot_succ_gap e B K
    omega
  have hor := Zef2TC.orI (α := osucc α) hg
    (Embedding.asg env ▹ φ) (Embedding.asg env ▹ ψ)
    (Zekd.lt_osucc hαNF) hαNF (osucc_NF hαNF) (clT α) D'
  have hmem : (Embedding.asg env ▹ φ ⋎ Embedding.asg env ▹ ψ)
      ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h
    simpa using this
  rwa [Finset.insert_eq_self.mpr hmem] at hor

/-- **`and`** — the two-premise join: control tower `osucc (e₁ + e₂)` (both strictly below,
`hardy_le_of_lt` fed by `norm eᵢ` absorbed into the structural `B`), root `osucc (α₁ + α₂)`
(`Nlog` absorbing + one `K`-rung of gate slack), budgets aligned by `max`/`mono`. -/
theorem budgetedEmbedsTC_and {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ ψ : SyntacticFormula ℒₒᵣ} (h : φ ⋏ ψ ∈ Γ)
    (ihp : BudgetedEmbedsTC (insert φ Γ)) (ihq : BudgetedEmbedsTC (insert ψ Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, e₂, he₂, ih₂⟩ := ihq
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_right_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_left_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  refine ⟨B₁ + B₂ + norm e₁ + norm e₂, max d₁ d₂, osucc (e₁ + e₂), heNF, fun env => ?_⟩
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  obtain ⟨K₂, α₂, hα₂NF, D₂⟩ := ih₂ env
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  refine ⟨max K₁ K₂ + 1, osucc (α₁ + α₂), osucc_NF haddNF, ?_⟩
  have hg₁ := D₁.gate
  have hg₂ := D₂.gate
  rw [Finset.image_insert] at D₁ D₂
  have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) K₁ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₁ heNF hlt₁ (by omega) (by omega) (by omega)
  have hff₂ : ∀ x, rel1 (ewRootSlot e₂ B₂) K₂ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₂ heNF hlt₂ (by omega) (by omega) (by omega)
  have D₁' := ((D₁.change_e (osucc (e₁ + e₂))).mono_f hff₁).mono_c (le_max_left d₁ d₂)
  have D₂' := ((D₂.change_e (osucc (e₁ + e₂))).mono_f hff₂).mono_c (le_max_right d₁ d₂)
  have hg : Nlog (osucc (α₁ + α₂))
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) 0 := by
    have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    have j₁ : rel1 (ewRootSlot e₁ B₁) K₁ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂)) (max K₁ K₂) 0 :=
      relSlot_le he₁ heNF hlt₁ (by omega) (le_max_left _ _) (by omega) 0
    have j₂ : rel1 (ewRootSlot e₂ B₂) K₂ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂)) (max K₁ K₂) 0 :=
      relSlot_le he₂ heNF hlt₂ (by omega) (le_max_right _ _) (by omega) 0
    have hgap := relSlot_succ_gap (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂) (max K₁ K₂)
    omega
  have hand := Zef2TC.andI (α := osucc (α₁ + α₂)) hg
    (Embedding.asg env ▹ φ) (Embedding.asg env ▹ ψ)
    (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
    (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
    hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'
  have hmem : (Embedding.asg env ▹ φ ⋏ Embedding.asg env ▹ ψ)
      ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h
    simpa using this
  rwa [Finset.insert_eq_self.mpr hmem] at hand

/-- **`cut`** — same two-premise join as `and`; the cut rank is `max`ed with
`φ.complexity + 1` (env-independent: rewriting preserves `complexity`) and the read gate
`complexity ≤ f 0` is paid by absorbing `φ.complexity` into the structural `B`. -/
theorem budgetedEmbedsTC_cut {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ : SyntacticFormula ℒₒᵣ}
    (ihp : BudgetedEmbedsTC (insert φ Γ)) (ihn : BudgetedEmbedsTC (insert (∼φ) Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, e₂, he₂, ih₂⟩ := ihn
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_right_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_left_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  refine ⟨B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity, max (max d₁ d₂) (φ.complexity + 1),
    osucc (e₁ + e₂), heNF, fun env => ?_⟩
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  obtain ⟨K₂, α₂, hα₂NF, D₂⟩ := ih₂ env
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  refine ⟨max K₁ K₂ + 1, osucc (α₁ + α₂), osucc_NF haddNF, ?_⟩
  have hg₁ := D₁.gate
  have hg₂ := D₂.gate
  rw [Finset.image_insert] at D₁ D₂
  have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) K₁ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₁ heNF hlt₁ (by omega) (by omega) (by omega)
  have hff₂ : ∀ x, rel1 (ewRootSlot e₂ B₂) K₂ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₂ heNF hlt₂ (by omega) (by omega) (by omega)
  have D₁' := ((D₁.change_e (osucc (e₁ + e₂))).mono_f hff₁).mono_c
    (c' := max (max d₁ d₂) (φ.complexity + 1))
    (le_trans (le_max_left d₁ d₂) (le_max_left _ _))
  have D₂' := ((D₂.change_e (osucc (e₁ + e₂))).mono_f hff₂).mono_c
    (c' := max (max d₁ d₂) (φ.complexity + 1))
    (le_trans (le_max_right d₁ d₂) (le_max_left _ _))
  rw [show Embedding.asg env ▹ (∼φ) = ∼(Embedding.asg env ▹ φ) by simp] at D₂'
  have hg : Nlog (osucc (α₁ + α₂))
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) 0 := by
    have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    have j₁ : rel1 (ewRootSlot e₁ B₁) K₁ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂))
            (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity)) (max K₁ K₂) 0 :=
      relSlot_le he₁ heNF hlt₁ (by omega) (le_max_left _ _) (by omega) 0
    have j₂ : rel1 (ewRootSlot e₂ B₂) K₂ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂))
            (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity)) (max K₁ K₂) 0 :=
      relSlot_le he₂ heNF hlt₂ (by omega) (le_max_right _ _) (by omega) 0
    have hgap := relSlot_succ_gap (osucc (e₁ + e₂))
      (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity) (max K₁ K₂)
    omega
  have hread : (Embedding.asg env ▹ φ).complexity
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) 0 := by
    simp only [Semiformula.complexity_rew]
    exact le_trans (by omega) (le_relSlot_zero _ _ _)
  have hcompl : (Embedding.asg env ▹ φ).complexity < max (max d₁ d₂) (φ.complexity + 1) := by
    simp only [Semiformula.complexity_rew]
    omega
  exact Zef2TC.cut hg (Embedding.asg env ▹ φ) hcompl hread
    (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
    (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
    hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'

/-- **`axm`** — PA-axiom leaf; THE hard pair's first half (= W1/W2 content).  Finite `𝗣𝗔⁻` +
equality axioms are true closed Δ₀-ish formulas after `asg env` — dischargeable by a
`trueRel`-driven bounded-truth lemma (the `Zef2TC` analogue of `provable_true`, using (Ax2)
where `embedC` used ω-completeness); the **induction schema** needs the bounded cut-tower
(the W1/W2 campaign).  Disclosed `sorry` — next E-1 block. -/
theorem budgetedEmbedsTC_axm {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (φ : SyntacticFormula ℒₒᵣ) (hφ : φ ∈ (𝗣𝗔 : Schema ℒₒᵣ)) (hΓ : φ ∈ Γ) :
    BudgetedEmbedsTC Γ := by
  sorry

/-- **`all`** — the ω-rule; THE hard pair's second half.  Per branch `n` the IH at `n :>ₙ env`
gives `(K_n, α_n)`; `Zef2TC.allω` needs a SINGLE root `α` with `β n < α` for all `n` and
premises at slot `rel1 f n` — so the per-branch `α_n, K_n` must be UNIFORMIZED into `α` and
absorbed into the branch relativization (the `EmbeddingBound.embedC_LX_bdd` uniform-ω-family
discipline, ported to the slot calculus).  Requires the ordinal-family bound port; disclosed
`sorry` — the block after `axm`. -/
theorem budgetedEmbedsTC_all {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ : SyntacticSemiformula ℒₒᵣ 1} (h : ∀⁰ φ ∈ Γ)
    (ih : BudgetedEmbedsTC (insert (Rewriting.free φ) (Γ.image Rewriting.shift))) :
    BudgetedEmbedsTC Γ := by
  sorry

/-! ### The value-congruent EM engine + the closed-term collapse (the `exs` kit)

Mirror of `provable_em_cong_gen`/`Provable.exI_closed` (`Embedding.lean`) with the `Zef2TC`
budget bookkeeping of `em_Zef2TC`; the atomic cases split on `atomTrue` and close by
`trueRel`/`trueNrel` — this is exactly where (Ax2) is load-bearing (in `Z∞` the split used
`axTrue`; `Zef2` alone has no true-literal leaf).  The congruence kit
(`stdClosedVal`/`atomTrue_rel_congr`/`embedding_subst_q_cons_app`) is banked in
`OperatorZinfty`. -/

private theorem em_cong_atomic_rel {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticSemiterm ℒₒᵣ n)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hαN : Nlog α ≤ f 0)
    (hp : (Rew.subst w ▹ Semiformula.rel r v) ∈ Γ)
    (hn : (∼(Rew.subst w' ▹ Semiformula.rel r v)) ∈ Γ) :
    Zef2TC α e H f c Γ := by
  have hp' : Semiformula.rel r (fun i => Rew.subst w (v i)) ∈ Γ := by
    simpa [Semiformula.rew_rel] using hp
  have hn' : Semiformula.nrel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
    simpa [Semiformula.rew_rel] using hn
  by_cases ht : atomTrue (Semiformula.rel r (fun i => Rew.subst w (v i)))
  · exact Zef2TC.trueRel hαN r _ ht hp'
  · have htn : atomTrue (Semiformula.nrel r (fun i => Rew.subst w (v i))) :=
      (atomTrue_nrel_iff_not_rel r _).mpr ht
    have htn' : atomTrue (Semiformula.nrel r (fun i => Rew.subst w' (v i))) :=
      (atomTrue_nrel_congr r _ _
        (fun i => embedding_valm_subst_congr w w' hval (v i))).mp htn
    exact Zef2TC.trueNrel hαN r _ htn' hn'

private theorem em_cong_atomic_nrel {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticSemiterm ℒₒᵣ n)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hαN : Nlog α ≤ f 0)
    (hp : (Rew.subst w ▹ Semiformula.nrel r v) ∈ Γ)
    (hn : (∼(Rew.subst w' ▹ Semiformula.nrel r v)) ∈ Γ) :
    Zef2TC α e H f c Γ := by
  have hp' : Semiformula.nrel r (fun i => Rew.subst w (v i)) ∈ Γ := by
    simpa [Semiformula.rew_nrel] using hp
  have hn' : Semiformula.rel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
    simpa [Semiformula.rew_nrel] using hn
  by_cases ht : atomTrue (Semiformula.nrel r (fun i => Rew.subst w (v i)))
  · exact Zef2TC.trueNrel hαN r _ ht hp'
  · have htn : atomTrue (Semiformula.rel r (fun i => Rew.subst w (v i))) := by
      by_contra hno
      exact ht ((atomTrue_nrel_iff_not_rel r _).mpr hno)
    have htn' : atomTrue (Semiformula.rel r (fun i => Rew.subst w' (v i))) :=
      (atomTrue_rel_congr r _ _
        (fun i => embedding_valm_subst_congr w w' hval (v i))).mp htn
    exact Zef2TC.trueRel hαN r _ htn' hn'

/-- **Value-congruent budgeted EM** (arity-general; the `exs`-case engine): for pointwise
value-equal closed substitutions `w, w'`, any sequent containing `Rew.subst w ▹ ψ` and
`∼(Rew.subst w' ▹ ψ)` is cut-free `Zef2TC`-derivable at the deterministic rung
`ofNat (2k+1)`.  Same budget discipline as `em_Zef2TC` (all hypotheses `rel1`-stable);
atomic cases via `trueRel`/`trueNrel` + `stdClosedVal` congruence — the (Ax2)-load-bearing
step. -/
theorem em_cong_Zef2TC (k : ℕ) :
    ∀ {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ) (ψ : SyntacticSemiformula ℒₒᵣ n),
      ψ.complexity ≤ k →
      (∀ i, stdClosedVal (w i) = stdClosedVal (w' i)) →
      ∀ {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq},
        Monotone f → (∀ m, m ≤ f m) → clog (2 * k + 1) ≤ f 0 →
        (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ →
        Zef2TC (ONote.ofNat (2 * k + 1)) e H f 0 Γ := by
  induction k with
  | zero =>
    intro n w w' ψ hk hval e H f Γ hmono hinfl hgate hp hn
    have hgate' : Nlog (ONote.ofNat 1) ≤ f 0 := le_trans (Nlog_ofNat_le 1) hgate
    cases ψ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hgate' (by simpa using hp)
    | hfalsum => exact Zef2TC.verumR hgate' (by simpa using hn)
    | hrel r v => exact em_cong_atomic_rel w w' hval r v hgate' hp hn
    | hnrel r v => exact em_cong_atomic_nrel w w' hval r v hgate' hp hn
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro n w w' ψ hk hval e H f Γ hmono hinfl hgate hp hn
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at hgate ⊢
    have hNF : ∀ m : ℕ, (ONote.ofNat m).NF := fun m => ONote.nf_ofNat m
    have hlt12 : ONote.ofNat (2 * k + 1) < ONote.ofNat (2 * k + 2) := ofNat_lt_ofNat (by omega)
    have hlt23 : ONote.ofNat (2 * k + 2) < ONote.ofNat (2 * k + 3) := ofNat_lt_ofNat (by omega)
    have hroot : Nlog (ONote.ofNat (2 * k + 3)) ≤ f 0 := le_trans (Nlog_ofNat_le _) hgate
    have hg2 : Nlog (ONote.ofNat (2 * k + 2)) ≤ f 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (clog_mono (by omega)) hgate)
    have hg1 : clog (2 * k + 1) ≤ f 0 := le_trans (clog_mono (by omega)) hgate
    cases ψ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hroot (by simpa using hp)
    | hfalsum => exact Zef2TC.verumR hroot (by simpa using hn)
    | hrel r v => exact em_cong_atomic_rel w w' hval r v hroot hp hn
    | hnrel r v => exact em_cong_atomic_nrel w w' hval r v hroot hp hn
    | hand a b =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
        have hn' : (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
        have h1 := ih (n := n) w w' a hak hval (e := e) (H := H) (f := f)
          (Γ := insert (Rew.subst w ▹ a)
            (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
          hmono hinfl hg1 (by simp) (by simp)
        have h2 := ih (n := n) w w' b hbk hval (e := e) (H := H) (f := f)
          (Γ := insert (Rew.subst w ▹ b)
            (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
          hmono hinfl hg1 (by simp) (by simp)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 2)) hg2
          (Rew.subst w ▹ a) (Rew.subst w ▹ b) hlt12 hlt12
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rw [Finset.insert_eq_self.mpr
          (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b))
            ∈ insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)
            by simp [hp'])] at hand
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot
          (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) hlt23
          (hNF _) (hNF _) (Cl.ofNat _) hand
        rwa [Finset.insert_eq_self.mpr hn'] at hor
    | hor a b =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
        have hn' : (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
        have h1 := ih (n := n) w w' a hak hval (e := e) (H := H) (f := f)
          (Γ := insert (∼(Rew.subst w' ▹ a))
            (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
          hmono hinfl hg1 (by simp) (by simp)
        have h2 := ih (n := n) w w' b hbk hval (e := e) (H := H) (f := f)
          (Γ := insert (∼(Rew.subst w' ▹ b))
            (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
          hmono hinfl hg1 (by simp) (by simp)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 2)) hg2
          (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) hlt12 hlt12
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot
          (Rew.subst w ▹ a) (Rew.subst w ▹ b) hlt23
          (hNF _) (hNF _) (Cl.ofNat _) hand
        rwa [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ
          by simp [hp'])] at hor
    | hall a =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
        have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
        have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
        have fam : ∀ m, Zef2TC (ONote.ofNat (2 * k + 2)) e (adjoin H m) (rel1 f m) 0
            (insert ((((Rew.subst w).q ▹ a))/[nm m]) Γ) := by
          intro m
          have hf0m : f 0 ≤ rel1 f m 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max m 0))
          have hvalm : ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) :=
            embedding_valm_cons_nm_congr w w' m hval
          have h0 := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
            (e := e) (H := adjoin H m) (f := rel1 f m)
            (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
              (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
            (rel1_monotone hmono m) (rel1_infl hinfl m) (le_trans hg1 hf0m)
            (by rw [← embedding_subst_q_cons_app]; simp)
            (by rw [← embedding_subst_q_cons_app]; simp)
          have hbound : m ≤ rel1 f m 0 := by
            simpa [rel1] using hinfl m
          have hexI := Zef2TC.exI (α := ONote.ofNat (2 * k + 2))
            (le_trans hg2 hf0m)
            ((Rew.subst w').q ▹ ∼a) m hlt12 (hNF _) (hNF _) (Cl.ofNat _) hbound
            (by
              have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                  = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
              rw [heq, Finset.insert_comm]
              exact h0)
          rwa [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hn')] at hexI
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot
          ((Rew.subst w).q ▹ a) (fun _ => ONote.ofNat (2 * k + 2)) (fun _ => hlt23)
          (fun _ => hNF _) (hNF _) (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hp'] at hall
    | hexs a =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
        have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
        have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
        have fam : ∀ m, Zef2TC (ONote.ofNat (2 * k + 2)) e (adjoin H m) (rel1 f m) 0
            (insert ((((Rew.subst w').q ▹ ∼a))/[nm m]) Γ) := by
          intro m
          have hf0m : f 0 ≤ rel1 f m 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max m 0))
          have hvalm : ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) :=
            embedding_valm_cons_nm_congr w w' m hval
          have h0 := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
            (e := e) (H := adjoin H m) (f := rel1 f m)
            (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
              (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
            (rel1_monotone hmono m) (rel1_infl hinfl m) (le_trans hg1 hf0m)
            (by rw [← embedding_subst_q_cons_app]; simp)
            (by rw [← embedding_subst_q_cons_app]; simp)
          have hbound : m ≤ rel1 f m 0 := by
            simpa [rel1] using hinfl m
          have hexI := Zef2TC.exI (α := ONote.ofNat (2 * k + 2))
            (le_trans hg2 hf0m)
            ((Rew.subst w).q ▹ a) m hlt12 (hNF _) (hNF _) (Cl.ofNat _) hbound h0
          rw [Finset.insert_eq_self.mpr
            (Finset.mem_insert_of_mem hp')] at hexI
          have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
              = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
          rw [heq]
          exact hexI
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot
          ((Rew.subst w').q ▹ ∼a) (fun _ => ONote.ofNat (2 * k + 2)) (fun _ => hlt23)
          (fun _ => hNF _) (hNF _) (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hn'] at hall

/-- Single-term wrapper: closed terms `s, s'` of equal standard value. -/
theorem em_cong1_Zef2TC (s s' : SyntacticTerm ℒₒᵣ)
    (hval : stdClosedVal s = stdClosedVal s')
    (ψ : SyntacticSemiformula ℒₒᵣ 1) {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq}
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hgate : clog (2 * ψ.complexity + 1) ≤ f 0)
    (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) :
    Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e H f 0 Γ := by
  refine em_cong_Zef2TC ψ.complexity ![s] ![s'] ψ le_rfl ?_ hmono hinfl hgate hp hn
  intro i
  cases i using Fin.cases with
  | zero => simpa using hval
  | succ j => exact j.elim0

/-- The relativization index is readable off the slot at `0`. -/
theorem index_le_relSlot_zero (e : ONote) (B K : ℕ) : K ≤ rel1 (ewRootSlot e B) K 0 := by
  simp only [rel1, ewRootSlot]
  omega

/-- **`exs`** — the closed-term collapse, DISCHARGED.  `asg env t` is closed with standard
value `m`; the value-congruent EM (`em_cong1_Zef2TC`, at pair `(nm m, asg env t)`) + one
`cut` at rank `complexity+1` convert the IH's `ψ'/[asg env t]` into `ψ'/[nm m]`, and `exI`
fires at witness `m` — env-dependent, absorbed into the relativization index
`K := max K₁ m + 3` (the `∃ K` amendment's raison d'être; `n ≤ f 0` paid by
`index_le_relSlot_zero`, the two ordinal-join gates by `relSlot_succ_gap` rungs). -/
theorem budgetedEmbedsTC_exs {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ : SyntacticSemiformula ℒₒᵣ 1} (h : ∃⁰ φ ∈ Γ) (t : SyntacticTerm ℒₒᵣ)
    (ih : BudgetedEmbedsTC (insert (φ/[t]) Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ih
  refine ⟨B₁ + φ.complexity + clog (2 * φ.complexity + 1), max d₁ (φ.complexity + 1), e₁,
    he₁, fun env => ?_⟩
  set B : ℕ := B₁ + φ.complexity + clog (2 * φ.complexity + 1) with hB
  set d : ℕ := max d₁ (φ.complexity + 1) with hd
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  -- the closed witness and its standard value
  set ψ' : SyntacticSemiformula ℒₒᵣ 1 := (Embedding.asg env).q ▹ φ with hψ'
  set s : SyntacticTerm ℒₒᵣ := Embedding.asg env t with hs
  set m : ℕ := stdClosedVal s with hm
  set K : ℕ := max K₁ m + 3 with hK
  set F : ℕ → ℕ := rel1 (ewRootSlot e₁ B) K with hF
  have hψc : ψ'.complexity = φ.complexity := by simp [hψ']
  have hf1 := ewRootSlot_f1 e₁ B
  have hFmono : Monotone F := rel1_monotone hf1.1.monotone K
  have hFinfl : ∀ x, x ≤ F x := rel1_infl (fun x => by have := hf1.2 x; omega) K
  -- the IH derivation, re-based to the joined budget and rewritten to the substituted head
  have hg₁ := D₁.gate
  rw [Finset.image_insert, Embedding.rew_subst_term (Embedding.asg env) φ t] at D₁
  have D₁' := (D₁.mono_f (relSlot_mono (show B₁ ≤ B by omega) (show K₁ ≤ K by omega))).mono_c
    (c' := d) (le_max_left _ _)
  -- left cut premise: add ψ'/[nm m] to the context
  have Dsrc : Zef2TC α₁ e₁ (fun _ => True) F d
      (insert (ψ'/[s]) (insert (ψ'/[nm m])
        (Γ.image (fun χ => Embedding.asg env ▹ χ)))) :=
    D₁'.wk D₁'.gate (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
  -- right cut premise: value-congruent EM at the pair (nm m, s)
  have hgateEM : clog (2 * ψ'.complexity + 1) ≤ F 0 := by
    rw [hψc]
    exact le_trans (by omega) (le_relSlot_zero e₁ B K)
  have Dcong : Zef2TC (ONote.ofNat (2 * ψ'.complexity + 1)) e₁ (fun _ => True) F 0
      (insert (∼(ψ'/[s])) (insert (ψ'/[nm m])
        (Γ.image (fun χ => Embedding.asg env ▹ χ)))) := by
    refine em_cong1_Zef2TC (nm m) s (by simp [hm]) ψ' hFmono hFinfl hgateEM ?_ ?_
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_self _ _
  have Dcong' := Dcong.mono_c (c' := d) (Nat.zero_le d)
  -- the cut, at root `osucc (α₁ + ofNat (2·complexity+1))`
  have hofNF : (ONote.ofNat (2 * ψ'.complexity + 1)).NF := ONote.nf_ofNat _
  have haddNF : (α₁ + ONote.ofNat (2 * ψ'.complexity + 1)).NF := by
    haveI := hα₁NF; haveI := hofNF; exact ONote.add_nf _ _
  have hslack : ∀ M, rel1 (ewRootSlot e₁ B) M 0 + 2
      ≤ rel1 (ewRootSlot e₁ B) (M + 2) 0 := by
    intro M
    have g1 := relSlot_succ_gap e₁ B M
    have g2 := relSlot_succ_gap e₁ B (M + 1)
    rw [show M + 1 + 1 = M + 2 from rfl] at g2
    omega
  have hgcut : Nlog (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))) ≤ F 0 := by
    rw [hF, hK]
    have hs' := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
    have hα₁K : rel1 (ewRootSlot e₁ B₁) K₁ 0 ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      relSlot_mono (by omega) (le_max_left _ _) 0
    have hof : Nlog (ONote.ofNat (2 * ψ'.complexity + 1)) ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (by rw [hψc]; omega)
        (le_relSlot_zero e₁ B (max K₁ m)))
    have hgap := hslack (max K₁ m)
    have hlast := relSlot_succ_gap e₁ B (max K₁ m + 2)
    rw [show max K₁ m + 2 + 1 = max K₁ m + 3 from rfl] at hlast
    omega
  have hcompl : (ψ'/[s]).complexity < d := by
    have : (ψ'/[s]).complexity = φ.complexity := by simp [hψ']
    omega
  have hread : (ψ'/[s]).complexity ≤ F 0 := by
    have hc : (ψ'/[s]).complexity = φ.complexity := by simp [hψ']
    rw [hc]
    exact le_trans (by omega) (le_relSlot_zero e₁ B K)
  have Dnum : Zef2TC (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))) e₁ (fun _ => True) F d
      (insert (ψ'/[nm m]) (Γ.image (fun χ => Embedding.asg env ▹ χ))) :=
    Zef2TC.cut hgcut (ψ'/[s]) hcompl hread
      (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hofNF) (Zekd.lt_osucc haddNF))
      (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hofNF) (Zekd.lt_osucc haddNF))
      hα₁NF hofNF (osucc_NF haddNF) (clT _) (clT _) Dsrc Dcong'
  -- the ∃-introduction at the numeral witness `m`
  refine ⟨K, osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))),
    osucc_NF (osucc_NF haddNF), ?_⟩
  have hgout : Nlog (osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1)))) ≤ F 0 := by
    rw [hF, hK]
    have hs' := Nlog_osucc_le (osucc_NF haddNF)
    have hs'' := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
    have hα₁K : rel1 (ewRootSlot e₁ B₁) K₁ 0 ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      relSlot_mono (by omega) (le_max_left _ _) 0
    have hof : Nlog (ONote.ofNat (2 * ψ'.complexity + 1)) ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (by rw [hψc]; omega)
        (le_relSlot_zero e₁ B (max K₁ m)))
    have g1 := relSlot_succ_gap e₁ B (max K₁ m)
    have g2 := relSlot_succ_gap e₁ B (max K₁ m + 1)
    have g3 := relSlot_succ_gap e₁ B (max K₁ m + 2)
    rw [show max K₁ m + 1 + 1 = max K₁ m + 2 from rfl] at g2
    rw [show max K₁ m + 2 + 1 = max K₁ m + 3 from rfl] at g3
    omega
  have hwit : m ≤ F 0 := le_trans (by omega) (index_le_relSlot_zero e₁ B K)
  have hexI := Zef2TC.exI (α := osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))))
    hgout ψ' m
    (Zekd.lt_osucc (osucc_NF haddNF)) (osucc_NF haddNF)
    (osucc_NF (osucc_NF haddNF)) (clT _) hwit Dnum
  have hmem : (∃⁰ ψ') ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h
    simpa [hψ'] using this
  rwa [Finset.insert_eq_self.mpr hmem] at hexI

/-- **The rung-E master ladder, assembled** (REAL induction, mirroring `SpikeW3Embedding`'s
skeleton): every `Derivation2` from `𝗣𝗔` is budgeted-embeddable into `Zef2TC`.  Seven of ten
cases are closed sorry-free above; the remaining leaves are `axm` (W1/W2), `all`
(uniform-ω-family port), `exs` (closed-term collapse). -/
theorem budgetedEmbedding_Zef2TC {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) :
    BudgetedEmbedsTC Γ := by
  induction d with
  | closed Γ φ hp hn => exact budgetedEmbedsTC_closed φ hp hn
  | axm φ hφ hΓ => exact budgetedEmbedsTC_axm φ hφ hΓ
  | verum h => exact budgetedEmbedsTC_verum h
  | @and Γ φ ψ h _dp _dq ihp ihq => exact budgetedEmbedsTC_and h ihp ihq
  | @or Γ φ ψ h _d ih => exact budgetedEmbedsTC_or h ih
  | @all Γ φ h _d ih => exact budgetedEmbedsTC_all h ih
  | @exs Γ φ h t _d ih => exact budgetedEmbedsTC_exs h t ih
  | @wk Δ Γ _d hsub ih => exact budgetedEmbedsTC_wk hsub ih
  | @shift Γ _d ih => exact budgetedEmbedsTC_shift ih
  | @cut Γ φ _dp _dn ihp ihn => exact budgetedEmbedsTC_cut ihp ihn

/-- **DRAFT2 (the block-3 amendment of `embedding_Zef2TC_DRAFT`; NOT ratified).**  Sole
change: the env-local relativization index `∃ K` inside `∀ m`, slot
`rel1 (ewRootSlot e B) K` — forced by the `exs` witness-budget seam (see the block-3
discovery note).  The fixed-slot DRAFT above is retained verbatim as flagged judge input. -/
theorem embedding_Zef2TC_DRAFT2 :
    (𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) →
      ∃ B d : ℕ, ∃ e : ONote, e.NF ∧ ∀ m : ℕ, ∃ K : ℕ, ∃ α : ONote, α.NF ∧
        ∃ H : ONote → Prop, Cl H α ∧
          Zef2TC α e H (rel1 (ewRootSlot e B) K) d {(goodsteinBodyE/[nm m])} := by
  sorry

end GoodsteinPA.E1EmbeddingGrind

-- Audit anchors.  The seven closed ladder cases are standard-triple
-- (`[propext, Classical.choice, Quot.sound]`, no sorryAx); the assembled master carries
-- `sorryAx` exactly through the three disclosed hard leaves (`axm`/`all`/`exs`).
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsTC_closed
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsTC_and
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsTC_cut
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedding_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.em_cong_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsTC_exs

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## E-1 block 5 — the GROWTH KIT: `Gexp = hardy (ω²)` dominates ℒₒᵣ term values

The `all` case's residue (and the coming V3 refinement of the master predicate): the env-local
witness budget must be BOUNDED BY A STRUCTURAL FUNCTION of the assignment, or the ω-rule cannot
uniformize the branches (`K_n` unbounded in `n` kills `rel1 f n` domination).  The mechanism
that pays every witness is the control tower: every closed-term value under `asg env` is
dominated by finitely many iterates of the single engine `Gexp := hardy (ω²)` applied to the
sup of the finitely many relevant `env` values. -/

/-- The growth engine: `H_{ω²}`. -/
noncomputable def Gexp : ℕ → ℕ := hardy (oadd (ONote.ofNat 2) 1 0)

theorem Gexp_eq (x : ℕ) : Gexp x = 2 ^ (x + 1) * (x + 1) - 1 := by
  have h := hardy_omega_pow_ofNat 2 x
  have h2 : fastGrowing (ONote.ofNat 2) (x + 1) = 2 ^ (x + 1) * (x + 1) := by
    rw [show ONote.ofNat 2 = 2 from rfl, ONote.fastGrowing_two]
  have hpos : 0 < 2 ^ (x + 1) * (x + 1) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.succ_pos x)
  unfold Gexp
  omega

theorem Gexp_monotone : Monotone Gexp := hardy_monotone _

theorem le_Gexp (x : ℕ) : x ≤ Gexp x := le_hardy _ x

theorem succ_le_Gexp (x : ℕ) : x + 1 ≤ Gexp x := by
  rw [Gexp_eq]
  have h2 : 2 ≤ 2 ^ (x + 1) := by
    calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (x + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * (x + 1) ≤ 2 ^ (x + 1) * (x + 1) := Nat.mul_le_mul_right _ h2
  omega

/-- The two closure facts term domination needs: `Gexp (max a b)` absorbs both `a + b`
and `a * b`. -/
theorem add_le_Gexp_max (a b : ℕ) : a + b ≤ Gexp (max a b) := by
  rw [Gexp_eq]
  have h2 : 2 ≤ 2 ^ (max a b + 1) := by
    calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (max a b + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * (max a b + 1) ≤ 2 ^ (max a b + 1) * (max a b + 1) := Nat.mul_le_mul_right _ h2
  have hab : a + b ≤ 2 * max a b := by omega
  omega

theorem mul_le_Gexp_max (a b : ℕ) : a * b ≤ Gexp (max a b) := by
  rw [Gexp_eq]
  have hab : a * b ≤ max a b * max a b :=
    Nat.mul_le_mul (le_max_left a b) (le_max_right a b)
  have h1 : max a b + 1 ≤ 2 ^ (max a b + 1) := le_of_lt Nat.lt_two_pow_self
  have h2 : (max a b + 1) * (max a b + 1) = max a b * max a b + 2 * max a b + 1 := by ring
  have h3 : (max a b + 1) * (max a b + 1) ≤ 2 ^ (max a b + 1) * (max a b + 1) :=
    Nat.mul_le_mul_right _ h1
  omega

theorem Gexp_iter_monotone (c : ℕ) : Monotone (Gexp^[c]) :=
  Gexp_monotone.iterate c

theorem le_Gexp_iter (c x : ℕ) : x ≤ Gexp^[c] x := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (le_Gexp _)

theorem Gexp_iter_le_iter {c c' : ℕ} (h : c ≤ c') (x : ℕ) : Gexp^[c] x ≤ Gexp^[c'] x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact Gexp_iter_monotone c (le_Gexp_iter k x)

theorem iter_le_Gexp_iter (c x : ℕ) : c ≤ Gexp^[c] x := by
  induction c with
  | zero => exact Nat.zero_le _
  | succ c ih =>
      rw [Function.iterate_succ_apply']
      have h1 := succ_le_Gexp (Gexp^[c] x)
      omega

/-- Iterates as a single Hardy value: `Gexp^[c] = H_{ω²·c}` — the control tower absorbs the
iterate budget (`hardy_single_coeff`; exponent `ofNat 2 ≠ 0`). -/
theorem Gexp_iter_eq_hardy (c : ℕ+) (x : ℕ) :
    Gexp^[(c : ℕ)] x = hardy (oadd (ONote.ofNat 2) c 0) x :=
  (hardy_single_coeff (ONote.ofNat 2) (by decide) c x).symm

/-! ### `envSup` — the canonical assignment sup -/

/-- Sup of the first `N` values of the assignment (the canonical witness-budget seed; `N` is
the sequent's structural fv bound). -/
def envSup (env : ℕ → ℕ) (N : ℕ) : ℕ := (Finset.range N).sup env

theorem envSup_mono_N (env : ℕ → ℕ) {N N' : ℕ} (h : N ≤ N') :
    envSup env N ≤ envSup env N' :=
  Finset.sup_mono (fun x hx => by
    simp only [Finset.mem_range] at hx ⊢; omega)

theorem le_envSup {env : ℕ → ℕ} {N x : ℕ} (hx : x < N) : env x ≤ envSup env N :=
  Finset.le_sup (Finset.mem_range.mpr hx)

/-- The ω-rule cons law: the branch assignment's sup collapses to `max n` of the root's. -/
theorem envSup_cons_le (env : ℕ → ℕ) (n N : ℕ) :
    envSup (n :>ₙ env) (N + 1) ≤ max n (envSup env N) := by
  refine Finset.sup_le fun x hx => ?_
  rcases x with _ | y
  · simp
  · have hy : y < N := by simpa using hx
    exact le_trans (by simpa using le_envSup hy) (le_max_right _ _)

/-! ### Term domination -/

/-- **Term domination**: every ℒₒᵣ term value under any assignment is bounded by structurally
many `Gexp`-iterates of the env-sup over a structural fv bound.  Induction on the term; the
`add`/`mul` closure facts pay the function cases.  This is the mechanism the `exs`/`all`
witness budgets reduce to (E–W: the control tower pays for term growth). -/
theorem term_val_le_Gexp_iter (t : SyntacticTerm ℒₒᵣ) :
    ∃ c N : ℕ, ∀ env : ℕ → ℕ,
      Semiterm.valm ℕ ![] env t ≤ Gexp^[c] (envSup env N) := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x =>
      exact ⟨0, x + 1, fun env => by
        simpa using le_envSup (Nat.lt_succ_self x)⟩
  | func f v ih =>
      match f, v with
      | LO.FirstOrder.Language.ORing.Func.zero, v =>
          refine ⟨0, 0, fun env => ?_⟩
          have hv : Semiterm.valm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.zero v) = 0 := by
            simp only [Semiterm.valm, Semiterm.val_func]; rfl
          simp [hv]
      | LO.FirstOrder.Language.ORing.Func.one, v =>
          refine ⟨1, 0, fun env => ?_⟩
          have h1 := iter_le_Gexp_iter 1 (envSup env 0)
          have hv : Semiterm.valm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.one v) = 1 := by
            simp only [Semiterm.valm, Semiterm.val_func]; rfl
          omega
      | LO.FirstOrder.Language.ORing.Func.add, v =>
          obtain ⟨c₀, N₀, h₀⟩ := ih 0
          obtain ⟨c₁, N₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, max N₀ N₁, fun env => ?_⟩
          have hb₀ : Semiterm.valm ℕ ![] env (v 0)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₀ env) (le_trans
              (Gexp_iter_le_iter (le_max_left c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_left N₀ N₁))))
          have hb₁ : Semiterm.valm ℕ ![] env (v 1)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₁ env) (le_trans
              (Gexp_iter_le_iter (le_max_right c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_right N₀ N₁))))
          have hadd : Semiterm.valm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.add v)
              = Semiterm.valm ℕ ![] env (v 0) + Semiterm.valm ℕ ![] env (v 1) := by
            simp only [Semiterm.valm, Semiterm.val_func]; rfl
          rw [hadd, Function.iterate_succ_apply']
          refine le_trans (add_le_Gexp_max _ _) (Gexp_monotone ?_)
          exact max_le hb₀ hb₁
      | LO.FirstOrder.Language.ORing.Func.mul, v =>
          obtain ⟨c₀, N₀, h₀⟩ := ih 0
          obtain ⟨c₁, N₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, max N₀ N₁, fun env => ?_⟩
          have hb₀ : Semiterm.valm ℕ ![] env (v 0)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₀ env) (le_trans
              (Gexp_iter_le_iter (le_max_left c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_left N₀ N₁))))
          have hb₁ : Semiterm.valm ℕ ![] env (v 1)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₁ env) (le_trans
              (Gexp_iter_le_iter (le_max_right c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_right N₀ N₁))))
          have hmul : Semiterm.valm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.mul v)
              = Semiterm.valm ℕ ![] env (v 0) * Semiterm.valm ℕ ![] env (v 1) := by
            simp only [Semiterm.valm, Semiterm.val_func]; rfl
          rw [hmul, Function.iterate_succ_apply']
          refine le_trans (mul_le_Gexp_max _ _) (Gexp_monotone ?_)
          exact max_le hb₀ hb₁

/-- Bridge: the `atomTrue`-evaluator value of the `asg`-closed term is the direct
`env`-valuation. -/
theorem stdClosedVal_asg (env : ℕ → ℕ) (t : SyntacticTerm ℒₒᵣ) :
    stdClosedVal (Embedding.asg env t) = Semiterm.valm ℕ ![] env t := by
  show Semiterm.val _ (fun _ => 0) (fun _ => 0) (Rew.rewrite (fun x => nm (env x)) t) = _
  rw [Semiterm.val_rewrite]
  have he : (fun _ => 0 : Fin 0 → ℕ) = ![] := funext (fun x => x.elim0)
  rw [he]
  congr 1
  funext x
  exact Embedding.valm_nm (env x) (fun _ => 0)

/-- **The `exs`/V3 witness gate**: the closed witness's standard value is dominated by
structurally many `Gexp`-iterates of the env-sup. -/
theorem stdClosedVal_asg_le_Gexp_iter (t : SyntacticTerm ℒₒᵣ) :
    ∃ c N : ℕ, ∀ env : ℕ → ℕ,
      stdClosedVal (Embedding.asg env t) ≤ Gexp^[c] (envSup env N) := by
  obtain ⟨c, N, h⟩ := term_val_le_Gexp_iter t
  exact ⟨c, N, fun env => by rw [stdClosedVal_asg]; exact h env⟩

end GoodsteinPA.E1EmbeddingGrind

#print axioms GoodsteinPA.E1EmbeddingGrind.term_val_le_Gexp_iter
#print axioms GoodsteinPA.E1EmbeddingGrind.stdClosedVal_asg_le_Gexp_iter
