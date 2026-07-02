/-
# SPIKE W4 — the operator cut-elim CONTROL-RAISING design spike (operator-commissioned, 2026-07-01)

Deciding experiment #2 of `MASTERPLAN-2026-07-01-ZERO-AXIOMS.md` §5 (W4).  This file is a **typed
skeleton**, NOT a proof campaign: the bounded rank-lowering step `operatorCutElimStepAux` is
assembled from one named `sorry`ed lemma per `Zekd` rule case by a REAL (non-`sorry`) induction,
and exactly ONE case — the **non-principal `allω` traversal**, the spike's mandated design
question — is proven for real.  Sorries elsewhere are expected and correct.
See `SPIKE-W4-CONTROL.md` (mandate) and `SPIKE-W4-VERDICT.md` (result).

Structural template: `src/GoodsteinPA/ZinftyGen.lean:1604` (`cutElimStepAux`, the unbounded
recursion).  Substrate: the control-ordinal operator calculus `Zekd`/`ZekdProv`/`ZekdSomeK`
(`src/GoodsteinPA/OperatorZinfty.lean`).

## The design answer this skeleton encodes (see the verdict for the full argument)

* **`expTower α := ω^α`** (as a literal `ONote`, so `< ε₀` for free) is the ordinal transform,
  exactly as in the unbounded step (`Provable (ω^(o d)) c Γ`).
* **`raise e α := e + ω^α`** is the family-uniform control raise — a function of the STRUCTURE
  `(e, α)` only, never of an ω-branch index.  Its two load-bearing properties are
  `raise_lt_raise` (strict monotonicity in `α`, via `Zekd.add_lt_add_left_NF`) and
  `norm_raise_le` (norm cost `≤ norm e + max (norm α) 1`).  The `e + f α` shape is the
  `hardy_add_collapse` (`H_{e+α} = H_e ∘ H_α`, `Hardy.lean:1686`) nesting shape.
* **The recursion runs at the `Zekd`/`ZekdProv` level (concrete witness index `k`), NOT at the
  `ZekdSomeK` surface** — the candidate someK-level statement cannot drive its own induction: the
  ω-case IH would give `∀ n, ∃ Kₙ, …` and `Zekd.allω` needs the swapped `∃ K, ∀ n, … max K n …`
  (the same `∀∃`↛`∃∀` trap SPIKE-W3 hit; same amendment).  The someK statement
  `operatorCutElimStep` is then a REAL corollary at the root (`mono_k` + `ofProv`).
* **Budget discipline**: the norm-carrying `ZekdProv` wrapper (the `cutReduceAllAux` discipline,
  `OperatorZinfty.lean:756`) threads `norm α < k + d` through the recursion; the conclusion's
  `d`-budget is `d + norm e + 1` — the `+ norm e + 1` pays the per-branch `mono_e` side condition
  `norm (raise e (β n)) ≤ max k n + d_out` (see `step_allω`).
-/
import GoodsteinPA.OperatorZinfty

namespace GoodsteinPA.SpikeW4

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZinfty

/-! ## The two explicit `ONote` transforms (spike objective #1) -/

/-- `ω^α` as an explicit `ONote` (`oadd α 1 0`).  Trivially `< ε₀`: every `ONote` denotes below
`ε₀`.  This is the bounded twin of the unbounded step's `Ordinal.omega0 ^ (o d)` bound. -/
def expTower (α : ONote) : ONote := oadd α 1 0

theorem expTower_NF {α : ONote} (hα : α.NF) : (expTower α).NF :=
  hα.oadd 1 NFBelow.zero

/-- Strict monotonicity of `ω^·` on notations (leading-exponent comparison). -/
theorem expTower_lt_expTower {β α : ONote} (hβ : β.NF) (h : β < α) :
    expTower β < expTower α :=
  oadd_lt_oadd_1 (expTower_NF hβ) h

@[simp] theorem norm_expTower (α : ONote) : norm (expTower α) = max (norm α) 1 :=
  Zekd.norm_omegaPow

/-- **The family-uniform control raise** `raise e α := e + ω^α` — a function of `(e, α)`
(structure) only, NEVER of an ω-branch index.  This is the spike's design pin: the witness-bound
control after one rank-lowering pass over a derivation of ordinal `α` at control `e`.  The
`e + f α` additive shape is exactly what `hardy_add_collapse` (`H_{e+α} = H_e ∘ H_α`) collapses,
so nested raises stay a single Hardy level.  `< ε₀` trivially (any `ONote`). -/
def raise (e α : ONote) : ONote := e + expTower α

theorem raise_NF {e α : ONote} (he : e.NF) (hα : α.NF) : (raise e α).NF := by
  haveI := he; haveI := expTower_NF hα
  exact ONote.add_nf e (expTower α)

/-- Strict monotonicity of the raise in the ordinal argument — THE uniformization tool: an
ω-family's per-branch raised controls `raise e (β n)` all sit strictly below the single
node-level `raise e α` (since `β n < α`), so `ZekdProv.mono_e` lifts every branch to the SAME
control.  This is what makes the raise family-uniform. -/
theorem raise_lt_raise {e β α : ONote} (he : e.NF) (hβ : β.NF) (hα : α.NF) (h : β < α) :
    raise e β < raise e α :=
  Zekd.add_lt_add_left_NF he (expTower_NF hβ) (expTower_NF hα) (expTower_lt_expTower hβ h)

/-- Norm cost of the raise: `norm (raise e α) ≤ norm e + max (norm α) 1`.  This is what the
`+ norm e + 1` in the step's `d`-budget pays for (the `mono_e` budget side condition
`norm e_src ≤ k + d`). -/
theorem norm_raise_le {e α : ONote} (he : e.NF) (hα : α.NF) :
    norm (raise e α) ≤ norm e + max (norm α) 1 := by
  have h := Zekd.norm_add_le he (expTower_NF hα)
  simpa [raise] using h

/-! ## One named case lemma per `Zekd` rule (spike objective #2)

Each mirrors an arm of the unbounded `cutElimStepAux` (`ZinftyGen.lean:1604`), stated over the
norm-carrying `ZekdProv` wrapper with the running-index discipline of `cutReduceAllAux`
(`OperatorZinfty.lean:789`): hypotheses are exactly what the master induction's arm can supply
(the constructor's own side conditions + the motive's package `e.NF`, `α.NF`, `norm α < k + d`,
+ the IHs at the premise indices).  Only `step_allω` — the mandated case — is proven. -/

/-- `axL` leaf: re-form the axiom at witness ordinal `0` (`ZekdProv`'s `≤`-slack).
Transparently `Zekd.axL` + `norm 0 = 0`; left `sorry` per the spike's one-case mandate. -/
theorem step_axL {e α : ONote} {k d c ar : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticTerm ℒₒᵣ)
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  sorry

/-- `verumR` leaf.  Transparently `Zekd.verumR` at witness ordinal `0`. -/
theorem step_verumR {e α : ONote} {k d c : ℕ} {Γ : Seq}
    (h : (⊤ : Form) ∈ Γ) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  sorry

/-- `trueRel` leaf: keep the leaf at its ORIGINAL ordinal `α` (`≤ expTower α` via the wrapper's
slack); the norm side condition rides `hnorm` and the enlarged budget. -/
theorem step_trueRel {e α : ONote} {k d c ar : ℕ} {Γ : Seq}
    (heNF : e.NF) (hαNF : α.NF) (hnorm : norm α < k + d)
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticTerm ℒₒᵣ)
    (htrue : atomTrue (Semiformula.rel r v)) (hmem : Semiformula.rel r v ∈ Γ) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  sorry

/-- `trueNrel` leaf (dual of `step_trueRel`). -/
theorem step_trueNrel {e α : ONote} {k d c ar : ℕ} {Γ : Seq}
    (heNF : e.NF) (hαNF : α.NF) (hnorm : norm α < k + d)
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticTerm ℒₒᵣ)
    (htrue : atomTrue (Semiformula.nrel r v)) (hmem : Semiformula.nrel r v ∈ Γ) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  sorry

/-- `wk` (same-ordinal sequent weakening): transparently `ZekdProv.weakening`. -/
theorem step_wk {e α : ONote} {k d c : ℕ} {Δ Γ : Seq}
    (hsub : Δ ⊆ Γ)
    (IH : ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Δ) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  sorry

/-- `weak` (ordinal-raising weakening): `mono_e` the IH's control up from `raise e β` to
`raise e α` (budget paid exactly as in `step_allω`), then ride the wrapper's `≤`-slack
`expTower β ≤ expTower α` (`ZekdProv.mono`) and weaken the sequent. -/
theorem step_weak {e α β : ONote} {k d c : ℕ} {Δ Γ : Seq}
    (heNF : e.NF) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (hτ : norm β < k + d) (hnorm : norm α < k + d) (hsub : Δ ⊆ Γ)
    (IH : ZekdProv (expTower β) (raise e β) k (d + norm e + 1) c Δ) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  sorry

/-- `andI` traversal: the FINITE (2-branch) instance of the uniformization pattern — `mono_e`
both IHs to the shared `raise e α`, unpack, `Zekd.andI`, re-wrap.  Same shape as `step_allω`
with `∀ n` replaced by two premises; deliberately left `sorry` per the one-case mandate. -/
theorem step_andI {e α βφ βψ : ONote} {k d c : ℕ} {Γ : Seq} {φ ψ : Form}
    (heNF : e.NF) (hβφ : βφ < α) (hβψ : βψ < α)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
    (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d) (hnorm : norm α < k + d)
    (IHφ : ZekdProv (expTower βφ) (raise e βφ) k (d + norm e + 1) c (insert φ Γ))
    (IHψ : ZekdProv (expTower βψ) (raise e βψ) k (d + norm e + 1) c (insert ψ Γ)) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c (insert (φ ⋏ ψ) Γ) := by
  sorry

/-- `orI` traversal (single-premise; `mono_e` + `Zekd.orI`). -/
theorem step_orI {e α β : ONote} {k d c : ℕ} {Γ : Seq} {φ ψ : Form}
    (heNF : e.NF) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (hτ : norm β < k + d) (hnorm : norm α < k + d)
    (IH : ZekdProv (expTower β) (raise e β) k (d + norm e + 1) c (insert φ (insert ψ Γ))) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c (insert (φ ⋎ ψ) Γ) := by
  sorry

/-- **THE MANDATED CASE — the non-principal `allω` traversal** (`SPIKE-W4-CONTROL.md`'s one open
design question), **proven for real**.

Per premise `n` the IH hands back a reduced derivation at the *branch-dependent* raised control
`raise e (β n)`.  Re-assembling the ω-node needs ONE control for the whole family; the spike's
question is whether a `(e, α)`-only function suffices.  It does:

1. `β n < α` and `raise` is strictly monotone in its ordinal argument (`raise_lt_raise`), so
   every branch control sits strictly below the single node-level `raise e α`;
2. `ZekdProv.mono_e` lifts branch `n` from `raise e (β n)` to `raise e α`; its budget side
   condition `norm (raise e (β n)) ≤ max k n + (d + norm e + 1)` is paid by `norm_raise_le` +
   the rule's own norm side condition `norm (β n) < max k n + d` — this is exactly what the
   `+ norm e + 1` in the step budget exists for, and it is UNIFORM in `n`;
3. the lifted family (now at one control, with per-branch ordinals `≤ expTower (β n) <
   expTower α` and norms carried by the wrapper) re-enters `Zekd.allω` at base index `k`.

No branch-dependent control, no `∃K` swap, no `hardy_add_collapse` needed in THIS case (the
collapse is the principal-cut tool).  FAIL-trigger T-W4 does not fire here. -/
theorem step_allω {e α : ONote} {k d c : ℕ} {Γ : Seq}
    {χ : SyntacticSemiformula ℒₒᵣ 1} {β : ℕ → ONote}
    (heNF : e.NF)
    (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
    (hτ : ∀ n, norm (β n) < max k n + d)
    (hnorm : norm α < k + d)
    (IH : ∀ n, ZekdProv (expTower (β n)) (raise e (β n)) (max k n) (d + norm e + 1) c
      (insert (χ/[nm n]) Γ)) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c (insert (∀⁰ χ) Γ) := by
  -- (1)+(2): lift every branch to the single family-uniform control `raise e α`.
  have IH' : ∀ n, ZekdProv (expTower (β n)) (raise e α) (max k n) (d + norm e + 1) c
      (insert (χ/[nm n]) Γ) := by
    intro n
    refine ZekdProv.mono_e (raise_NF heNF (hβNF n)) (raise_NF heNF hαNF)
      (raise_lt_raise heNF (hβNF n) hαNF (hβ n)) ?_ (IH n)
    -- the budget side condition: norm (raise e (β n)) ≤ max k n + (d + norm e + 1)
    have h1 := norm_raise_le heNF (hβNF n)
    have h2 := hτ n
    omega
  -- (3): extract the reduced family (the wrapper is an `∃`; `choose` the per-branch data).
  have IH'' : ∀ n, ∃ α', α' ≤ expTower (β n) ∧ α'.NF ∧
      norm α' < max k n + (d + norm e + 1) ∧
      Zekd α' (raise e α) (max k n) (d + norm e + 1) c (insert (χ/[nm n]) Γ) := IH'
  choose β' hle hNF hnorm' D using IH''
  -- re-enter the ω-rule at the uniform raised control and base index `k`.
  refine ZekdProv.of (expTower_NF hαNF) ?_
    (Zekd.allω χ β'
      (fun n => lt_of_le_of_lt (hle n) (expTower_lt_expTower (hβNF n) (hβ n)))
      hNF (expTower_NF hαNF) hnorm' D)
  -- the node's own norm side condition: norm (ω^α) = max (norm α) 1 < k + (d + norm e + 1)
  simp only [norm_expTower]
  omega

/-- `exI` traversal: `mono_e` the IH (as in `step_allω`), and re-pay the witness bound
`n ≤ hardy e (k + d) ≤ hardy (raise e α) (k + (d + norm e + 1))` — hardy-monotone in the
argument (`hardy_monotone`) and in the ordinal along a reachability chain (the same
`norm e ≤ k + d`-gated raise `Zekd.mono_e` performs internally). -/
theorem step_exI {e α β : ONote} {k d c n : ℕ} {Γ : Seq}
    {φ : SyntacticSemiformula ℒₒᵣ 1}
    (heNF : e.NF) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (hτ : norm β < k + d) (hnorm : norm α < k + d)
    (hbound : n ≤ hardy e (k + d))
    (IH : ZekdProv (expTower β) (raise e β) k (d + norm e + 1) c (insert (φ/[nm n]) Γ)) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c (insert (∃⁰ φ) Γ) := by
  sorry

/-- Kept cut (rank `< c`): `mono_e`-unify the two IHs at `raise e α`, re-cut at the lowered
rank (`Zekd.cut` with `hkeep`), absorb `osucc`-style ordinal bookkeeping in the wrapper's
`≤`-slack below `expTower α` (`ω^α` is additively principal). -/
theorem step_cut_keep {e α βφ βψ : ONote} {k d c : ℕ} {Γ : Seq} {φ : Form}
    (heNF : e.NF) (hβφ : βφ < α) (hβψ : βψ < α)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
    (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d) (hnorm : norm α < k + d)
    (hkeep : φ.complexity < c)
    (IH1 : ZekdProv (expTower βφ) (raise e βφ) k (d + norm e + 1) c (insert φ Γ))
    (IH2 : ZekdProv (expTower βψ) (raise e βψ) k (d + norm e + 1) c (insert (∼φ) Γ)) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  sorry

/-- **Principal cut (rank exactly `c`)** — cites the BANKED reduction surfaces per the mandate
(do NOT re-prove): ∧/∨ → `Zekd.cutReduceConj/Disj` (`OperatorZinfty.lean:664/:686`); ∀/∃ →
`cutReduceAllAux` (`:789`) composed with the control raise (`cutReduceAllAux_control` shape,
`:2283`), where `hardy_add_collapse` keeps the nested control a single Hardy level.

Two obligations the skeleton SURFACES here for the W4 phase (see the verdict):
* the rank-0 sub-cases need bounded twins of `ZinftyGen`'s `atomCut`/`removeFalsum` — NOT yet
  banked in `OperatorZinfty`;
* the ∀/∃ sub-case needs `cutReduceAllAux` generalized from the FIXED-family index `k₀` to the
  running index `max k₀ n` (the known `OperatorZinfty.lean:764` scope gap), and its
  `+ norm (fam ordinal) + 1` d-bump does NOT fit this statement's uniform `d + norm e + 1`
  budget under an enclosing ω-node — the located hard core of W4 (verdict §"the residual"). -/
theorem step_cut_principal {e α βφ βψ : ONote} {k d c : ℕ} {Γ : Seq} {φ : Form}
    (heNF : e.NF) (hβφ : βφ < α) (hβψ : βψ < α)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
    (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d) (hnorm : norm α < k + d)
    (hξeq : φ.complexity = c)
    (IH1 : ZekdProv (expTower βφ) (raise e βφ) k (d + norm e + 1) c (insert φ Γ))
    (IH2 : ZekdProv (expTower βψ) (raise e βψ) k (d + norm e + 1) c (insert (∼φ) Γ)) :
    ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  sorry

/-! ## The assembled step (spike objective #2: a REAL induction) -/

/-- **The bounded rank-lowering recursion** (`cutElimStepAux`'s bounded twin; Towsner §19.7 with
§19.6 witness control).  A `Zekd` derivation of cut rank `< c + 1` at `(α, e, k, d)` becomes
cut-rank `< c` at ordinal `ω^α`, the family-uniform raised control `e + ω^α`, the SAME witness
base index `k`, and `d`-budget `d + norm e + 1`.

The induction is REAL (non-`sorry`): every arm is a single `exact` into its named case lemma, so
the statement's coherence under the global recursion — IH shapes, running-index discipline, the
uniform raise — is machine-checked even though most cases' proofs are disclosed sorries.  The
`c' = c + 1` equation threads the rank because `c'` is an INDEX of `Zekd` (unlike the unbounded
`Deriv`, whose `cr` is a function). -/
theorem operatorCutElimStepAux :
    ∀ {α e : ONote} {k d c' : ℕ} {Γ : Seq}, Zekd α e k d c' Γ →
      ∀ {c : ℕ}, c' = c + 1 → e.NF → α.NF → norm α < k + d →
      ZekdProv (expTower α) (raise e α) k (d + norm e + 1) c Γ := by
  intro α e k d c' Γ D
  induction D with
  | axL r v hp hn =>
      intro c _hc _heNF _hαNF _hnorm
      exact step_axL r v hp hn
  | verumR h =>
      intro c _hc _heNF _hαNF _hnorm
      exact step_verumR h
  | trueRel r v htrue _hτ _hANF hmem =>
      intro c _hc heNF hαNF hnorm
      exact step_trueRel heNF hαNF hnorm r v htrue hmem
  | trueNrel r v htrue _hτ _hANF hmem =>
      intro c _hc heNF hαNF hnorm
      exact step_trueNrel heNF hαNF hnorm r v htrue hmem
  | wk hsub _dd ih =>
      intro c hc heNF hαNF hnorm
      exact step_wk hsub (ih hc heNF hαNF hnorm)
  | weak hβ hβNF _hANF hτ hsub _dd ih =>
      intro c hc heNF hαNF hnorm
      exact step_weak heNF hβ hβNF hαNF hτ hnorm hsub (ih hc heNF hβNF hτ)
  | andI φ ψ hβφ hβψ hβφNF hβψNF _hANF hτφ hτψ _dφ _dψ ihφ ihψ =>
      intro c hc heNF hαNF hnorm
      exact step_andI heNF hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ hnorm
        (ihφ hc heNF hβφNF hτφ) (ihψ hc heNF hβψNF hτψ)
  | orI φ ψ hβ hβNF _hANF hτ _dd ih =>
      intro c hc heNF hαNF hnorm
      exact step_orI heNF hβ hβNF hαNF hτ hnorm (ih hc heNF hβNF hτ)
  | allω φ β hβ hβNF _hANF hτ _dd ih =>
      intro c hc heNF hαNF hnorm
      exact step_allω heNF hβ hβNF hαNF hτ hnorm
        (fun n => ih n hc heNF (hβNF n) (hτ n))
  | exI φ n hβ hβNF _hANF hτ hbound _dd ih =>
      intro c hc heNF hαNF hnorm
      exact step_exI heNF hβ hβNF hαNF hτ hnorm hbound (ih hc heNF hβNF hτ)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF _hANF hτφ hτψ _d₁ _d₂ ih₁ ih₂ =>
      intro c hc heNF hαNF hnorm
      by_cases hkeep : φ.complexity < c
      · exact step_cut_keep heNF hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ hnorm hkeep
          (ih₁ hc heNF hβφNF hτφ) (ih₂ hc heNF hβψNF hτψ)
      · have hlt : φ.complexity < c + 1 := hc ▸ hcompl
        have hξeq : φ.complexity = c := by omega
        exact step_cut_principal heNF hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ hnorm hξeq
          (ih₁ hc heNF hβφNF hτφ) (ih₂ hc heNF hβψNF hτψ)

/-- **The pinned step statement at the `ZekdSomeK` surface** (`SPIKE-W4-CONTROL.md` objective #1,
with the ONE mandatory amendment: the conclusion's `d`-budget is `d + norm e + 1`, not `d` — the
`mono_e` uniformization is not free, and the constant is a function of the input control only).

A REAL corollary of the recursion (this proof is complete): the wrapper's `∃K` is opened at the
ROOT only, `mono_k`'d up to pay the root norm side condition, and re-packed by `ofProv`.  This is
where the `∃K`-compositionality question of the verdict criteria is answered: the existential
never enters the induction, so it cannot break the IHs. -/
theorem operatorCutElimStep {α e : ONote} {d c : ℕ} {Γ : Seq}
    (hα : α.NF) (he : e.NF)
    (h : ZekdSomeK α e d (c + 1) Γ) :
    ZekdSomeK (expTower α) (raise e α) (d + norm e + 1) c Γ := by
  rcases h with ⟨K, D⟩
  have D' : Zekd α e (max K (norm α + 1)) d (c + 1) Γ := D.mono_k (le_max_left _ _)
  have hprov : ZekdProv (expTower α) (raise e α) (max K (norm α + 1)) (d + norm e + 1) c Γ :=
    operatorCutElimStepAux D' rfl he hα (by omega)
  exact ZekdSomeK.ofProv (expTower_NF hα) hprov

end GoodsteinPA.SpikeW4

-- Real axiom footprint of the assembled step (expect `sorryAx` + the 3 canonical; NO new
-- `axiom` declarations anywhere in this file):
#print axioms GoodsteinPA.SpikeW4.operatorCutElimStep
-- The mandated case is genuinely sorry-free (choice enters via `choose`):
#print axioms GoodsteinPA.SpikeW4.step_allω
