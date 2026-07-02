/-
# SPIKE Z1 — the `Zᵉ` seam + Σ₁-instance spike (operator-commissioned, 2026-07-02)

Deciding experiment #4 (`SPIKE-Z1-SEAMS.md`), first session of the `Zᵉ` fork green-lit after
T-W4B fired (`SPIKE-W4B-VERDICT.md`).  This file pins a **minimal `Zeh` core** and kernel-runs
the two W4B-refuted seams in `Zeh` form, plus the concrete-`H` / read-off probe.  It is a
probe, NOT a calculus rebuild: the two reductions are pinned `sorry` (statement-level, per the
W4B discipline) and every seam-crossing membership fact is a REAL closure proof.

## Structure

* §0 duplicates the SPIKE-W4 transforms (`expTower`, `raise`, the `wmul` family) — `wip/`
  files are not importable modules.
* §1 is the operator layer: `IsOperator` (the pin's four closure conditions), the inductive
  closure `Cl`, the relativization `adjoin`/`relOp` (the work order's recommended
  generation-from-`gen ∪ {ofNat n}` formulation), and THREE kernel findings that shape the
  amended pin:
  - **(K1) `Cl_of_NF` (vacuity)**: every normal-form `ONote` lies in `Cl S` for EVERY `S` —
    at the `ε₀` level, any set closed under the pin's four operations is everything, so
    set-membership carries no numeric information.  (This matches the literature: Buchholz
    operators are genuinely restrictive only at impredicative levels, through the
    collapsing-function clauses of `C_γ(δ)`; cf. Freund, *A second course on ordinal
    analysis*, Def. 3.10/5.4.  At the `ε₀`/PA level the numeric content of
    Buchholz–Wainer 1987 lives in the BOUNDING LEMMA's parameters, not in operator
    membership.)
  - **(K2) `finite_part_unbounded` + `mono_e_membership_gate_refuted`**: the pin's `exI`
    designation "`n ≤ hardy e m` for some `m ∈ H ∩ ℕ`" is kernel-refuted as a bound source
    (the finite part is all of ℕ), and a membership-gated `mono_e` is kernel-refuted
    (`hardy` genuinely DECREASES under the pinned additive raise at small arguments:
    `raise (ofNat 5) 1 = ω` by computation and `hardy ω 0 = 1 < 5 = hardy (ofNat 5) 0`).
    The amended designation (A1): the numeric argument is a judgment-carried STAGE `m`,
    threaded `max m n` at ω-premises — Buchholz–Wainer's Bounding Lemma form (witness
    bounded by a fast-growing function at the sequent's numeric parameters).
  - **(K3) `norm_ball_not_add_closed`**: no norm-ball is `+`-closed, so no concrete `H`
    can both satisfy the closure conditions and certify norms — (K1) is not an artifact
    of a bad representation choice.
* §2 pins the minimal `Zeh` core: exactly the mandated rules (`axL`, `allω` at the
  relativization + running stage, `exI` at `n ≤ hardy e m`, `cut`, `weak`, plus the `wk`
  companion) with every numeric side condition of `Zekd` replaced by `Cl`-membership and
  the `ZekdProv` NORM-wrapper deleted (the `≤`-slack/NF/membership wrapper `ZehProv`
  remains — only the norm clause dies).  `mono_H` (the pin's replacement for
  `mono_k`/`mono_d`) is a REAL proof.
* §3 pins the two grind-shaped leaves `sorry` (disclosed): `allInv_Zeh` (the inversion
  suite is lap-2+ rebuild) and `cutReduceAllAuxRunning_Zeh` (the W4B running-family
  reduction, output ordinal `osucc (α + γ)`, output control `raise e α`, budget slot
  REPLACED by membership — statement under test, not the port).
* §4 runs the two seams:
  - `probe_cut_all_arm_Zeh` (**seam-1 reversal**, a REAL proof): the ∀/∃ arm at an
    ω-branch consuming both pins.  Where W4B's arm emitted the unabsorbable slot
    `(d + norm e + 1) + norm αf + 1`, the `Zeh` arm's only output-side obligation is
    membership `Cl (adjoin H nBr) (osucc (αf + γf))` — derived by TWO constructor steps
    (`seam1_membership_absorbed`), kernel-real, no sorried membership.
  - `two_level_config_Zeh` + `probe_allomega_reassembly_Zeh` (**seam-2 reversal**,
    sorry-free): the W4B branch-unbounded family `ω·(n+1)` (premise norms `n+1`) and the
    reduction-output class `osucc (ω·(n+1) + ω·(n+1))` both re-enter `Zeh.allω` — the
    branch-dependent quantity is a per-branch MEMBER (an `n`-sized closure tree,
    `wmul_mem`), and there is no uniform slot to overflow.
* §5 is the Q2 probe: `IsOperator (Cl S)` (proven), the read-off lemma
  `readoff_sigma1` — the Buchholz–Wainer Bounding-Lemma analog, PROVEN (not just
  statable) at rank 0 for the ∀-free Σ₁ shape: witnesses are bounded by `hardy e m`, the
  judgment's control and stage; membership plays NO role in the bound — plus a concrete
  two-node kernel instance.

## Amendments to the pin surfaced by this probe (verdict §amendments)

* **A1 (stage designation)**: `Zeh` carries a stage `m : ℕ`; `exI` bounds its witness by
  `hardy e m`; ω-premises run at `(adjoin H n, max m n)`.  "Some `m ∈ H ∩ ℕ`" is
  kernel-refuted (K2/`finite_part_unbounded`).
* **A2 (common-control motive)**: the step motive must hold its IHs at ONE control (the
  per-branch raise-then-`mono_e`-unify mechanism of SPIKE-W4's `step_allω` has NO `Zeh`
  analog: its budget gate was paid by `Zekd`'s numeric `hτ`, which `Zeh` deletes, and
  membership cannot pay it — `mono_e_membership_gate_refuted`).  The probes below state
  the arm's IHs at a common control `E` accordingly.

Standing doctrine honored: no `src/` edits, no new `axiom` declarations, no someK-level
existentials inside inductions, `e` constant through a derivation, branch dependence only
via the relativization.
-/
import GoodsteinPA.OperatorZinfty

namespace GoodsteinPA.SpikeZ1

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZinfty

/-! ## §0 The SPIKE-W4 transforms (duplicated from `wip/SpikeW4CutElim.lean` /
`wip/SpikeW4BBudget.lean`, which are not importable modules; definitions identical). -/

/-- `ω^α` as an explicit `ONote` (`oadd α 1 0`) — SPIKE-W4's ordinal transform. -/
def expTower (α : ONote) : ONote := oadd α 1 0

theorem expTower_NF {α : ONote} (hα : α.NF) : (expTower α).NF :=
  hα.oadd 1 NFBelow.zero

theorem expTower_lt_expTower {β α : ONote} (hβ : β.NF) (h : β < α) :
    expTower β < expTower α :=
  oadd_lt_oadd_1 (expTower_NF hβ) h

@[simp] theorem norm_expTower (α : ONote) : norm (expTower α) = max (norm α) 1 :=
  Zekd.norm_omegaPow

/-- SPIKE-W4's family-uniform control raise `raise e α := e + ω^α`. -/
def raise (e α : ONote) : ONote := e + expTower α

theorem raise_NF {e α : ONote} (he : e.NF) (hα : α.NF) : (raise e α).NF := by
  haveI := he; haveI := expTower_NF hα
  exact ONote.add_nf e (expTower α)

theorem raise_lt_raise {e β α : ONote} (he : e.NF) (hβ : β.NF) (hα : α.NF) (h : β < α) :
    raise e β < raise e α :=
  Zekd.add_lt_add_left_NF he (expTower_NF hβ) (expTower_NF hα) (expTower_lt_expTower hβ h)

/-- `ω·(m+1)` as an explicit `ONote` (the W4B two-level-configuration family). -/
def wmul (m : ℕ) : ONote := oadd 1 m.succPNat 0

theorem wmul_NF (m : ℕ) : (wmul m).NF := nf_one.oadd m.succPNat NFBelow.zero

@[simp] theorem norm_one : norm (1 : ONote) = 1 := rfl

@[simp] theorem norm_wmul (m : ℕ) : norm (wmul m) = m + 1 := by
  rw [wmul, norm_oadd, norm_one, norm_zero, Nat.succPNat_coe]
  omega

/-- Equal-exponent CNF merge, parametric (kernel-computed; W4B's rail brick). -/
theorem wmul_add_wmul (a b : ℕ) :
    wmul a + wmul b = oadd 1 (a.succPNat + b.succPNat) 0 := rfl

theorem one_lt_omegaO : (1 : ONote) < ONote.omega :=
  oadd_lt_oadd_1 nf_one ONote.zero_lt_one

theorem omegaO_NF : (ONote.omega).NF := nf_one.oadd 1 NFBelow.zero

theorem wmul_lt_expTower_omega (m : ℕ) : wmul m < expTower ONote.omega :=
  oadd_lt_oadd_1 (wmul_NF m) one_lt_omegaO

/-- Any `oadd 1 K 1`-shaped notation (an `osucc` of an `ω·K` notation) sits below `ω^ω`. -/
theorem osucc_omega_coeff_lt (K : ℕ+) : osucc (oadd 1 K 0) < expTower ONote.omega := by
  have h : (osucc (oadd 1 K 0)).NF := osucc_NF (nf_one.oadd K NFBelow.zero)
  rw [show osucc (oadd 1 K 0) = oadd 1 K 1 from rfl] at h ⊢
  exact oadd_lt_oadd_1 h one_lt_omegaO

theorem osucc_wmul_lt_expTower_omega (m : ℕ) : osucc (wmul m) < expTower ONote.omega :=
  osucc_omega_coeff_lt m.succPNat

/-! ## §1 The operator layer

`IsOperator` bundles the pin's four closure conditions.  `Cl S` is the inductive closure of a
generator set `S` under exactly those operations (the work order's recommended
"generation from `gen`" formulation): membership witnesses are finite trees, closure lemmas
are constructor applications, and `IsOperator (Cl S)` is immediate.  The relativization
`H[n]` is generation from the adjoined generator set `adjoin H n`. -/

/-- The pin's closure conditions: closed under `+`, `ω^·` (`expTower`), `osucc`, `ofNat`. -/
structure IsOperator (H : ONote → Prop) : Prop where
  ofNat_mem : ∀ n : ℕ, H (ONote.ofNat n)
  add_mem : ∀ {α β : ONote}, H α → H β → H (α + β)
  expTower_mem : ∀ {α : ONote}, H α → H (expTower α)
  osucc_mem : ∀ {α : ONote}, H α → H (osucc α)

/-- Inductive closure of a generator set under the pin's four operations.  Membership
witnesses are finite trees — the "represented, countable" operator shape. -/
inductive Cl (S : ONote → Prop) : ONote → Prop
  | base {β : ONote} : S β → Cl S β
  | ofNat (n : ℕ) : Cl S (ONote.ofNat n)
  | add {α β : ONote} : Cl S α → Cl S β → Cl S (α + β)
  | expTower {α : ONote} : Cl S α → Cl S (expTower α)
  | osucc {α : ONote} : Cl S α → Cl S (osucc α)

/-- The closure of ANY generator set is an operator (the pin's conditions, verbatim). -/
theorem isOperator_Cl (S : ONote → Prop) : IsOperator (Cl S) where
  ofNat_mem := Cl.ofNat
  add_mem := Cl.add
  expTower_mem := Cl.expTower
  osucc_mem := Cl.osucc

/-- Closure is monotone in the generators (feeds `Zeh.mono_H`). -/
theorem Cl_mono {S S' : ONote → Prop} (h : ∀ β, S β → S' β) :
    ∀ {β : ONote}, Cl S β → Cl S' β := by
  intro β hβ
  induction hβ with
  | base hb => exact Cl.base (h _ hb)
  | ofNat n => exact Cl.ofNat n
  | add _ _ ih₁ ih₂ => exact Cl.add ih₁ ih₂
  | expTower _ ih => exact Cl.expTower ih
  | osucc _ ih => exact Cl.osucc ih

/-- `Cl` is the LEAST operator over its generators: closure membership maps into any
`IsOperator` set containing the generators (the bridge between the abstract-`H` and
generated-`H` formulations of the pin). -/
theorem Cl_sub_of_isOperator {S H : ONote → Prop} (hop : IsOperator H)
    (hSH : ∀ β, S β → H β) : ∀ {β : ONote}, Cl S β → H β := by
  intro β hβ
  induction hβ with
  | base hb => exact hSH _ hb
  | ofNat n => exact hop.ofNat_mem n
  | add _ _ ih₁ ih₂ => exact hop.add_mem ih₁ ih₂
  | expTower _ ih => exact hop.expTower_mem ih
  | osucc _ ih => exact hop.osucc_mem ih

/-- The relativization generator set: adjoin the branch numeral (the work order's
"`H[n]` is generation from `gen ∪ {ofNat n}`").  `Zeh.allω` runs premise `n` over it. -/
def adjoin (H : ONote → Prop) (n : ℕ) : ONote → Prop := fun β => H β ∨ β = ONote.ofNat n

/-- The relativized operator `H[n]`. -/
def relOp (H : ONote → Prop) (n : ℕ) : ONote → Prop := Cl (adjoin H n)

/-! ### The kernel findings (K1)–(K3): what set-membership can and cannot carry at `ε₀`

These are the structural facts the verdict's amendments rest on.  They are POSITIVE for the
seams (every membership obligation is derivable, so no slot can overflow) and NEGATIVE for
any hope that membership certifies numeric (norm) information. -/

/-- `ω^e·n` (zero tail) is in every closure, by `n`-fold equal-exponent merge of
`expTower e` (kernel-computed merges via `repr_inj`). -/
theorem oaddZero_mem {S : ONote → Prop} {ε : ONote} (hε : ε.NF) (hεS : Cl S ε) :
    ∀ n : ℕ+, Cl S (oadd ε n 0) := by
  have key : ∀ k : ℕ, Cl S (oadd ε k.succPNat 0) := by
    intro k
    induction k with
    | zero => exact Cl.expTower hεS
    | succ k ih =>
        have hNF : (oadd ε k.succPNat 0).NF := hε.oadd _ NFBelow.zero
        have hNF' : (expTower ε).NF := expTower_NF hε
        have hNF'' : (oadd ε (k + 1).succPNat 0).NF := hε.oadd _ NFBelow.zero
        haveI := hNF; haveI := hNF'; haveI := hNF''
        have hsum : oadd ε k.succPNat 0 + expTower ε = oadd ε (k + 1).succPNat 0 := by
          refine repr_inj.mp ?_
          rw [repr_add (oadd ε k.succPNat 0) (expTower ε)]
          simp only [expTower, ONote.repr, Nat.succPNat_coe, PNat.one_coe,
            Nat.cast_one, add_zero, mul_one]
          have hc : (((k + 1).succ : ℕ) : Ordinal) = ((k.succ : ℕ) : Ordinal) + 1 := by
            push_cast
            try rfl
          rw [hc, mul_add, mul_one]
        exact hsum ▸ Cl.add ih (Cl.expTower hεS)
  intro n
  have h := key n.natPred
  rwa [PNat.succPNat_natPred] at h

/-- **(K1) VACUITY.**  Every normal-form notation is in the closure of EVERY generator set:
at the `ε₀` level, all of the notation system is hereditarily generated from numerals by
`+` and `ω^·`.  Consequence: the pinned membership side conditions are uniformly
dischargeable (good for the seams) and carry NO numeric information (fatal for any
membership-based bound). -/
theorem Cl_of_NF {S : ONote → Prop} : ∀ {β : ONote}, β.NF → Cl S β := by
  intro β
  induction β with
  | zero =>
      intro _
      exact Cl.ofNat 0
  | oadd ε n a ihε iha =>
      intro h
      have hε : ε.NF := h.fst
      have ha : a.NF := h.snd
      have hhead : (oadd ε n 0).NF := hε.oadd n NFBelow.zero
      haveI := hhead; haveI := ha; haveI := h
      have hsplit : oadd ε n 0 + a = oadd ε n a := by
        refine repr_inj.mp ?_
        rw [repr_add (oadd ε n 0) a]
        simp [ONote.repr]
      exact hsplit ▸ Cl.add (oaddZero_mem hε (ihε hε) n) (iha ha)

/-- **(K2a)** The finite part of every closure is ALL of ℕ — so the pin's original `exI`
designation "some `m ∈ H ∩ ℕ`" designates nothing (amendment A1: the stage is
judgment-carried). -/
theorem finite_part_unbounded (S : ONote → Prop) : ∀ m : ℕ, Cl S (ONote.ofNat m) :=
  Cl.ofNat

/-- The pinned additive raise genuinely ABSORBS a numeral base (kernel-computed):
`raise (ofNat 5) 1 = ofNat 5 + ω = ω`. -/
theorem raise_absorbs_base : raise (ONote.ofNat 5) 1 = ONote.omega := rfl

/-- **(K2b) The membership-gated `mono_e` is kernel-refuted.**  There are `e < e'` (indeed
`e' = raise e 1`, the pin's own raise shape), both normal-form, both in EVERY closure, with
`hardy e' m < hardy e m`: `hardy ω 0 = 1 < 5 = hardy (ofNat 5) 0`.  So no `Zeh`-rule
package of (NF, `<`, membership) facts can re-establish the `exI` bound after a raise —
`Zekd.mono_e`'s numeric gate `norm e ≤ k + d` does NOT "become `e ∈ H`"; the domination
content must come from elsewhere (amendment A2 / the verdict's re-scoping). -/
theorem mono_e_membership_gate_refuted :
    ∃ (e e' : ONote) (m : ℕ), e.NF ∧ e'.NF ∧ e < e' ∧ e' = raise e 1 ∧
      (∀ S : ONote → Prop, Cl S e ∧ Cl S e') ∧ hardy e' m < hardy e m := by
  refine ⟨ONote.ofNat 5, ONote.omega, 0, ?_, omegaO_NF, ?_, rfl, ?_, ?_⟩
  · exact ONote.nf_ofNat 5
  · rw [lt_def, repr_ofNat]
    have h : (ONote.omega).repr = Ordinal.omega0 := by simp [ONote.omega, ONote.repr]
    rw [h]
    exact Ordinal.natCast_lt_omega0 5
  · intro S
    exact ⟨Cl.ofNat 5, Cl.expTower (Cl.ofNat 1)⟩
  · rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega, hardy_ofNat]
    omega

/-- **(K3)** No norm-ball is `+`-closed (equal-exponent merges are additive in the head
coefficient — W4B's rail).  So (K1) is not a representation artifact: no concrete `H` can
satisfy the pinned closure conditions AND certify a norm bound. -/
theorem norm_ball_not_add_closed (R : ℕ) (hR : 1 ≤ R) :
    ∃ α β : ONote, norm α ≤ R ∧ norm β ≤ R ∧ R < norm (α + β) := by
  refine ⟨wmul (R - 1), wmul (R - 1), by rw [norm_wmul]; omega, by rw [norm_wmul]; omega, ?_⟩
  rw [wmul_add_wmul, norm_oadd, norm_one, norm_zero]
  have : ((R - 1).succPNat + (R - 1).succPNat : ℕ+) = (2 * R : ℕ) := by
    simp [Nat.succPNat, PNat.add_coe]
    omega
  omega

/-! ## §2 The minimal `Zeh` core (the pin, with amendment A1)

`Zeh α e H m c Γ`: derivation ordinal `α`, control ordinal `e` (constant through a
derivation; witness bound `hardy e m`), operator GENERATOR slot `H` (side conditions are
`Cl H`-membership — the judgment carries the ordinals-in-`H` demands directly, replacing
every `norm _ < k + d`), stage `m` (amendment A1 — the designated numeric argument of the
`exI` bound; the `Zᵉ` analog of the `k`-axis), cut rank `c`, sequent `Γ`.

Exactly the work order's mandated rules: `axL`, `allω` (premises at the relativization
`adjoin H n` and running stage `max m n`), `exI` (hardy-based witness bound at the stage),
`cut`, `weak` (source ordinal ∈ `Cl H` — the judge's re-anchor closure: every rule demands
its ordinals ∈ `H`, no retroactive absolution), plus `weak`'s same-ordinal companion `wk`
(sequent weakening; `Zekd` carries both, and the probes' sequent cleanup needs it).

The `ZekdProv` NORM-wrapper has no twin (its norm clause is deleted); the `≤`-slack/NF
bookkeeping wrapper survives as `ZehProv` below, with the norm clause replaced by
membership. -/
inductive Zeh : ONote → ONote → (ONote → Prop) → ℕ → ℕ → Seq → Prop
  | axL {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq} {ar : ℕ}
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zeh α e H m c Γ
  | wk {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Δ Γ : Seq}
      (hsub : Δ ⊆ Γ) (dd : Zeh α e H m c Δ) : Zeh α e H m c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {m c : ℕ} {Δ Γ : Seq}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zeh β e H m c Δ) : Zeh α e H m c Γ
  | allω {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq}
      (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c (insert (φ/[nm n]) Γ)) :
      Zeh α e H m c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq}
      (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ hardy e m)
      (dd : Zeh β e H m c (insert (φ/[nm n]) Γ)) : Zeh α e H m c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq}
      (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zeh βφ e H m c (insert φ Γ)) (d₂ : Zeh βψ e H m c (insert (∼φ) Γ)) :
      Zeh α e H m c Γ

namespace Zeh

/-- **`mono_H` — the pin's replacement for `mono_k`/`mono_d`** (a REAL proof): raise the
generator set and the stage together.  The `exI` bound rides `hardy_monotone` (argument
monotonicity — no ordinal-raise, hence no gate); memberships ride `Cl_mono`. -/
theorem mono_H : ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq},
    Zeh α e H m c Γ → ∀ {H' : ONote → Prop} {m' : ℕ},
    (∀ β, H β → H' β) → m ≤ m' → Zeh α e H' m' c Γ := by
  intro α e H m c Γ dd
  induction dd with
  | axL r v hp hn => intro H' m' _ _; exact Zeh.axL r v hp hn
  | wk hsub _ ih => intro H' m' hH hm; exact Zeh.wk hsub (ih hH hm)
  | weak hβ hβNF hαNF hβH hsub _ ih =>
      intro H' m' hH hm
      exact Zeh.weak hβ hβNF hαNF (Cl_mono hH hβH) hsub (ih hH hm)
  | allω φ β hβ hβNF hαNF hβH _ ih =>
      intro H' m' hH hm
      refine Zeh.allω φ β hβ hβNF hαNF
        (fun n => Cl_mono (fun γ hγ => hγ.imp_left (hH γ)) (hβH n))
        (fun n => ih n (fun γ hγ => hγ.imp_left (hH γ)) (max_le_max hm (le_refl n)))
  | exI φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro H' m' hH hm
      exact Zeh.exI φ n hβ hβNF hαNF (Cl_mono hH hβH)
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hH hm)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro H' m' hH hm
      exact Zeh.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (Cl_mono hH hβφH) (Cl_mono hH hβψH)
        (ih₁ hH hm) (ih₂ hH hm)

/-- Sequent weakening (height-preserving). -/
theorem weakening {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Δ Γ : Seq}
    (hsub : Δ ⊆ Γ) (dd : Zeh α e H m c Δ) : Zeh α e H m c Γ :=
  Zeh.wk hsub dd

end Zeh

/-- The `≤`-slack bookkeeping wrapper (`ZekdProv`'s twin with the NORM clause deleted —
the simplification the fork buys — and the ordinal's `Cl H`-membership carried instead:
"the judgment carries `α ∈ H` directly"). -/
def ZehProv (α e : ONote) (H : ONote → Prop) (m c : ℕ) (Γ : Seq) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Zeh α' e H m c Γ

namespace ZehProv

theorem of {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq}
    (hNF : α.NF) (hH : Cl H α) (D : Zeh α e H m c Γ) : ZehProv α e H m c Γ :=
  ⟨α, le_refl _, hNF, hH, D⟩

theorem mono {α β e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq}
    (hα : α ≤ β) : ZehProv α e H m c Γ → ZehProv β e H m c Γ := by
  rintro ⟨α', hα', hNF, hH, D⟩
  exact ⟨α', le_trans hα' hα, hNF, hH, D⟩

theorem weakening {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ Δ : Seq} (h : Γ ⊆ Δ) :
    ZehProv α e H m c Γ → ZehProv α e H m c Δ := by
  rintro ⟨α', hα', hNF, hH, D⟩
  exact ⟨α', hα', hNF, hH, D.wk h⟩

end ZehProv

/-! ## §3 The two pinned reductions (grind-shaped leaves, bodies `sorry` BY DESIGN)

Both are statement pins: the inversion suite and the reduction port are the lap-2+ rebuild,
forbidden here.  Their STATEMENTS are what the seam probes consume — the composition
arithmetic (now: membership algebra) is under test, not the ports. -/

/-- **PIN (disclosed sorry #1): ∀-inversion, `Zeh` form** — mirrors the banked
`Zekd.allInv` (`OperatorZinfty.lean:484`) verbatim: the extracted instance runs at the
relativization `adjoin H n₀` and the raised stage `max m n₀` (was: raised index
`max k n₀`, `d` inert). -/
theorem allInv_Zeh {φ₀ : SyntacticSemiformula ℒₒᵣ 1} (n₀ : ℕ) :
    ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq},
      Zeh α e H m c Γ → (∀⁰ φ₀) ∈ Γ →
      Zeh α e (adjoin H n₀) (max m n₀) c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  sorry

/-- **PIN (disclosed sorry #2): the running-family §19.6 reduction, `Zeh` form** —
mirrors W4B's `cutReduceAllAuxRunning` with the numeric budget slots REPLACED by
membership, exactly per the work order:

* input family at the running relativization/stage `(adjoin H n, max m₀ n)` — precisely
  `allInv_Zeh`'s output shape (the handoff type-checks in `probe_cut_all_arm_Zeh` below);
* output ordinal class `osucc (α + γ)` (unchanged);
* output control `raise e α` (unchanged — SPIKE-W4's raise; W4B's disclosed caveat (ii),
  possible witness-insufficiency of this raise when `ω^α < e`, carries verbatim);
* the `(dd + norm α + 1)`-budget of the `Zekd` statement is GONE: the output wrapper
  carries `Cl H`-membership of the output ordinal instead, which closure DERIVES
  (`seam1_membership_absorbed`) — there is no slot for the `norm α_fam`-bump to overflow. -/
theorem cutReduceAllAuxRunning_Zeh {φ : SyntacticSemiformula ℒₒᵣ 1} {c m₀ : ℕ}
    {α e : ONote} {H : ONote → Prop} {Γ : Seq}
    (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF) (hαH : Cl H α)
    (fam : ∀ n, Zeh α e (adjoin H n) (max m₀ n) c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {m : ℕ} {Δ : Seq}, Zeh γ e H m c Δ → γ.NF → Cl H γ →
      m₀ ≤ m → (∃⁰ ∼φ) ∈ Δ →
      ZehProv (osucc (α + γ)) (raise e α) H m c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  sorry

/-! ## §4 The two seam probes (Q1) -/

/-- **The seam-1 reversal, isolated**: the reduction-output ordinal class `osucc (α + γ)`
is a MEMBER by two constructor steps whenever its components are — this replaces W4B's
unabsorbable `+ norm α_fam + 1` budget bump.  Kernel-real, from `IsOperator`'s conditions
(`Cl`'s constructors), never from a sorried membership. -/
theorem seam1_membership_absorbed {S : ONote → Prop} {αf γf : ONote}
    (hα : Cl S αf) (hγ : Cl S γf) : Cl S (osucc (αf + γf)) :=
  Cl.osucc (Cl.add hα hγ)

/-- `ω·(n+1)` is a member of every closure — by an `n`-sized tree of equal-exponent
merges.  THE seam-2 reversal brick: the branch-`n` quantity whose NORM (`n+1`) overflowed
every W4B slot is, in `Zeh`, a per-branch MEMBER (finite tree), not a bound. -/
theorem wmul_mem (S : ONote → Prop) (n : ℕ) : Cl S (wmul n) := by
  induction n with
  | zero => exact Cl.expTower (Cl.ofNat 1)
  | succ n ih =>
      have h : wmul n + wmul 0 = wmul (n + 1) := rfl
      exact h ▸ Cl.add ih (Cl.expTower (Cl.ofNat 1))

/-- **Non-vacuity (W4B §3's two-level configuration, `Zeh` form; sorry-free).**  ONE
`allω` node at `ω^ω` whose EVERY branch `n` is a rank-`c` principal ∀/∃ cut with premise
ordinals `ω·(n+1)` — the branch-unbounded configuration that killed the `(k,d)` calculus,
realized as a legal `Zeh` derivation: every side condition is a membership, discharged by
a REAL per-branch closure tree.  (In `Zekd` the same configuration was legal only via the
`max k n + d` slack; here there is no numeric condition at all.) -/
theorem two_level_config_Zeh {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticTerm ℒₒᵣ)
    (χ ψ : SyntacticSemiformula ℒₒᵣ 1) {e : ONote} {H : ONote → Prop} {m : ℕ} {Γ : Seq}
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    Zeh (expTower ONote.omega) e H m ((∀⁰ χ).complexity + 1) (insert (∀⁰ ψ) Γ) := by
  refine Zeh.allω ψ (fun n => osucc (wmul n))
    (fun n => osucc_wmul_lt_expTower_omega n)
    (fun n => osucc_NF (wmul_NF n))
    (expTower_NF omegaO_NF)
    (fun n => Cl.osucc (wmul_mem _ n))
    (fun n => ?_)
  -- branch n: the rank-c principal ∀/∃ cut, premise ordinals ω·(n+1) — memberships by
  -- closure (contrast W4B: premise NORMS n+1, legal only through the max k n + d slack)
  refine Zeh.cut (∀⁰ χ) (Nat.lt_succ_self _)
    (Zekd.lt_osucc (wmul_NF n)) (Zekd.lt_osucc (wmul_NF n))
    (wmul_NF n) (wmul_NF n) (osucc_NF (wmul_NF n))
    (wmul_mem _ n) (wmul_mem _ n) ?_ ?_
  · exact Zeh.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))
  · exact Zeh.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))

/-- **Seam-1 composition probe (a REAL proof; its only sorry-dependence is the two §3
pins).**  The ∀/∃ arm of the principal-cut case at an ω-branch `nBr`, consuming the pins.

IH shape: the step motive's IHs at the branch position — at the branch's relativization
`adjoin H nBr`, running stage `max m nBr`, and (amendment A2) a COMMON control `E`: the
per-branch raise-then-unify mechanism of `Zekd`/`step_allω` is unavailable in `Zeh`
(`mono_e_membership_gate_refuted` — its budget gate was `Zekd`'s numeric `hτ`, deleted
here), so a workable `Zeh` motive must hold one control through the recursion.

What the arm kernel-checks end-to-end: `allInv_Zeh` feeding the ∀-side IH produces the
running family in EXACTLY the reduction pin's input shape (the handoff type-checks); the
reduction applies at the ∃-side; the sequent cleans up; and the emission's output-side
obligation set is: membership of `osucc (αf + γf)` at the branch relativization — derived
by `seam1_membership_absorbed` from the IHs' carried memberships, a REAL closure proof.
**The seam-1 reversal**: where W4B's arm emitted slot `(d + norm e + 1) + norm αf + 1`
against a motive demanding `d + norm e + 1` (kernel-unpayable, `seam1_uniform_slot_unpayable`),
the `Zeh` arm's emission carries NO output-side numeric obligation at all — the membership
it carries is exactly the motive's demanded form, and it is derivable for every branch. -/
theorem probe_cut_all_arm_Zeh {E : ONote} {H : ONote → Prop} {m nBr c : ℕ} {Γ : Seq}
    {χ : SyntacticSemiformula ℒₒᵣ 1} {βφ βψ : ONote}
    (hENF : E.NF) (hχc : χ.complexity < c)
    (IH1 : ZehProv (expTower βφ) E (adjoin H nBr) (max m nBr) c (insert (∀⁰ χ) Γ))
    (IH2 : ZehProv (expTower βψ) E (adjoin H nBr) (max m nBr) c (insert (∃⁰ ∼χ) Γ)) :
    ∃ αf γf : ONote, αf.NF ∧ αf ≤ expTower βφ ∧ γf ≤ expTower βψ ∧
      Cl (adjoin H nBr) (osucc (αf + γf)) ∧
      ZehProv (osucc (αf + γf)) (raise E αf) (adjoin H nBr) (max m nBr) c Γ := by
  obtain ⟨α₁, hle₁, hNF₁, hH₁, D₁⟩ := IH1
  obtain ⟨γ₁, hle₂, hNF₂, hH₂, D₂⟩ := IH2
  -- the RUNNING family, exactly the reduction pin's input shape: allInv_Zeh hands branch
  -- n₁ at the iterated relativization and the running stage max (max m nBr) n₁
  have fam : ∀ n₁, Zeh α₁ E (adjoin (adjoin H nBr) n₁) (max (max m nBr) n₁) c
      (insert (χ/[nm n₁]) Γ) := by
    intro n₁
    exact (allInv_Zeh n₁ D₁ (Finset.mem_insert_self _ _)).weakening
      (Finset.insert_subset_insert _ (Finset.erase_insert_subset _ _))
  -- the reduction pin, then clean the sequent
  have hred := cutReduceAllAuxRunning_Zeh hχc hNF₁ hENF hH₁ fam D₂ hNF₂ hH₂
    le_rfl (Finset.mem_insert_self _ _)
  refine ⟨α₁, γ₁, hNF₁, hle₁, hle₂, seam1_membership_absorbed hH₁ hH₂, ?_⟩
  exact hred.weakening (Finset.union_subset (Finset.erase_insert_subset _ _)
    (Finset.Subset.refl Γ))

/-- **Seam-2 reversal probe (sorry-free): the ω-node re-assembles over the
reduction-output class.**  Take the branch family in the CLASS the arm emits — ordinals
`osucc (ω·(n+1) + ω·(n+1))` (the `osucc (αf + γf)` splice class over W4B's two-level
family, whose `Zekd` slots grew like `n`) — at the relativization `adjoin H n` and the
running stage `max m n`.  `Zeh.allω` consumes them DIRECTLY: "every branch's output is
`H[n]`-controlled" IS the ω-rule's premise form.  Every membership is a real per-branch
closure tree; there is no uniform slot to overflow (contrast `seam2_no_uniform_slot`:
`Zekd.allω`'s single `d` was unpayable over this very family). -/
theorem probe_allomega_reassembly_Zeh {e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq}
    {χ : SyntacticSemiformula ℒₒᵣ 1}
    (dd : ∀ n, Zeh (osucc (wmul n + wmul n)) e (adjoin H n) (max m n) c
      (insert (χ/[nm n]) Γ)) :
    Zeh (expTower ONote.omega) e H m c (insert (∀⁰ χ) Γ) := by
  refine Zeh.allω χ (fun n => osucc (wmul n + wmul n))
    (fun n => ?_) (fun n => ?_) (expTower_NF omegaO_NF)
    (fun n => seam1_membership_absorbed (wmul_mem _ n) (wmul_mem _ n)) dd
  · rw [wmul_add_wmul]
    exact osucc_omega_coeff_lt _
  · rw [wmul_add_wmul]
    exact osucc_NF (nf_one.oadd _ NFBelow.zero)

/-! ## §5 The concrete-`H` / read-off probe (Q2)

The concrete represented `H` is `Cl gen` for a (finite, decidable) generator set — an
inductive closure whose membership witnesses are finite trees; `IsOperator (Cl gen)` is
`isOperator_Cl`.  By (K1) its membership predicate is vacuous on normal forms, so — this
is the probe's central Q2 finding — **the bounding read-off cannot and need not consume
membership**: what Buchholz–Wainer 1987 actually licenses (Bounding Lemma 5) is a bound
by a fast-growing/Hardy function at the judgment's NUMERIC parameters, over ∀-free
positive Σ₁ sequents.  In `Zeh`'s decoupled form that is: witnesses `≤ hardy e m`, `e`
and `m` read off the ROOT judgment of the cut-free (rank-0) derivation.  The lemma below
PROVES this read-off — at the abstract-`H` level, per-instance (the matrix `φ` is a
parameter with atomic instances; truth is `atomTrue`, no universal evaluator, no truth
predicate, no non-arithmetic quantification).  Consequence for the "new headline risk":
the read-off consumes NO `H`-data, so Σ₁-definability of the concrete `H` is NOT on the
read-off path at all. -/

/-- Sequent shape for the read-off: every member is the target `∃⁰ φ`, an already-bounded
instance of `φ`, or a literal.  (BW87's "positive Σ₁(N)" restriction: ∀-free.) -/
def ReadoffShape (φ : SyntacticSemiformula ℒₒᵣ 1) (e : ONote) (m : ℕ) (Γ : Seq) : Prop :=
  ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ (∃ n ≤ hardy e m, ψ = φ/[nm n]) ∨
    (∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- Read-off conclusion: a bounded true instance of the target, or a true literal
somewhere in the sequent (the escape BW87's Bounding Lemma also carries). -/
def ReadoffGoal (φ : SyntacticSemiformula ℒₒᵣ 1) (e : ONote) (m : ℕ) (Γ : Seq) : Prop :=
  (∃ n ≤ hardy e m, atomTrue (φ/[nm n])) ∨
    (∃ ψ ∈ Γ, atomTrue ψ ∧
      ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- **The bounding read-off (Q2), PROVEN — the Buchholz–Wainer Bounding-Lemma analog.**
From a rank-0 (cut-free) `Zeh` derivation of a `ReadoffShape` sequent whose target matrix
has atomic instances: a witness `n ≤ hardy e m` with `φ/[nm n]` true, or a true literal in
the sequent.  The bound consumes ONLY the judgment's control `e` and stage `m`:
memberships never enter (kernel-witnessed here by the proof using no `Cl` fact), and the
`allω`/`cut` cases are vacuous (∀-free shape; rank 0). -/
theorem readoff_sigma1 {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v) :
    ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq},
      Zeh α e H m c Γ → c = 0 → ReadoffShape φ e m Γ → ReadoffGoal φ e m Γ := by
  intro α e H m c Γ dd
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      intro _ _
      -- one of the dual literals is true (classically); either yields the escape disjunct
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact Or.inr ⟨_, hp, htrue, ar, r, v, Or.inl rfl⟩
      · refine Or.inr ⟨_, hn, ?_, ar, r, v, Or.inr rfl⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel] using htrue
  | @wk α e H m c Δ Γ hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @allω α e H m c Γ χ β hβ hβNF hαNF hβH _ _ =>
      intro _ hshape
      -- the ∀-free shape excludes the ω-rule: its principal formula fits no disjunct
      rcases hshape (∀⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n, _, h⟩ | ⟨ar, r, v, h | h⟩
      · exact absurd h (by simp [UnivQuantifier.all, ExsQuantifier.exs])
      · obtain ⟨ar, r, v, hrel⟩ := hφinst n
        rw [hrel] at h
        exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
  | @exI α β e H m c Γ χ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc hshape
      -- the principal formula can only be the target ∃⁰ φ
      have hχφ : χ = φ := by
        rcases hshape (∃⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n', _, h⟩ | ⟨ar, r, v, h | h⟩
        · simpa [ExsQuantifier.exs] using h
        · obtain ⟨ar, r, v, hrel⟩ := hφinst n'
          rw [hrel] at h
          exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
      have hφχ : φ = χ := hχφ.symm
      subst hφχ
      -- premise shape: the new instance carries the rule's own bound n ≤ hardy e m
      have hshape' : ReadoffShape φ e m (insert (φ/[nm n]) Γ) := by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inr (Or.inl ⟨n, hbound, rfl⟩)
        · exact hshape ψ (Finset.mem_insert_of_mem hψΓ)
      rcases ih hc hshape' with h | ⟨ψ, hψ, htrue, hlit⟩
      · exact Or.inl h
      · rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · -- the true literal IS the fresh instance: the witness lands
          exact Or.inl ⟨n, hbound, htrue⟩
        · exact Or.inr ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue, hlit⟩
  | @cut α βφ βψ e H m c Γ χ hcompl _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc _
      exact absurd hcompl (by omega)

/-- **The headline-instantiation read-off (statable AND proven at the abstract level).**
The W5/M2-exit shape: a rank-0 `Zeh` root deriving the single per-instance Σ₁ sequent
`{∃⁰ φ}` (atomic matrix) yields a numeric witness `≤ hardy e m` — the form the exit
consumes.  Per-instance discipline: `φ` is a parameter, truth is `atomTrue`, no universal
evaluator.  No `H`-data appears in the conclusion. -/
theorem headline_readoff {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    {α e : ONote} {H : ONote → Prop} {m : ℕ}
    (dd : Zeh α e H m 0 {(∃⁰ φ)}) :
    ∃ n ≤ hardy e m, atomTrue (φ/[nm n]) := by
  have hshape : ReadoffShape φ e m {(∃⁰ φ)} := by
    intro ψ hψ
    rw [Finset.mem_singleton] at hψ
    exact Or.inl hψ
  rcases readoff_sigma1 hφinst dd rfl hshape with h | ⟨ψ, hψ, _, ⟨ar, r, v, hlit⟩⟩
  · exact h
  · rw [Finset.mem_singleton] at hψ
    subst hψ
    rcases hlit with h | h <;> exact absurd h (by simp [ExsQuantifier.exs])

/-- **Concrete kernel instance of the read-off** (the work order's "small concrete case"):
a two-node derivation — `exI` at witness `3` over an `axL` leaf — at control `ω` and stage
`1`; the rule's bound is `3 ≤ hardy ω 1 = 3`, kernel-computed exactly (`hardy_omega`). -/
theorem concrete_readoff_instance {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v : Fin ar → SyntacticTerm ℒₒᵣ) (φ : SyntacticSemiformula ℒₒᵣ 1)
    {H : ONote → Prop} :
    Zeh (osucc 0) ONote.omega H 1 0
      (insert (∃⁰ φ) (insert (Semiformula.rel r v) {Semiformula.nrel r v})) := by
  refine Zeh.exI φ 3 (Zekd.lt_osucc NF.zero) NF.zero (osucc_NF NF.zero)
    (Cl.ofNat 0) (by rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]) ?_
  exact Zeh.axL r v
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- The concrete stage/control bound of the instance, kernel-computed: `hardy ω 1 = 3`. -/
theorem concrete_bound_computes : hardy ONote.omega 1 = 3 := by
  rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]

/-! ## §6 Addendum: the literature's actual PA-level operator shape (function-valued slots)

Surfaced mid-spike from Eguchi–Weiermann, *A simplified characterisation of provably
computable functions of `ID₁`* (arXiv:1205.2879, 2012; on disk:
`papers/eguchi-weiermann-2012-operator-controlled-id1.{pdf,md}`), Definition 23 +
Lemma 25, which combines Buchholz's ORDINAL operators `F` with NUMBER-THEORETIC
operators `f` (their conclusion states the split: `F` analyzes the Π¹₁-consequences,
`f` the Π⁰₂-consequences): the judgment carries a numeric FUNCTION `f : ℕ → ℕ`; every
norm side condition is `N(·) ≤ f 0` (the Witnessing Lemma bounds every existential
witness by `f 0`); the ω-rule relativizes `f` by max-adjunction
(`f[n] x := f (max n x)` — `Zekd`'s `max k n` axis, operator-dress); and CUT-REDUCTION
outputs the COMPOSITION `f ∘ g` of the premises' functions (collapse transfinitely
iterates, `f ↦ f^{F^α(0)+1}`, norm-gated).  This is the doctrine
"budgets in a motive are functions of structure" with the slot itself FUNCTION-valued —
the recursion restructuring that W4B's probe space (ℕ-valued slots) could not express and
whose existence the W4B verdict explicitly deferred to the `Zᵉ` fork.  The three kernel
facts below are the algebra that makes both seams absorbable in that form; the verdict
pins them as the binding carrier of the numeric data that (K1)–(K3) prove set-membership
CANNOT carry. -/

/-- The Eguchi–Weiermann max-relativization of a number-theoretic operator. -/
def rel1 (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun x => f (max n x)

/-- **The reassembly algebra (Eguchi–Weiermann Lemma 25's commutation, kernel-checked):**
max-relativization commutes with composition definitionally — a composed (cut-reduced)
slot re-enters the ω-rule's premise form with no residue.  This is the function-slot
analog of the seam-2 re-entry that the single-ℕ `d` could never make. -/
theorem rel1_comp (f g : ℕ → ℕ) (n : ℕ) : rel1 (f ∘ g) n = f ∘ rel1 g n := rfl

/-- **Seam 2 absorbed by a function slot** (contrast `SpikeW4B.seam2_no_uniform_slot`,
which refuted every ℕ-slot `D` against exactly this family): the two-level
configuration's branch-`n` demand is paid by ONE function-valued slot evaluated through
its own relativization. -/
theorem seam2_function_slot_payable (dBase eNorm : ℕ) :
    ∃ f : ℕ → ℕ, ∀ n : ℕ, (dBase + eNorm + 1) + norm (expTower (wmul n)) + 1 ≤ rel1 f n 0 := by
  refine ⟨fun x => dBase + eNorm + x + 3, fun n => ?_⟩
  have h : norm (expTower (wmul n)) = n + 1 := by
    rw [norm_expTower, norm_wmul]; omega
  rw [h]
  simp [rel1]
  omega

/-- **Seam 1 absorbed by composition** (contrast `SpikeW4B.seam1_uniform_slot_unpayable`:
`¬(dd + x + 1 ≤ dd)` for every ℕ-slot): the reduction's output demand is not required to
re-enter the INPUT slot — it re-enters the COMPOSED slot, which pays any structural bump
exactly. -/
theorem seam1_bump_absorbed_by_composition (x : ℕ) :
    ∃ g : ℕ → ℕ, ∀ dd : ℕ, dd + x + 1 ≤ g dd :=
  ⟨fun dd => dd + x + 1, fun _ => le_rfl⟩

/-- **Concrete explicit membership tree** (Q2's "explicit tree" check): the seam-1 splice
ordinal over branch 3 of the two-level family, `osucc (ω·4 + ω·4)`, as a closure tree over
an arbitrary generator set — 2 constructor steps over two 4-step `wmul` trees. -/
example (S : ONote → Prop) : Cl S (osucc (wmul 3 + wmul 3)) :=
  seam1_membership_absorbed (wmul_mem S 3) (wmul_mem S 3)

end GoodsteinPA.SpikeZ1

/-! ## Real axiom footprints (work-order requirement: `sorryAx` only via the two disclosed
§3 pins + the 3 canonical; NO new `axiom` declarations anywhere in this file). -/

-- §1 operator layer: the closure findings (sorry-free)
#print axioms GoodsteinPA.SpikeZ1.isOperator_Cl
#print axioms GoodsteinPA.SpikeZ1.Cl_of_NF
#print axioms GoodsteinPA.SpikeZ1.finite_part_unbounded
#print axioms GoodsteinPA.SpikeZ1.mono_e_membership_gate_refuted
#print axioms GoodsteinPA.SpikeZ1.norm_ball_not_add_closed
-- §2 structural layer (sorry-free)
#print axioms GoodsteinPA.SpikeZ1.Zeh.mono_H
-- §3 the two pins (bodies sorried by design)
#print axioms GoodsteinPA.SpikeZ1.allInv_Zeh
#print axioms GoodsteinPA.SpikeZ1.cutReduceAllAuxRunning_Zeh
-- §4 Q1: the seam probes (seam-1 arm depends on the pins ⟹ sorryAx, disclosed; the
-- membership/reassembly lemmas and the configuration are sorry-free)
#print axioms GoodsteinPA.SpikeZ1.seam1_membership_absorbed
#print axioms GoodsteinPA.SpikeZ1.wmul_mem
#print axioms GoodsteinPA.SpikeZ1.two_level_config_Zeh
#print axioms GoodsteinPA.SpikeZ1.probe_cut_all_arm_Zeh
#print axioms GoodsteinPA.SpikeZ1.probe_allomega_reassembly_Zeh
-- §5 Q2: the read-off (sorry-free)
#print axioms GoodsteinPA.SpikeZ1.readoff_sigma1
#print axioms GoodsteinPA.SpikeZ1.headline_readoff
#print axioms GoodsteinPA.SpikeZ1.concrete_readoff_instance
-- §6 the function-slot algebra (sorry-free)
#print axioms GoodsteinPA.SpikeZ1.rel1_comp
#print axioms GoodsteinPA.SpikeZ1.seam2_function_slot_payable
#print axioms GoodsteinPA.SpikeZ1.seam1_bump_absorbed_by_composition
