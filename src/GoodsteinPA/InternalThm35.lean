/-
# `InternalThm35.lean` — Rathjen 2014 Theorem 3.5, the M-internal block-tail (codes)

**Rathjen "Goodstein revisited" Theorem 3.5 (PA).** From a *slow* descending ε₀-sequence
`α₀ ≻ α₁ ≻ …` (slow: `C(αₙ) ≤ K·(n+1)`) one builds a descending sequence `β₀ ≻ β₁ ≻ …` with the
*tight* canonical-form bound `C(βᵣ) ≤ r+1`, by the reindex

  `β_{K·(n+1)+i} := ω·αₙ + (K−i)`     (`n < ω`, `0 ≤ i < K`).

This file builds the **block-tail** of that sequence — the indices `r ≥ K`, where the reindex
`r ↦ (n,i)` is `n = (r−K)/K`, `i = (r−K)%K` (internal division in `V ⊧ 𝗜𝚺₁`). It proves the three
load-bearing facts of Thm 3.5 for these indices, all from the existing single-step toolkit
(`icmp_betaTail_within`/`icmp_betaTail_boundary`/`isNF_iadd_finite`/`iC_betaTail_le`):

* `bbtail_isNF`    — every `βᵣ` is a valid NF code;
* `bbtail_C_le`    — the *tight* slowness `C(βᵣ) ≤ r+1` (Thm 3.5's headline bound, exact);
* `bbtail_desc`    — strict `≺`-descent `β_{r+1} ≺ βᵣ` (within-block and block-boundary cases).

It is **level-agnostic** (no Grzegorczyk `g`, no Ackermann) and so route-independent: it consumes a
slow descent and is reused by both the Con(PA) route (Rathjen Cor 3.7 / Thm 2.8) and any model-internal
descent argument. The deep crux that *produces* the slow input `α` is Cor 3.4 (the internal
Grzegorczyk `g`-padding, internal level `l : V`); the finite ω-tower **prefix** `r < K` (Rathjen's
`βⱼ = Σ_{i} ω_{s−i}`) — which fills indices `0..K−1` down to `β_K`, needing an internal ω-tower on
codes — is the one remaining piece toward a single sequence indexed from `0`. See
`route-resolved-prwo-gentzen` (memory) and `PENDING_WORK.md`.
-/
import GoodsteinPA.InternalCor34

namespace GoodsteinPA.InternalONote

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Thm 3.5 block-tail term** (codes, internal index `r ≥ K`). With `q = r − K`,
`n = q/K`, `i = q%K`, this is `βᵣ = ω·αₙ + (K − i)`. -/
noncomputable def bbtail (K : V) (α : V → V) (r : V) : V :=
  iadd (iomul (α ((r - K) / K))) (ocOadd 0 (K - (r - K) % K) 0)

/-- `(r−K)%K < K`, hence `K − (r−K)%K ≥ 1`, so the finite tail `K − (r−K)%K` is nonzero. -/
private lemma sub_mod_pos {K : V} (hK : 0 < K) (r : V) : 0 < K - (r - K) % K :=
  pos_sub_iff_lt.mpr (mod_lt _ hK)

/-- **Thm 3.5, NF invariant.** Every block-tail term is a valid normal-form code. -/
theorem bbtail_isNF {K : V} (hK : 0 < K) {α : V → V} (hNF : ∀ n, isNF (α n)) (r : V) :
    isNF (bbtail K α r) :=
  isNF_iadd_finite (hNF _) (sub_mod_pos hK r).ne'

/-- **Thm 3.5, tight slowness bound** `C(βᵣ) ≤ r + 1` for `r ≥ K`. The reindex makes the generic
`K·(n+1)+i+1` bound (`iC_betaTail_le`) collapse to exactly `r+1`, because `K·(q/K)+q%K = q = r−K`. -/
theorem bbtail_C_le {K : V} {α : V → V} (hslow : ∀ n, iC (α n) ≤ K * (n + 1)) {r : V} (hr : K ≤ r) :
    iC (bbtail K α r) ≤ r + 1 := by
  have hbound := iC_betaTail_le (c := α ((r - K) / K)) (K := K)
    (n := (r - K) / K) (i := (r - K) % K) (hslow _)
  refine le_trans hbound (le_of_eq ?_)
  -- `K·(q/K + 1) + q%K + 1 = q + K + 1 = r + 1`, using `K·(q/K) + q%K = q` and `(r−K)+K = r`.
  have hdm : K * ((r - K) / K) + (r - K) % K = r - K := div_add_mod (r - K) K
  have hrK : (r - K) + K = r := sub_add_self_of_le hr
  calc K * ((r - K) / K + 1) + (r - K) % K + 1
      = (K * ((r - K) / K) + (r - K) % K) + K + 1 := by
        rw [mul_add, mul_one, add_right_comm (K * ((r - K) / K)) K ((r - K) % K)]
    _ = (r - K) + K + 1 := by rw [hdm]
    _ = r + 1 := by rw [hrK]

/-- **Thm 3.5, strict descent** `β_{r+1} ≺ βᵣ` for `r ≥ K`. The reindex successor `r ↦ r+1` either
stays within a block (`i+1 < K`: same `ω·αₙ` head, the finite tail drops by one — `icmp_betaTail_within`)
or crosses a block boundary (`i+1 = K`: `α_{n+1} ≺ αₙ` drops the head — `icmp_betaTail_boundary`).
The whole case split is internal division: `(q+1)/K`, `(q+1)%K` from `q/K`, `q%K` (`q = r−K`). -/
theorem bbtail_desc {K : V} (hK : 0 < K) {α : V → V} (hNF : ∀ n, isNF (α n))
    (hdesc : ∀ n, icmp (α (n + 1)) (α n) = 0) {r : V} (hr : K ≤ r) :
    icmp (bbtail K α (r + 1)) (bbtail K α r) = 0 := by
  -- `(r+1) − K = (r−K) + 1`.
  have hq1 : (r + 1) - K = (r - K) + 1 := by
    have h1 : r + 1 = ((r - K) + 1) + K := by rw [add_right_comm, sub_add_self_of_le hr]
    rw [h1, add_sub_self]
  simp only [bbtail]
  rw [hq1]
  set q := r - K with hq
  set n := q / K with hn
  set i := q % K with hi
  have hi_lt : i < K := mod_lt q hK
  have hdm : K * n + i = q := div_add_mod q K
  -- `q + 1 = K·n + (i+1)`.
  have hexp : q + 1 = K * n + (i + 1) := by rw [← add_assoc, hdm]
  rcases lt_or_eq_of_le (show i + 1 ≤ K from succ_le_iff_lt.mpr hi_lt) with hcase | hcase
  · -- within-block: `i+1 < K`
    have hquot : (q + 1) / K = n := by rw [hexp]; exact div_mul_add' n K hcase
    have hmod : (q + 1) % K = i + 1 := by
      rw [hexp, mod_mul_add' n (i + 1) hK, mod_eq_self_of_lt hcase]
    have hKi : (K - (i + 1)) + 1 = K - i := by
      rw [← Arithmetic.sub_sub]
      exact sub_add_self_of_le (Arithmetic.one_le_of_zero_lt _ (pos_sub_iff_lt.mpr hi_lt))
    rw [hquot, hmod, ← hKi]
    exact icmp_betaTail_within (α n) (K - (i + 1))
  · -- block boundary: `i+1 = K`
    have hexpB : q + 1 = K * (n + 1) := by rw [hexp, hcase, mul_add, mul_one]
    have hquot : (q + 1) / K = n + 1 := by rw [hexpB]; exact div_mul' (n + 1) hK
    have hmod : (q + 1) % K = 0 := by rw [hexpB]; exact mod_mul_self_right (n + 1) K
    rw [hquot, hmod, Arithmetic.sub_zero]
    exact icmp_betaTail_boundary (hNF (n + 1)) (hNF n) (hdesc n) K (K - i)

end GoodsteinPA.InternalONote
