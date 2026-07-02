/-
# PROBE / TARGET: the exact Hardy–fast-growing bridge at `ω^α`

Corrects lap-177's claim "the substrate has no fast-growing `F`": `ONote.fastGrowing` IS defined
(mathlib) and the repo carries its full growth theory (`Hardy.lean` §Basic).  The repo's B4 note
(`Hardy.lean:1082`) calls the bridge `H_{ω^α} = f_α`, but that EQUALITY is kernel-FALSE (off by a
shift) — a second "convincing identity" trap this session.  Kernel `#eval` (α ∈ {0,1,2}) pins the
EXACT relation:

    hardy (oadd α 1 0) n + 1 = fastGrowing α (n + 1)          -- i.e. H_{ω^α}(n) = f_α(n+1) − 1

Anchors below (`native_decide`).  This is the crux upper-bound ingredient for the P1 raised-control
obligation: with `raise e α' = e + ω^{α'}` in the ABSORBING regime (lap 178), the raised control is
`≈ hardy(ω^{α'})`, and this bridge gives the UPPER bound `hardy(ω^{α'}) n < fastGrowing α' (n+1)`,
reducing P1 to E–W Lemma 19 `fastGrowing α' ≤ f^{iterate}` (the genuine fast-growing domination).

Pure Hardy/fastGrowing growth theory about STABLE defs (mathlib `fastGrowing` + repo `hardy`);
calculus-independent (no `Zeh`, no pin, no cut-elim machinery); the repo's own long-horizon target
B4, sharpened to its exact ONote form.  Base case proven; successor/limit steps are the open grind
(the classical Cichoń–Wainer correspondence, via the `H_{ω^β·k}` intermediate).
-/
import GoodsteinPA.Hardy

namespace GoodsteinPA.FastGrowing

open ONote

/-! ### Faithfulness anchors — the exact shift is kernel-checked, not guessed -/

example : hardy (oadd 0 1 0) 3 + 1 = fastGrowing 0 (3 + 1) := by native_decide
example : hardy (oadd 1 1 0) 3 + 1 = fastGrowing 1 (3 + 1) := by native_decide
example : hardy (oadd 1 1 0) 4 + 1 = fastGrowing 1 (4 + 1) := by native_decide
example : hardy (oadd 2 1 0) 1 + 1 = fastGrowing 2 (1 + 1) := by native_decide
example : hardy (oadd 2 1 0) 2 + 1 = fastGrowing 2 (2 + 1) := by native_decide

-- and the EQUALITY H_{ω^α}=f_α is FALSE (off by ≥1) — recorded so no lap re-attempts it:
example : hardy (oadd 1 1 0) 3 ≠ fastGrowing 1 3 := by native_decide

/-- **TARGET (open): the exact Hardy–fast-growing bridge at `ω^α`.**
`H_{ω^α}(n) + 1 = f_α(n+1)`.  By well-founded recursion on `α`:
* `α = 0`: `H_{ω^0}(n) = H_1(n) = n+1`, `f_0(n+1) = succ(n+1) = n+2`.  ✓ (proven below).
* `α = β+1`: `ω^{β+1}` is a limit with `ω^{β+1}[i] = ω^β·(i+1)`; needs the intermediate
  `H_{ω^β·k}` law relating `k`-fold `f_β`-iteration — the crux of the classical correspondence.
* `α` limit: `ω^α[i] = ω^{α[i]}`, so the IH at `α[i] < α` transfers through `fastGrowing_limit`.
The successor/limit steps are the open grind (target B4). -/
theorem hardy_omega_pow_add_one (α : ONote) : ∀ n : ℕ,
    hardy (oadd α 1 0) n + 1 = fastGrowing α (n + 1) := by
  intro n
  rcases hα : fundamentalSequence α with (_ | β) | f
  · -- α = 0: H_{ω^0} = H_1 = (·+1); f_0 = succ.
    have h0 : α = 0 := by
      have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact hp
    subst h0
    have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
    rw [hardy_succ (oadd 0 1 0) hfs1, hardy_zero, fastGrowing_zero]
    rfl
  · -- α = β+1 (successor exponent): ω^{β+1} limit, needs the H_{ω^β·k} intermediate. TARGET B4.
    sorry
  · -- α limit: ω^α[i] = ω^{α[i]}, IH transfers via fastGrowing_limit. TARGET B4.
    sorry

/-- **The usable corollary (open, follows from the target):** the UPPER bound the P1 raised-control
obligation needs — `hardy(ω^α)(n) < fastGrowing α (n+1)`, hence `≤ fastGrowing α (n+1)`. -/
theorem hardy_omega_pow_lt_fastGrowing (α : ONote) (n : ℕ) :
    hardy (oadd α 1 0) n < fastGrowing α (n + 1) := by
  have h := hardy_omega_pow_add_one α n
  omega

end GoodsteinPA.FastGrowing
