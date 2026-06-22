/-
# `src/GoodsteinPA/SeamDefinability.lean` — binary representability for the F seam (Worker B, step 2)

Foundation's `codeOfREPred` (`Representation.lean:245`) turns a unary r.e. predicate into an
`ℒₒᵣ`-`Semisentence` of arity 1 with the spec `ℕ ⊧/![x] (codeOfREPred A) ↔ A x`. The arithmetization
seam needs the **binary** version: an `ℒₒᵣ`-formula defining the order relation `lt : ℕ → ℕ → Prop`.

`codeOfREPred₂` builds it from the same `codeOfPartrec'` primitive (arity `k+1`, here `k = 2`), and
`codeOfREPred₂_spec` is the binary analogue of `codeOfREPred_spec` — a faithful port of that proof.
-/
import GoodsteinPA.EpsilonOrder
import Foundation.FirstOrder.Arithmetic.R0.Representation

namespace GoodsteinPA.SeamDefinability

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open Classical

/-- Binary representability: an `ℒₒᵣ`-`Semisentence` of arity 2 coding the r.e. relation `R`. -/
noncomputable def codeOfREPred₂ (R : ℕ → ℕ → Prop) : Semisentence ℒₒᵣ 2 :=
  let f : List.Vector ℕ 2 →. Unit :=
    fun v ↦ Part.assert (R (v.get 0) (v.get 1)) fun _ ↦ Part.some ()
  (codeOfPartrec' (fun v ↦ (f v).map fun _ ↦ 0))/[‘0’, #0, #1]

/-- The binary analogue of `codeOfREPred_spec`. -/
lemma codeOfREPred₂_spec {R : ℕ → ℕ → Prop}
    (hR : REPred fun v : List.Vector ℕ 2 ↦ R (v.get 0) (v.get 1)) {m n : ℕ} :
    ℕ ⊧/![m, n] (codeOfREPred₂ R) ↔ R m n := by
  let f : List.Vector ℕ 2 →. Unit :=
    fun v ↦ Part.assert (R (v.get 0) (v.get 1)) fun _ ↦ Part.some ()
  suffices
      ℕ ⊧/![m, n] ((codeOfPartrec' fun v ↦ Part.map (fun _ ↦ 0) (f v))/[‘0’, #0, #1]) ↔ R m n from this
  have hpart : Partrec fun v : List.Vector ℕ 2 ↦ (f v).map fun _ ↦ 0 :=
    Partrec.map hR (Computable.const 0).to₂
  simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, f]
    using (codeOfPartrec'_spec (Nat.Partrec'.of_part hpart) (v := ![m, n]) (y := 0)).trans (by simp [f])

end GoodsteinPA.SeamDefinability
