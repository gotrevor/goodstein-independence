/-
# `wip/GentzenCon.lean` — Crux 2 scaffold: Gentzen `PRWO(ε₀) → Con(𝗣𝗔)` (Rathjen 2014 Thm 2.8)

**Status: DISCLOSED-SORRY SCAFFOLD (wip, off the build target).** This file grounds the second
Phase-2 girder of `Reduction.goodstein_implies_consistency` into a typed, lemma-by-lemma architecture.
Every deep obligation is an honest `sorry`/`axiom` citing Rathjen 2014 §2 (read lap 49, see
`CRUX2-GENTZEN-2026-06-23.md`). The point of the scaffold is to (a) pin the **PRWO formulation** — the
shared hinge of both cruxes and the project's highest confabulation-risk piece — as a concrete,
type-checked `Sentence ℒₒᵣ` built on the repo's *existing* ε₀-ordering formula `precφ`, with a
standard-model faithfulness audit; and (b) validate that crux 1 (`γ → PRWO`) and crux 2 (`PRWO → Con`)
chain into exactly the `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)` interface that `Reduction.lean` needs.

## Why PRWO is a *schema* (per-formula), not a single ∀-over-indices sentence
Rathjen states PRWO(ε₀) = "no infinitely descending **primitive recursive** ε₀-sequence." Expressing
"`f` is primitive recursive" with the index `e` as an **object** variable would need a universal
evaluator / Kleene-T predicate arithmetized inside the theory. **Foundation has none** (mapped lap 50:
`code`/`codeOfPartrec'`/`codeOfREPred` all encode a *meta-level* function into a *fixed* formula; there
is no `Eval(e,n,y)` with `e` a first-order term). So — as is standard for Gentzen/Rathjen in PA — PRWO is
a **schema**: one instance `prwoInstance seq` per ℒₒᵣ-formula `seq(y,n)` (= "the graph `y = f n`").
This is exactly what the proof needs:
* **crux 1** (`γ → PRWO`, Rathjen §3) proves the instance for an *arbitrary* primrec descent graph;
* **crux 2** (`PRWO → Con`, Gentzen) uses the *single* instance for `n ↦ ord(Rⁿ d₀)`.

## The ε₀-ordering is already a machine-checked ℒₒᵣ formula
`SeamDefinability.precφ : Semisentence ℒₒᵣ 2` codes `natCode a < natCode b` (a ≺ b in ε₀) with the spec
`precφ_spec : ℕ ⊧/![m,n] precφ ↔ natCode m < natCode n` (axiom-clean modulo one `native_decide`, F-φ).
Since `natCode : ℕ ≃ NONote` is a *bijection onto all CNF notations*, every `n : ℕ` already denotes a
valid `< ε₀` ordinal — so PRWO needs **no separate `isNF` predicate**, only `precφ`.
-/
import GoodsteinPA.SeamDefinability
import GoodsteinPA.Reduction

namespace GoodsteinPA.GentzenCon

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.SeamDefinability GoodsteinPA.Epsilon0Complete

/-! ## Step 1 — the PRWO formulation (the shared hinge) -/

/-- **PRWO(ε₀), one schema instance.** For a sequence presented by its graph formula
`seq(y, n)` ("`y` is the value at position `n`"; arg `#0` = value, `#1` = index, matching the
`codeOfPartrec'` output-first convention), `prwoInstance seq` is the closed `ℒₒᵣ`-sentence

  `¬ ∀ n y z, (seq(y,n) ∧ seq(z,n+1)) → z ≺ y`,

i.e. **"`seq` does not strictly ≺-descend at every step"** = "no infinite descent through `seq`."
For a *total functional* graph this is literally Rathjen's `∃ n, ¬(f(n+1) ≺ f n)` — which is the whole
content of PRWO, because `ε₀` is well-founded so any total `f` must fail to descend somewhere.
`z ≺ y` is `precφ z y` (= `natCode z < natCode y`). -/
noncomputable def prwoInstance (seq : Semisentence ℒₒᵣ 2) : Sentence ℒₒᵣ :=
  “¬ ∀ n y z, (!seq y n ∧ !seq z (n + 1)) → !precφ z y”

/-- **Faithfulness audit (standard model).** In `ℕ`, `prwoInstance seq` holds **iff** the sequence
described by `seq` is not everywhere-≺-descending — the meta-level PRWO statement, with the order read
through the *same* `natCode` coding the rest of the seam uses. This is the encoding-correctness anchor
for the formulation (cf. `Bridge.goodsteinSentence_faithful` for `γ`). -/
theorem prwoInstance_faithful (seq : Semisentence ℒₒᵣ 2) :
    (ℕ ⊧ₘ prwoInstance seq) ↔
      ¬ (∀ n y z : ℕ, (ℕ ⊧/![y, n] seq) → (ℕ ⊧/![z, n + 1] seq) →
          natCode z < natCode y) := by
  unfold prwoInstance
  rw [models_iff]
  simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Semiformula.eval_all,
    Semiformula.eval_substs, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.neg_eq, LogicalConnective.Prop.arrow_eq, LogicalConnective.Prop.and_eq,
    Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.constant_eq_singleton, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Semiterm.val_bvar, Semiterm.val_operator₂, Semiterm.val_operator₀, Structure.Add.add,
    Structure.numeral_eq_numeral, ORingStructure.one_eq_one, precφ_spec]
  constructor
  · intro h hall; exact h (fun a b c hconj => hall a b c hconj.1 hconj.2)
  · intro h hall; exact h (fun n y z hYN hZN => hall n y z ⟨hYN, hZN⟩)

/-! ## Step 2 — the Gentzen reduction substrate (Rathjen 2014 Thm 2.8(i), p. 9)

Gentzen (via Buchholz [6]): an ordinal assignment `ord` and a reduction procedure `R` on coded `𝗣𝗔`
derivations, both **primitive recursive**, with `ord(R D) ≺ ord D` whenever `D` derives the empty
sequent (eq. (5)). Built over Foundation's arithmetized `Theory.Derivation : V → Prop`
(`Bootstrapping/Syntax/Proof/Basic.lean:459`); here stated over ℕ-codes for the meta layer. -/

/-- Ordinal assignment: a coded derivation ↦ its `natCode`-indexed `ε₀`-ordinal. Primitive recursive
(Buchholz [6]). Placeholder; the real `ord` is an `ℒₒᵣ`-arithmetized primrec function. -/
axiom ord : ℕ → ℕ

/-- Gentzen's reduction procedure on coded derivations. Primitive recursive (Buchholz [6]).
Placeholder; the real `R` is an `ℒₒᵣ`-arithmetized primrec function. -/
axiom R : ℕ → ℕ

/-- `R` maps a derivation of the empty sequent to another derivation of the empty sequent.
`derivesEmpty d` abbreviates "`d` codes a `𝗣𝗔`-derivation of `⊥`" (the meta stand-in for
`Theory.DerivationOf d ⌜⊥⌝`). -/
axiom derivesEmpty : ℕ → Prop

axiom R_preserves_empty {d : ℕ} : derivesEmpty d → derivesEmpty (R d)

/-- **Equation (5) — the deep Gentzen core.** The reduction strictly lowers the assigned ordinal.
THE ordinal-analysis content (Buchholz [6] = `papers/buchholz-on-gentzens-first-consistency-proof.pdf`
+ `papers/siders-gentzen-consistency-proofs-arithmetic.pdf`). -/
axiom ord_R_descends {d : ℕ} : derivesEmpty d → natCode (ord (R d)) < natCode (ord d)

/-- The Gentzen descent sequence `n ↦ ord(Rⁿ d)` from a derivation `d` of `⊥`. Strictly
≺-descending below `ε₀` by `ord_R_descends` + `R_preserves_empty` — an infinite primrec descent,
the witness against PRWO. -/
noncomputable def gentzenDescent (d : ℕ) : ℕ → ℕ := fun n => ord (R^[n] d)

theorem derivesEmpty_iterate {d : ℕ} (hd : derivesEmpty d) (n : ℕ) :
    derivesEmpty (R^[n] d) := by
  induction n with
  | zero => simpa using hd
  | succ k ih => rw [Function.iterate_succ_apply']; exact R_preserves_empty ih

theorem gentzenDescent_descends {d : ℕ} (hd : derivesEmpty d) (n : ℕ) :
    natCode (gentzenDescent d (n + 1)) < natCode (gentzenDescent d n) := by
  have hiter : derivesEmpty (R^[n] d) := derivesEmpty_iterate hd n
  simpa [gentzenDescent, Function.iterate_succ_apply'] using ord_R_descends hiter

/-- The `ℒₒᵣ`-formula presenting `n ↦ ord(Rⁿ d₀)` as a graph `seq(y,n)`, where `d₀` is the
canonical (least) derivation of `⊥` available under `¬Con`. Arithmetized from `ord`/`R`/`Theory.proof`
+ bounded iteration; placeholder pending the primrec encodings above. -/
axiom gentzenDescentφ : Semisentence ℒₒᵣ 2

/-! ## Step 3 — the two cruxes, and their assembly into the `Reduction.lean` interface -/

/-- **Crux 2 — Gentzen Thm 2.8(i): `PRWO(ε₀) → Con(𝗣𝗔)`.** If `𝗣𝗔` proves the PRWO instance for the
Gentzen descent, then `𝗣𝗔` proves its own consistency: inside `𝗣𝗔`, `¬Con` yields a derivation `d₀`
of `⊥`, whence `n ↦ ord(Rⁿ d₀)` is an infinite primrec ε₀-descent (`gentzenDescent_descends`),
contradicting `prwoInstance gentzenDescentφ`. Held at `sorry` — the deep ordinal-analysis girder
(needs `ord`/`R`/eq (5) arithmetized in `𝗣𝗔`). -/
theorem gentzen_prwo_implies_consistency :
    𝗣𝗔 ⊢ prwoInstance gentzenDescentφ → 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent := by
  sorry

/-- **Crux 1 — Rathjen §3: `γ → PRWO(ε₀)` (every primrec instance).** From `𝗣𝗔 ⊢ γ`, `𝗣𝗔` proves the
PRWO instance for any primrec descent graph (the internal Cor 3.4 slow-down → Thm 3.5 → Lemma 3.6
pipeline; `InternalThm35` done, internal Cor 3.4 = the internal-Grzegorczyk crux). Held at `sorry`. -/
theorem goodstein_implies_prwo (seq : Semisentence ℒₒᵣ 2) :
    𝗣𝗔 ⊢ ↑goodsteinSentence → 𝗣𝗔 ⊢ prwoInstance seq := by
  sorry

/-- **The assembly.** Crux 1 (at the Gentzen-descent instance) ∘ crux 2 = exactly the girder
`Reduction.goodstein_implies_consistency`. This `wip` theorem REFINES that single `sorry` into the
two-girder chain; it is **not** promoted to `src/` until both cruxes are real (anti-fraud). -/
theorem goodstein_implies_consistency_via_gentzen :
    𝗣𝗔 ⊢ ↑goodsteinSentence → 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent := fun hγ =>
  gentzen_prwo_implies_consistency (goodstein_implies_prwo gentzenDescentφ hγ)

/-! ## Seam checks (machine-checked integration guards)

Integration seams are this project's historical bug source (free-X vs primrec, code↔order encoding
mismatches). The `example`s below **compile iff the two cruxes actually chain into the headline route** —
they are guards, not new content, and will keep guarding as the `sorry` bodies are discharged. -/

/-- **SEAM 1 — ONE shared `PRWO(ε₀)`.** Crux 1 *outputs* `𝗣𝗔 ⊢ prwoInstance gentzenDescentφ` and crux 2
*consumes* the same; this composition type-checks **only if both reference the identical `prwoInstance`
Lean def** (same ε₀-order `precφ`, same descent encoding). Two faithful-but-distinct PRWO statements
would fail here. -/
example (hγ : 𝗣𝗔 ⊢ ↑goodsteinSentence) : 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent :=
  gentzen_prwo_implies_consistency (goodstein_implies_prwo gentzenDescentφ hγ)

/-- **SEAM 2 — crux 2's `Con(𝗣𝗔)` is Foundation's `Con[𝗣𝗔]`.** The whole route ends at Gödel II
(`peano_not_proves_consistency = consistent_unprovable 𝗣𝗔`, proven about `↑𝗣𝗔.consistent`). This
`example` discharges `False` from `𝗣𝗔 ⊢ γ` by feeding the assembly's output **straight into Gödel II** —
it type-checks **only if that output is definitionally Foundation's `↑𝗣𝗔.consistent`** (not a
hand-rolled consistency lookalike). -/
example (hγ : 𝗣𝗔 ⊢ ↑goodsteinSentence) : False :=
  peano_not_proves_consistency (goodstein_implies_consistency_via_gentzen hγ)

/-- **SEAM 3 — the assembly IS the open girder, end-to-end.** Routing the assembly through the
already-axiom-clean Gödel-II hook `not_proves_of_implies_consistency` yields the headline precursor
`𝗣𝗔 ⊬ ↑goodsteinSentence`. This single type-check validates: (a) crux-1 output = crux-2 input (seam 1),
(b) crux-2 output = Foundation Con (seam 2), and (c) `goodsteinSentence`/`Con` match the `Reduction.lean`
girder `goodstein_implies_consistency : 𝗣𝗔 ⊢ ↑goodsteinSentence → 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent` (identical type).
Once both crux `sorry`s are real, `goodstein_implies_consistency_via_gentzen` drops in for that girder. -/
example : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  not_proves_of_implies_consistency goodstein_implies_consistency_via_gentzen

end GoodsteinPA.GentzenCon
