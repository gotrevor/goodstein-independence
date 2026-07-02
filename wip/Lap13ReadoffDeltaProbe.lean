import GoodsteinPA.OperatorZef2
import GoodsteinPA.Embedding

/-!
# lap-13 SERIES-1 lane D — the rank-0 `Zef2` soundness core for the Δ₀ read-off

Toward the R-4 `readoff_delta0_Zef2` (Δ₀ read-off, `<BoundedInstance> = DeltaZero`).  This file
proves the KERNEL of it — rank-0 `Zef2` soundness with the hard Π (`allω`) combination — and
precisely scopes the remaining bounded-witness layer.  Off the build; port `sound0` to src.

## PROVEN here: `sound0` (rank-0 soundness, the Π-combination)

`sound0 : Zef2 α e H f 0 Γ → ∃ ψ ∈ Γ, atomTrue ψ`.  The `allω` (Π) case is the genuine new content
over the atomic `readoff_sigma1_Zef`: for a `∀⁰`-node, either some branch's true member lies in the
shared context `Γ` (return it), or every branch is true at its own instance `φ/[nm n]` — whence
`∀⁰ φ` is true (`atomTrue (∀⁰ φ) = ∀ k, atomTrue (φ/[nm k])`, via `eval_all`/`eval_substs`/`valm_nm`).
This is slot-INDEPENDENT (truth does not see `f`).

## SCOPED (the remaining Towsner §5.4 content): the bounded outer witness `n ≤ f 0`

R-4 needs `∃ n ≤ f 0, atomTrue (φ/[nm n])`, i.e. the E–W witnessing bound.  The clean idea — return,
for an existential member, a witness `≤ f 0` carried from the `exI` rule's own `hbound` — is
KERNEL-FALSE as a uniform payload, for a precise reason:

> **The witness bound is SLOT-LOCAL, and `allω` relativizes the slot.**  An `allω` node's conclusion
> is at slot `f`, but its branches are at slot `rel1 f n` (`rel1 f n 0 = f n`, NOT `f 0`).  A true
> member of the shared context extracted from branch `n` carries a witness `≤ f n`, which need not be
> `≤ f 0` (there is no `Monotone f` hypothesis).  So a single `∀ n, ψ = ∃⁰ φ' → ∃ m ≤ f 0, …` payload
> is not inductively maintainable across `allω`.  Compounding it: a contracted `∃⁰ φ` can be TRAPPED
> in an `allω` branch's context and only re-`exI`'d deeper at a relativized slot, so its witness is
> bounded by `f k`, not `f 0`.

The genuine discharge therefore threads the bound at the LOCAL slot and needs a
contraction/well-foundedness argument (Towsner §5.4 witnessing lemma).  `sound0` is the reusable
truth core it will call; the bound layer is the next 1–2 laps.  (For non-contracted derivations of
the singleton `{∃⁰ φ}` — `exI` keeps slot `f`, and `{∃⁰ φ}` has no `∀⁰` member so `allω` never fires
at the top level — the bound is immediate from the top `exI`; the contraction case is the residue.)
-/

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote
open GoodsteinPA.OperatorZinfty
open GoodsteinPA.Embedding (valm_nm)

/-- **Rank-0 `Zef2` soundness.**  A cut-free derivation of `Γ` has a standard-model-true member.
The `allω` case combines: either some branch's true member is in the shared context `Γ` (done), or
every branch is true at its own instance `φ/[nm n]` — whence `∀⁰ φ` is true. -/
theorem sound0 : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → c = 0 → ∃ ψ ∈ Γ, atomTrue ψ := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro _
      -- one of the complementary literals is true in ℕ
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact ⟨_, hp, htrue⟩
      · refine ⟨_, hn, ?_⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel] using htrue
  | @wk α e H f c Δ Γ hαN hsub _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @allω α e H f c Γ hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro hc
      rcases Classical.em (∃ n : ℕ, ∃ ψ ∈ Γ, atomTrue ψ) with hctx | hctx
      · obtain ⟨n, ψ, hψ, htrue⟩ := hctx
        exact ⟨ψ, Finset.mem_insert_of_mem hψ, htrue⟩
      · -- every branch is true at its own instance ⇒ ∀⁰ φ is true
        refine ⟨∀⁰ φ, Finset.mem_insert_self _ _, ?_⟩
        have hall : ∀ n, atomTrue (φ/[nm n]) := by
          intro n
          obtain ⟨ψ, hψ, htrue⟩ := ih n hc
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact htrue
          · exact absurd ⟨n, ψ, hψΓ, htrue⟩ hctx
        simp only [atomTrue, Semiformula.eval_all]
        intro x
        have hx := hall x
        simpa [atomTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hx
  | @exI α β e H f c Γ hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · -- true at the witnessed instance ⇒ ∃⁰ φ is true
        refine ⟨∃⁰ φ, Finset.mem_insert_self _ _, ?_⟩
        simp only [atomTrue, Semiformula.eval_ex]
        exact ⟨n, by
          simpa [atomTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using htrue⟩
      · exact ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue⟩
  | @cut α βφ βψ e H f c Γ hαN φ hcompl hcutRead _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc; subst hc
      exact absurd hcompl (by omega)

end GoodsteinPA.OperatorZeh
