/-
# Crux-2 blueprint — the genuine reduct ⟹ the Gentzen contradiction, as sorried leaves

**Blueprint (judge, 2026-06-24).** Decomposes the single open girder `Reduction.goodstein_implies_consistency`
into precise, named, sorried leaves M1a–M3, so the crux-2 contradiction `¬Con(𝗣𝗔) → False` follows
**by construction** — the assembly is wired here, not "at the end." Increasing the sorry count is the
*point*: one fat `sorry` split into small precise ones is progress, not regress.

Grounded in the existing `InternalZ` API (verified against HEAD): `ZDerivation`, `ZDerivesEmpty`, `iord`,
`icmp`, `iR2`, `RedSound`, `iord_iR2_iterate_descends`, `inference_critical_pair`. The genuine reduct
`red` (Buchholz §6 `red` / Def 3.2) *replaces* the ordinal-faithful-but-invalid `iR2`; everything the
box banked for `iR2` (the one-step ordinal descent) re-states over `red` and the descent then becomes
**unconditional** once `redSound` (M1b) is proven.

⚠️ SEED — not yet compiled by the judge (can't host-build against the live box). The grind's first task
is to make this file elaborate (fix any signature drift against HEAD), then discharge the leaves
M1a → M1b → M2 → M3. Deliberately NOT imported by `GoodsteinPA.lean`, so it cannot affect the default
`lake build GoodsteinPA`. Literature + lap budgets: `E-CRUX2-ROADMAP-2026-06-24.md`.
-/
import GoodsteinPA.InternalZ
import GoodsteinPA.Zsubst
import GoodsteinPA.RedZKDescent
import GoodsteinPA.Reduction
import GoodsteinPA.IIter

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## M1a — the genuine validity-faithful reduct `red` + construction correctness
Buchholz §6 `red` / Def 3.2: a 5-case primrec dispatch on the tag; the critical/`K`-case builds the
auxiliaries `d{0},d{1}` per 3.2(5.1) from the redex `inference_critical_pair` (L3.1) and the rank bound
`inference_critical_pair_rank` (T3.4(a)) — both already in `InternalZ`. -/

/- **M1a — DONE.** The genuine reduct `red` (5-case tag dispatch; critical `K`-case = `iRcritG`, the
genuine recombination on correct reduced endsequents) is now defined + `𝚺₁`-definable in `InternalZ`,
with per-rule recursion equations (`red_zAtom`/`red_zIall`/`red_zIneg`/`red_zInd`/`red_zAxAll`/`red_zAxNeg`/
`red_zK`). The placeholder def is removed — `red` is `InternalZ.red`. -/

/-- **M1a — DONE (route B, lap 96).** `red` preserves the end-sequent on the chain-reduct rules
(`Ind`, `K`) of a `∅→⊥` derivation. With the conclusion-reducing `iRKr` the chain `K`-case keeps `Π`
only when the selected premise is `Rep`; on the ⊥-orbit that holds by Cor 2.1
(`InternalZ.fstIdx_red_of_emptyAnt_botSucc`). -/
theorem fstIdx_red {d : V} (hd : ZDerivation d)
    (hant : seqAnt (fstIdx d) = (∅ : V)) (hsucc : seqSucc (fstIdx d) = (^⊥ : V))
    (htag : zTag d = 3 ∨ zTag d = 4) :
    fstIdx (red d) = fstIdx d := fstIdx_red_of_emptyAnt_botSucc hd hant hsucc htag

/-! ## M1b — `RedSound` for `red`: validity as the parallel-induction invariant
Buchholz Thm 3.4(b) / Thm 6.2: principal sequent ⊆ Γ, cut-rank `< m`. Proved as a SEPARATE simultaneous
induction over the same `red` (not recovered post-hoc from the ordinal side) — threading the banked
`zKValidFDef` (faithful validity). This is the cut-elimination core; everything downstream is plumbing. -/

/-! ### `redSound` decomposed: structural induction skeleton + two precise validity residuals

`redSound` is the genuine cut-elimination soundness. We prove the GENERAL form
`redSoundGen : ∀ d, ZDerivation d → ZDerivation (red d)` by `zDerivation_induction`; the seven `ZPhi`
disjuncts split as:

* **atom / Ax∀ / Ax¬** (`red = d`): rebuilt directly from the disjunct via `zDerivation_iff.mpr`.
* **I∀ / I¬** (`red = d₀`, the premise): the immediate sub-derivation, from the IH.
* **Ind** (`red = zK s (irk p) (iIndReductSeq d₀ d₁ 1)`): a chain whose premises are the Ind premises
  (`znth_iIndReductSeq_ZDerivation`); a genuine `ZDerivation` once the produced chain is valid — the
  residual `zKValid_iIndReduct_of_zInd` (Buchholz Thm 3.4, Ind case).
* **K** (`red = iRK …`, the 5.1/5.2.1/5.2.2 dispatch): the genuine recombination is a `ZDerivation`
  given every premise reduct `red dᵢ` is — the residual `ZDerivation_red_zK` (Buchholz Thm 3.4, K case;
  the heart of cut-elimination).

This splits the single fat `redSound` `sorry` into exactly the two deep Buchholz-3.4 validity facts. -/

/-- **Residual (Ind case of Buchholz Thm 3.4).** The Ind-reduct chain `zK s (irk p) (iIndReductSeq d₀ d₁ 1)`
of a valid `Ind` inference is FAITHFULLY valid (`zKValidF`, no criticality). The chain's `Seq` structure
and per-premise derivability are free (`znth_iIndReductSeq_ZDerivation`); this is the validity-threading
obligation. (Stated at `zKValidF` not `zKValid`: the reduct chain need not be critical.) -/
theorem zKValidF_iIndReduct_of_zInd {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1)) :
    zKValidF s (irk p) (iIndReductSeq d0 d1 1) := sorry

/-! ### ⚠️ OBSTRUCTION (lap 136) — `zKValidF_iIndReduct_of_zInd` is FALSE as stated

The `k=1` Ind reduct sequence `iIndReductSeq d0 d1 1 = ⟨d1, d0⟩` (index 0 = `d1` the step premise, index
1 = `d0` the base premise; `lh = 2`). Its `zKValidF` REQUIRES `isChainInf s (irk p) ⟨d1,d0⟩`, whose exit
clause demands SOME premise `j0 ∈ {0,1}` carry the conclusion succedent (`chainAsucc ds j0 = seqSucc s`)
or `⊥`. The two premise succedents are `seqSucc (fstIdx d1) = F(a+1)` and `seqSucc (fstIdx d0) = F(0)`
(`zIndWff`), while the conclusion succedent is `seqSucc s = F(t)` for the Ind term `t = π₂ at'`. So a valid
reduct chain FORCES `F(t) ∈ {F(a+1), F(0)}` (modulo `⊥`) — true only for a DEGENERATE term (`t = 0`, or
`t` substituting like `a+1`). For a genuine Ind node with an arbitrary closed term (e.g. `t = numeral 5`,
`a` fresh) this is violated: `substs1 5 p ≠ substs1 0 p`, `≠ substs1 (a+1) p`. The reduct also has the
WRONG order vs the proven critical reduct (`isChainInf_iCritReductSeq`: source FIRST, cut-user LAST —
`⟨d0,d1⟩`), and threading at premise `d1` would need `F(a) ∈ Γ` (eigenvar, fresh → false).

The two theorems below prove this obstruction IN-KERNEL. Consequence: the genuine Ind reduct cannot be a
single `k=1` finite chain; it is the recursive predecessor cut `red(Ind@F(t)) = K^{irk p}⟨Ind@F(t'),
d1[a:=t']⟩` for `t = t'+1` (and `= d0` for `t = 0`), which decreases the term and recurses. See
`PENDING_WORK.md` lap-136 for the corrected-reduct attack. -/

/-- **OBSTRUCTION ½ (pure chain combinatorics).** `isChainInf s r (iIndReductSeq d0 d1 1)` forces ONE of
the two premise succedents to coincide with the conclusion succedent `seqSucc s` (or `⊥`): the only exit
indices for a length-2 chain are `0` (succedent `seqSucc (fstIdx d1)`) and `1` (succedent
`seqSucc (fstIdx d0)`). No `ZDerivation`/`zIndWff` hypothesis. -/
theorem isChainInf_iIndReduct_exit {s r d0 d1 : V}
    (hc : isChainInf s r (iIndReductSeq d0 d1 1)) :
    seqSucc (fstIdx d1) = seqSucc s ∨ seqSucc (fstIdx d1) = (^⊥ : V) ∨
      seqSucc (fstIdx d0) = seqSucc s ∨ seqSucc (fstIdx d0) = (^⊥ : V) := by
  have hlh : lh (iIndReductSeq d0 d1 1) = 2 := by
    rw [iIndReductSeq, Seq.lh_seqCons d0 (iRepeatSeq_seq d1 1), iRepeatSeq_lh, one_add_one_eq_two]
  have h0 : znth (iIndReductSeq d0 d1 1) 0 = d1 := by
    rw [iIndReductSeq,
      znth_seqCons_of_lt (iRepeatSeq_seq d1 1) d0 (by rw [iRepeatSeq_lh]; exact one_pos),
      znth_iRepeatSeq 0 one_pos]
  have h1 : znth (iIndReductSeq d0 d1 1) 1 = d0 := by
    have hself := znth_seqCons_self (iRepeatSeq_seq d1 1) d0
    rw [iRepeatSeq_lh] at hself
    rw [iIndReductSeq]; exact hself
  obtain ⟨j0, hj0, hexit, _, _⟩ := hc
  rw [hlh] at hj0
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hj0) with rfl | rfl
  · rw [show chainAsucc (iIndReductSeq d0 d1 1) 0 = seqSucc (fstIdx d1) from by
      unfold chainAsucc; rw [h0]] at hexit
    rcases hexit with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [show chainAsucc (iIndReductSeq d0 d1 1) 1 = seqSucc (fstIdx d0) from by
      unfold chainAsucc; rw [h1]] at hexit
    rcases hexit with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- **OBSTRUCTION 2/2 (the term constraint).** With the `zIndWff` succedent data, a valid `k=1` Ind reduct
chain forces the conclusion succedent `seqSucc s = F(t)` to equal `F(a+1)` or `F(0)` (or a premise
succedent to be `⊥`). For a genuine Ind node (`t = π₂ at'` an arbitrary closed term) this is FALSE — the
kernel-verified refutation of `zKValidF_iIndReduct_of_zInd` as stated. -/
theorem zKValidF_iIndReduct_forces_degenerate {s at' p d0 d1 : V}
    (hwff : zIndWff (zInd s at' p d0 d1))
    (hv : zKValidF s (irk p) (iIndReductSeq d0 d1 1)) :
    seqSucc s = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.qqAdd (qqFvar (π₁ at'))
        (Bootstrapping.Arithmetic.numeral 1)) p
      ∨ seqSucc s = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) p
      ∨ seqSucc (fstIdx d1) = (^⊥ : V) ∨ seqSucc (fstIdx d0) = (^⊥ : V) := by
  obtain ⟨hc, _⟩ := hv
  obtain ⟨⟨_, h0succ⟩, ⟨_, _, h1succ⟩, _, _, _⟩ := hwff
  simp only [zIndPrem0_zInd, zIndPrem1_zInd, zIndP_zInd, zIndEig_zInd, fstIdx_zInd] at h0succ h1succ
  rcases isChainInf_iIndReduct_exit hc with h | h | h | h
  · exact Or.inl (by rw [← h]; exact h1succ)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl (by rw [← h]; exact h0succ))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ### Toward the CORRECTED Ind reduct (lap 136) — telescoping chain-validity

The genuine Ind reduct (the fix for the obstruction above) is the **substituted multi-step chain**
`⟨d0, d1[a:=0], …, d1[a:=k-1]⟩` (`k =` value of the Ind term `t`): premise 0 = base `d0 : Γ→F(0)`, premise
`i+1 = d1[a:=i] : Γ,F(i)→F(i+1)`, exit `j0 = k` carrying `F(k)=F(t)`. The validity of THAT chain is
`isChainInf`, whose content is purely that the antecedents TELESCOPE. `isChainInf_telescope` below proves
exactly that — the k-step generalization of `isChainInf_iCritReductSeq` (the proven k=1 case) — abstractly
over any sequence with the telescoping shape, so the concrete (PR-built) substituted reduct only has to
supply the per-premise end-sequent read-outs. This is the reusable validity core. -/

/-- **Telescoping chain-validity** (general Buchholz cut-chain, k steps). A length-`k+1` premise sequence
whose antecedents telescope — premise `0`'s antecedent threads into `Γ = seqAnt s`, and each premise `i+1`'s
antecedent threads into `Γ ∪ {chainAsucc ds i}` (the prior premise's succedent) — with the LAST premise
(index `k`) carrying the conclusion succedent `seqSucc s` (or `⊥`), and the non-exit succedents rank-bounded,
is `isChainInf`-valid (exit `j0 = k`). The k-step generalization of `isChainInf_iCritReductSeq`. -/
theorem isChainInf_telescope {s r ds k : V} (hk : lh ds = k + 1)
    (hbase : ∀ B, inAnt B (chainAnt ds 0) → inAnt B (seqAnt s))
    (hstep : ∀ i < k, ∀ B, inAnt B (chainAnt ds (i + 1)) →
        inAnt B (seqAnt s) ∨ B = chainAsucc ds i)
    (hexit : chainAsucc ds k = seqSucc s ∨ chainAsucc ds k = (^⊥ : V))
    (hrank : ∀ i < k, irk (chainAsucc ds i) ≤ r) :
    isChainInf s r ds := by
  refine ⟨k, by rw [hk]; exact lt_add_one k, hexit, ?_, hrank⟩
  intro i hi B hB
  rcases eq_or_ne i 0 with rfl | hne
  · exact Or.inl (hbase B hB)
  · have h1i : 1 ≤ i := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hne)
    have hi1 : i - 1 + 1 = i := tsub_add_cancel_of_le h1i
    have hjk : i - 1 < k := lt_iff_succ_le.mpr (by rw [hi1]; exact hi)
    rw [← hi1] at hB
    rcases hstep (i - 1) hjk B hB with h | h
    · exact Or.inl h
    · exact Or.inr ⟨i - 1, tsub_lt_self (pos_iff_ne_zero.mpr hne) one_pos, h⟩

/-! ### The CORRECTED Ind reduct sequence `iIndReductSeqG = ⟨d0, d1[a:=0], …, d1[a:=k-1]⟩`

The genuine (validity-bearing) Ind reduct, built by primitive recursion on `k` (the value of the Ind term):
`zero ↦ ⟨d0⟩`, `succ i ↦ seqCons ih (zsubst d1 a (numeral i))` (append the `i`-substituted step). Unlike the
ordinal-shadow `iIndReductSeq d0 d1 1 = ⟨d1,d0⟩` (lap-136 obstruction: not valid), this telescopes — premise
`i+1 = d1[a:=numeral i]` concludes `Γ,F(i)→F(i+1)`, threading its `F(i)` against premise `i`'s succedent —
so `isChainInf_telescope` gives its `zKValidF`. -/

noncomputable def iIndReductSeqG.blueprint : PR.Blueprint 3 where
  zero := .mkSigma “y d0 d1 a. !seqConsDef y 0 d0”
  succ := .mkSigma “y ih i d0 d1 a.
    ∃ ni, !(Bootstrapping.Arithmetic.numeralGraph) ni i ∧
      ∃ z, !zsubstDef z d1 a ni ∧ !seqConsDef y ih z”

noncomputable def iIndReductSeqG.construction : PR.Construction V iIndReductSeqG.blueprint where
  zero := fun x ↦ seqCons ∅ (x 0)
  succ := fun x i ih ↦ seqCons ih (zsubst (x 1) (x 2) (Bootstrapping.Arithmetic.numeral i))
  zero_defined := .mk fun v ↦ by simp [iIndReductSeqG.blueprint, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iIndReductSeqG.blueprint, seqCons_defined.iff,
      (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff, zsubst_defined.iff]

/-- `iIndReductSeqG d0 d1 a k = ⟨d0, d1[a:=0], …, d1[a:=k-1]⟩` (length `k+1`). -/
noncomputable def iIndReductSeqG (d0 d1 a k : V) : V := iIndReductSeqG.construction.result ![d0, d1, a] k

@[simp] lemma iIndReductSeqG_zero (d0 d1 a : V) : iIndReductSeqG d0 d1 a 0 = seqCons ∅ d0 := by
  simp [iIndReductSeqG, iIndReductSeqG.construction]

@[simp] lemma iIndReductSeqG_succ (d0 d1 a k : V) :
    iIndReductSeqG d0 d1 a (k + 1) =
      seqCons (iIndReductSeqG d0 d1 a k) (zsubst d1 a (Bootstrapping.Arithmetic.numeral k)) := by
  simp [iIndReductSeqG, iIndReductSeqG.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iIndReductSeqGDef : 𝚺₁.Semisentence 5 :=
  iIndReductSeqG.blueprint.resultDef.rew (Rew.subst ![#0, #4, #1, #2, #3])

instance iIndReductSeqG_defined : 𝚺₁-Function₄ (iIndReductSeqG : V → V → V → V → V) via iIndReductSeqGDef :=
  .mk fun v ↦ by simp [iIndReductSeqG.construction.result_defined_iff, iIndReductSeqGDef]; rfl

instance iIndReductSeqG_definable : 𝚺₁-Function₄ (iIndReductSeqG : V → V → V → V → V) :=
  iIndReductSeqG_defined.to_definable
instance iIndReductSeqG_definable' (Γ) : Γ-[m + 1]-Function₄ (iIndReductSeqG : V → V → V → V → V) :=
  iIndReductSeqG_definable.of_sigmaOne

@[simp] lemma iIndReductSeqG_seq (d0 d1 a k : V) : Seq (iIndReductSeqG d0 d1 a k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [iIndReductSeqG_zero]; exact seq_empty.seqCons d0
  case succ k ih => rw [iIndReductSeqG_succ]; exact ih.seqCons _

@[simp] lemma iIndReductSeqG_lh (d0 d1 a k : V) : lh (iIndReductSeqG d0 d1 a k) = k + 1 := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [iIndReductSeqG_zero, Seq.lh_seqCons d0 seq_empty, lh_empty]
  case succ k ih => rw [iIndReductSeqG_succ, Seq.lh_seqCons _ (iIndReductSeqG_seq d0 d1 a k), ih]

/-- Premise `0` of the corrected reduct is the base `d0` (any `k`). -/
lemma znth_iIndReductSeqG_zero (d0 d1 a : V) : ∀ k, znth (iIndReductSeqG d0 d1 a k) 0 = d0 := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [iIndReductSeqG_zero]
    have h := znth_seqCons_self seq_empty d0
    rwa [lh_empty] at h
  case succ k ih =>
    rw [iIndReductSeqG_succ,
      znth_seqCons_of_lt (iIndReductSeqG_seq d0 d1 a k) _ (by rw [iIndReductSeqG_lh]; simp)]
    exact ih

/-- Premise `i+1` of the corrected reduct is the `i`-substituted step `d1[a:=numeral i]` (`i < k`). -/
lemma znth_iIndReductSeqG_step (d0 d1 a : V) : ∀ k, ∀ i < k,
    znth (iIndReductSeqG d0 d1 a k) (i + 1) = zsubst d1 a (Bootstrapping.Arithmetic.numeral i) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ k ih =>
    intro i hi
    rw [iIndReductSeqG_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hi) with hik | hik
    · rw [znth_seqCons_of_lt (iIndReductSeqG_seq d0 d1 a k) _
        (by rw [iIndReductSeqG_lh]; simpa using hik)]
      exact ih i hik
    · rw [hik]
      have h := znth_seqCons_self (iIndReductSeqG_seq d0 d1 a k)
        (zsubst d1 a (Bootstrapping.Arithmetic.numeral k))
      rwa [iIndReductSeqG_lh] at h

/-! ### `chainAsucc`/`chainAnt` readouts of the corrected reduct (prerequisites for the tag-3 `isChainInf`)

The threading/exit/rank conditions of `isChainInf s (irk p) (iIndReductSeqG d0 d1 a k)` (via the reusable
`isChainInf_of_last`) read the reduct only through its per-premise end-sequent projections `chainAsucc`/
`chainAnt` (`= seqSucc/seqAnt ∘ fstIdx ∘ znth`). These four resolve those projections to the base premise
`d0` (index 0) and the eigensubstituted step premise `d1[a:=numeral i]` (index `i+1`, `i < k`), so the
`isChainInf` assembly can apply `seqSucc_zsubst_zInd_step` (succedent `F(i+1)`) + the antecedent-threading
data directly. Pure `znth_iIndReductSeqG_zero`/`_step` rewrites — no `ZDerivation` hypothesis. -/

/-- Succedent of the base premise (index 0) of the corrected reduct = `seqSucc (fstIdx d0)`. -/
lemma chainAsucc_iIndReductSeqG_zero (d0 d1 a k : V) :
    chainAsucc (iIndReductSeqG d0 d1 a k) 0 = seqSucc (fstIdx d0) := by
  unfold chainAsucc; rw [znth_iIndReductSeqG_zero d0 d1 a k]

/-- Succedent of step premise `i+1` (`i < k`) of the corrected reduct = succedent of `d1[a:=numeral i]`. -/
lemma chainAsucc_iIndReductSeqG_step (d0 d1 a : V) {k i : V} (hi : i < k) :
    chainAsucc (iIndReductSeqG d0 d1 a k) (i + 1)
      = seqSucc (fstIdx (zsubst d1 a (Bootstrapping.Arithmetic.numeral i))) := by
  unfold chainAsucc; rw [znth_iIndReductSeqG_step d0 d1 a k i hi]

/-- Antecedent of the base premise (index 0) of the corrected reduct = `seqAnt (fstIdx d0)`. -/
lemma chainAnt_iIndReductSeqG_zero (d0 d1 a k : V) :
    chainAnt (iIndReductSeqG d0 d1 a k) 0 = seqAnt (fstIdx d0) := by
  unfold chainAnt; rw [znth_iIndReductSeqG_zero d0 d1 a k]

/-- Antecedent of step premise `i+1` (`i < k`) of the corrected reduct = antecedent of `d1[a:=numeral i]`. -/
lemma chainAnt_iIndReductSeqG_step (d0 d1 a : V) {k i : V} (hi : i < k) :
    chainAnt (iIndReductSeqG d0 d1 a k) (i + 1)
      = seqAnt (fstIdx (zsubst d1 a (Bootstrapping.Arithmetic.numeral i))) := by
  unfold chainAnt; rw [znth_iIndReductSeqG_step d0 d1 a k i hi]

/-- **Succedent of the LAST premise (index `k`, `k>0`) of the corrected reduct** = succedent of the top
eigensubstituted step `d1[a:=numeral (k-1)]`. The exact `chainAsucc` the `isChainInf` EXIT clause reads at
`j0 = lh - 1 = k`. Pure arithmetic specialization of `chainAsucc_iIndReductSeqG_step` at `i = k-1`. -/
lemma chainAsucc_iIndReductSeqG_last (d0 d1 a : V) {k : V} (hk : 0 < k) :
    chainAsucc (iIndReductSeqG d0 d1 a k) k
      = seqSucc (fstIdx (zsubst d1 a (Bootstrapping.Arithmetic.numeral (k - 1)))) := by
  have hkk : k - 1 + 1 = k := sub_add_self_of_le (pos_iff_one_le.mp hk)
  have hstep := chainAsucc_iIndReductSeqG_step d0 d1 a (k := k) (i := k - 1) (tsub_lt_self hk one_pos)
  rwa [hkk] at hstep

/-- **Ind-step succedent under eigensubstitution.** The step premise `d1 : Γ,F(a)→F(a+1)` of a valid Ind
node, substituted `a := t`, has succedent `F(t+1) = substs1 (t ^+ 𝟏) p` (modulo eigenvar freshness on `p`,
`fvSubst a t p = p`). The Ind-step analog of `seqSucc_zsubst_zIall_premise`; this is the telescoping
succedent `chainAsucc` of premise `i+1` of the corrected reduct (with `t = numeral i`). Since `^+ = qqAdd`
and `𝟏 = numeral 1`, `numeral_succ_pos` turns `t ^+ 𝟏` into `numeral (i+1)` for `i > 0`. -/
theorem seqSucc_zsubst_zInd_step {s at' p d0 d1 t : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hZ : ZDerivation (zInd s at' p d0 d1))
    (hpfresh : fvSubst ℒₒᵣ (π₁ at') t p = p) :
    seqSucc (fstIdx (zsubst d1 (π₁ at') t)) =
      substs1 ℒₒᵣ (Bootstrapping.Arithmetic.qqAdd t (Bootstrapping.Arithmetic.numeral 1)) p := by
  obtain ⟨_, hd1, hwff⟩ := zDerivation_zInd_inv hZ
  obtain ⟨_, ⟨_, _, h1succ⟩, _, hsf, _⟩ := hwff
  simp only [zIndPrem1_zInd, zIndEig_zInd, zIndP_zInd] at h1succ hsf
  have hv : IsSemiterm ℒₒᵣ 0
      (Bootstrapping.Arithmetic.qqAdd (qqFvar (π₁ at')) (Bootstrapping.Arithmetic.numeral 1)) :=
    isSemiterm_succVar (π₁ at')
  rw [fstIdx_zsubst (π₁ at') t hd1, seqSucc_fvSubstSeqt, h1succ,
    fvSubst_substs1 ht hv hsf,
    termFvSubst_qqAdd _ _ _ _ ((IsSemiterm.fvar (L := ℒₒᵣ) 0 (π₁ at')).isUTerm)
      (Bootstrapping.Arithmetic.numeral_uterm 1),
    termFvSubst_fvar_self (L := ℒₒᵣ), termFvSubst_numeral, hpfresh]

/-! ### Branch recursion equations for the tag-4 dispatch (table lookups resolved to `red dᵢ`)

`red (zK s r ds) = iRK (zK s r ds) (redTable …)` dispatches on two `permIdx` sentinels. These three
equations resolve the `redTable` lookups to `red dᵢ` (via `znth_redTable_eq_red`, exactly as `red_zK_crit`
does for the 5.1 branch), so each branch is stated over the genuine per-premise reduct the IH supplies. -/

-- (`red_zK_rep` / `red_zK_splice` / `red_zK_rep_nonchain` now live in `Zsubst.lean` and are imported;
-- the former local copies here were removed to avoid duplicate declarations once Crux2Blueprint imports
-- `GoodsteinPA.Zsubst` for the route-B regularity threading.)

/-! ### Explicit-pair generalization of the critical-cut reduct (the EXISTENCE-form tag-5/6 key)

The lap-129 refutation forced the engine STALL onto a deterministic redex finder (`redexI`/`redexJ`). The
lap-135 existence-form pivot says: at a ⊥-chain K-node we are free to PICK the cut pair `(i,j)` (e.g.
`(cutPartner, majorIdx)`) one-shot, with no threaded finder. The critical-cut SOUNDNESS is already
pair-parametric at the `iCritReductG` level (`ZDerivation_iCritReductG_of` takes the two modified premise
sequences explicitly — InternalZ:9736), and the REPLACE workhorse `ZDerivation_iCritReplaceReduce_of`/`_general`
is parametric in the replaced index. The lone obstruction to building the principal cut at an ARBITRARY pair
without the engine re-key was that `cutFormula d` (InternalZ:6648) reads `redexI d`/`redexJ d`. `cutFormulaAt`
abstracts those to explicit indices `i` (the R-redex) and `j` (the L-redex), with `cutFormula d =
cutFormulaAt (redexI d) (redexJ d) d` by `rfl`. The two half-derivation lemmas (`ZDerivation_corrected_haux0`
etc.) then generalize to explicit pairs (`_at` twins below). This dissolves the tag-5/6 dependence on the
forbidden engine re-key (`redexI/redexJ = (cutPartner, majorIdx)`), leaving only the descent + the
cutPartner-is-principal-R-intro datum. -/

/-- **Explicit-pair cut formula** — `cutFormula` with the redex pair `(redexI d, redexJ d)` abstracted to an
arbitrary R-index `i` and L-index `j`. `cutFormula d = cutFormulaAt (redexI d) (redexJ d) d` definitionally
(`cutFormula_eq_cutFormulaAt`). -/
noncomputable def _root_.GoodsteinPA.InternalZ.cutFormulaAt (i j d : V) : V :=
  if π₁ (chainAsucc (zKseq d) i - 1) = 6 then
    substs1 ℒₒᵣ
      (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) j)))))
      (π₂ (chainAsucc (zKseq d) i - 1))
  else
    neg ℒₒᵣ (π₁ (π₂ (chainAsucc (zKseq d) i - 1)))

/-- `cutFormula d = cutFormulaAt (redexI d) (redexJ d) d` — the explicit pair `(redexI d, redexJ d)`
recovers the finder-keyed `cutFormula`. -/
@[simp] lemma cutFormulaAt_redex (d : V) :
    cutFormulaAt (redexI d) (redexJ d) d = cutFormula d := rfl

/-- `∀`-case readout (explicit pair): when the R-redex's principal is `∀F`, the stripped cut formula is the
`L^k`-instance `F(k)` of the L-redex `j`. The pair-parametric twin of `cutFormula_all`. -/
lemma cutFormulaAt_all {i j d p : V} (hA : chainAsucc (zKseq d) i = (^∀ p : V)) :
    cutFormulaAt i j d = substs1 ℒₒᵣ
      (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) j))))) p := by
  unfold cutFormulaAt
  rw [hA, if_pos (by simp [qqAll])]
  simp [qqAll]

/-- `¬`-case readout (explicit pair): when the R-redex's principal is `¬A = inegF A`, the stripped cut
formula is `A`. The pair-parametric twin of `cutFormula_neg`. -/
lemma cutFormulaAt_neg {i j d p : V} (hp : IsUFormula ℒₒᵣ p)
    (hA : chainAsucc (zKseq d) i = inegF p) :
    cutFormulaAt i j d = p := by
  unfold cutFormulaAt
  rw [hA, if_neg (by simp [inegF, qqOr])]
  simp [inegF, qqOr, hp.neg_neg]

/-- **`haux0_at` — the EXPLICIT-PAIR R-side half (Buchholz Thm 3.4(a), ∀-case).** `ZDerivation_corrected_haux0`
with the redex pair abstracted to an arbitrary R-index `i` (the `I∀` premise) and L-index `j` (supplying the
`L^k`-instance `k = π₁(π₂(tp dⱼ))`). The cut formula is `cutFormulaAt i j (zK s r ds)`. This is the genuine
EXISTENCE-form supplier: the descent picks `(i,j) = (cutPartner, majorIdx)` directly. `ZDerivation_corrected_haux0`
is the `(redexI, redexJ)` instance (`cutFormulaAt_redex`). The proof is `ZDerivation_iCritReplaceReduce_of` (the
index-parametric REPLACE workhorse) on the re-principalized reduct `zsubst d0 a (numeral k)`. -/
theorem ZDerivation_corrected_haux0_at {s r ds i j sᵢ a p d0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : i < lh ds)
    (hdi : znth ds i = zIall sᵢ a p d0)
    (hfresh_eig : maxEigen d0 < a)
    (hpfresh : fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds j))))) p = p)
    (hΓfresh : fvSubstSeq a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds j))))) (seqAnt sᵢ) = seqAnt sᵢ)
    (hsucc_wff : IsUFormula ℒₒᵣ (cutFormulaAt i j (zK s r ds)))
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (seqSetSucc s (cutFormulaAt i j (zK s r ds))) r
      (seqUpdate ds i
        (zsubst d0 a (Bootstrapping.Arithmetic.numeral
          (π₁ (π₂ (tp (znth ds j)))))))) := by
  have hst : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral
      (π₁ (π₂ (tp (znth ds j)))) : V) := by simp
  have hZdi : ZDerivation (zIall sᵢ a p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 _ hi
  have hZred : ZDerivation (zsubst d0 a (Bootstrapping.Arithmetic.numeral
      (π₁ (π₂ (tp (znth ds j)))))) :=
    ZDerivation_zsubst_zIall_premise hst hZdi hfresh_eig
  have htrack : fstIdx (zsubst d0 a (Bootstrapping.Arithmetic.numeral
      (π₁ (π₂ (tp (znth ds j)))))) =
        seqSetSucc sᵢ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral
          (π₁ (π₂ (tp (znth ds j))))) p) :=
    fstIdx_zsubst_zIall_premise hst hZdi hpfresh hΓfresh
  have hchain_i : chainAnt ds i = seqAnt sᵢ := by
    unfold chainAnt; rw [hdi, fstIdx_zIall]
  have hA : chainAsucc (zKseq (zK s r ds)) i = (^∀ p : V) := by
    rw [zKseq_zK]; unfold chainAsucc; rw [hdi, fstIdx_zIall]; exact (zDerivation_zIall_inv hZdi).2.1
  have hcut : substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral
      (π₁ (π₂ (tp (znth ds j))))) p = cutFormulaAt i j (zK s r ds) := by
    rw [cutFormulaAt_all hA, zKseq_zK]
  refine ZDerivation_iCritReplaceReduce_of hi hZ hZred ?_ ?_ ?_ hthread hrank ?_ ?_ ?_ ?_ ?_ ?_
  · rw [htrack, seqAnt_seqSetSucc, hchain_i]
  · rw [htrack, seqSucc_seqSetSucc, seqSucc_seqSetSucc, hcut]
  · rw [seqAnt_seqSetSucc]
  · rw [seqSucc_seqSetSucc]; exact hsucc_wff
  · exact iperm_tp_fstIdx_of_ZDerivation hZred
  · exact (tag_uformula_of_ZDerivation hZred).1
  · exact (tag_uformula_of_ZDerivation hZred).2.1
  · exact (tag_uformula_of_ZDerivation hZred).2.2.1
  · exact (tag_uformula_of_ZDerivation hZred).2.2.2

/-- **`haux0` — the corrected inversion's R-side half (Buchholz Thm 3.4(a), ∀-case), DISCHARGED.** The exact
analogue of `ZDerivation_zK_replace_zIall_of` at the cut INSTANCE `k` instead of `0`: replacing the R-redex
premise `zIall sᵢ a p d0` of a critical chain by the re-principalized reduct `zsubst d0 a (numeral k)`
(deriving `Γ → F(k) = Γ → cutFormula d`), with the conclusion succedent reduced to `cutFormula d`, yields a
`ZDerivation`. This is one of the two halves `ZDerivation_iRcritG_of` needs — the half `red`'s instance-`0`
reduct provably cannot supply (lap-114 finding). Discharged ENTIRELY by the banked
`ZDerivation_iCritReplaceReduce_of` + the lap-114 linchpins (`fstIdx_zsubst_zIall_premise`,
`seqSucc_corrected_redexI_eq_cutFormula` via `cutFormula_all`), modulo only the orbit data: O1
(`maxEigen d0 < a`), O3 freshness (`hpfresh`/`hΓfresh`), the cut-formula wff, and the threading/rank up to
`redexI` (`redexI ≤ j₀`, from the parent `zKValid`; lap-113 `irk_chainAsucc_redexI_le`). `k` is the L-redex
instance `π₁(π₂(tp (redexJ premise)))` — the SAME `k` `cutFormula` reads. This proves the corrected reduct's
R-half is sound; the `red`-redefinition (re-key `iRNextG` tag-4 to emit this reduct) + `haux1` (the
symmetric L-half) + threading-data supply remain. -/
theorem ZDerivation_corrected_haux0 {s r ds sᵢ a p d0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hdi : znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0)
    (hfresh_eig : maxEigen d0 < a)
    (hpfresh : fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) p = p)
    (hΓfresh : fvSubstSeq a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) (seqAnt sᵢ) = seqAnt sᵢ)
    (hsucc_wff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hthread : ∀ i' ≤ redexI (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexI (zK s r ds), irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (seqSetSucc s (cutFormula (zK s r ds))) r
      (seqUpdate ds (redexI (zK s r ds))
        (zsubst d0 a (Bootstrapping.Arithmetic.numeral
          (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds)))))))))) :=
  -- the `(redexI, redexJ)` instance of the explicit-pair `_at` lemma (`cutFormulaAt_redex`, a `rfl`-bridge)
  ZDerivation_corrected_haux0_at hZ hi hdi hfresh_eig hpfresh hΓfresh hsucc_wff hthread hrank

/-- **`haux1_at` — the EXPLICIT-PAIR L-side half (Buchholz Thm 3.4(a), ∀-case).** `ZDerivation_corrected_haux1`
with the L-redex index abstracted to an arbitrary `j` and the cut formula abstracted to an arbitrary `Cc`
(`haux1` reads the cut formula only as a value, via `hsj`/`hCwff` — it never computes it). The §5 logical
axiom `Ax^1` and the `isChainInf_growAnt` threading are index/value-parametric. `ZDerivation_corrected_haux1`
is the `(j := redexJ, Cc := cutFormula)` instance. In the existence-form assembly `Cc := cutFormulaAt i j d`
matches `haux0_at`'s R-half cut formula. -/
theorem ZDerivation_corrected_haux1_at {s r ds j sⱼ p k' C Cc : V}
    (hZ : ZDerivation (zK s r ds))
    (hj : j < lh ds)
    (hdj : znth ds j = zAxAll sⱼ p k')
    (hSeqs : Seq (seqAnt s))
    (hCwff : IsUFormula ℒₒᵣ Cc)
    (hSeqsj : Seq (seqAnt sⱼ))
    (hsj : seqSucc sⱼ = Cc) :
    ZDerivation (zK (seqAddAnt Cc s) r
      (seqUpdate ds j (zAx1 (seqAddAnt Cc sⱼ) C))) := by
  obtain ⟨hciParent, _, _, _, _, _, hcf, hss, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  have hsuccj : IsUFormula ℒₒᵣ (seqSucc sⱼ) := by
    have := hcf j hj
    rwa [chainAsucc, hdj, fstIdx_zAxAll] at this
  have hZredL : ZDerivation (zAx1 (seqAddAnt Cc sⱼ) C) :=
    zDerivation_zAx1_intro (by
      rw [seqSucc_seqAddAnt]; exact (inAnt_seqAddAnt hSeqsj).mpr (Or.inl hsj))
  have hci : isChainInf (seqAddAnt Cc s) r
      (seqUpdate ds j (zAx1 (seqAddAnt Cc sⱼ) C)) := by
    refine isChainInf_growAnt hj hSeqs ?_ ?_ ?_ hciParent
    · rw [chainAnt, hdj, fstIdx_zAxAll]; exact hSeqsj
    · rw [fstIdx_zAx1, seqSucc_seqAddAnt, chainAsucc, hdj, fstIdx_zAxAll]
    · rw [fstIdx_zAx1, seqAnt_seqAddAnt, chainAnt, hdj, fstIdx_zAxAll]
  refine ZDerivation_iCritReplaceReduce_general hj hZ hZredL hci
    (by rw [seqSucc_seqAddAnt]; exact hss)
    (by rw [seqAnt_seqAddAnt]; exact forall_IsUFormula_seqCons hSeqs hsa hCwff)
    (by rw [fstIdx_zAx1, seqSucc_seqAddAnt]; exact hsuccj)
    (by rw [tp_zAx1, fstIdx_zAx1]; exact iperm_isymRep _)
    (fun h => by simp at h) (fun h => by simp at h)
    (fun h => by simp at h) (fun h => by simp at h)

/-- **`haux1` — the corrected inversion's L-side half (Buchholz Thm 3.4(a), ∀-case), ASSEMBLED modulo the
two genuine §5 obligations.** The L-redex `dⱼ = znth ds (redexJ d)` is an `axAll` left-axiom `Ax^{∀p,k}`
(`hdj`). Buchholz §5 case 2.1: its critical reduct is `dⱼ[0] = Ax^1_{F(k),Γⱼ→F(k)}` — the §5 **logical
axiom** `Ax^1` (tag 7), whose antecedent GAINS the cut instance `F(k) = cutFormula d` and whose succedent
is `F(k)` (so it is a genuine logical axiom, succedent ∈ antecedent). In the engine this is
`v = zAx1 (seqAddAnt (cutFormula d) sⱼ) C`. Replacing premise `redexJ` of the critical chain by `v` and
growing the conclusion antecedent by `cutFormula d` (`seqAddAnt`) yields a `ZDerivation` — discharged via
`ZDerivation_iCritReplaceReduce_general` (the antecedent-growth replace constructor, exactly as the I¬
replace `ZDerivation_zK_replace_zIneg_of` uses), with all tag-formula conjuncts vacuous (`tp v = isymRep`,
`zTag v = 7`). The TWO genuine residuals are isolated as hypotheses: **(O-L1)** `hZredL` — that the §5 logical
axiom `zAx1 …` is itself a `ZDerivation` (tag 7 is NOT yet a `ZPhi` disjunct; this is the L-side analogue of
the R-side `ZDerivation_zsubst_zIall_premise`, and the genuine next prerequisite), and **(O-L2)** `hci` — the
threading reconstruction `isChainInf` for the grown-antecedent chain at the corrected reduct (the L-side
analogue of `haux0`'s `hthread`/`hrank`; built from the parent `isChainInf` restricted to `≤ j₀` with the
`F(k)`-weakened antecedent, lap-113 `irk_chainAsucc_redexJ` reasoning). This proves the L-half is sound for
the re-principalized reduct: the inversion's L-side reduces to making `zAx1` a sound derivation + the
threading datum — NOT new deep machinery. Exact analogue of `ZDerivation_corrected_haux0` on the L-side. -/
theorem ZDerivation_corrected_haux1 {s r ds sⱼ p k' C : V}
    (hZ : ZDerivation (zK s r ds))
    (hj : redexJ (zK s r ds) < lh ds)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxAll sⱼ p k')
    (hSeqs : Seq (seqAnt s))
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqsj : Seq (seqAnt sⱼ))
    (hsj : seqSucc sⱼ = cutFormula (zK s r ds)) :
    ZDerivation (zK (seqAddAnt (cutFormula (zK s r ds)) s) r
      (seqUpdate ds (redexJ (zK s r ds))
        (zAx1 (seqAddAnt (cutFormula (zK s r ds)) sⱼ) C))) :=
  -- the `(j := redexJ, Cc := cutFormula)` instance of the explicit-pair `_at` lemma
  ZDerivation_corrected_haux1_at hZ hj hdj hSeqs hCwff hSeqsj hsj

/-- **`haux1_neg_at` — the EXPLICIT-PAIR ¬-case ANTECEDENT half.** `ZDerivation_corrected_haux1_neg` with the
R-redex index abstracted to arbitrary `i` and the cut formula to arbitrary `Cc` (used only via `hcut : Cc = p`
and `hCwff`). `ZDerivation_corrected_haux1_neg` is the `(i := redexI, Cc := cutFormula)` instance. -/
theorem ZDerivation_corrected_haux1_neg_at {s r ds i sᵢ p d0 Cc : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : i < lh ds)
    (hdi : znth ds i = zIneg sᵢ p d0)
    (hcut : Cc = p)
    (hCwff : IsUFormula ℒₒᵣ Cc)
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (seqAddAnt Cc s) r (seqUpdate ds i d0)) := by
  have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 i hi
  obtain ⟨hZd0, _hsucceq, ⟨hbot, hmem, hp⟩, _, _⟩ := zDerivation_zIneg_inv hZdi
  obtain ⟨-, -, -, -, -, -, -, hss, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  have hchain_i : chainAnt ds i = seqAnt sᵢ := by unfold chainAnt; rw [hdi, fstIdx_zIneg]
  rw [hcut]
  refine ZDerivation_iCritReplaceReduce_general hi hZ hZd0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine isChainInf_reduceR_membership hi (Or.inr hbot) ?_ ?_ hrank
    · intro B hB
      rw [hd0ant] at hB
      rcases (inAnt_seqCons hSeqsi).mp hB with rfl | hBin
      · left; exact (inAnt_seqAddAnt hSeqs).mpr (Or.inl rfl)
      · rcases hthread i le_rfl B (by rw [hchain_i]; exact hBin) with hins | hex
        · left; exact (inAnt_seqAddAnt hSeqs).mpr (Or.inr hins)
        · right; exact hex
    · intro i' hi' B hB
      rcases hthread i' (le_of_lt hi') B hB with hins | hex
      · left; exact (inAnt_seqAddAnt hSeqs).mpr (Or.inr hins)
      · right; exact hex
  · rw [seqSucc_seqAddAnt]; exact hss
  · rw [seqAnt_seqAddAnt]
    exact forall_IsUFormula_seqCons hSeqs hsa (hcut ▸ hCwff)
  · rw [hbot]; simp
  · exact iperm_tp_fstIdx_of_ZDerivation hZd0
  · exact (tag_uformula_of_ZDerivation hZd0).1
  · exact (tag_uformula_of_ZDerivation hZd0).2.1
  · exact (tag_uformula_of_ZDerivation hZd0).2.2.1
  · exact (tag_uformula_of_ZDerivation hZd0).2.2.2

/-- **`haux1_neg` — the ¬-case inversion's ANTECEDENT half (Buchholz Thm 3.4(a), ¬-subcase `d{1}`).**
For a critical cut on `¬A` (so `cutFormula d = A`, via `cutFormula_neg`), the antecedent half `d{1} =
K^r_{A,Π}(i/dᵢ[0])` replaces the **R**-redex `i = redexI d` (the `I¬` rule `zIneg sᵢ A d0`) by its reduct
`dᵢ[0] = d0` (Buchholz Def 3.2 clause 3, `d[0] := d₀`) — `d0` derives `A,Γᵢ→⊥`. The conclusion gains `A`
in its antecedent (`seqAddAnt (cutFormula d) Π`) while KEEPING the chain endform succedent `D = seqSucc Π`;
since `d0`'s succedent is `⊥`, the `isChainInf` re-points its distinguished tip to `i` (the `⊥`-endform),
which is exactly why arbitrary `D` is fine here (`isChainInf_reduceR_membership`, `Or.inr` branch). This is
the ¬-side analogue of the ∀ R-half `ZDerivation_corrected_haux0`, and structurally mirrors the I¬
non-`Rep` replace `ZDerivation_zK_replace_zIneg_of` (which sets `D := ⊥`); the only genuine extra orbit
datum is the faithful premise-antecedent `hd0ant : seqAnt (fstIdx d0) = (seqAnt sᵢ),A` (`zInegWff` pins
only `A ∈ antecedent`). -/
theorem ZDerivation_corrected_haux1_neg {s r ds sᵢ p d0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hcut : cutFormula (zK s r ds) = p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hthread : ∀ i' ≤ redexI (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexI (zK s r ds), irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (seqAddAnt (cutFormula (zK s r ds)) s) r
      (seqUpdate ds (redexI (zK s r ds)) d0)) :=
  -- the `(i := redexI, Cc := cutFormula)` instance of the explicit-pair `_at` lemma
  ZDerivation_corrected_haux1_neg_at hZ hi hdi hcut hCwff hSeqs hSeqsi hd0ant hthread hrank

/-- **`haux0_neg_at` — the EXPLICIT-PAIR ¬-case SUCCEDENT half.** `ZDerivation_corrected_haux0_neg` with the
L-redex index abstracted to arbitrary `j` and the cut formula to arbitrary `Cc` (used only via `hcut : Cc = p`
and `hCwff`). `ZDerivation_corrected_haux0_neg` is the `(j := redexJ, Cc := cutFormula)` instance. -/
theorem ZDerivation_corrected_haux0_neg_at {s r ds j sⱼ p Cc : V}
    (hZ : ZDerivation (zK s r ds))
    (hj : j < lh ds)
    (hdj : znth ds j = zAxNeg sⱼ p)
    (hcut : Cc = p)
    (hCwff : IsUFormula ℒₒᵣ Cc)
    (hthread : ∀ i' ≤ j, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < j, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (seqSetSucc s Cc) r
      (seqUpdate ds j (zAx1 (seqSetSucc sⱼ p) p))) := by
  have hpmem : inAnt p (seqAnt sⱼ) :=
    (zDerivation_zAxNeg_inv (hdj ▸ (zDerivation_zK_inv hZ).2 _ hj)).2.2
  have hZv : ZDerivation (zAx1 (seqSetSucc sⱼ p) p) :=
    zDerivation_zAx1_intro (by rw [seqSucc_seqSetSucc, seqAnt_seqSetSucc]; exact hpmem)
  have hchain_j : chainAnt ds j = seqAnt sⱼ := by unfold chainAnt; rw [hdj, fstIdx_zAxNeg]
  refine ZDerivation_iCritReplaceReduce_of hj hZ hZv ?_ ?_ ?_ hthread hrank ?_ ?_
    (fun h => by simp at h) (fun h => by simp at h) (fun h => by simp at h) (fun h => by simp at h)
  · rw [fstIdx_zAx1, seqAnt_seqSetSucc, hchain_j]
  · rw [fstIdx_zAx1, seqSucc_seqSetSucc, seqSucc_seqSetSucc, hcut]
  · rw [seqAnt_seqSetSucc]
  · rw [seqSucc_seqSetSucc]; exact hCwff
  · rw [tp_zAx1, fstIdx_zAx1]; exact iperm_isymRep _

/-- **`haux0_neg` — the ¬-case inversion's SUCCEDENT half (Buchholz Thm 3.4(a), ¬-subcase `d{0}`).**
For a critical cut on `¬A` (so `cutFormula d = A`, via `cutFormula_neg`), the succedent half `d{0} =
K^r_{Π.A(d)}(j/dⱼ[0])` replaces the **L**-redex `j = redexJ d` (the `axNeg` axiom `zAxNeg sⱼ A`) by its §5
reduct `dⱼ[0] = Ax^1_{Γⱼ→A}` (Buchholz Lemma 5.1 case 2.2: `tp(Ax^{¬A,0}) = L⁰_{¬A}`, `Π0 = Γⱼ→A`). The
reduct `zAx1 (seqSetSucc sⱼ A) A` derives `Γⱼ→A` and the conclusion succedent is set to `A = cutFormula d`
(antecedent KEPT). This is the ¬-side analogue of the ∀ R-half `ZDerivation_corrected_haux0`, via the
KEEP-antecedent/set-succedent constructor `ZDerivation_iCritReplaceReduce_of`.

**The §5 residual `hpmem : inAnt A (seqAnt sⱼ)` is now DISCHARGED (lap 118).** Buchholz 2.2's side
condition `A,¬A ∈ Γ` for the axNeg axiom is now carried by the strengthened `zAxNeg` ZPhi disjunct (the 7th
disjunct's 4th conjunct `inAnt p (seqAnt s)`), so `zDerivation_zAxNeg_inv` returns BOTH `¬A∈Γ` AND `A∈Γ`.
The membership is recovered in-proof from the axNeg premise's own derivation (`zDerivation_zK_inv` +
`zDerivation_zAxNeg_inv`), so the orbit hypothesis is gone — the ¬-side analogue of lap-115's `zAx1`
8th-disjunct discharge of the L-half. -/
theorem ZDerivation_corrected_haux0_neg {s r ds sⱼ p : V}
    (hZ : ZDerivation (zK s r ds))
    (hj : redexJ (zK s r ds) < lh ds)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hthread : ∀ i' ≤ redexJ (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexJ (zK s r ds), irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (seqSetSucc s (cutFormula (zK s r ds))) r
      (seqUpdate ds (redexJ (zK s r ds)) (zAx1 (seqSetSucc sⱼ p) p))) :=
  -- the `(j := redexJ, Cc := cutFormula)` instance of the explicit-pair `_at` lemma
  ZDerivation_corrected_haux0_neg_at hZ hj hdj hcut hCwff hthread hrank

/-- **`haux0_neg` with the §5 axNeg reduct ABOVE the tip (`redexJ > j0`) — KEEP-TIP route (lap 144).** The
succedent half replaces premise `redexJ` (the `zAxNeg` axiom) by `Ax^1_{Γⱼ→A}` and SETS the conclusion
succedent to `A = cutFormula`. The standard `ZDerivation_corrected_haux0_neg` re-points the chain tip to
`redexJ`, forcing threading up to `redexJ` — NOT free from `zKValid` when `redexJ > j0`. Here, on a ⊥-orbit
whose distinguished tip `j0` carries `⊥` (`hbot`), the replaced premise lands strictly ABOVE the tip
(`j0 < redexJ`), so chain-validity is rebuilt with the SAME tip `j0` (`isChainInf_reduceR_keepTip`): the new
conclusion succedent `A` is irrelevant (the tip uses the `⊥`-exit disjunct), and only threading/rank up to
`j0` are needed — exactly the `chainInf_redexI_data` tip datum. Fed through the explicit-`hci`
`ZDerivation_iCritReplaceReduce_general`. -/
theorem ZDerivation_corrected_haux0_neg_keepTip {s r ds j0 sⱼ p : V}
    (hZ : ZDerivation (zK s r ds))
    (hj : redexJ (zK s r ds) < lh ds)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hj0i : j0 < redexJ (zK s r ds)) (hj0 : j0 < lh ds)
    (hbot : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i' ≤ j0, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank0 : ∀ i' < j0, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (seqSetSucc s (cutFormula (zK s r ds))) r
      (seqUpdate ds (redexJ (zK s r ds)) (zAx1 (seqSetSucc sⱼ p) p))) := by
  have hpmem : inAnt p (seqAnt sⱼ) :=
    (zDerivation_zAxNeg_inv (hdj ▸ (zDerivation_zK_inv hZ).2 _ hj)).2.2
  have hZv : ZDerivation (zAx1 (seqSetSucc sⱼ p) p) :=
    zDerivation_zAx1_intro (by rw [seqSucc_seqSetSucc, seqAnt_seqSetSucc]; exact hpmem)
  obtain ⟨_, _, _, _, _, _, _, _, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  refine ZDerivation_iCritReplaceReduce_general hj hZ hZv
    (isChainInf_reduceR_keepTip hj hj0i hj0 hbot
      (seqAnt_seqSetSucc s (cutFormula (zK s r ds))) hthread0 hrank0)
    ?_ ?_ ?_ ?_ (fun h => by simp at h) (fun h => by simp at h) (fun h => by simp at h)
    (fun h => by simp at h)
  · rw [seqSucc_seqSetSucc]; exact hCwff
  · rw [seqAnt_seqSetSucc]; exact hsa
  · rw [fstIdx_zAx1, seqSucc_seqSetSucc, ← hcut]; exact hCwff
  · rw [tp_zAx1, fstIdx_zAx1]; exact iperm_isymRep _

/-- **`haux0_neg` from the ⊥-orbit TIP datum — dispatches on `redexJ ≤ j0` (lap 144).** Given the
`chainInf_redexI_data` tip `j0` (carrying `⊥`, threading/rank up to `j0`), supplies the succedent half
WITHOUT the `redexJ ≤ j0` obligation: if `redexJ ≤ j0` the standard `ZDerivation_corrected_haux0_neg` takes
threading restricted from `j0`; if `redexJ > j0` the keep-tip route
(`ZDerivation_corrected_haux0_neg_keepTip`) rebuilds chain-validity at the unchanged tip `j0`. This is the
lone place the ¬-case needed `redexJ ≤ j0` (`PENDING_WORK` lap-142/143) — now discharged unconditionally. -/
theorem ZDerivation_corrected_haux0_neg_botOrbit {s r ds j0 sⱼ p : V}
    (hZ : ZDerivation (zK s r ds))
    (hj : redexJ (zK s r ds) < lh ds)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hj0 : j0 < lh ds)
    (hbot : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i' ≤ j0, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank0 : ∀ i' < j0, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (seqSetSucc s (cutFormula (zK s r ds))) r
      (seqUpdate ds (redexJ (zK s r ds)) (zAx1 (seqSetSucc sⱼ p) p))) := by
  by_cases hle : redexJ (zK s r ds) ≤ j0
  · exact ZDerivation_corrected_haux0_neg hZ hj hdj hcut hCwff
      (fun i' hi' => hthread0 i' (le_trans hi' hle))
      (fun i' hi' => hrank0 i' (lt_of_lt_of_le hi' hle))
  · push_neg at hle
    exact ZDerivation_corrected_haux0_neg_keepTip hZ hj hdj hcut hCwff hle hj0 hbot hthread0 hrank0

/-- **THE corrected critical-cut inversion, ¬-case — SOUNDNESS PROVEN (modulo the §5 `A∈Γⱼ` orbit datum).**
The negation analogue of `ZDerivation_iRcritG_corrected`: for a critical cut on `¬A` whose redex pair is an
`I¬` R-redex (`zIneg sᵢ A d0`, `redexI`) and an `axNeg` L-redex (`zAxNeg sⱼ A`, `redexJ`), the
SWAPPED-half reduct `iRcritGNeg d ρ` is a genuine `ZDerivation` for any `ρ` emitting the corrected reducts:
- R-redex (`redexI`): `ρ (redexI d) = d0` — the `I¬` child `dᵢ[0] = d₀` deriving `A,Γᵢ→⊥` (no substitution),
- L-redex (`redexJ`): `ρ (redexJ d) = zAx1 (seqSetSucc sⱼ A) A` — the §5 axNeg reduct `dⱼ[0] = Ax^1_{Γⱼ→A}`.
Both stripped halves (`ZDerivation_corrected_haux0_neg`/`_haux1_neg`) feed `ZDerivation_iRcritGNeg_of`; the
cut-rank drop `rk(cutFormula d) ≤ r−1` is `irk_cutFormula_lt`'s ¬-branch (`rk(A) < rk(¬A) ≤ r`), and the
conclusion well-formedness from the parent chain validity. **This is the genuine mathematical content of the
¬-case inversion — the second (and last) critical sub-case after the lap-116 ∀-case** — and it is now
UNCONDITIONALLY sound (the lap-117 `hpmem` residual was discharged lap 118 by strengthening the `zAxNeg`
ZPhi disjunct to carry `A∈Γ`; see `ZDerivation_corrected_haux0_neg`). What remains is purely the engine
re-keying (`red`'s tag-4 critical branch must dispatch ∀/¬ and emit `iRcritGNeg` here). -/
theorem ZDerivation_iRcritGNeg_corrected_neg {s r ds sᵢ sⱼ p d0 : V} {ρ : V → V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hj : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hρI : ρ (redexI (zK s r ds)) = d0)
    (hρJ : ρ (redexJ (zK s r ds)) = zAx1 (seqSetSucc sⱼ p) p)
    (hcut : cutFormula (zK s r ds) = p)
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hthread : ∀ i' ≤ redexJ (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexJ (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r) :
    ZDerivation (iRcritGNeg (zK s r ds) ρ) := by
  obtain ⟨_, _, _, _, _, _, _, hss, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 _ hi
  have hChsucc : chainAsucc ds (redexI (zK s r ds)) = (inegF p : V) := by
    unfold chainAsucc; rw [hdi, fstIdx_zIneg]; exact (zDerivation_zIneg_inv hZdi).2.1
  refine ZDerivation_iRcritGNeg_of (d := zK s r ds) (ρ := ρ) ?_ ?_ ?_ ?_ hCwff ?_ ?_
  · -- haux0 (¬ succedent half): redexJ ↦ §5 axNeg reduct `Ax^1_{Γⱼ→A}`
    rw [hρJ]; simp only [fstIdx_zK, zKrank_zK, zKseq_zK]
    exact ZDerivation_corrected_haux0_neg hZ hj hdj hcut hCwff hthread hrank
  · -- haux1 (¬ antecedent half): redexI ↦ I¬ child `d0`
    rw [hρI]; simp only [fstIdx_zK, zKrank_zK, zKseq_zK]
    exact ZDerivation_corrected_haux1_neg hZ hi hdi hcut hCwff hSeqs hSeqsi hd0ant
      (fun i' hi' => hthread i' (le_trans hi' (le_of_lt hIJ)))
      (fun i' hi' => hrank i' (lt_trans hi' hIJ))
  · -- hsAnt
    rw [fstIdx_zK]; exact hSeqs
  · -- hCrk: rk(cutFormula d) ≤ r − 1 (T3.4(a) strict drop, ¬-case rk(A) < rk(¬A))
    rw [zKrank_zK]
    refine le_pred_of_lt (irk_cutFormula_lt ?_ ?_ ?_)
    · rw [zKseq_zK]; exact (zDerivation_zK_inv hZ).2 _ hi
    · rw [zKseq_zK, hChsucc, hdi, tp_zIneg]
    · rw [zKseq_zK]; exact hrankI
  · -- hssUf
    rw [fstIdx_zK]; exact hss
  · -- hsaUf
    rw [fstIdx_zK]; exact hsa

/-- **The corrected ¬-case inversion, ⊥-orbit TIP form (lap 144) — `redexJ ≤ j0`-FREE.** The `_botOrbit`
twin of `ZDerivation_iRcritGNeg_corrected_neg`: takes the `chainInf_redexI_data` tip `j0` (with
`redexI < j0`, `⊥`-exit `hbot`, threading/rank up to `j0`) instead of the `redexJ`-bounded threading the
original demanded. The succedent half (`haux0`) routes through `ZDerivation_corrected_haux0_neg_botOrbit`
(the keep-tip dispatcher, the ONE place that needed `redexJ ≤ j0`); the antecedent half (`haux1`) and the
cut-rank drop need only `redexI`-bounded data, supplied by restricting from `j0` via `redexI < j0`. -/
theorem ZDerivation_iRcritGNeg_corrected_neg_botOrbit {s r ds j0 sᵢ sⱼ p d0 : V} {ρ : V → V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hj : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hρI : ρ (redexI (zK s r ds)) = d0)
    (hρJ : ρ (redexJ (zK s r ds)) = zAx1 (seqSetSucc sⱼ p) p)
    (hcut : cutFormula (zK s r ds) = p)
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hIj0 : redexI (zK s r ds) < j0) (hj0 : j0 < lh ds)
    (hbot : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i' ≤ j0, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank0 : ∀ i' < j0, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (iRcritGNeg (zK s r ds) ρ) := by
  obtain ⟨_, _, _, _, _, _, _, hss, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 _ hi
  have hChsucc : chainAsucc ds (redexI (zK s r ds)) = (inegF p : V) := by
    unfold chainAsucc; rw [hdi, fstIdx_zIneg]; exact (zDerivation_zIneg_inv hZdi).2.1
  refine ZDerivation_iRcritGNeg_of (d := zK s r ds) (ρ := ρ) ?_ ?_ ?_ ?_ hCwff ?_ ?_
  · -- haux0 (¬ succedent half) via the keep-tip dispatcher (drops the `redexJ ≤ j0` need)
    rw [hρJ]; simp only [fstIdx_zK, zKrank_zK, zKseq_zK]
    exact ZDerivation_corrected_haux0_neg_botOrbit hZ hj hdj hcut hCwff hj0 hbot hthread0 hrank0
  · -- haux1 (¬ antecedent half): redexI ↦ I¬ child `d0`, threading up to redexI < j0
    rw [hρI]; simp only [fstIdx_zK, zKrank_zK, zKseq_zK]
    exact ZDerivation_corrected_haux1_neg hZ hi hdi hcut hCwff hSeqs hSeqsi hd0ant
      (fun i' hi' => hthread0 i' (le_trans hi' (le_of_lt hIj0)))
      (fun i' hi' => hrank0 i' (lt_trans hi' hIj0))
  · -- hsAnt
    rw [fstIdx_zK]; exact hSeqs
  · -- hCrk: rk(cutFormula d) ≤ r − 1
    rw [zKrank_zK]
    refine le_pred_of_lt (irk_cutFormula_lt ?_ ?_ ?_)
    · rw [zKseq_zK]; exact (zDerivation_zK_inv hZ).2 _ hi
    · rw [zKseq_zK, hChsucc, hdi, tp_zIneg]
    · rw [zKseq_zK]; exact hrank0 _ hIj0
  · -- hssUf
    rw [fstIdx_zK]; exact hss
  · -- hsaUf
    rw [fstIdx_zK]; exact hsa

/-- **The ¬-case critical reduct is SOUND — concrete-`ρ` specialization** (the `critReductNeg` twin of
`ZDerivation_iRcritG_critReductCorr`). `ZDerivation (iRcritGNeg d (critReductNeg d))` for the genuine
¬-case reduct supplier, given the orbit data. The two emission equations `hρI`/`hρJ` of
`ZDerivation_iRcritGNeg_corrected_neg` discharge by read-off from `critReductNeg`'s definition
(`critReductNeg_redexI`/`_redexJ`): at `redexI` the `I¬` child `red dᵢ = d₀` (`red_zIneg`), at `redexJ` the
§5 axNeg reduct `Ax^1_{Γⱼ→A}` (`fstIdx_zAxNeg = sⱼ`, `cutFormula d = A`). This is exactly the object the
re-keyed `red` should produce at a critical chain whose R-redex is `I¬` — soundness PROVEN, modulo only the
engine re-keying (`red_zK_crit` ↦ polarity dispatch) and the orbit invariants. Together with
`ZDerivation_iRcritG_critReductCorr` (∀-case), the two polarity-specific reduct suppliers are now both
soundness-certified against their concrete engine `ρ`. -/
theorem ZDerivation_iRcritGNeg_critReductNeg {s r ds sᵢ sⱼ p d0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hj : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p)
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hthread : ∀ i' ≤ redexJ (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexJ (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r) :
    ZDerivation (iRcritGNeg (zK s r ds) (critReductNeg (zK s r ds))) := by
  refine ZDerivation_iRcritGNeg_corrected_neg (sᵢ := sᵢ) (sⱼ := sⱼ) (p := p) (d0 := d0)
    hZ hi hj hIJ hdi hdj ?_ ?_ hcut hd0ant hCwff hSeqs hSeqsi hthread hrank hrankI
  · -- hρI: `critReductNeg` at `redexI` → the `I¬` child `zInegPrem dᵢ = d₀`
    rw [critReductNeg_redexI (ne_of_lt hIJ), zKseq_zK, hdi, zInegPrem_zIneg]
  · -- hρJ: `critReductNeg` at `redexJ` → the §5 axNeg reduct `Ax^1_{Γⱼ→A}`
    rw [critReductNeg_redexJ, zKseq_zK, hdj, fstIdx_zAxNeg, hcut]

/-- **Explicit-pair `iCritReductG` SOUNDNESS (∀-case) — lap-139 NEXT step 1, ASSEMBLED (lap 140).** The
pair-parametric assembly of the lap-139 `_at` halves (`haux0_at` R-side + `haux1_at` L-side) into a full
`ZDerivation` of the CLOSED critical reduct `iCritReductG`, at an ARBITRARY R-intro/L-axiom pair `(i, j)` —
**NO `redexI/redexJ`, NO `iRcritG`** (which bake the deterministic finder). Mirrors `ZDerivation_iRcritG_corrected`
but routes through `ZDerivation_iCritReductG_of` directly, supplying the two halves at the explicit pair. The
cut-rank STRICT drop `irk (cutFormulaAt i j d) ≤ r − 1` is `irk_substs1_lt_all` on the I∀ matrix (`cutFormulaAt_all`).

This is the soundness SKELETON `descent_step_K_tag5` instantiates at `(i, j) = (cutPartner, majorIdx)` — taking
`hdi : znth ds i = zIall …` (the principal R-intro) as a HYPOTHESIS, so it is INDEPENDENT of the lap-140 residual
(`tp(cutPartner) = isymR (^∀p)`); that residual only enters when discharging `hdi` at the existence-form call site. -/
theorem ZDerivation_iCritReductG_all_at {s r ds i j sᵢ a p d0 sⱼ pj k' C : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : i < lh ds)
    (hdi : znth ds i = zIall sᵢ a p d0)
    (hj : j < lh ds)
    (hdj : znth ds j = zAxAll sⱼ pj k')
    (hfresh_eig : maxEigen d0 < a)
    (hpfresh : fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds j))))) p = p)
    (hΓfresh : fvSubstSeq a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds j))))) (seqAnt sᵢ) = seqAnt sᵢ)
    (hSeqs : Seq (seqAnt s))
    (hSeqsj : Seq (seqAnt sⱼ))
    (hsj : seqSucc sⱼ = cutFormulaAt i j (zK s r ds))
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r)
    (hrankI : irk (chainAsucc ds i) ≤ r) :
    ZDerivation (iCritReductG s (cutFormulaAt i j (zK s r ds)) (r - 1) r r
      (seqUpdate ds i (zsubst d0 a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds j)))))))
      (seqUpdate ds j (zAx1 (seqAddAnt (cutFormulaAt i j (zK s r ds)) sⱼ) C))) := by
  obtain ⟨_, _, _, _, _, _, _, hss, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  have hZdi : ZDerivation (zIall sᵢ a p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 _ hi
  have hsfp : IsSemiformula ℒₒᵣ 1 p := (zDerivation_zIall_inv hZdi).2.2.2.2
  have hChsucc : chainAsucc ds i = (^∀ p : V) := by
    unfold chainAsucc; rw [hdi, fstIdx_zIall]; exact (zDerivation_zIall_inv hZdi).2.1
  have hcutEq : cutFormulaAt i j (zK s r ds) = substs1 ℒₒᵣ
      (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth ds j))))) p := by
    rw [cutFormulaAt_all (by rw [zKseq_zK]; exact hChsucc), zKseq_zK]
  have hCwff : IsUFormula ℒₒᵣ (cutFormulaAt i j (zK s r ds)) := by
    rw [hcutEq]
    exact (IsSemiformula.substs1 (by simp : IsSemiterm ℒₒᵣ 0
      (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth ds j)))) : V)) hsfp).isUFormula
  have hCrk : irk (cutFormulaAt i j (zK s r ds)) ≤ r - 1 := by
    refine le_pred_of_lt ?_
    rw [hcutEq]
    refine lt_of_lt_of_le (irk_substs1_lt_all (m := 0) hsfp (by simp)) ?_
    rw [← hChsucc]; exact hrankI
  exact ZDerivation_iCritReductG_of
    (ZDerivation_corrected_haux0_at hZ hi hdi hfresh_eig hpfresh hΓfresh hCwff hthread hrank)
    (ZDerivation_corrected_haux1_at (C := C) (Cc := cutFormulaAt i j (zK s r ds))
      hZ hj hdj hSeqs hCwff hSeqsj hsj)
    hSeqs hCrk hCwff hss hsa

/-- **THE corrected critical-cut inversion — SOUNDNESS PROVEN for the re-principalized reduct.** This is
the assembly the lap-114 crux finding pointed to: for ANY reduct function `ρ` that emits the CORRECTED
critical reducts at the two redexes
- R-redex (I∀): `ρ (redexI d) = zsubst d0 a (numeral k)` — re-principalized at the L-instance `k`
  (NOT the engine's instance-`0`), and
- L-redex (axAll): `ρ (redexJ d) = zAx1 (seqAddAnt (cutFormula d) sⱼ) C` — the §5 logical axiom `Ax^1`,

the closed critical reduct `iRcritG d ρ` is a genuine `ZDerivation`. Both stripped halves
(`ZDerivation_corrected_haux0`/`_haux1`) are fed to the banked `ZDerivation_iRcritG_of`; the rank-side
conjunct `rk(cutFormula d) ≤ r−1` comes from `irk_cutFormula_lt` (T3.4(a) strict drop, the I∀ premise's
matrix closedness supplying the substitution-rank invariance), and the conclusion well-formedness from the
parent chain validity (`zKValidF_of_ZDerivation_zK`). **What remains is purely engine-plumbing:** the
hypotheses `hρI`/`hρJ` hold for the engine `ρ = zAxReduct ∘ red` ONLY after `red`'s tag-4 critical branch
(`iRcritG`/`iRKc`) is re-keyed to substitute the L-instance `k` and emit `zAx1` at the redexes — the
`ZDerivation_red_zK_crit` (false-as-stated under the current `ρ`) becomes provable by `red_zK_crit` + this
lemma once that re-keying lands. The genuine mathematical content of the inversion is HERE, and it is sound. -/
theorem ZDerivation_iRcritG_corrected {s r ds sᵢ sⱼ a p pj k' C d0 : V} {ρ : V → V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hj : redexJ (zK s r ds) < lh ds)
    (hdi : znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k')
    (hρI : ρ (redexI (zK s r ds)) = zsubst d0 a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))))
    (hρJ : ρ (redexJ (zK s r ds)) = zAx1 (seqAddAnt (cutFormula (zK s r ds)) sⱼ) C)
    (hfresh_eig : maxEigen d0 < a)
    (hpfresh : fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) p = p)
    (hΓfresh : fvSubstSeq a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) (seqAnt sᵢ) = seqAnt sᵢ)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s))
    (hSeqsj : Seq (seqAnt sⱼ))
    (hsj : seqSucc sⱼ = cutFormula (zK s r ds))
    (hthread : ∀ i' ≤ redexI (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexI (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r) :
    ZDerivation (iRcritG (zK s r ds) ρ) := by
  obtain ⟨_, _, _, _, _, _, _, hss, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  have hZdi : ZDerivation (zIall sᵢ a p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 _ hi
  have hChsucc : chainAsucc ds (redexI (zK s r ds)) = (^∀ p : V) := by
    unfold chainAsucc; rw [hdi, fstIdx_zIall]; exact (zDerivation_zIall_inv hZdi).2.1
  refine ZDerivation_iRcritG_of (d := zK s r ds) (ρ := ρ) ?_ ?_ ?_ ?_ hCwff ?_ ?_
  · -- haux0 (R-half): the re-principalized I∀ reduct
    rw [hρI]; simp only [fstIdx_zK, zKrank_zK, zKseq_zK]
    exact ZDerivation_corrected_haux0 hZ hi hdi hfresh_eig hpfresh hΓfresh hCwff hthread hrank
  · -- haux1 (L-half): the §5 logical-axiom reduct
    rw [hρJ]; simp only [fstIdx_zK, zKrank_zK, zKseq_zK]
    exact ZDerivation_corrected_haux1 hZ hj hdj hSeqs hCwff hSeqsj hsj
  · -- hsAnt
    rw [fstIdx_zK]; exact hSeqs
  · -- hCrk: rk(cutFormula d) ≤ r − 1 (T3.4(a) strict drop)
    rw [zKrank_zK]
    refine le_pred_of_lt (irk_cutFormula_lt ?_ ?_ ?_)
    · rw [zKseq_zK]; exact (zDerivation_zK_inv hZ).2 _ hi
    · rw [zKseq_zK, hChsucc, hdi, tp_zIall]
    · rw [zKseq_zK]; exact hrankI
  · -- hssUf
    rw [fstIdx_zK]; exact hss
  · -- hsaUf
    rw [fstIdx_zK]; exact hsa

/-- **The corrected critical reduct is SOUND — concrete-`ρ` specialization (no `ρ`-emission side goals).**
`ZDerivation (iRcritG d (critReductCorr d))` for the genuine re-principalized reduct supplier, given the
orbit data. The two emission equations `hρI`/`hρJ` of `ZDerivation_iRcritG_corrected` discharge by `simp`
from `critReductCorr`'s definition (`hIJ : redexI < redexJ` disambiguates the redex slots, `hdi`/`hdj`
compute the accessors). This is exactly the object `red` should produce at a critical chain — soundness
PROVEN, modulo only the engine re-keying (`red_zK_crit` ↦ `critReductCorr`) and the orbit invariants. -/
theorem ZDerivation_iRcritG_critReductCorr {s r ds sᵢ sⱼ a p pj k' d0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hj : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k')
    (hfresh_eig : maxEigen d0 < a)
    (hpfresh : fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) p = p)
    (hΓfresh : fvSubstSeq a (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) (seqAnt sᵢ) = seqAnt sᵢ)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s))
    (hSeqsj : Seq (seqAnt sⱼ))
    (hsj : seqSucc sⱼ = cutFormula (zK s r ds))
    (hthread : ∀ i' ≤ redexI (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexI (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r) :
    ZDerivation (iRcritG (zK s r ds) (critReductCorr (zK s r ds))) := by
  refine ZDerivation_iRcritG_corrected (sᵢ := sᵢ) (sⱼ := sⱼ) (a := a) (p := p) (pj := pj)
    (k' := k') (C := cutFormula (zK s r ds)) (d0 := d0)
    hZ hi hj hdi hdj ?_ ?_ hfresh_eig hpfresh hΓfresh hCwff hSeqs hSeqsj hsj hthread hrank hrankI
  · -- hρI: `critReductCorr` at `redexI` (skip the `redexJ` branch via `hIJ.ne`, then read off the accessors)
    rw [critReductCorr, if_neg (ne_of_lt hIJ), if_pos rfl, zKseq_zK, hdi,
      zIallPrem_zIall, zIallEig_zIall]
  · -- hρJ: `critReductCorr` at `redexJ` (the `redexJ` branch fires; `fstIdx (zAxAll sⱼ …) = sⱼ`)
    rw [critReductCorr, if_pos rfl, zKseq_zK, hdj, fstIdx_zAxAll]

/-- **The re-keyed critical reduct `iRKcCrit` is SOUND — ∀-case, freshness now supplied from the orbit.**
The soundness payoff of the freshness campaign, keyed on the engine-swap reduct `iRKcCrit` (parallel to
`ZRegular_iRKcCrit` / `ZFresh_iRKcCrit`). Where `ZDerivation_iRcritG_critReductCorr` takes the freshness
conditions `hpfresh`/`hΓfresh` as bare hypotheses, this consumes the orbit invariant `ZFresh (zK s r ds)`
(plus the matrix wff `hpwff`) and discharges them INTERNALLY via `zfresh_critReductCorr_freshness` — closing
the lap-114 instance-`0`-vs-`k` obstruction on the supply side. The remaining hypotheses are the genuine
non-freshness chain-validity plumbing (`hCwff`/`hSeqs`/`hSeqsj`/`hsj`/`hthread`/`hrank`/`hrankI`), all
derivable from `isChainInf` (see `PENDING_WORK` lap-128 step (c)). With `iRKcCrit_eq_corr`, this IS the
`ZDerivation_red_zK_crit` ∀-branch under the engine swap (`red_zK_crit ↦ iRKcCrit`). -/
theorem ZDerivation_iRKcCrit_all {s r ds sᵢ sⱼ a p pj k' d0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hj : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k')
    (hfresh_eig : maxEigen d0 < a)
    (hfresh : ZFresh (zK s r ds))
    (hpwff : IsUFormula ℒₒᵣ p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s))
    (hSeqsj : Seq (seqAnt sⱼ))
    (hsj : seqSucc sⱼ = cutFormula (zK s r ds))
    (hthread : ∀ i' ≤ redexI (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexI (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r) :
    ZDerivation (iRKcCrit (zK s r ds)) := by
  have htag1 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) = 1 := by
    rw [zKseq_zK, hdi]; exact zTag_zIall _ _ _ _
  rw [iRKcCrit_eq_corr htag1 (ne_of_lt hIJ)]
  obtain ⟨hpfresh, hΓfresh⟩ :=
    zfresh_critReductCorr_freshness (zDerivation_zK_inv hZ).1 hfresh hi hdi hpwff
  exact ZDerivation_iRcritG_critReductCorr hZ hi hj hIJ hdi hdj hfresh_eig hpfresh hΓfresh
    hCwff hSeqs hSeqsj hsj hthread hrank hrankI

/-- **The re-keyed critical reduct `iRKcCrit` is SOUND — ¬-case** (the `ZDerivation_iRKcCrit_all` twin for
an `I¬` R-redex, `zTag dᵢ = 2 ≠ 1`). No freshness is involved: the §3.2-case-5.1 ¬-reduct is the red-free
`I¬` child `zInegPrem dᵢ = d0` plus the §5 `axNeg` axiom `Ax^1_{Γⱼ→A}` (succedent SET). Delegates to the
PROVEN `ZDerivation_iRcritGNeg_critReductNeg` through `iRKcCrit_eq_neg`. Together with
`ZDerivation_iRKcCrit_all` this covers both polarities of the engine swap's `ZDerivation_red_zK_crit`
re-proof; the bundle is the non-freshness chain-validity plumbing (`hcut`/`hd0ant`/`hSeqs`/`hSeqsi`/
threading/rank), all derivable from `isChainInf` (`PENDING_WORK` lap-128 step 2). -/
theorem ZDerivation_iRKcCrit_neg {s r ds sᵢ sⱼ p d0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hj : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p)
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hthread : ∀ i' ≤ redexJ (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexJ (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r) :
    ZDerivation (iRKcCrit (zK s r ds)) := by
  have htag2 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) ≠ 1 := by
    rw [zKseq_zK, hdi, zTag_zIneg]; simp
  rw [iRKcCrit_eq_neg htag2 (ne_of_lt hIJ)]
  exact ZDerivation_iRcritGNeg_critReductNeg hZ hi hj hIJ hdi hdj hcut hd0ant
    hCwff hSeqs hSeqsi hthread hrank hrankI

/-- **The re-keyed critical reduct `iRKcCrit` is SOUND — ¬-case, ⊥-orbit TIP form (lap 144).** The
`_botOrbit` twin of `ZDerivation_iRKcCrit_neg`: consumes the `chainInf_redexI_data` tip `j0` directly
(threading/rank up to `j0`, `⊥`-exit `hbot`, `redexI < j0`), so it is **`redexJ ≤ j0`-FREE** — the lone
obstruction that kept the critical ¬-case open (`PENDING_WORK` lap-142). Rewrites `iRKcCrit_eq_neg` then
feeds the concrete `critReductNeg` reduct to `ZDerivation_iRcritGNeg_corrected_neg_botOrbit`. With this the
¬-case joins the ∀-case (`ZDerivation_iRKcCrit_critical_all`) OFF `red`'s false soundness. -/
theorem ZDerivation_iRKcCrit_neg_botOrbit {s r ds j0 sᵢ sⱼ p d0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hi : redexI (zK s r ds) < lh ds)
    (hj : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p)
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hIj0 : redexI (zK s r ds) < j0) (hj0 : j0 < lh ds)
    (hbot : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i' ≤ j0, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank0 : ∀ i' < j0, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (iRKcCrit (zK s r ds)) := by
  have htag2 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) ≠ 1 := by
    rw [zKseq_zK, hdi, zTag_zIneg]; simp
  rw [iRKcCrit_eq_neg htag2 (ne_of_lt hIJ)]
  refine ZDerivation_iRcritGNeg_corrected_neg_botOrbit (sᵢ := sᵢ) (sⱼ := sⱼ) (p := p) (d0 := d0)
    hZ hi hj hIJ hdi hdj ?_ ?_ hcut hd0ant hCwff hSeqs hSeqsi hIj0 hj0 hbot hthread0 hrank0
  · rw [critReductNeg_redexI (ne_of_lt hIJ), zKseq_zK, hdi, zInegPrem_zIneg]
  · rw [critReductNeg_redexJ, zKseq_zK, hdj, fstIdx_zAxNeg, hcut]

/-- **The re-keyed critical reduct is SOUND from `zKValid` — BOTH polarities consolidated.** Discharges the
redex-structural inputs (`hi`/`hj`/`hIJ`/`hdi`/`hdj` + the polarity dispatch) from the chain's own validity
via `redZKReady_of_zKValid`, leaving only the genuine residual plumbing: the cut/conclusion well-formedness
(`hCwff`/`hSeqs`), the `redexJ`-bounded threading/rank (`hthread`/`hrank` — the UNIFORM bound that matches
`isChainInf`'s tip data and restricts to each case's per-redex bound by `redexI < redexJ`), and the per-node
side-data bundles `hAll`/`hNeg` (the freshness-free orbit invariants, conditioned on the node shape so the
caller proves only the branch that fires). The ∀-branch's freshness is self-supplied from the orbit `ZFresh`
(through `ZDerivation_iRKcCrit_all`). **This IS `ZDerivation_red_zK_crit` modulo only the engine swap**
(`red_zK_crit ↦ iRKcCrit`): once `red`'s tag-4 critical branch emits `iRKcCrit`, the sorry'd
`ZDerivation_red_zK_crit` is this lemma fed the orbit bundle. -/
theorem ZDerivation_iRKcCrit_of_zKValid {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hvalid : zKValid s r ds)
    (hfresh : ZFresh (zK s r ds))
    (hZSeq : ZSeqAnt (zK s r ds))
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s))
    (hthread : ∀ i' ≤ redexJ (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexJ (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hAll : ∀ sᵢ sⱼ a p pj k' d0,
        znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0 →
        znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k' →
        maxEigen d0 < a ∧ IsUFormula ℒₒᵣ p ∧ seqSucc sⱼ = cutFormula (zK s r ds)) :
    ZDerivation (iRKcCrit (zK s r ds)) := by
  obtain ⟨hIJ, hJlt, hcase⟩ := redZKReady_of_zKValid hZ hvalid
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  -- The `Seq (seqAnt sⱼ)` fact the ∀-half needs is DERIVED from the orbit's `ZSeqAnt` invariant
  -- (`seq_seqAnt_zK_premise`); the I¬-half's antecedent shape + `Seq` are read straight off the redex
  -- premise by `zDerivation_zIneg_inv` (the lap-134 `zInegAntWff` strengthening) — so `hNeg` is GONE.
  have hds : Seq ds := (zDerivation_zK_inv hZ).1
  have hmem : ∀ i < lh ds, ZDerivation (znth ds i) := (zDerivation_zK_inv hZ).2
  rcases hcase with ⟨sᵢ, sⱼ, a, p, pj, k', d0, hdi, hdj, _hirk, _hsj⟩ |
    ⟨sᵢ, sⱼ, p, d0, hdi, hdj, hcut, _hpUf⟩
  · obtain ⟨heig, hpwff, hsj⟩ := hAll sᵢ sⱼ a p pj k' d0 hdi hdj
    have hSeqsj : Seq (seqAnt sⱼ) := by
      have h := seq_seqAnt_zK_premise hds hZSeq hJlt (hmem _ hJlt) (by rw [hdj]; simp)
      rwa [hdj, fstIdx_zAxAll] at h
    exact ZDerivation_iRKcCrit_all hZ hIlt hJlt hIJ hdi hdj heig hfresh hpwff hCwff hSeqs hSeqsj hsj
      (fun i' hi' => hthread i' (le_trans hi' (le_of_lt hIJ)))
      (fun i' hi' => hrank i' (lt_trans hi' hIJ))
      (hrank _ hIJ)
  · have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ hmem _ hIlt
    obtain ⟨_, _, _, hSeqsi, hd0ant⟩ := zDerivation_zIneg_inv hZdi
    exact ZDerivation_iRKcCrit_neg hZ hIlt hJlt hIJ hdi hdj hcut hd0ant hCwff hSeqs hSeqsi
      hthread hrank (hrank _ hIJ)

/-- **Soundness of the re-keyed reduct from the `isChainInf` TIP data** — the natural interface the chain
construction supplies. `isChainInf` carries its threading/rank bounded by the distinguished tip `j0` (the
premise holding the conclusion succedent); this restricts that tip-bounded data down to the `redexJ` bound
`ZDerivation_iRKcCrit_of_zKValid` consumes, GIVEN the single structural bound `redexJ ≤ j0` (the redex pair
lies at/below the tip). That bound is the lone remaining structural obligation of the soundness front (it is
free when the chain carries the last-premise tip `j0 = lh ds − 1`, `isChainInf_of_last`). The per-node
bundle `hAll`/`hNeg` is unchanged (those facts route through the same tip-threading — see `PENDING_WORK`
lap-128 late). -/
theorem ZDerivation_iRKcCrit_of_isChainInf {s r ds j0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hvalid : zKValid s r ds)
    (hfresh : ZFresh (zK s r ds))
    (hZSeq : ZSeqAnt (zK s r ds))
    (hJj0 : redexJ (zK s r ds) ≤ j0)
    (hthread0 : ∀ i' ≤ j0, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank0 : ∀ i' < j0, irk (chainAsucc ds i') ≤ r)
    (hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)))
    (hSeqs : Seq (seqAnt s))
    (hAll : ∀ sᵢ sⱼ a p pj k' d0,
        znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0 →
        znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k' →
        maxEigen d0 < a ∧ IsUFormula ℒₒᵣ p ∧ seqSucc sⱼ = cutFormula (zK s r ds)) :
    ZDerivation (iRKcCrit (zK s r ds)) :=
  ZDerivation_iRKcCrit_of_zKValid hZ hvalid hfresh hZSeq hCwff hSeqs
    (fun i' hi' => hthread0 i' (le_trans hi' hJj0))
    (fun i' hi' => hrank0 i' (lt_of_lt_of_le hi' hJj0))
    hAll

/-- **⊥-orbit specialization of the re-keyed critical reduct's soundness** (lap 130). On a `∅→⊥` chain the
two "ambient" plumbing inputs to `ZDerivation_iRKcCrit_of_zKValid` are now FREE: `hCwff` is
`cutFormula_wff_of_zKValid` (`InternalZ.lean`, the cut formula is always well-formed), and `hSeqs` is
`seq_empty` (the conclusion antecedent `seqAnt s = ∅` is trivially a `Seq`). So the residual surface of the
LEFT-soundness front is reduced to exactly the **per-node bundle** `hAll`/`hNeg` and the **threading/rank**
`hthread`/`hrank`. ⚠️ The per-node facts `hAll`'s `seqSucc sⱼ = cutFormula` (the ∀-axiom succedent IS the
cut instance `F(k)`) and `hNeg`'s `seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p` (the I¬ premise antecedent
is exactly `Γ,p`) are EXACT-SHAPE equalities that the current loose `zAxAll`/`zIneg` `ZPhi` disjuncts (which
carry only `inAnt`/membership) do NOT supply — the precise remaining obstruction (fix: strengthen those
disjuncts to the genuine axiom/rule shapes, mirroring the lap-118 `zAxNeg` `A∈Γ` strengthening). -/
theorem ZDerivation_iRKcCrit_botOrbit {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hvalid : zKValid s r ds)
    (hfresh : ZFresh (zK s r ds))
    (hZSeq : ZSeqAnt (zK s r ds))
    (hant : seqAnt s = (∅ : V))
    (hthread : ∀ i' ≤ redexJ (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < redexJ (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hAll : ∀ sᵢ sⱼ a p pj k' d0,
        znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0 →
        znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k' →
        maxEigen d0 < a ∧ IsUFormula ℒₒᵣ p ∧ seqSucc sⱼ = cutFormula (zK s r ds)) :
    ZDerivation (iRKcCrit (zK s r ds)) :=
  ZDerivation_iRKcCrit_of_zKValid hZ hvalid hfresh hZSeq
    (cutFormula_wff_of_zKValid hZ hvalid)
    (by rw [hant]; exact seq_empty)
    hthread hrank hAll

/-- **5.1 critical sub-residual — THE cut-elimination prize.** When the chain is critical, `red = iRcritG
d ρ` with `ρ` the recursive premise reducts; delegates to `ZDerivation_iRcritG_of`, which reduces it to the
two stripped half-derivations `haux0` (`Γ → cutFormula d`) / `haux1` (Buchholz Thm 3.4(a) inversion).

⚠️⚠️ **LAP-114 CRUX FINDING — this is FALSE for `ρ = zAxReduct ∘ red`; `red`'s critical reduct is unsound.**
`haux0`'s threading (`isChainInf`) forces its R-redex premise to derive exactly `cutFormula d = F(k)` with
`k` the L-redex (axAll) instance (`cutFormula_all`). But for an I∀ R-redex `red` gives `zAxReduct (red
premise) = zsubst d0 a (numeral 0)` — instance **0**, not `k` (`red_zIall`). Instance-0 is correct for the
ordinal DESCENT (`iord (zsubst d0 a n)` is instance-invariant — why `iord_descent_red` survives) but WRONG
for SOUNDNESS. **The fix is re-principalization at `k`** (Buchholz §3.2 case 5.1): the R-redex premise must
be `zsubst d0 a (numeral k)`, whose succedent `= cutFormula d` by `seqSucc_zsubst_zIall_premise` (banked,
`Zsubst.lean`), and which is a `ZDerivation` by `ZDerivation_zsubst_zIall_premise`. So the inversion is NOT
a multi-year wall — it is a contained `red`-redefinition (re-key the tag-4 critical branch of `iRNextG` to
substitute the L-redex instance), with the building blocks already in `src/`. The descent (laps 108-113)
survives the 0→k change. See `PENDING_WORK` lap-114 + `ANALYSIS-2026-06-25-lap114-inversion-instance-mismatch.md`.

(Statement kept at the current `ρ` to document the gap honestly; the corrected reduct is the next lap's work.) -/
theorem ZDerivation_red_zK_crit {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (h1 : ¬ permIdx (zK s r ds) < lh ds) :
    ZDerivation (iRcritG (zK s r ds) (fun n => zAxReduct (red (znth ds n)))) := sorry

/-- **`tp` is `Rep` off the I/Ax tags.** `tp d = isymRep` whenever `zTag d ∉ {1,2,5,6}` (i.e. `d` is an
atom/Ind/chain). -/
theorem tp_eq_isymRep_of_zTag {d : V}
    (h : zTag d ≠ 1 ∧ zTag d ≠ 2 ∧ zTag d ≠ 5 ∧ zTag d ≠ 6) : tp d = isymRep := by
  unfold tp; rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2]

/-- **The chain-`Rep` `tp` facts are FREE (lap 100).** For a chain node `d` (`zTag d = 4`), both `tp d` and
`tp (red d)` are `isymRep` UNCONDITIONALLY: `tp` of any chain is `Rep` (`tp_eq_isymRep_of_zTag` off the
I/Ax tags), and `red` of a chain is again a chain (`red (zK …) = iRK …`, `zTag_iRK = 4`), so its `tp` is
`Rep` too. This discharges two of the three `redZKReady` chain-`Rep` conjuncts — the genuine residual is the
conclusion-preservation `fstIdx (red d) = fstIdx d` (route-B Rep-reduction, hereditary). The strengthened
`redSound` motive uses this to supply `redZKReady`'s `hchainRep` from just the `fstIdx` tracking. -/
theorem tp_red_isymRep_of_zTag_4 {d : V} (hZ : ZDerivation d) (htag : zTag d = 4) :
    tp d = isymRep ∧ tp (red d) = isymRep := by
  refine ⟨tp_eq_isymRep_of_zTag ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [htag]; simp
  · rw [htag]; simp
  · rw [htag]; simp
  · rw [htag]; simp
  · rcases zDerivation_iff.mp hZ with ⟨s', heq, _⟩ | ⟨s', a, p, d0, heq, _, _, _⟩ |
      ⟨s', p, d0, heq, _, _, _⟩ | ⟨s', at', p, d0, d1, heq, _, _, _⟩ | ⟨s', r', ds', heq, _, _, _⟩ |
      ⟨s', p, k, heq, _, _⟩ | ⟨s', p, heq, _, _⟩ | ⟨s', C, heq, _⟩
    · exact absurd (heq ▸ htag) (by rw [zTag_zAtom]; simp)
    · exact absurd (heq ▸ htag) (by rw [zTag_zIall]; simp)
    · exact absurd (heq ▸ htag) (by rw [zTag_zIneg]; simp)
    · exact absurd (heq ▸ htag) (by rw [zTag_zInd]; simp)
    · rw [heq, red_zK]; exact tp_eq_isymRep_of_zTag (by rw [zTag_iRK]; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp)
    · exact absurd (heq ▸ htag) (by rw [zTag_zAxAll]; simp)
    · exact absurd (heq ▸ htag) (by rw [zTag_zAxNeg]; simp)
    · exact absurd (heq ▸ htag) (by rw [zTag_zAx1]; simp)

/-- **`red` of a `Rep` derivation preserves the endsequent and stays `Rep`.** For `tp v = isymRep`
(i.e. `v` an atom/Ind/chain), Buchholz's `tp(v) = Rep ⟹ v[0] ⊢ end(v)`: `red v` keeps `fstIdx` and is
again a `Rep` derivation. **Route B (lap 96):** for the chain case the conclusion-reducing `iRKr` keeps
`Π` only when the selected premise is `Rep`, supplied by `hsel` (vacuous for atom/Ind; on the ⊥-orbit it
holds by Cor 2.1). This is the local faithfulness fact behind case 5.2.2 keeping the conclusion `Π`. -/
theorem red_rep_of_tp_isymRep {v : V} (hZ : ZDerivation v) (htp : tp v = isymRep)
    (hsel : zTag v = 4 → permIdx v < lh (zKseq v) →
      tp (znth (zKseq v) (permIdx v)) = isymRep) :
    fstIdx (red v) = fstIdx v ∧ tp (red v) = isymRep := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · exact ⟨by rw [red_zAtom], by rw [red_zAtom, tp_zAtom]⟩
  · exact absurd htp (by rw [tp_zIall]; exact isymR_ne_isymRep _)
  · exact absurd htp (by rw [tp_zIneg]; exact isymR_ne_isymRep _)
  · refine ⟨by rw [red_zInd, iRInd_zInd, fstIdx_zK, fstIdx_zInd], ?_⟩
    rw [red_zInd, iRInd_zInd, tp_zK]
  · refine ⟨?_, ?_⟩
    · rw [red_zK]; exact fstIdx_iRK_of_Rep (fun h1 _ => hsel (by simp) h1)
    · rw [red_zK]
      exact tp_eq_isymRep_of_zTag (by rw [zTag_iRK]; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp)
  · exact absurd htp (by rw [tp_zAxAll]; exact isymLk_ne_isymRep _ _)
  · exact absurd htp (by rw [tp_zAxNeg]; exact isymLk_ne_isymRep _ _)
  · exact ⟨by rw [red_zAx1], by rw [red_zAx1, tp_zAx1]⟩

/-- From `tp v = isymRep`, the I/Ax tags are excluded. -/
theorem zTag_not_iAx_of_tp_isymRep {v : V} (h : tp v = isymRep) :
    zTag v ≠ 1 ∧ zTag v ≠ 2 ∧ zTag v ≠ 5 ∧ zTag v ≠ 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro ht <;> simp only [tp, ht] at h <;> simp at h

-- (`tp_isymRep_of_emptyAnt_botSucc` — Buchholz Cor 2.1 — was promoted to `InternalZ` this lap, where
-- the route-B `fstIdx_red_of_emptyAnt_botSucc` consumes it; the duplicate copy is removed.)

/-- **5.2.2 replace sub-residual — PROVED for a `Rep` selected premise whose own reduct keeps its
endsequent.** Route B (lap 96): `red (zK s r ds)` now emits the reduced conclusion `tpReduce (tp dᵢ) Π 0`;
for a `Rep` selected premise (`htp`) `tpReduce` is the identity, so the goal collapses to the keep-`Π`
`iCritAux` form. Validity then needs `red dᵢ` to keep `dᵢ`'s endsequent and own-permissibility
(`hredfst`/`hredtp` — the route-B conclusion-tracking IH, `red_rep_of_tp_isymRep` instantiated for `dᵢ`),
so `ZDerivation_iCritAux_of` applies. `hredfst`/`hredtp` are the route-B invariant supplied by the
`redSoundF` induction; on the ⊥-orbit they hold hereditarily by Cor 2.1. -/
theorem ZDerivation_red_zK_replace {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (h1 : permIdx (zK s r ds) < lh ds)
    (htp : tp (znth ds (permIdx (zK s r ds))) = isymRep)
    (hredfst : fstIdx (red (znth ds (permIdx (zK s r ds)))) = fstIdx (znth ds (permIdx (zK s r ds))))
    (hredtp : tp (red (znth ds (permIdx (zK s r ds)))) = isymRep) :
    ZDerivation (zK (tpReduce (tp (znth ds (permIdx (zK s r ds)))) s 0) r
      (seqUpdate ds (permIdx (zK s r ds)) (red (znth ds (permIdx (zK s r ds)))))) := by
  set i := permIdx (zK s r ds) with hi_def
  rw [htp, tpReduce_isymRep]
  have hgoal : zK s r (seqUpdate ds i (red (znth ds i)))
      = iCritAux (zK s r ds) i (red (znth ds i)) := by rw [iCritAux_zK]
  rw [hgoal]
  obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
  have hZv : ZDerivation (red (znth ds i)) := hred i h1
  obtain ⟨hne1, hne2, hne5, hne6⟩ := zTag_not_iAx_of_tp_isymRep hredtp
  exact ZDerivation_iCritAux_of h1 hZ hZv hredfst
    (by rw [hredtp]; exact iperm_isymRep _)
    (fun h => absurd h hne1) (fun h => absurd h hne2)
    (fun h => absurd h hne5) (fun h => absurd h hne6)

/-- **5.2.1 splice sub-residual. ⚠ FALSE as stated** (lap-90 finding): needs `tp dᵢ = isymRep` AND `dᵢ`
critical (so `red dᵢ = iRcritG dᵢ …` genuinely has the two reduct-halves `znth (zKseq (red dᵢ)) {0,1}`).
For a non-`Rep` `dᵢ` the halves are junk. Holds on the ⊥-orbit. Delegates (under the restriction) to
`ZDerivation_seqInsert_of_zK` with the spliced `isChainInf` at rank `max(rk(A), r)`. -/
theorem ZDerivation_red_zK_splice {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds))))) :
    ZDerivation (zK s
        (max (irk (seqSucc (fstIdx
          (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))) r)
        (seqInsert ds (permIdx (zK s r ds))
          (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)
          (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1))) := sorry

/-- **I∀ non-`Rep` replace — FULLY ASSEMBLED modulo the orbit invariants (lap 99).** The capstone proving
the validity infrastructure SUFFICES for the hardest non-`Rep` case: when the selected premise `dᵢ = znth ds
i` is an I∀ node (`zIall sᵢ a p d0`), the genuine reduct `red dᵢ = zsubst d0 a 0` (deriving `Γ→F(0)`) feeds
`ZDerivation_iCritReplaceReduce_of` to produce the conclusion-reduced chain `zK (tpReduce (tp dᵢ) s 0) r
(seqUpdate ds i (red dᵢ))`. EVERYTHING is discharged from banked lemmas — `red_zIall_tpReduce` (the I∀
conclusion-tracking, needs the O3 freshness `hpfresh`/`hΓfresh`), `iperm_tp_fstIdx_of_ZDerivation` +
`tag_uformula_of_ZDerivation` (the reduct's own well-formedness), `seqAnt_seqSetSucc`/`seqSucc_seqSetSucc`.
The ONLY un-discharged inputs are the genuine orbit data: O3 freshness (`hpfresh`/`hΓfresh`), the threading/
rank up to `i` (`hthread`/`hrank`, from `permIdx ≤ j₀`), and the reduced succedent well-formedness
(`hsucc_wff`) — exactly what the strengthened `redSoundGen` motive must supply (PENDING_WORK lap-99 path A).
This DE-RISKS the entire non-`Rep` route: the I∀ case is mechanically complete given the invariants. -/
theorem ZDerivation_zK_replace_zIall_of {s r ds i sᵢ a p d0 : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds)
    (hdi : znth ds i = zIall sᵢ a p d0)
    (hZred : ZDerivation (red (zIall sᵢ a p d0)))
    (hpfresh : fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral 0) p = p)
    (hΓfresh : fvSubstSeq a (Bootstrapping.Arithmetic.numeral 0) (seqAnt sᵢ) = seqAnt sᵢ)
    (hsucc_wff : IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) p))
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (tpReduce (tp (znth ds i)) s 0) r (seqUpdate ds i (red (znth ds i)))) := by
  have hZdi : ZDerivation (zIall sᵢ a p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 i hi
  have htrack : fstIdx (red (zIall sᵢ a p d0))
      = seqSetSucc sᵢ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) p) := by
    rw [red_zIall_tpReduce hZdi hpfresh hΓfresh, tp_zIall, fstIdx_zIall, tpReduce_isymR_all]
  have hchain_i : chainAnt ds i = seqAnt sᵢ := by
    unfold chainAnt; rw [hdi, fstIdx_zIall]
  rw [hdi, tp_zIall, tpReduce_isymR_all]
  refine ZDerivation_iCritReplaceReduce_of hi hZ hZred ?_ ?_ ?_ hthread hrank ?_ ?_ ?_ ?_ ?_ ?_
  · rw [htrack, seqAnt_seqSetSucc, ← hchain_i]
  · rw [htrack, seqSucc_seqSetSucc, seqSucc_seqSetSucc]
  · rw [seqAnt_seqSetSucc]
  · rw [seqSucc_seqSetSucc]; exact hsucc_wff
  · exact iperm_tp_fstIdx_of_ZDerivation hZred
  · exact (tag_uformula_of_ZDerivation hZred).1
  · exact (tag_uformula_of_ZDerivation hZred).2.1
  · exact (tag_uformula_of_ZDerivation hZred).2.2.1
  · exact (tag_uformula_of_ZDerivation hZred).2.2.2

/-- **I¬ non-`Rep` replace — FULLY ASSEMBLED modulo the orbit invariants (lap 100).** The I¬ analogue of
`ZDerivation_zK_replace_zIall_of`: when the selected premise `dᵢ = zIneg sᵢ p d0` is an I¬ node, the
genuine reduct `red dᵢ = d0` (Buchholz Def 3.2 clause 3 — `d[0] := d₀`, **no** substitution, unlike I∀)
derives `p,Γ→⊥`, which IS the reduced sequent `tpReduce (R_¬p) Π 0 = p,Γ→⊥` (antecedent gains the cut
formula `p`, succedent → `⊥`). It feeds the unifying `ZDerivation_iCritReplaceReduce_general` (membership-
form `isChainInf`, since here the antecedent GROWS rather than being kept) to produce the conclusion-reduced
chain `zK (tpReduce (tp dᵢ) s 0) r (seqUpdate ds i (red dᵢ))`. EVERYTHING is discharged from banked lemmas
(`isChainInf_reduceR_membership`, `inAnt_seqAddAnt`, `forall_IsUFormula_seqCons`,
`iperm_tp_fstIdx_of_ZDerivation` + `tag_uformula_of_ZDerivation` for the reduct's wff). The ONLY
un-discharged inputs are the genuine orbit data: the faithful premise-antecedent `hd0ant`
(`seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p` — the I¬ analogue of I∀'s O3 freshness; `zInegWff` pins only
`p ∈ antecedent`), the conclusion `Seq`-wellformedness (`hSeqs`/`hSeqsi`), and the threading/rank up to `i`
(`hthread`/`hrank`, from `permIdx ≤ j₀`) — exactly what the strengthened `redSoundGen` motive must supply.
This DE-RISKS the I¬ branch: it is mechanically complete given the invariants. -/
theorem ZDerivation_zK_replace_zIneg_of {s r ds i sᵢ p d0 : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds)
    (hdi : znth ds i = zIneg sᵢ p d0)
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (tpReduce (tp (znth ds i)) s 0) r (seqUpdate ds i (red (znth ds i)))) := by
  have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 i hi
  obtain ⟨hZd0, _hsucceq, ⟨hbot, hmem, hp⟩, _, _⟩ := zDerivation_zIneg_inv hZdi
  have hSeqs' : Seq (seqAnt (seqSetSucc s (^⊥ : V))) := by rw [seqAnt_seqSetSucc]; exact hSeqs
  have hchain_i : chainAnt ds i = seqAnt sᵢ := by unfold chainAnt; rw [hdi, fstIdx_zIneg]
  -- conclusion-antecedent wff of the parent chain (`zKValidF` field 9)
  obtain ⟨-, -, -, -, -, -, -, -, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  rw [hdi, tp_zIneg, tpReduce_isymR_neg p s 0 hp, red_zIneg]
  refine ZDerivation_iCritReplaceReduce_general hi hZ hZd0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the membership-form `isChainInf` for the reduced conclusion `p,Γ→⊥`
    refine isChainInf_reduceR_membership hi (Or.inr hbot) ?_ ?_ hrank
    · -- at-`i` antecedent threading: `B ∈ seqAnt (fstIdx d0) = (seqAnt sᵢ),p`
      intro B hB
      rw [hd0ant] at hB
      rcases (inAnt_seqCons hSeqsi).mp hB with rfl | hBin
      · left; exact (inAnt_seqAddAnt hSeqs').mpr (Or.inl rfl)
      · rcases hthread i le_rfl B (by rw [hchain_i]; exact hBin) with hins | hex
        · left; exact (inAnt_seqAddAnt hSeqs').mpr (Or.inr (by rw [seqAnt_seqSetSucc]; exact hins))
        · right; exact hex
    · -- below-`i` antecedent threading inherits, weakened through the new antecedent
      intro i' hi' B hB
      rcases hthread i' (le_of_lt hi') B hB with hins | hex
      · left; exact (inAnt_seqAddAnt hSeqs').mpr (Or.inr (by rw [seqAnt_seqSetSucc]; exact hins))
      · right; exact hex
  · -- conclusion succedent wff: `⊥`
    rw [seqSucc_seqAddAnt, seqSucc_seqSetSucc]; simp
  · -- conclusion antecedent wff: `(seqAnt s),p`, each entry a `UFormula`
    rw [seqAnt_seqAddAnt, seqAnt_seqSetSucc]
    exact forall_IsUFormula_seqCons hSeqs hsa hp
  · -- reduct succedent wff: `⊥`
    rw [hbot]; simp
  · exact iperm_tp_fstIdx_of_ZDerivation hZd0
  · exact (tag_uformula_of_ZDerivation hZd0).1
  · exact (tag_uformula_of_ZDerivation hZd0).2.1
  · exact (tag_uformula_of_ZDerivation hZd0).2.2.1
  · exact (tag_uformula_of_ZDerivation hZd0).2.2.2

/-- **axAll non-`Rep` replace — FULLY ASSEMBLED modulo the orbit invariants (lap 100).** The §5-∀-axiom
analogue, and the **cleanest** of the four: when the selected premise `dᵢ = zAxAll sᵢ p k` is a §5 left
∀-axiom, the reduct is the IDENTITY (`red dᵢ = dᵢ`, Buchholz Def 3.2 case 5.2.2 axiom case — no premise
change), so `seqUpdate ds i (red dᵢ) = ds`, and the conclusion gains the cut-formula instance `F(k) =
substs1 (numeral k) p` in its ANTECEDENT (`tpReduce (L^k_{∀p}) Π 0 = F(k),Γ→D`). The validity is pure
conclusion-antecedent monotonicity (`ZDerivation_zK_seqAddAnt`) — the threading only RELAXES, so **no
`i ≤ j₀` threading datum is needed** (unlike I∀/I¬). The only un-discharged inputs are the conclusion
`Seq`-wellformedness (`hSeqs`) and the cut-instance formula-hood (`hAwff`, the orbit/wff datum the
strengthened `redSoundGen` motive supplies). -/
theorem ZDerivation_zK_replace_zAxAll_of {s r ds i sᵢ p k : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds)
    (hdi : znth ds i = zAxAll sᵢ p k)
    (hSeqs : Seq (seqAnt s))
    (hAwff : IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p)) :
    ZDerivation (zK (tpReduce (tp (znth ds i)) s 0) r (seqUpdate ds i (red (znth ds i)))) := by
  have hds : Seq ds := (zDerivation_zK_inv hZ).1
  have hred_eq : red (znth ds i) = znth ds i := by rw [hdi, red_zAxAll]
  have htp_eq : tpReduce (tp (znth ds i)) s 0
      = seqAddAnt (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p) s := by
    rw [hdi, tp_zAxAll, tpReduce_isymLk_all]
  rw [hred_eq, seqUpdate_znth_self hds hi, htp_eq]
  exact ZDerivation_zK_seqAddAnt hZ hSeqs hAwff

/-- **The ⊥-orbit "reduce-ready" obligation for a chain (the consolidated motive residual, lap 100).**
Bundles EXACTLY the orbit-invariant data the two `ZDerivation_red_zK` replace branches need at the selected
premise `dᵢ = znth ds (permIdx)`: (a) the chain-`Rep` conclusion-tracking (`tp dᵢ = Rep` ∧ `red dᵢ` keeps
`fstIdx`/stays `Rep`) for a non-critical chain `dᵢ` (⊥-orbit Cor 2.1); (b) the conclusion `Seq`-wff; (c) the
selection-bounded threading/rank (`permIdx ≤ j₀`); (d) the per-tag freshness/faithful-antecedent/wff for an
I∀/I¬/axAll `dᵢ`. This is the SINGLE obligation the strengthened `redSoundGen` motive must produce per chain
node; with it, `ZDerivation_red_zK` is fully assembled (modulo the lone axNeg residual in
`ZDerivation_red_zK_nonRep`). -/
def redZKReady (s r ds : V) : Prop :=
  ( permIdx (zK s r ds) < lh ds → zTag (znth ds (permIdx (zK s r ds))) = 4 →
      permIdx (znth ds (permIdx (zK s r ds))) < lh (zKseq (znth ds (permIdx (zK s r ds)))) →
      tp (znth ds (permIdx (zK s r ds))) = isymRep ∧
      fstIdx (red (znth ds (permIdx (zK s r ds)))) = fstIdx (znth ds (permIdx (zK s r ds))) ∧
      tp (red (znth ds (permIdx (zK s r ds)))) = isymRep ) ∧
  Seq (seqAnt s) ∧
  ( ∀ i' ≤ permIdx (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
      inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'' ) ∧
  ( ∀ i' < permIdx (zK s r ds), irk (chainAsucc ds i') ≤ r ) ∧
  ( ∀ sᵢ a p d0, znth ds (permIdx (zK s r ds)) = zIall sᵢ a p d0 →
      fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral 0) p = p ∧
      fvSubstSeq a (Bootstrapping.Arithmetic.numeral 0) (seqAnt sᵢ) = seqAnt sᵢ ∧
      IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) p) ) ∧
  ( ∀ sᵢ p d0, znth ds (permIdx (zK s r ds)) = zIneg sᵢ p d0 →
      seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p ∧ Seq (seqAnt sᵢ) ) ∧
  ( ∀ sᵢ p k, znth ds (permIdx (zK s r ds)) = zAxAll sᵢ p k →
      IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p) )

/-- **The non-`Rep` replace dispatch, FULLY ASSEMBLED for 3/4 tags (lap 100).** Routes the non-chain,
non-`Rep` selected premise `dᵢ = znth ds (permIdx)` by its node tag into the matching banked capstone:
`zIall`→`ZDerivation_zK_replace_zIall_of`, `zIneg`→`_zIneg_of`, `zAxAll`→`_zAxAll_of`. The atom/Ind tags
are excluded by `htp` (their `tp = isymRep`), the chain tag by `htag`. The per-tag orbit invariants
(freshness/faithful-antecedent/wff) are supplied as the bundled hypotheses `hIall`/`hIneg`/`hAxAll`
(conditioned on the node shape, so the caller proves only the branch that fires), the conclusion `Seq`-wff
as `hSeqs`, and the selection-bounded threading/rank as `hthread`/`hrank` (from `permIdx_le_of_isPermPrem`
+ `thread_rank_restrict_of_le`). **axNeg (tag 6) is the lone residual** (`sorry`, Path C): its reduct is a
succedent REPLACEMENT (`Γ→p`) with no premise carrying succedent `p`, so the membership-`isChainInf` route
does not apply — it needs Buchholz's genuine ¬-axiom cut (premise restructuring). This lemma DISCHARGES the
non-`Rep` branch of `ZDerivation_red_zK` modulo (a) the orbit-invariant bundle and (b) axNeg. -/
theorem ZDerivation_red_zK_nonRep {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (h1 : permIdx (zK s r ds) < lh ds)
    (htag : zTag (znth ds (permIdx (zK s r ds))) ≠ 4)
    (htp : ¬ tp (znth ds (permIdx (zK s r ds))) = isymRep)
    (hSeqs : Seq (seqAnt s))
    (hthread : ∀ i' ≤ permIdx (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < permIdx (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hIall : ∀ sᵢ a p d0, znth ds (permIdx (zK s r ds)) = zIall sᵢ a p d0 →
        fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral 0) p = p ∧
        fvSubstSeq a (Bootstrapping.Arithmetic.numeral 0) (seqAnt sᵢ) = seqAnt sᵢ ∧
        IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) p))
    (hIneg : ∀ sᵢ p d0, znth ds (permIdx (zK s r ds)) = zIneg sᵢ p d0 →
        seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p ∧ Seq (seqAnt sᵢ))
    (hAxAll : ∀ sᵢ p k, znth ds (permIdx (zK s r ds)) = zAxAll sᵢ p k →
        IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p)) :
    ZDerivation (zK (tpReduce (tp (znth ds (permIdx (zK s r ds)))) s 0) r
      (seqUpdate ds (permIdx (zK s r ds)) (red (znth ds (permIdx (zK s r ds)))))) := by
  have hdiZ : ZDerivation (znth ds (permIdx (zK s r ds))) := (zDerivation_zK_inv hZ).2 _ h1
  rcases zDerivation_iff.mp hdiZ with ⟨s', heq, _⟩ | ⟨s', a, p, d0, heq, _, _, _⟩ |
    ⟨s', p, d0, heq, _, _, _⟩ | ⟨s', at', p, d0, d1, heq, _, _, _⟩ | ⟨s', r', ds', heq, _, _, _⟩ |
    ⟨s', p, k, heq, _, _⟩ | ⟨s', p, heq, _, _⟩ | ⟨s', C, heq, _⟩
  · exact absurd (by rw [heq]; exact tp_zAtom s') htp
  · obtain ⟨hpfresh, hΓfresh, hsucc_wff⟩ := hIall s' a p d0 heq
    exact ZDerivation_zK_replace_zIall_of hZ h1 heq (heq ▸ hred _ h1)
      hpfresh hΓfresh hsucc_wff hthread hrank
  · obtain ⟨hd0ant, hSeqsi⟩ := hIneg s' p d0 heq
    exact ZDerivation_zK_replace_zIneg_of hZ h1 heq hd0ant hSeqs hSeqsi hthread hrank
  · exact absurd (by rw [heq]; exact tp_zInd s' at' p d0 d1) htp
  · exact absurd (by rw [heq, zTag_zK]) htag
  · exact ZDerivation_zK_replace_zAxAll_of hZ h1 heq hSeqs (hAxAll s' p k heq)
  · -- axNeg (Path C residual): succedent-replacement `Γ→p`, needs Buchholz's ¬-axiom cut. OPEN.
    sorry
  · exact absurd (by rw [heq]; exact tp_zAx1 s' C) htp

/-- **Residual (K case of Buchholz Thm 3.4 — the cut-elimination core).** The genuine reduct `red` of a
valid chain `zK s r ds` is again a `ZDerivation`, given that the reduct of every premise is. Dispatches
(via `red_zK_crit` / `red_zK_rep` / `red_zK_splice`) into the three Buchholz case-5 sub-residuals; each
delegates to a banked validity constructor (`ZDerivation_iRcritG_of` / `ZDerivation_iCritAux_of_zK` /
`ZDerivation_seqInsert_of_zK`). -/
theorem ZDerivation_red_zK {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (hready : redZKReady s r ds) :
    ZDerivation (red (zK s r ds)) := by
  obtain ⟨hchainRep, hSeqs, hthread, hrank, hIall, hIneg, hAxAll⟩ := hready
  by_cases h1 : permIdx (zK s r ds) < lh ds
  · -- non-critical chain: dispatch on the GATED `iRK` (lap 95) — first on whether the selected
    -- premise `dᵢ` is a chain (`zTag dᵢ = 4`), then on `dᵢ`'s own criticality
    by_cases htag : zTag (znth ds (permIdx (zK s r ds))) = 4
    · by_cases h2 : permIdx (znth ds (permIdx (zK s r ds)))
          < lh (zKseq (znth ds (permIdx (zK s r ds))))
      · -- chain selected premise, non-critical → 5.2.2 replace (route-B reduced conclusion).
        -- The ⊥-orbit Cor 2.1 conclusion-tracking is supplied by `redZKReady`'s `hchainRep`.
        rw [red_zK_rep h1 h2]
        obtain ⟨htp, hredfst, hredtp⟩ := hchainRep h1 htag h2
        exact ZDerivation_red_zK_replace hZ hred h1 htp hredfst hredtp
      · -- chain selected premise, critical → 5.2.1 splice (`htag` supplies the genuine reduct-halves)
        rw [red_zK_splice h1 h2 htag]
        exact ZDerivation_red_zK_splice hZ hred h1 h2
    · -- NON-chain selected premise → 5.2.2 replace with conclusion-reduction `tpReduce (tp dᵢ) Π n`.
      -- (Lap-95 GATED dispatch — the OLD `iRK` mis-spliced here.) The deep validity residual:
      -- a keep-Π replace is faithful only for `tp = Rep`, so the conclusion must reduce (lap-90).
      rw [red_zK_rep_nonchain h1 htag]
      by_cases htp : tp (znth ds (permIdx (zK s r ds))) = isymRep
      · -- atom / Ind: `tp dᵢ = Rep`, `tpReduce` is the identity, conclusion `Π` KEPT. The premise
        -- reduct keeps its endsequent + stays `Rep` (`red_rep_of_tp_isymRep`, with `hsel` vacuous since
        -- `zTag dᵢ ≠ 4`), so the keep-`Π` `ZDerivation_red_zK_replace` discharges it. (Lap 99.)
        have hdiZ : ZDerivation (znth ds (permIdx (zK s r ds))) := (zDerivation_zK_inv hZ).2 _ h1
        obtain ⟨hredfst, hredtp⟩ := red_rep_of_tp_isymRep hdiZ htp (fun h4 _ => absurd h4 htag)
        exact ZDerivation_red_zK_replace hZ hred h1 htp hredfst hredtp
      · -- I∀ / I¬ / axAll → the three banked capstones; axNeg the lone residual. ALL ASSEMBLED in
        -- `ZDerivation_red_zK_nonRep`, fed the per-tag orbit data from `redZKReady`. (Lap 100.)
        exact ZDerivation_red_zK_nonRep hZ hred h1 htag htp hSeqs hthread hrank hIall hIneg hAxAll
  · -- 5.1 critical
    rw [red_zK_crit h1]
    exact ZDerivation_red_zK_crit hZ hred h1

/-- **`redSound`, general form. ⚠ FALSE IN FULL GENERALITY — scaffold only.** See
`ANALYSIS-2026-06-25-lap90-red-faithful-only-for-rep.md`: the repo's `red` keeps the chain conclusion
`Π` (`fstIdx_iRK = fstIdx d`), so it equals Buchholz's `d[0]` only when `tp(d) = Rep`. For a chain whose
minimal-permissible premise `dᵢ` is an I-rule/axiom (`tp(dᵢ) ≠ Rep`), Buchholz 5.2.2 reduces the
conclusion to `tp(dᵢ)(Π,0) ≠ Π`, so the repo's `red` is unfaithful and `red d` is not a `ZDerivation`.
The TRUE target is `redSound` over `ZDerivesEmpty` (the ⊥-orbit, all-`Rep` by Cor 2.1). The 5 trivial
cases below + `red_zK_rep`/`red_zK_splice` are reusable; the two deep cases are the open frontier. -/
theorem redSoundGen : ∀ d : V, ZDerivation d → ZRegular d → ZDerivation (red d) := by
  have key : ∀ d : V, ZDerivation d → (ZRegular d → ZDerivation (red d)) := by
    apply zDerivation_induction (P := fun d : V => ZRegular d → ZDerivation (red d))
    · definability
    · intro C hC d hphi hreg
      rcases hphi with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, hd0, hsucc, hwff⟩ |
        ⟨s, p, d0, rfl, hd0, hsucc, hwff⟩ |
        ⟨s, at', p, d0, d1, rfl, hd0, hd1, hwff⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
        ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin, hin2⟩ | ⟨s, C, rfl, hin⟩
      · -- zAtom: red = identity
        rw [red_zAtom]; exact zDerivation_iff.mpr (Or.inl ⟨s, rfl, hin⟩)
      · -- zIall: red = zsubst d0 a (numeral 0); regularity ⟹ maxEigen d0 < a ⟹ ZDerivation_zsubst.
        rw [red_zIall]
        rw [ZRegular, zReg_zIall] at hreg
        have hlt : maxEigen d0 < a :=
          ltFlag_eq_zero_iff.mp (nonpos_iff_eq_zero.mp (hreg ▸ le_max_left _ _))
        exact ZDerivation_zsubst (by simp) d0 (hC d0 hd0).1 hlt
      · -- zIneg: red = d0
        rw [red_zIneg]; exact (hC d0 hd0).1
      · -- zInd: red = chain reduct; residual supplies validity
        have hZ : ZDerivation (zInd s at' p d0 d1) := zDerivation_iff.mpr
          (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨s, at', p, d0, d1, rfl, (hC d0 hd0).1, (hC d1 hd1).1, hwff⟩))))
        rw [red_zInd, iRInd_zInd, zDerivation_iff]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, irk p, iIndReductSeq d0 d1 1, rfl, iIndReductSeq_seq d0 d1 1,
            fun i hi => znth_iIndReductSeq_ZDerivation (hC d0 hd0).1 (hC d1 hd1).1 i hi,
            zKValidF_iIndReduct_of_zInd hZ⟩))))
      · -- zK: the dispatch; residual supplies validity-preservation. Premise reducts from the IH,
        -- fed the premise regularity (`ZRegular_zK_premise`) from the chain's own regularity.
        -- THE consolidated motive residual: `redZKReady s r ds` (the per-node ⊥-orbit invariant bundle
        -- — chain-Rep Cor 2.1 + Seq-wff + selection threading + per-tag freshness). To discharge it the
        -- motive must be strengthened to carry these hereditarily (PENDING_WORK lap-100 Path 1/A1). OPEN.
        refine ZDerivation_red_zK
          (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨s, r, ds, rfl, hds, fun i hi => (hC (znth ds i) (hmem i hi)).1, hvalid⟩))))))
          (fun i hi => (hC (znth ds i) (hmem i hi)).2 (ZRegular_zK_premise hds hreg hi)) ?_
        sorry
      · -- zAxAll: red = identity
        rw [red_zAxAll]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨s, p, k, rfl, hp, hin⟩))))))
      · -- zAxNeg: red = identity
        rw [red_zAxNeg]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨s, p, rfl, hp, hin, hin2⟩)))))))
      · -- zAx1: red = identity
        rw [red_zAx1]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr ⟨s, C, rfl, hin⟩)))))))
  exact key

/-- **The regular ⊥-orbit predicate.** Route B threads eigenvariable regularity (`ZRegular`, O1) alongside
`ZDerivesEmpty`: the genuine reduct `red` does the I∀ eigensubst `zsubst d0 a 0`, which is a `ZDerivation`
only when the node is regular (`maxEigen d0 < a`). The embedding (M2) produces a regular derivation; `red`
preserves both (`ZRegular_red` for O1, `fstIdx_red` for the conclusion). -/
def ZDerivesEmptyR (d : V) : Prop := ZDerivesEmpty d ∧ ZRegular d ∧ ZFresh d ∧ ZSeqAnt d

/-- **M1b — THE nut.** The `red`-reduct of a contradiction derivation is again a genuine `ZDerivation`.
(Re-pointed `RedSound`, off the dead `iR2`.) A corollary of `redSoundGen`; the regularity comes from the
regular ⊥-orbit (`ZDerivesEmptyR`). -/
theorem redSound : ∀ d : V, ZDerivesEmptyR d → ZDerivation (red d) :=
  fun d h => redSoundGen d h.1.1 h.2.1

/-- **`iord_descent_red`, Ind case (lap 100).** For an Ind node (`zTag d = 3`), `red d = iRInd d` (a chain
reduct), and the ordinal strictly descends — directly from the banked `iord_descent_iRInd_of_ZDerivation`.
This is the Ind leaf of `iord_descent_red`'s dispatch (the orbit's `d` is only Ind or K — atoms/I-rules/
axioms can't conclude `∅→⊥`). The K case is the deep residual (mirrors `ZDerivation_red_zK`'s dispatch on
the ordinal side: `iord_descent_iCritAux`/`_seqInsert`/`_iRcrit_of_chain`). -/
theorem iord_descent_red_zInd (d : V) (hd : ZDerivation d) (htag : zTag d = 3) :
    icmp (iord (red d)) (iord d) = 0 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp at htag
  · simp at htag
  · simp at htag
  · rw [red_zInd]; exact iord_descent_iRInd_of_ZDerivation _ hd htag
  · simp at htag
  · simp at htag
  · simp at htag
  · simp at htag

/-- **M1b (descent re-point, one step).** The banked ordinal descent, restated over `red`. A `∅→⊥`
derivation has top tag `3` (Ind) or `4` (K/cut) (`zTag_Ind_or_K_of_ZDerivesEmpty`).

**lap-108 narrowing:** the **Ind branch is now PROVEN in place** (via the banked `iord_descent_red_zInd`);
the residual `sorry` is isolated to exactly the **K/cut case** (tag 4), where `red (zK s r ds) = iRK …`
dispatches the three Buchholz Def-3.2 case-5 sub-reducts (5.1 critical `iRcritG` / 5.2.1 splice / 5.2.2
replace, `red_zK_crit`/`_splice`/`_rep`). Only the *critical* sub-reduct's descent is banked
(`iord_descent_iR2_zK_of_valid`, for the `iR2`-ρ — needs re-pointing to the `red`-ρ); the splice/replace
sub-reduct descents are the genuine open ordinal-analysis core. See `STATUS.md` / `PENDING_WORK.md` lap-107. -/
theorem iord_descent_red {d : V} (hd : ZDerivesEmptyR d) :
    red d = d ∨ icmp (iord (red d)) (iord d) = 0 := by
  rcases zTag_Ind_or_K_of_ZDerivesEmpty hd.1 with htag | htag
  · -- Ind (tag 3): `red d = iRInd d`, banked STRICT descent (RIGHT disjunct). PROVEN.
    exact Or.inr (iord_descent_red_zInd d hd.1.1 htag)
  · -- K/cut (tag 4): dispatch on the `permIdx` criticality sentinel.
    rcases zDerivation_iff.mp hd.1.1 with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ |
      ⟨s, p, d0, rfl, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
      ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    · simp at htag
    · simp at htag
    · simp at htag
    · simp at htag
    · -- the genuine K-rule node `zK s r ds`
      have hreg : ∀ i < lh ds, ZRegular (znth ds i) :=
        fun i hi => ZRegular_zK_premise hds hd.2.1 hi
      by_cases hcrit : permIdx (zK s r ds) < lh ds
      · -- NON-critical: `red (zK s r ds) = K^r(i/red dᵢ)` (replace, 5.2.2), `i = permIdx`. Dispatch on the
        -- selected premise's tag and feed the banked premise-IH to `iord_descent_red_zK_replace_eq`.
        -- The I-rule/Ind sub-cases have NON-recursive banked `iRedDescent` bundles (`iRedDescent_zIneg`/
        -- `_zInd`); the chain sub-case needs the strong-induction recursion; atom/axiom sub-cases are the
        -- engine FIXPOINT defect (`red dᵢ = dᵢ` ⟹ no descent, `red_zK_fixpoint_of_atom_selected`, PENDING
        -- lap-109). The I∀ sub-case needs the eigensubst regularity bundle.
        have hdiZ : ZDerivation (znth ds (permIdx (zK s r ds))) := hmem _ hcrit
        rcases zDerivation_iff.mp hdiZ with ⟨s', heq, _⟩ | ⟨s', a', p', d0, heq, hd0, _⟩ |
          ⟨s', p', d0, heq, hd0, _⟩ | ⟨s', at'', p', d0, d1, heq, hd0, hd1, _⟩ |
          ⟨s', r', ds', heq, hds', hmem', hvalid'⟩ | ⟨s', p', k, heq, _, _⟩ | ⟨s', p', heq, _, _⟩ |
          ⟨s', C', heq, _⟩
        · -- atom (tag 0): `red dᵢ = dᵢ` (`zAtom` is `red`-normal, `tp = isymRep`, Rep-reduce is the
          -- identity), so the WHOLE node is a genuine `red`-FIXPOINT. The disjunctive descent closes
          -- on the LEFT — `red_zK_fixpoint_of_atom_selected` (lap 109, banked). No descent needed.
          exact Or.inl (red_zK_fixpoint_of_atom_selected hds hcrit heq)
        · -- I∀ (tag 1): `red dᵢ = zsubst d0 a 0`, banked `iRedDescent_red_zIall` (eigensubst-invariant
          -- ordinal bundle, no regularity needed) — no recursion.
          have htag_ne4 : zTag (znth ds (permIdx (zK s r ds))) ≠ 4 := by rw [heq]; simp
          refine Or.inr (iord_descent_red_zK_replace_eq hds hmem hcrit
            (red_zK_rep_nonchain hcrit htag_ne4) ?_)
          rw [heq]; exact iRedDescent_red_zIall (heq ▸ hdiZ)
        · -- I¬ (tag 2): `red dᵢ = d0`, banked `iRedDescent_zIneg` — no recursion.
          have htag_ne4 : zTag (znth ds (permIdx (zK s r ds))) ≠ 4 := by rw [heq]; simp
          refine Or.inr (iord_descent_red_zK_replace_eq hds hmem hcrit
            (red_zK_rep_nonchain hcrit htag_ne4) ?_)
          rw [heq, red_zIneg]; exact iRedDescent_zIneg (isNF_iotil_of_ZDerivation d0 hd0)
        · -- Ind (tag 3): `red dᵢ = iRInd dᵢ`, banked `iRedDescent_zInd` — no recursion.
          have htag_ne4 : zTag (znth ds (permIdx (zK s r ds))) ≠ 4 := by rw [heq]; simp
          refine Or.inr (iord_descent_red_zK_replace_eq hds hmem hcrit
            (red_zK_rep_nonchain hcrit htag_ne4) ?_)
          rw [heq, red_zInd]
          exact iRedDescent_zInd (isNF_iotil_of_ZDerivation d0 hd0) (isNF_iotil_of_ZDerivation d1 hd1)
        · -- chain (tag 4): the recursive core. Dispatch on `dᵢ`'s OWN criticality; each branch is reduced
          -- to its recursion output by the banked interface wrappers, so the residual `sorry`s are now
          -- EXACTLY the strong-induction IH (replace) / the critical-reduct halves' descent (splice).
          have htag4 : zTag (znth ds (permIdx (zK s r ds))) = 4 := by rw [heq]; exact zTag_zK _ _ _
          by_cases h2 : permIdx (znth ds (permIdx (zK s r ds)))
              < lh (zKseq (znth ds (permIdx (zK s r ds))))
          · -- `dᵢ` non-critical → REPLACE. Disjunctive form: if `dᵢ` is itself a `red`-fixpoint the
            -- whole node is too (LEFT); otherwise the strong-induction premise IH gives strict descent
            -- (RIGHT, wired via `iord_descent_red_zK_chain_replace`). The disjunction is TRUE either
            -- way; residual `sorry` = the IH recursion (the chain-REPLACE strong induction, lap 111+).
            refine Or.inr (iord_descent_red_zK_chain_replace hds hmem hcrit h2 ?_)
            sorry
          · -- `dᵢ` critical → SPLICE; the two halves' `õ`/`idg`/NF bounds are supplied by the banked
            -- `iCrit_halves_descend` (the critical reduct's halves reduce `dᵢ`'s OWN premise sequence at
            -- the redex, so each fold descends below `dᵢ`); only the rank bound `hr'` remains residual.
            have hcrit' : ¬ permIdx (zK s' r' ds') < lh ds' := by
              have h2c := h2; rw [heq, zKseq_zK] at h2c; exact h2c
            have hreg' : ∀ i < lh ds', ZRegular (znth ds' i) := fun i hi =>
              ZRegular_zK_premise hds' (heq ▸ hreg (permIdx (zK s r ds)) hcrit) hi
            have hvalidZ : zKValid s' r' ds' :=
              zKValid_iff_zKValidF_and_zKCritical.mpr ⟨hvalid', zKCritical_of_not_permIdx_lt hcrit'⟩
            have hrankI' : irk (chainAsucc ds' (redexI (zK s' r' ds'))) ≤ r' :=
              irk_chainAsucc_redexI_le hvalidZ
            obtain ⟨ha, hb, hag, hbg, hNFa, hNFb, hrk7⟩ :=
              iCrit_halves_descend hcrit' hds' hmem' hreg' hvalidZ hrankI'
            rw [← heq] at ha hb hag hbg hNFa hNFb hrk7
            refine Or.inr (iord_descent_red_zK_chain_splice hds hmem hcrit h2 htag4 ?_ ha hb hag hbg hNFa hNFb)
            -- `hr'`: `max (irk A(dᵢ)) r ≤ idg (zK s r ds)`. The strict drop `irk A(dᵢ) < r' = zKrank dᵢ`
            -- (`hrk7`) chains: `< r' ≤ idg dᵢ ≤ iseqMaxIdg ds`, so `≤ iseqMaxIdg ds - 1 ≤ idg (zK s r ds)`;
            -- `r ≤ idg (zK s r ds)` directly. All `idg` arithmetic now PROVEN.
            have hr'_le_idgdi : r' ≤ idg (znth ds (permIdx (zK s r ds))) := by
              rw [heq]; exact r_le_idg_zK s' r' ds' hds'
            have hdi_le : idg (znth ds (permIdx (zK s r ds))) ≤ iseqMaxIdg ds :=
              le_iseqMaxIdgAux (lh ds) _ hcrit
            have hinner : irk (seqSucc (fstIdx (znth (zKseq
                (red (znth ds (permIdx (zK s r ds))))) 0))) < idg (znth ds (permIdx (zK s r ds))) :=
              lt_of_lt_of_le hrk7 hr'_le_idgdi
            rw [idg_zK s r ds hds]
            exact max_le
              (le_trans (le_trans (le_pred_of_lt hinner) (tsub_le_tsub_right hdi_le 1))
                (le_max_right _ _))
              (le_max_left _ _)
        · -- axAll (tag 5): VACUOUS in a ⊥-orbit — the SELECTION INVARIANT (lap 111). Cor 2.1
          -- (`tp_selected_isymRep_of_emptyAnt_botSucc`) forces the selected premise of a `∅→⊥` K-node
          -- to have `tp = isymRep`, but an L-axiom has `tp = isymLk ≠ isymRep`. So `permIdx` never
          -- selects a lone axiom L-leaf; this branch cannot occur.
          exfalso
          have hant : seqAnt s = (∅ : V) := by have h := hd.1.2.1; rwa [fstIdx_zK] at h
          have hsucc : seqSucc s = (^⊥ : V) := by have h := hd.1.2.2; rwa [fstIdx_zK] at h
          have hrep := tp_selected_isymRep_of_emptyAnt_botSucc hd.1.1 hant hsucc hcrit
          rw [heq, tp_zAxAll] at hrep
          exact isymLk_ne_isymRep _ _ hrep
        · -- axNeg (tag 6): VACUOUS — same Cor 2.1 selection invariant (`tp = isymRep` vs an L-axiom's
          -- `isymLk`).
          exfalso
          have hant : seqAnt s = (∅ : V) := by have h := hd.1.2.1; rwa [fstIdx_zK] at h
          have hsucc : seqSucc s = (^⊥ : V) := by have h := hd.1.2.2; rwa [fstIdx_zK] at h
          have hrep := tp_selected_isymRep_of_emptyAnt_botSucc hd.1.1 hant hsucc hcrit
          rw [heq, tp_zAxNeg] at hrep
          exact isymLk_ne_isymRep _ _ hrep
        · -- zAx1 (tag 7): `red dᵢ = dᵢ` (`red_zAx1`, `tp = isymRep`), so the whole node is a
          -- `red`-FIXPOINT — descent closes on the LEFT (mirror of the atom case).
          exact Or.inl (red_zK_fixpoint_of_zAx1_selected hds hcrit heq)
      · -- CRITICAL (5.1): `red (zK s r ds) = iRcritG …`, banked descent. Criticality is supplied by the
        -- `permIdx = lh ds` sentinel (`zKCritical_of_not_permIdx_lt`), so the full `zKValid` is in hand.
        exact Or.inr (iord_descent_red_zK_crit hcrit hds hmem hreg
          (zKValid_iff_zKValidF_and_zKCritical.mpr ⟨hvalid, zKCritical_of_not_permIdx_lt hcrit⟩))
    · simp at htag
    · simp at htag
    · simp at htag

/-! ## Connectives — PROVEN from the leaves (this is the "no wiring step" demonstration)
With `redSound` in hand, `ZDerivesEmpty` is closed under the whole `red`-orbit and the ε₀-descent is
**unconditional** — mirrors `ZDerivesEmpty_iterate` / `iord_iR2_iterate_descends`, minus the `RedSound`
hypothesis. Bodies left `sorry` here only because this file is uncompiled; they are pure plumbing copies. -/

/-- **`red` preserves `ZDerivesEmptyR`** (mirror of `ZDerivesEmpty_iR2`, now route-B): a regular
contradiction derivation reduces to one — `redSound` gives `ZDerivation (red d)`, `fstIdx_red` transfers
the empty antecedent + `⊥` succedent, and `ZRegular_red` (O1) preserves regularity. -/
theorem ZDerivesEmptyR_red {d : V} (h : ZDerivesEmptyR d) : ZDerivesEmptyR (red d) := by
  have hfst : fstIdx (red d) = fstIdx d :=
    fstIdx_red h.1.1 h.1.2.1 h.1.2.2 (zTag_Ind_or_K_of_ZDerivesEmpty h.1)
  exact ⟨⟨redSound d h, by rw [hfst]; exact h.1.2.1, by rw [hfst]; exact h.1.2.2⟩,
    ZRegular_red d h.1.1 h.2.1, ZFresh_red d h.1.1 h.2.2.1, ZSeqAnt_red d h.1.1 h.2.2.2⟩

/-- `ZDerivesEmptyR` is closed under the `red`-orbit (no hypothesis — `redSound`+`ZRegular_red` discharge it). -/
theorem ZDerivesEmptyR_red_iterate {z : V} (hz : ZDerivesEmptyR z) :
    ∀ n : ℕ, ZDerivesEmptyR (red^[n] z)
  | 0 => by simpa using hz
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact ZDerivesEmptyR_red (ZDerivesEmptyR_red_iterate hz n)

/-- **The per-step crux-2 dichotomy** (lap 111, disjunctive `iord_descent_red`). At each `red`-orbit
step, either the step is a `red`-**fixpoint** (`red^[n+1] z = red^[n] z`) or `iord` strictly `≺`-descends.
The endgame (`false_of_ZDerivesEmpty`) closes either way: a fixpoint of `red` on a ⊥-orbit is a cut-free
∅→⊥ derivation (absurd), and a never-fixpoint orbit is an infinite ε₀-descent (`PRWO(ε₀)` forbids it). -/
theorem iord_red_iterate_descends {z : V} (hz : ZDerivesEmptyR z) (n : ℕ) :
    red^[n+1] z = red^[n] z ∨ icmp (iord (red^[n+1] z)) (iord (red^[n] z)) = 0 := by
  rw [Function.iterate_succ_apply']
  exact iord_descent_red (ZDerivesEmptyR_red_iterate hz n)

/-! ## M2 — the C0.5 Foundation→Z bridge
`Z ⊇ 𝗣𝗔` on closed sequents, M-internal (Bryce–Goré `Peano.v` blueprint, B1–B3; the PA-induction axiom
maps directly to Z's native `Ind`, skipping their biggest sub-tower). Populates `ZDerivesEmpty` from a
Foundation ⊥-proof. -/

/-- **M2.** A model-internal `𝗣𝗔`-derivation of the (coded) empty/`⊥` sequent yields a `Z`-derivation
of the empty sequent. ⚠️ **Signature to pin against Foundation's coded-provability API:** the confirmed
primitive `Theory.DerivationOf (d s : V) := fstIdx d = s ∧ T.Derivation d` takes a *coded sequent*
`s : V` (here `∅`/the `⊥`-sequent), NOT a `Sentence ℒₒᵣ` (the in-repo doc was loose); the exact
`𝗣𝗔`-internal theory term `T` is the box's to fix (it is what `¬ 𝗣𝗔.Consistent M` unfolds to internally,
cf. `Reduction.peano_not_proves_consistency`). -/
theorem foundation_bot_to_Z_empty {d : V} (hd : (𝗣𝗔 : Theory ℒₒᵣ).Derivation d) (h0 : fstIdx d = ∅) :
    ∃ z : V, ZDerivesEmptyR z := sorry

/-! ## M3 — assemble the Gentzen contradiction
An inconsistency gives a `ZDerivesEmpty` (M2) whose `red`-orbit is an infinite ε₀-descent (M1b ⟹
`iord_red_iterate_descends`), which `PRWO(ε₀)`/well-foundedness forbids. This is the payload that
discharges the deep axiom `GentzenCon.gentzen_descent_of_inconsistent`; the existing `Reduction.lean`
+ `GentzenCon` scaffolding carries it the rest of the way to `goodstein_implies_consistency` and the
headline — no new top-level wiring. -/

/-! ### Existence-form endgame (lap-135 PIVOT) — the monolithic `false_of_ZDerivesEmpty` DECOMPOSED

The lap-129 refutation ("`red`-fixpoint ⟹ cut-free" is FALSE for the `permIdx` engine) blocked the direct
proof of `false_of_ZDerivesEmpty` via the `iord_red_iterate_descends` dichotomy (its fixpoint branch is a
non-cut-free STALL). The lap-132/135 reframe replaces the deterministic engine with the EXISTENCE of a
descending reduct (`ZDerivesEmptyR_descent_step`, E') + the `𝚺₁` least-witness `redLeast` against
`PRWO(ε₀)` (`prwo_forbids_existence_descent`). The fixpoint branch DISAPPEARS — `majorIdx` never stalls on
the ⊥-orbit (`majorIdx_botOrbit_reducible`). This block decomposes the single monolithic termination
`sorry` into TWO named, individually-attackable sub-`sorry`s (`descent_step_K_majorIdx` = the per-step
math; `prwo_forbids_existence_descent` = the M3 PRWO plumbing) plus SORRY-FREE descent infrastructure. -/

/-- **Explicit-reduct REPLACE descent kernel (index-generic, `red`-free), SORRY-FREE.** The termination
half the existence form needs at `majorIdx`. `iRedDescent_red_zK_replace_eq` proves the same bundle but
keys its conclusion to `red (zK s r ds)` via an `hred` true only at `permIdx`; here the reduct is the
EXPLICIT `zK s r (seqUpdate ds i v)`. Proof = that kernel's body with `red (znth ds i) ↦ v`, final
`rw [hred]` dropped (`iotil`/`idg` are conclusion-label & `red`-agnostic — read only the premise seq). -/
theorem iRedDescent_zK_replace_explicit {s r ds i v : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hIH : iRedDescent v (znth ds i)) :
    iRedDescent (zK s r (seqUpdate ds i v)) (zK s r ds) := by
  have hNF : ∀ n, isNF (iotil (znth ds n)) := fun n => by
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  have hNF' : ∀ n, isNF (iotil (znth (seqUpdate ds i v) n)) := fun n => by
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hIH.nf
    · rw [znth_seqUpdate_of_ne hne]; exact hNF n
  have hle : ∀ n, idg (znth (seqUpdate ds i v) n) ≤ idg (znth ds n) := fun n => by
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hIH.dg_le
    · rw [znth_seqUpdate_of_ne hne]
  have heq : ∀ n, n ≠ i →
      iotil (znth (seqUpdate ds i v) n) = iotil (znth ds n) :=
    fun n hne => by rw [znth_seqUpdate_of_ne hne]
  have hlt : icmp (iotil (znth (seqUpdate ds i v) i)) (iotil (znth ds i)) = 0 := by
    rw [znth_seqUpdate_self hi]; exact hIH.otil_lt
  exact ⟨idg_zK_le_replace hds (seqUpdate_seq ds i _) (seqUpdate_lh ds i _) hle,
    iotil_zK_lt_replace hds (seqUpdate_seq ds i _) (seqUpdate_lh ds i _) hi hlt heq hNF hNF',
    isNF_iotil_zK (seqUpdate_seq ds i _) (fun n _ => hNF' n)⟩

/-- **`iord`-descent corollary** of `iRedDescent_zK_replace_explicit` (the form the existence step
consumes — strict `iord` drop of the explicit `majorIdx`-replace reduct). SORRY-FREE. -/
theorem iord_descent_zK_replace_explicit {s r ds i v : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hIH : iRedDescent v (znth ds i)) :
    icmp (iord (zK s r (seqUpdate ds i v))) (iord (zK s r ds)) = 0 :=
  iord_descent_of_iRedDescent (iRedDescent_zK_replace_explicit hds hmem hi hIH)
    (isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation _ (hmem n hn)))

/-- **tag-3 (Ind major premise) DESCENT, SORRY-FREE** — the termination half of `descent_step_K_majorIdx`'s
Ind case. `red dⱼ = iRInd dⱼ` (`red_zInd`) descends below `dⱼ` (`iRedDescent_zInd`), fed to the explicit
kernel. The tag-3 residual of `descent_step_K_majorIdx` is then PURELY the soundness witness. -/
theorem descent_K_majorIdx_Ind_descends {s r ds : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n))
    (hmlt : majorIdx (zK s r ds) < lh ds)
    (hind : zTag (znth ds (majorIdx (zK s r ds))) = 3) :
    icmp (iord (zK s r (seqUpdate ds (majorIdx (zK s r ds))
            (red (znth ds (majorIdx (zK s r ds)))))))
         (iord (zK s r ds)) = 0 := by
  have hjZ : ZDerivation (znth ds (majorIdx (zK s r ds))) := hmem _ hmlt
  have hIH : iRedDescent (red (znth ds (majorIdx (zK s r ds))))
      (znth ds (majorIdx (zK s r ds))) := by
    rcases zDerivation_iff.mp hjZ with ⟨s', heq, _⟩ | ⟨s', a', p', d0', heq, _, _⟩ |
      ⟨s', p', d0', heq, _, _⟩ | ⟨s', at'', p', d0', d1', heq, _, _, _⟩ |
      ⟨s', r', ds', heq, _, _, _⟩ | ⟨s', p', k', heq, _, _⟩ | ⟨s', p', heq, _, _⟩ | ⟨s', C', heq, _⟩
    · rw [heq] at hind; simp at hind
    · rw [heq] at hind; simp at hind
    · rw [heq] at hind; simp at hind
    · rw [heq, red_zInd]
      obtain ⟨hd0Z, hd1Z, _⟩ := zDerivation_zInd_inv (heq ▸ hjZ)
      exact iRedDescent_zInd (isNF_iotil_of_ZDerivation _ hd0Z) (isNF_iotil_of_ZDerivation _ hd1Z)
    · rw [heq] at hind; simp at hind
    · rw [heq] at hind; simp at hind
    · rw [heq] at hind; simp at hind
    · rw [heq] at hind; simp at hind
  exact iord_descent_zK_replace_explicit hds hmem hmlt hIH

/-! ### Critical/non-critical reframe (lap 141) — Buchholz §3.2 case 5.1 vs 5.2, via the GENUINE engine `red`

The lap-140 tag-{3,4,5,6} decomposition keys the reduct on the *major premise's* inference symbol, and its
tag-5/6 leaves wall on proving the major premise's cut partner is a PRINCIPAL R-intro (Buchholz criticality,
not merely "a premise with that succedent"). **That wall is an ARTIFACT of the major-premise framing.**
Buchholz's actual reduction (Def 3.2 case 5) splits on whether the chain is CRITICAL, NOT on the major
premise's tag — and the genuine engine `red` realizes the faithful split (on the critical branch it equals
`iRcritG …`, the genuine SOUND reduct sharing `iord` with the ordinal-shadow `iRcrit`). Keying the dispatch
on the `permIdx` criticality sentinel:
- **5.1 critical** (`¬ permIdx < lh ds` = `zKCritical`): `red` DESCENDS (`iord_descent_red_zK_crit`, banked,
  sorry-free) — and inside it Lemma 3.1 (`inference_critical_pair`) supplies the PRINCIPAL pair `(i,j)` with
  `tp dᵢ = R_{Aᵢ}` FOR FREE, so there is **no producer-principal proof**. Soundness is `ZDerivesEmptyR_red`
  (red's standard orbit soundness), which routes through the PRE-EXISTING red-R2 residual
  `ZDerivation_red_zK_crit` (`Crux2Blueprint:1108`) — NOT a new obligation, and NOT the wrong-reduct
  `ZDerivesEmptyR (iR2 …)` (which is FALSE-risk: `iR2 = iRcrit` is the ordinal-shadow with WRONG endsequents).
- **5.2 non-critical** (`permIdx < lh ds`): the `permIdx`-selected Rep premise is replaced/spliced (incl. the
  lap-129 atom/`Ax¹` stall, resolved by the §5 atomic reduction). The single remaining NEW open leaf.

This overturns lap-139's "the existence reframe does not obviate the deep content" *for the tag-5/6 sub-case*:
the producer-principal obstruction is gone; what remains is the standard red-R2 (1108, pre-existing) + the
non-critical 5.2 recursion. -/

/-- **CRITICAL-case soundness via the GENUINE re-keyed reduct `iRKcCrit` — ∀-redex case, PROVEN from the
orbit alone (lap 142).** For a regular `∅→⊥` chain that is critical (`¬ permIdx < lh ds`) whose R-redex is
an `I∀` (`hAcase`), `iRKcCrit (zK s r ds)` is a genuine `ZDerivation`. **This realizes the operator-mandated
existence-form spike for the dominant critical sub-case:** it reuses the BANKED per-reduct soundness
`ZDerivation_iRKcCrit_all` (laps 112-119) DIRECTLY from the chain's own `zKValid`/`ZFresh`/`ZSeqAnt`, with
NO dependence on `red`/`redSound` (whose critical reduct is the FALSE-as-stated instance-`0` shadow
`ZDerivation_red_zK_crit`) and NO selection-correctness campaign.

Every input is now derivable: redex data (`redZKReady_of_zKValid`, ∀-branch — now also yielding
`seqSucc sⱼ = cutFormula` via the `zAxAll` disjunct's `zAxAllSuccWff`); eigen-freshness `maxEigen d0 < a`
(premise `ZRegular`); matrix wff (the I∀ premise's `zIallWff`); cut wff (`cutFormula_wff_of_zKValid`); the
axAll premise's `Seq` antecedent (`seq_seqAnt_zK_premise`); and the threading/rank **up to `redexI`**
(`chainInf_redexI_data` gives `redexI < j0`, restricting the `isChainInf` data). Only the ∀-half R-redex
needs threading — `ZDerivation_iRcritG_corrected`'s `haux1` L-half takes none — so `redexI < j0` suffices,
and the `redexJ ≤ j0` obligation that blocks the ¬-case (`PENDING_WORK` lap-142) never arises here. -/
theorem ZDerivation_iRKcCrit_critical_all {s r ds : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hcrit : ¬ permIdx (zK s r ds) < lh ds)
    (hAcase : ∃ sᵢ a p d0, znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0) :
    ZDerivation (iRKcCrit (zK s r ds)) := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  have hvalid : zKValid s r ds := zKValid_iff_zKValidF_and_zKCritical.mpr
    ⟨zKValidF_of_ZDerivation_zK hZ, zKCritical_of_not_permIdx_lt hcrit⟩
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨hIJ, hJlt, hcase⟩ := redZKReady_of_zKValid hZ hvalid
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  rcases hcase with ⟨sᵢ, sⱼ, a, p, pj, k', d0, hdi, hdj, _hirk, hsj⟩ |
    ⟨sᵢ, sⱼ, p, d0, hdi, hdj, _hcut, _hpUf⟩
  · -- ∀-redex: assemble the orbit data and apply the banked `ZDerivation_iRKcCrit_all`.
    have hZdi : ZDerivation (zIall sᵢ a p d0) := hdi ▸ hmem _ hIlt
    obtain ⟨_, _, hwff⟩ := zDerivation_zIall_inv hZdi
    have hpwff : IsUFormula ℒₒᵣ p := hwff.2.2.isUFormula
    have hregI : ZRegular (zIall sᵢ a p d0) := hdi ▸ ZRegular_zK_premise hds hd.2.1 hIlt
    have heig : maxEigen d0 < a := maxEigen_lt_of_regular_zIall hregI
    have hant : seqAnt s = (∅ : V) := by have h := hd.1.2.1; rwa [fstIdx_zK] at h
    have hSeqsj : Seq (seqAnt sⱼ) := by
      have h := seq_seqAnt_zK_premise hds hd.2.2.2 hJlt (hmem _ hJlt) (by rw [hdj]; simp)
      rwa [hdj, fstIdx_zAxAll] at h
    obtain ⟨j0, _, hI_lt_j0, hthread0, hrank0, _⟩ := chainInf_redexI_data hvalid
    exact ZDerivation_iRKcCrit_all hZ hIlt hJlt hIJ hdi hdj heig hd.2.2.1 hpwff
      (cutFormula_wff_of_zKValid hZ hvalid) (by rw [hant]; exact seq_empty) hSeqsj hsj
      (fun i' hi' => hthread0 i' (le_of_lt (lt_of_le_of_lt hi' hI_lt_j0)))
      (fun i' hi' => hrank0 i' (lt_trans hi' hI_lt_j0))
      (irk_chainAsucc_redexI_le hvalid)
  · -- ¬-redex branch: the R-redex is `zIneg`, contradicting the `I∀` hypothesis `hAcase`.
    exfalso
    obtain ⟨sᵢ', a', p', d0', hdi'⟩ := hAcase
    rw [hdi'] at hdi
    exact absurd (congrArg zTag hdi) (by rw [zTag_zIall, zTag_zIneg]; simp)

/-- **CRITICAL ∀-case (Buchholz §3.2 case 5.1, I∀ R-redex) — RED-FREE (lap 143).** A regular critical
`∅→⊥` chain whose R-redex is an `I∀` has the GENUINE corrected reduct `iRKcCrit (zK s r ds)` as a
strictly-`iord`-descending `ZDerivesEmptyR` reduct — witnessing the existence-form `∃ d'` with `iRKcCrit`,
NOT `red`. SOUNDNESS = `ZDerivation_iRKcCrit_critical_all` (lap-142, sorry-free, NO `red`/`redSoundGen`);
the three orbit invariants = `ZRegular_/ZFresh_/ZSeqAnt_iRKcCrit_of_zK`; DESCENT = `iord_descent_iRKcCrit_corr`
(banked). This DROPS the dominant critical sub-case off the kernel-FALSE `red`-soundness chain
(`ZDerivation_red_zK_crit` :1108 / `zKValidF_iIndReduct_of_zInd` :80). -/
theorem descent_step_K_critical_all {s r ds : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hcrit : ¬ permIdx (zK s r ds) < lh ds)
    (hAcase : ∃ sᵢ a p d0, znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  have hvalid : zKValid s r ds := zKValid_iff_zKValidF_and_zKCritical.mpr
    ⟨zKValidF_of_ZDerivation_zK hZ, zKCritical_of_not_permIdx_lt hcrit⟩
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨hIJ, hJlt, hcase⟩ := redZKReady_of_zKValid hZ hvalid
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  refine ⟨iRKcCrit (zK s r ds),
    ⟨⟨ZDerivation_iRKcCrit_critical_all hd hcrit hAcase, ?_, ?_⟩,
      ZRegular_iRKcCrit_of_zK hds hZ hd.2.1 hvalid, ZFresh_iRKcCrit_of_zK hds hZ hd.2.2.1 hvalid,
      ZSeqAnt_iRKcCrit_of_zK hds hZ hd.2.2.2 hvalid⟩, ?_⟩
  · rw [fstIdx_iRKcCrit]; exact hd.1.2.1
  · rw [fstIdx_iRKcCrit]; exact hd.1.2.2
  · rcases hcase with ⟨sᵢ, sⱼ, a, p, pj, k', d0, hdi, hdj, hirk, _hsj⟩ |
      ⟨sᵢ, sⱼ, p, d0, hdi, _hdj, _hcut, _hpUf⟩
    · exact iord_descent_iRKcCrit_corr hds hmem hvalid hIlt hJlt hIJ hdi hdj hirk
    · exfalso
      obtain ⟨sᵢ', a', p', d0', hdi'⟩ := hAcase
      rw [hdi'] at hdi
      exact absurd (congrArg zTag hdi) (by rw [zTag_zIall, zTag_zIneg]; simp)

/-- **CRITICAL ¬-case (Buchholz §3.2 case 5.1, I¬ R-redex) — RED-FREE (lap 144).** A regular critical
`∅→⊥` chain whose R-redex is an `I¬` has the GENUINE corrected reduct `iRKcCrit (zK s r ds)` as a
strictly-`iord`-descending `ZDerivesEmptyR` reduct — witnessing the existence-form `∃ d'` with `iRKcCrit`,
NOT `red`. SOUNDNESS = `ZDerivation_iRKcCrit_neg_botOrbit` (the `redexJ ≤ j0`-FREE keep-tip form: when the
§5 axNeg reduct lands above the ⊥-orbit tip `j0`, chain-validity is rebuilt at the unchanged tip); the
three orbit invariants = `ZRegular_/ZFresh_/ZSeqAnt_iRKcCrit_of_zK`; DESCENT = `iord_descent_iRKcCrit_neg`
(banked). This DROPS the second (and last) critical sub-case off the kernel-FALSE `red`-soundness chain —
the lap-142 `redexJ ≤ j0` obstruction is dissolved via `isChainInf_reduceR_keepTip`. -/
theorem descent_step_K_critical_neg {s r ds : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hcrit : ¬ permIdx (zK s r ds) < lh ds)
    (hNcase : ∃ sᵢ p d0, znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  have hvalid : zKValid s r ds := zKValid_iff_zKValidF_and_zKCritical.mpr
    ⟨zKValidF_of_ZDerivation_zK hZ, zKCritical_of_not_permIdx_lt hcrit⟩
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨hIJ, hJlt, hcase⟩ := redZKReady_of_zKValid hZ hvalid
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  have hant : seqAnt s = (∅ : V) := by have h := hd.1.2.1; rwa [fstIdx_zK] at h
  have hsucc : seqSucc s = (^⊥ : V) := by have h := hd.1.2.2; rwa [fstIdx_zK] at h
  rcases hcase with ⟨sᵢ, sⱼ, a, p, pj, k', d0, hdi, _hdj, _hirk, _hsj⟩ |
      ⟨sᵢ, sⱼ, p, d0, hdi, hdj, hcut, _hpUf⟩
  · -- ∀-redex contradicts the I¬ hypothesis `hNcase`
    exfalso
    obtain ⟨sᵢ', p', d0', hdi'⟩ := hNcase
    rw [hdi'] at hdi
    exact absurd (congrArg zTag hdi) (by rw [zTag_zIneg, zTag_zIall]; simp)
  · -- ¬-redex: witness `iRKcCrit` via the keep-tip ⊥-orbit soundness (`redexJ ≤ j0`-free)
    have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ hmem _ hIlt
    obtain ⟨_, _, _, hSeqsi, hd0ant⟩ := zDerivation_zIneg_inv hZdi
    have hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)) := cutFormula_wff_of_zKValid hZ hvalid
    obtain ⟨j0, hj0, hIj0, hthread0, hrank0, hAj0⟩ := chainInf_redexI_data hvalid
    have hbot : chainAsucc ds j0 = (^⊥ : V) := hAj0.elim (fun h => h.trans hsucc) id
    refine ⟨iRKcCrit (zK s r ds),
      ⟨⟨ZDerivation_iRKcCrit_neg_botOrbit hZ hIlt hJlt hIJ hdi hdj hcut hd0ant hCwff
          (by rw [hant]; exact seq_empty) hSeqsi hIj0 hj0 hbot hthread0 hrank0, ?_, ?_⟩,
        ZRegular_iRKcCrit_of_zK hds hZ hd.2.1 hvalid, ZFresh_iRKcCrit_of_zK hds hZ hd.2.2.1 hvalid,
        ZSeqAnt_iRKcCrit_of_zK hds hZ hd.2.2.2 hvalid⟩, ?_⟩
    · rw [fstIdx_iRKcCrit]; exact hd.1.2.1
    · rw [fstIdx_iRKcCrit]; exact hd.1.2.2
    · exact iord_descent_iRKcCrit_neg hds hmem hvalid hIlt hJlt hIJ hdi hdj hcut (hcut ▸ hCwff)

/-- **CRITICAL case (Buchholz §3.2 case 5.1) — dispatcher, FULLY RED-FREE (lap 144).** Case-splits on the
R-redex polarity (the `redZKReady_of_zKValid` ∀/¬ disjunction): I∀ → `descent_step_K_critical_all`
(RED-FREE, lap 143); I¬ → `descent_step_K_critical_neg` (RED-FREE, lap 144, via the `redexJ ≤ j0`-free
keep-tip soundness). NO `red`/`redSoundGen`/false-:80/:1108 dependence on EITHER branch — this whole lemma
is now `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`). The lap-141 regression to `red` is
fully undone. -/
theorem descent_step_K_critical {s r ds : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hcrit : ¬ permIdx (zK s r ds) < lh ds) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  have hvalid : zKValid s r ds := zKValid_iff_zKValidF_and_zKCritical.mpr
    ⟨zKValidF_of_ZDerivation_zK hZ, zKCritical_of_not_permIdx_lt hcrit⟩
  obtain ⟨_, _, hcase⟩ := redZKReady_of_zKValid hZ hvalid
  rcases hcase with ⟨sᵢ, sⱼ, a, p, pj, k', d0, hdi, _⟩ | ⟨sᵢ, sⱼ, p, d0, hdi, _⟩
  · exact descent_step_K_critical_all hd hcrit ⟨sᵢ, a, p, d0, hdi⟩
  · exact descent_step_K_critical_neg hd hcrit ⟨sᵢ, p, d0, hdi⟩

/-! ### Decoupling the redex machinery from CRITICALITY (lap 147)

The `iRKcCrit` soundness/descent/invariants are ALL criticality-free given the redex data (verified:
`ZDerivation_iRKcCrit_all`/`_neg_botOrbit` take only redex+threading+`ZFresh`; `iord_descent_iRcrit_of_redex`
takes redex existence; `ZRegular/ZFresh/ZSeqAnt_iRKcCrit` take the redex data). Criticality is consumed in
EXACTLY one place — `isRedexPair_redexCode_of_zKValid` → `inference_critical_pair_of_chain` — to PROVE a redex
exists. These lemmas supply that existence from a concrete redex pair instead, so the whole critical-reduct
engine becomes available to ANY chain with a redex (in particular the non-critical `axMajor` sub-case, whose
cut-partner `(i′, majorIdx)` IS a redex pair when `i′` directly R-introduces the cut formula). -/

/-- **Decoupled redex finder** — `redexCode` lands on a redex whenever ONE exists in range, no criticality. -/
lemma isRedexPair_redexCode_of_exists {s r ds : V}
    (hex : ∃ c < (⟪lh ds, lh ds⟫ : V), isRedexPair ds c) :
    isRedexPair ds (redexCode (zK s r ds)) := by
  obtain ⟨c, hclt, hc⟩ := hex
  have hex' : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by rw [zKseq_zK]; exact ⟨c, hclt, hc⟩
  simpa only [zKseq_zK] using redexCode_isRedexPair hex'

/-- **The pair-monotone redex bound, criticality-free.** Given the `isChainInf` exit `j0` and ANY in-region
redex pair `⟪i0, j1⟫` (`i0 < j1 ≤ j0`), the canonical least redex satisfies `redexI < j0` — so the
`isChainInf` threading/rank up to `j0` restricts to `redexI`. Extracted from `chainInf_redexI_data`'s tail
(its pair-monotone argument) with the redex SUPPLIED rather than manufactured from criticality. -/
lemma redexI_lt_of_redexPair {s r ds i0 j1 j0 : V}
    (hij : i0 < j1) (hj1 : j1 ≤ j0) (hj0 : j0 < lh ds) (hpair : isRedexPair ds (⟪i0, j1⟫ : V)) :
    redexI (zK s r ds) < j0 := by
  have hjlt : j1 < lh ds := lt_of_le_of_lt hj1 hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hrc : isRedexPair ds (redexCode (zK s r ds)) :=
    isRedexPair_redexCode_of_exists ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hpair⟩
  have hcode_le : redexCode (zK s r ds) ≤ (⟪i0, j1⟫ : V) := by
    have hm := redexAux_min ds ⟪lh ds, lh ds⟫ ⟪i0, j1⟫ (pair_lt_pair hilt hjlt) hpair
    simpa [redexCode, zKseq_zK] using hm
  have hpair_eq : (⟪redexI (zK s r ds), redexJ (zK s r ds)⟫ : V) = redexCode (zK s r ds) :=
    pair_unpair (redexCode (zK s r ds))
  have hpair_le : (⟪redexI (zK s r ds), redexJ (zK s r ds)⟫ : V) ≤ ⟪i0, j1⟫ := by
    rw [hpair_eq]; exact hcode_le
  have hle_disj : redexI (zK s r ds) ≤ i0 ∨ redexJ (zK s r ds) ≤ j1 := by
    by_contra h; push_neg at h
    exact absurd (lt_of_lt_of_le (pair_lt_pair h.1 h.2) hpair_le) (_root_.lt_irrefl _)
  rcases hle_disj with hle | hle
  · exact lt_of_le_of_lt hle (lt_of_lt_of_le hij hj1)
  · exact lt_of_lt_of_le (lt_of_lt_of_le hrc.1 hle) hj1

/-- **Decoupled redex reader** — the `redZKReady_of_zKValid` ∀/¬ disjunction, with the redex EXISTENCE
supplied as a hypothesis (`hex`) and only the faithful validity `zKValidF` (NO criticality) for the
formula-hood side-conditions. Identical body to `redZKReady_of_zKValid` modulo the redex source. -/
lemma redZKReady_of_zKValidF_exists {s r ds : V}
    (hZ : ZDerivation (zK s r ds)) (hvalidF : zKValidF s r ds)
    (hex : ∃ c < (⟪lh ds, lh ds⟫ : V), isRedexPair ds c) :
    redexI (zK s r ds) < redexJ (zK s r ds) ∧ redexJ (zK s r ds) < lh ds ∧
    ( (∃ sᵢ sⱼ a p pj k' d0,
        znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0 ∧
        znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k' ∧
        irk (^∀ pj : V) = irk (cutFormula (zK s r ds)) + 1 ∧
        seqSucc sⱼ = cutFormula (zK s r ds))
    ∨ (∃ sᵢ sⱼ p d0,
        znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0 ∧
        znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p ∧
        cutFormula (zK s r ds) = p ∧ IsUFormula ℒₒᵣ p) ) := by
  have hrc : isRedexPair ds (redexCode (zK s r ds)) := isRedexPair_redexCode_of_exists hex
  obtain ⟨hRi, hLj⟩ := redexPair_tp hrc
  rw [show π₁ (redexCode (zK s r ds)) = redexI (zK s r ds) from rfl] at hRi hLj
  rw [show π₂ (redexCode (zK s r ds)) = redexJ (zK s r ds) from rfl] at hLj
  have hIJ : redexI (zK s r ds) < redexJ (zK s r ds) := hrc.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
  have hZi := hmem _ hIlt
  have hZj := hmem _ hJlt
  obtain ⟨_, hperm0, _, hf2, _, hf6, _⟩ := hvalidF
  refine ⟨hIJ, hJlt, ?_⟩
  rcases zDerivation_isymR_form hZi hRi with ⟨sᵢ, a, p, d0, hdi, hAp⟩ | ⟨sᵢ, p, d0, hdi, hAn⟩
  · rcases zDerivation_isymLk_form hZj hLj with ⟨sⱼ, pj, hdj, hApj⟩ | ⟨sⱼ, pp, hdj, _, hAnn⟩
    · left
      have hpjp : pj = p := by
        have h : (^∀ p : V) = (^∀ pj : V) := hAp.symm.trans hApj
        simpa using h.symm
      have hsf : IsSemiformula ℒₒᵣ 1 p := by
        rcases tp_isymR_form_wff hZi hRi with ⟨p', hp'eq, hsf'⟩ | ⟨p', hp'eq, _⟩
        · have h : (^∀ p : V) = (^∀ p' : V) := hAp.symm.trans hp'eq
          rwa [show p' = p from by simpa using h.symm] at hsf'
        · exact absurd (hAp.symm.trans hp'eq) (by simp [qqAll, inegF, qqOr])
      have hChA : chainAsucc ds (redexI (zK s r ds)) = (^∀ p : V) := by
        have hp := hperm0 _ hIlt
        rw [hRi, iperm_isymR_iff] at hp
        exact hp.symm.trans hAp
      have hcut : cutFormula (zK s r ds) = substs1 ℒₒᵣ
          (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) p := by
        have h := cutFormula_all (d := zK s r ds) (by rw [zKseq_zK]; exact hChA)
        rwa [zKseq_zK] at h
      refine ⟨sᵢ, sⱼ, a, p, pj, _, d0, hdi, hdj, ?_, ?_⟩
      · rw [hpjp, hcut, irk_substs1 hsf (by simp : IsSemiterm ℒₒᵣ 0
          (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds)))))) : V)),
          irk_all hsf.isUFormula]
      · have hsucc : seqSucc sⱼ = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral
            (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) pj :=
          (zDerivation_zAxAll_inv (hdj ▸ hZj)).2.2
        rw [hsucc, hpjp, hcut]
    · exact absurd (hAp.symm.trans hAnn) (by simp [qqAll, inegF, qqOr])
  · rcases zDerivation_isymLk_form hZj hLj with ⟨sⱼ, pj, hdj, hApj⟩ | ⟨sⱼ, pp, hdj, _, hAnn⟩
    · exact absurd (hApj.symm.trans hAn) (by simp [qqAll, inegF, qqOr])
    · right
      have hpUf : IsUFormula ℒₒᵣ p := by
        have h := hf2 _ hIlt (by rw [hdi]; exact zTag_zIneg _ _ _)
        rwa [hdi, zInegF_zIneg] at h
      have hppUf : IsUFormula ℒₒᵣ pp := by
        have h := hf6 _ hJlt (by rw [hdj]; exact zTag_zAxNeg _ _)
        rwa [hdj, zAxNegF_zAxNeg] at h
      have hppp : pp = p := by
        have h : (inegF p : V) = inegF pp := hAn.symm.trans hAnn
        simp only [inegF, qqOr_inj] at h
        exact ((neg_inj_iff hpUf hppUf).mp h.1).symm
      have hChA : chainAsucc ds (redexI (zK s r ds)) = inegF p := by
        have hpm := hperm0 _ hIlt
        rw [hRi, iperm_isymR_iff] at hpm
        exact hpm.symm.trans hAn
      have hcut : cutFormula (zK s r ds) = p :=
        cutFormula_neg (d := zK s r ds) hpUf (by rw [zKseq_zK]; exact hChA)
      exact ⟨sᵢ, sⱼ, p, d0, hdi, hppp ▸ hdj, hcut, hpUf⟩

/-- **`iRKcCrit` DESCENDS — ∀-case, criticality-free** (the `iord_descent_iRKcCrit_corr` twin with the redex
SUPPLIED via `hex` instead of derived from criticality). Routes through `iord_descent_iRcrit_of_redex`
(criticality-free) rather than `iord_descent_iRcrit_of_chain'`; the per-redex bundles `hbI`/`hbJ` are
identical (they never used criticality). `hr : 1 ≤ r` replaces the rank fact `chainInf` gave for free. -/
lemma iord_descent_iRKcCrit_corr_of_redex {s r ds sᵢ sⱼ a p pj k' d0 : V}
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i)) (hr : 1 ≤ r)
    (hex : ∃ c < (⟪lh ds, lh ds⟫ : V), isRedexPair ds c)
    (hIlt : redexI (zK s r ds) < lh ds) (hJlt : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k')
    (hirk : irk (^∀ pj : V) = irk (cutFormula (zK s r ds)) + 1) :
    icmp (iord (iRKcCrit (zK s r ds))) (iord (zK s r ds)) = 0 := by
  have h1 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) = 1 := by
    rw [zKseq_zK, hdi]; exact zTag_zIall _ _ _ _
  rw [iRKcCrit_eq_corr h1 (ne_of_lt hIJ)]
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n; rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  have hbI : iRedDescent (critReductCorr (zK s r ds) (redexI (zK s r ds)))
      (znth ds (redexI (zK s r ds))) := by
    rw [critReductCorr, if_neg (ne_of_lt hIJ), if_pos rfl, zKseq_zK, hdi,
      zIallPrem_zIall, zIallEig_zIall]
    exact iRedDescent_zsubst_zIall
      (by simp : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds)))))) : V)).isUTerm (hdi ▸ hmem _ hIlt)
  have hbJ : iRedDescent (critReductCorr (zK s r ds) (redexJ (zK s r ds)))
      (znth ds (redexJ (zK s r ds))) := by
    rw [critReductCorr, if_pos rfl]
    simp only [zKseq_zK, hdj, fstIdx_zAxAll]
    exact iRedDescent_zAx1_zAxAll_of_irk hirk
  rw [iord_iRcritG_eq_iRcrit]
  exact iord_descent_iRcrit_of_redex hds hnf hr (by simpa only [zKseq_zK] using hex) hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-- **`iRKcCrit` DESCENDS — ¬-case, criticality-free** (the `iord_descent_iRKcCrit_neg` twin, redex SUPPLIED).
Same decoupling as `iord_descent_iRKcCrit_corr_of_redex`, plus the two reduct-fold NF facts `hNFI`/`hNFJ`
that `iord_iRcritGNeg_eq_iRcrit` needs. -/
lemma iord_descent_iRKcCrit_neg_of_redex {s r ds sᵢ sⱼ p d0 : V}
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i)) (hr : 1 ≤ r)
    (hex : ∃ c < (⟪lh ds, lh ds⟫ : V), isRedexPair ds c)
    (hIlt : redexI (zK s r ds) < lh ds) (hJlt : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p) (hp : IsUFormula ℒₒᵣ p) :
    icmp (iord (iRKcCrit (zK s r ds))) (iord (zK s r ds)) = 0 := by
  have h1 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) ≠ 1 := by
    rw [zKseq_zK, hdi, zTag_zIneg]; simp
  rw [iRKcCrit_eq_neg h1 (ne_of_lt hIJ)]
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n; rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  have hbI : iRedDescent (critReductNeg (zK s r ds) (redexI (zK s r ds)))
      (znth ds (redexI (zK s r ds))) := by
    rw [critReductNeg_redexI (ne_of_lt hIJ), zKseq_zK, hdi, zInegPrem_zIneg]
    exact iRedDescent_zIneg
      (isNF_iotil_of_ZDerivation d0 (zDerivation_zIneg_inv (hdi ▸ hmem _ hIlt)).1)
  have hbJ : iRedDescent (critReductNeg (zK s r ds) (redexJ (zK s r ds)))
      (znth ds (redexJ (zK s r ds))) := by
    rw [critReductNeg_redexJ, zKseq_zK, hdj, fstIdx_zAxNeg, hcut]
    exact iRedDescent_zAx1_zAxNeg_gen hp
  have hNFI : isNF (iseqNaddIdg (seqUpdate (zKseq (zK s r ds)) (redexI (zK s r ds))
      (critReductNeg (zK s r ds) (redexI (zK s r ds))))) := by
    rw [zKseq_zK]
    exact isNF_iseqNaddIdg (fun n _ => by
      rcases eq_or_ne n (redexI (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hIlt]; exact hbI.nf
      · rw [znth_seqUpdate_of_ne hne]; exact hNF n)
  have hNFJ : isNF (iseqNaddIdg (seqUpdate (zKseq (zK s r ds)) (redexJ (zK s r ds))
      (critReductNeg (zK s r ds) (redexJ (zK s r ds))))) := by
    rw [zKseq_zK]
    exact isNF_iseqNaddIdg (fun n _ => by
      rcases eq_or_ne n (redexJ (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hJlt]; exact hbJ.nf
      · rw [znth_seqUpdate_of_ne hne]; exact hNF n)
  rw [iord_iRcritGNeg_eq_iRcrit (zK s r ds) (critReductNeg (zK s r ds)) hNFI hNFJ]
  exact iord_descent_iRcrit_of_redex hds hnf hr (by simpa only [zKseq_zK] using hex) hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-! ### `descent_step_K_majorIdx` — DECOMPOSED critical / non-critical (lap 141, Buchholz §3.2 case 5)

**Reframed from the lap-140 major-premise-tag split** (which walled on tag-5/6 "the major premise's cut
partner is a PRINCIPAL R-intro"). Buchholz's reduction (Def 3.2 case 5) splits on whether the chain is
CRITICAL, NOT on the major premise's tag — and the genuine engine `red` realizes the faithful split. The
dispatcher case-splits on the `permIdx` criticality sentinel:
- critical (`¬ permIdx < lh ds`) → `descent_step_K_critical`, CLOSED RED-FREE via the genuine `iRKcCrit`
  reduct (lap 143 ∀-case + lap 144 ¬-case; `#print axioms`-clean), no producer-principal proof (Lemma 3.1
  hands back the principal pair from criticality alone);
- non-critical (`permIdx < lh ds`) → `descent_step_K_noncritical`, Buchholz case 5.2 (the one open leaf). -/

/-- **The critical-cut reduct descends from a REDEX, no criticality (lap 147).** A regular `∅→⊥` chain
with the `isChainInf` exit data (`j0`/⊥-exit/threading/rank) and ANY in-region redex pair `⟪i0,j1⟫`
(`i0 < j1 ≤ j0`) has the genuine `iRKcCrit` reduct as a strictly-`iord`-descending `ZDerivesEmptyR`. This
WIRES the lap-147 decoupling: redex via `redZKReady_of_zKValidF_exists`, bound via `redexI_lt_of_redexPair`,
soundness via `ZDerivation_iRKcCrit_all`/`_neg_botOrbit` (criticality-free), descent via
`iord_descent_iRKcCrit_corr_of_redex`/`_neg_of_redex`, invariants via the no-`_of_zK` `ZRegular/ZFresh/
ZSeqAnt_iRKcCrit`. **Subsumes `descent_step_K_critical` (which sources the redex from criticality) and is the
engine for `descent_step_K_noncrit_axMajor`'s has-redex sub-case (cut-partner an R-intro).** -/
theorem descent_step_K_hasRedex {s r ds i0 j1 j0 : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hj0 : j0 < lh ds) (hbot0 : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hij : i0 < j1) (hj1 : j1 ≤ j0) (hpair : isRedexPair ds (⟪i0, j1⟫ : V)) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  have hvalidF : zKValidF s r ds := zKValidF_of_ZDerivation_zK hZ
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hjlt : j1 < lh ds := lt_of_le_of_lt hj1 hj0
  have hilt0 : i0 < lh ds := lt_trans hij hjlt
  have hex : ∃ c < (⟪lh ds, lh ds⟫ : V), isRedexPair ds c :=
    ⟨⟪i0, j1⟫, pair_lt_pair hilt0 hjlt, hpair⟩
  have hIlt_j0 : redexI (zK s r ds) < j0 := redexI_lt_of_redexPair hij hj1 hj0 hpair
  obtain ⟨hIJ, hJlt, hcase⟩ := redZKReady_of_zKValidF_exists hZ hvalidF hex
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  have hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r := hrank0 _ hIlt_j0
  have hca : ∀ i < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds i) := hvalidF.2.2.2.2.2.2.1
  rcases hcase with ⟨sᵢ, sⱼ, a, p, pj, k', d0, hdi, hdj, hirk, hsj⟩ |
      ⟨sᵢ, sⱼ, p, d0, hdi, hdj, hcut, hpUf⟩
  · -- ∀-redex
    have hZdi : ZDerivation (zIall sᵢ a p d0) := hdi ▸ hmem _ hIlt
    obtain ⟨_, hssi, hwff⟩ := zDerivation_zIall_inv hZdi
    have hpwff : IsUFormula ℒₒᵣ p := hwff.2.2.isUFormula
    have hregI : ZRegular (zIall sᵢ a p d0) := hdi ▸ ZRegular_zK_premise hds hd.2.1 hIlt
    have heig : maxEigen d0 < a := maxEigen_lt_of_regular_zIall hregI
    have hSeqsj : Seq (seqAnt sⱼ) := by
      have h := seq_seqAnt_zK_premise hds hd.2.2.2 hJlt (hmem _ hJlt) (by rw [hdj]; simp)
      rwa [hdj, fstIdx_zAxAll] at h
    have hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)) := by
      have h := hca _ hJlt; rw [chainAsucc, hdj, fstIdx_zAxAll, hsj] at h; exact h
    have hChAI : chainAsucc ds (redexI (zK s r ds)) = (^∀ p : V) := by
      rw [chainAsucc, hdi, fstIdx_zIall]; exact hssi
    have hr : 1 ≤ r := by
      have h1 : (1 : V) ≤ irk (chainAsucc ds (redexI (zK s r ds))) := by
        rw [hChAI, irk_all hpwff]; exact self_le_add_left 1 (irk p)
      exact le_trans h1 hrankI
    refine ⟨iRKcCrit (zK s r ds),
      ⟨⟨ZDerivation_iRKcCrit_all hZ hIlt hJlt hIJ hdi hdj heig hd.2.2.1 hpwff hCwff
          (by rw [hant]; exact seq_empty) hSeqsj hsj
          (fun i' hi' => hthread0 i' (le_of_lt (lt_of_le_of_lt hi' hIlt_j0)))
          (fun i' hi' => hrank0 i' (lt_trans hi' hIlt_j0)) hrankI, ?_, ?_⟩,
        ?_, ?_, ?_⟩, ?_⟩
    · rw [fstIdx_iRKcCrit]; exact hd.1.2.1
    · rw [fstIdx_iRKcCrit]; exact hd.1.2.2
    · refine ZRegular_iRKcCrit ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZRegular_zK_premise hds hd.2.1 hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZRegular_zK_premise hds hd.2.1 hIlt
      · rw [zKseq_zK, hdi]; exact Or.inl (zTag_zIall _ _ _ _)
    · refine ZFresh_iRKcCrit ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZFresh_zK_premise hds hd.2.2.1 hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZFresh_zK_premise hds hd.2.2.1 hIlt
      · rw [zKseq_zK, hdi]; exact Or.inl (zTag_zIall _ _ _ _)
    · refine ZSeqAnt_iRKcCrit ?_ ?_ ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZSeqAnt_zK_premise hds hd.2.2.2 hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZSeqAnt_zK_premise hds hd.2.2.2 hIlt
      · rw [fstIdx_zK]; exact seq_seqAnt_zK hd.2.2.2
      · rw [zKseq_zK, hdj, fstIdx_zAxAll]; exact hSeqsj
      · rw [zKseq_zK, hdi]; exact Or.inl (zTag_zIall _ _ _ _)
    · exact iord_descent_iRKcCrit_corr_of_redex hds hmem hr hex hIlt hJlt hIJ hdi hdj hirk
  · -- ¬-redex (botOrbit form: `redexJ ≤ j0`-free)
    have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ hmem _ hIlt
    obtain ⟨_, hssi, _, hSeqsi, hd0ant⟩ := zDerivation_zIneg_inv hZdi
    have hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)) := hcut ▸ hpUf
    have hChAI : chainAsucc ds (redexI (zK s r ds)) = (inegF p : V) := by
      rw [chainAsucc, hdi, fstIdx_zIneg]; exact hssi
    have hr : 1 ≤ r := by
      have h1 : (1 : V) ≤ irk (chainAsucc ds (redexI (zK s r ds))) := by
        rw [hChAI, irk_inegF hpUf]; exact self_le_add_left 1 (irk p)
      exact le_trans h1 hrankI
    refine ⟨iRKcCrit (zK s r ds),
      ⟨⟨ZDerivation_iRKcCrit_neg_botOrbit hZ hIlt hJlt hIJ hdi hdj hcut hd0ant hCwff
          (by rw [hant]; exact seq_empty) hSeqsi hIlt_j0 hj0 hbot0 hthread0 hrank0, ?_, ?_⟩,
        ?_, ?_, ?_⟩, ?_⟩
    · rw [fstIdx_iRKcCrit]; exact hd.1.2.1
    · rw [fstIdx_iRKcCrit]; exact hd.1.2.2
    · refine ZRegular_iRKcCrit ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZRegular_zK_premise hds hd.2.1 hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZRegular_zK_premise hds hd.2.1 hIlt
      · rw [zKseq_zK, hdi]; exact Or.inr (zTag_zIneg _ _ _)
    · refine ZFresh_iRKcCrit ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZFresh_zK_premise hds hd.2.2.1 hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZFresh_zK_premise hds hd.2.2.1 hIlt
      · rw [zKseq_zK, hdi]; exact Or.inr (zTag_zIneg _ _ _)
    · refine ZSeqAnt_iRKcCrit ?_ ?_ ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZSeqAnt_zK_premise hds hd.2.2.2 hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZSeqAnt_zK_premise hds hd.2.2.2 hIlt
      · rw [fstIdx_zK]; exact seq_seqAnt_zK hd.2.2.2
      · rw [zKseq_zK]
        have h := seq_seqAnt_zK_premise hds hd.2.2.2 hJlt (hmem _ hJlt) (by rw [hdj]; simp)
        rwa [hdj] at h ⊢
      · rw [zKseq_zK, hdi]; exact Or.inr (zTag_zIneg _ _ _)
    · exact iord_descent_iRKcCrit_neg_of_redex hds hmem hr hex hIlt hJlt hIJ hdi hdj hcut hpUf

/-! ### Non-critical K-step (Buchholz §3.2 case 5.2) — SPLIT on has-redex-below-the-exit (lap 147)

The lap-147 criticality decoupling (`descent_step_K_hasRedex`) refines the §5.2 obligation into a clean
dichotomy on whether the chain has a redex pair `⟪i0,j1⟫` BELOW the `isChainInf` exit `j0`:

- **has bounded redex** → `descent_step_K_hasRedex` (PROVEN, criticality-free `iRKcCrit` cut). This is the
  Buchholz §14.253 principal case realized off `red` — and it now covers the non-critical chains too, the
  half the lap-141 critical/non-critical split left open. Note `majorIdx ≤ j0` (first ⊥-exit), so a tag-5/6
  major premise with a DIRECT R-intro cut-partner lands here.
- **no bounded redex** → `descent_step_K_noncrit_recurse` (the lone residual). By `majorPrem_tag_mem` the
  major premise is then a `Rep` node (`zInd`/sub-`zK`, tag 3/4) — Buchholz §14.254 REPLACE — or a tag-5/6
  L-axiom whose cut-partner is itself a chain (no direct R-intro). Both REDUCE THE MAJOR PREMISE (a derivation
  of `Γₘ→⊥`, `Γₘ` possibly nonempty) — the GENERAL `Γ→⊥` Z-derivation reduction, closure via strong
  `iord`-induction (Buchholz Thm 2.1 / Cor 2.1). The one genuinely deep remaining piece. -/

/-- **Shared §14.254 REPLACE step (off `red`, off criticality) — the reusable plumbing of BOTH no-redex
sub-cases.** If SOME premise `i` of the `∅→⊥` chain `zK s r ds` has a SAME-end-sequent
(`fstIdx v = fstIdx (znth ds i)`, i.e. Buchholz `tp(dᵢ) = Rep` — the reduction step does not change `dᵢ`'s
endsequent, §14.254) strictly-`iord`-descending reduct `v` that is itself a regular/fresh/seqAnt
`ZDerivation`, then replacing it — `zK s r (seqUpdate ds i v) = iCritAux (zK s r ds) i v` — yields a
strictly-`iord`-descending `ZDerivesEmptyR`. This realizes Buchholz §14.254 `d[0] = K^r_Θ(i ∕ dᵢ[0])` at the
assembly layer, wiring the banked `ZDerivation_iCritAux_of` (chain validity, `zKValidF_seqUpdate`) +
`iord_descent_iCritAux_of_ZDerivation` (the N1-IH descent) + `ZRegular/ZFresh/ZSeqAnt_zK_of_seqUpdate`
(invariant preservation). The reduct's own well-formedness side-conditions are discharged UNIFORMLY from
`ZDerivation v` (`iperm_tp_fstIdx_of_ZDerivation` + `zKValidF_leafconds_of_ZDerivation`), so the only genuine
remaining content of each no-redex case is PRODUCING `v` — the Rep-reduct of the major premise (§14.254a,
`repMajor`) or of its upstream cut-partner (§14.254b, `axMajor`) — i.e. the GENERAL `Γ→⊥` reduction
(recursion on a structurally-smaller premise). -/
theorem descent_step_K_replace {s r ds i v : V}
    (hd : ZDerivesEmptyR (zK s r ds)) (hi : i < lh ds)
    (hZv : ZDerivation v) (hregv : ZRegular v) (hfreshv : ZFresh v) (hseqantv : ZSeqAnt v)
    (hvfst : fstIdx v = fstIdx (znth ds i))
    (hdesc : iRedDescent v (znth ds i)) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hant : seqAnt s = (∅ : V) := by have h := hd.1.2.1; rwa [fstIdx_zK] at h
  have hsucc : seqSucc s = (^⊥ : V) := by have h := hd.1.2.2; rwa [fstIdx_zK] at h
  have hperm_v := iperm_tp_fstIdx_of_ZDerivation hZv
  obtain ⟨hf1, hf2, hf5, hf6⟩ := zKValidF_leafconds_of_ZDerivation hZv
  refine ⟨iCritAux (zK s r ds) i v, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · exact ZDerivation_iCritAux_of hi hZ hZv hvfst hperm_v hf1 hf2 hf5 hf6
  · rw [iCritAux_zK, fstIdx_zK]; exact hant
  · rw [iCritAux_zK, fstIdx_zK]; exact hsucc
  · rw [iCritAux_zK]
    exact ZRegular_zK_of_seqUpdate (fun m hm => ZRegular_zK_premise hds hd.2.1 hm) hregv
  · rw [iCritAux_zK]
    exact ZFresh_zK_of_seqUpdate (fun m hm => ZFresh_zK_premise hds hd.2.2.1 hm) hfreshv
  · rw [iCritAux_zK]
    exact ZSeqAnt_zK_of_seqUpdate (seqAntSeqFlag_zK_of_ZSeqAnt hd.2.2.2)
      (fun m hm => ZSeqAnt_zK_premise hds hd.2.2.2 hm) hseqantv
  · exact iord_descent_iCritAux_of_ZDerivation hZ hi hdesc.otil_lt hdesc.dg_le hdesc.nf


/-- **⊥-orbit collapse of the Ind formula (lap 145).** If `substs1 t p = ^⊥` for a 1-ary semiformula
`p`, then `p = ^⊥`. Substitution preserves the top connective (`substs_*`), and `^⊥` is the only
constructor whose substitution is `^⊥`. **This dissolves the lap-144 "internal term-value `k = ⟦t⟧`"
prerequisite**: on a `∅→⊥` orbit a `zIndWff` node has conclusion succedent `substs1 t p = seqSucc s = ⊥`,
forcing `p = ⊥`, so *every* premise of the Ind reduct `iIndReductSeqG` carries succedent `⊥` for ANY `k`
(the `hexit` clause needs no term evaluation). -/
lemma eq_falsum_of_substs1_falsum {t p : V} (hv : IsSemiformula ℒₒᵣ 1 p)
    (h : substs1 ℒₒᵣ t p = (^⊥ : V)) : p = (^⊥ : V) := by
  rcases (IsSemiformula.case_iff (L := ℒₒᵣ)).mp hv with
    ⟨k, R, vv, hR, hvv, rfl⟩ | ⟨k, R, vv, hR, hvv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩
  · rw [substs1, substs_rel hR hvv.isUTerm] at h; simp [qqRel, qqFalsum] at h
  · rw [substs1, substs_nrel hR hvv.isUTerm] at h; simp [qqNRel, qqFalsum] at h
  · rw [substs1, substs_verum (L := ℒₒᵣ)] at h; simp [qqVerum, qqFalsum] at h
  · rfl
  · rw [substs1, substs_and h₁.isUFormula h₂.isUFormula] at h; simp [qqAnd, qqFalsum] at h
  · rw [substs1, substs_or h₁.isUFormula h₂.isUFormula] at h; simp [qqOr, qqFalsum] at h
  · rw [substs1, substs_all h₁.isUFormula] at h; simp [qqAll, qqFalsum] at h
  · rw [substs1, substs_ex h₁.isUFormula] at h; simp [qqExs, qqFalsum] at h

/-! ### Descent of the corrected Ind reduct `iIndReductSeqG` at `k = 1` (lap 145)

On a `∅→⊥` orbit the Ind formula collapses to `⊥` (`eq_falsum_of_substs1_falsum`), so EVERY premise of the
Ind reduct carries succedent `⊥` and the exit clause needs no term evaluation — in particular the **`k = 1`**
reduct `iIndReductSeqG d0 d1 a 1 = ⟨d0, d1[a:=0]⟩` already exits at `⊥`. Its `iord` DESCENT (independent of
the antecedent-threading soundness question) reduces to that of the ordinal shadow `iIndReductSeq d0 d1 1 =
⟨d1, d0⟩` (banked `iord_descent_iIndReduct`): both are 2-element sequences over the SAME multiset of premise
ordinals (`idg/iotil` are substitution-invariant, `idg_zsubst`/`iotil_zsubst`), so the folds differ by a
SINGLE `inadd`/`max` commutation — **no `inadd_assoc`** (which the repo lacks for general `k`). -/

private lemma iIndReductSeqG_one (d0 d1 a : V) :
    iIndReductSeqG d0 d1 a 1 = seqCons (seqCons ∅ d0) (zsubst d1 a (Bootstrapping.Arithmetic.numeral 0)) := by
  rw [show (1 : V) = 0 + 1 from (zero_add 1).symm, iIndReductSeqG_succ, iIndReductSeqG_zero]

/-- `idg` of the genuine `k=1` Ind reduct = `idg` of the ordinal shadow (single `max`-commute). -/
private lemma idg_zK_iIndReductSeqG_one_eq {s' p d0 d1 a : V} (hd1 : ZDerivation d1) :
    idg (zK s' (irk p) (iIndReductSeqG d0 d1 a 1)) = idg (zK s' (irk p) (iIndReductSeq d0 d1 1)) := by
  rw [idg_zK _ _ _ (iIndReductSeqG_seq d0 d1 a 1), idg_zK _ _ _ (iIndReductSeq_seq d0 d1 1),
    iseqMaxIdg_iIndReductSeq one_pos, iIndReductSeqG_one,
    iseqMaxIdg_seqCons (seq_empty.seqCons d0), iseqMaxIdg_seqCons seq_empty, iseqMaxIdg_empty,
    idg_zsubst (Bootstrapping.Arithmetic.numeral_uterm 0) a d1 hd1, zero_max, max_comm (idg d0) (idg d1)]

/-- `õ` of the genuine `k=1` Ind reduct = `õ` of the ordinal shadow (single `inadd`-commute). -/
private lemma iotil_zK_iIndReductSeqG_one_eq {s' p d0 d1 a : V}
    (hd0 : ZDerivation d0) (hd1 : ZDerivation d1) :
    iotil (zK s' (irk p) (iIndReductSeqG d0 d1 a 1)) = iotil (zK s' (irk p) (iIndReductSeq d0 d1 1)) := by
  have hd0nf := isNF_iotil_of_ZDerivation d0 hd0
  have hd1nf := isNF_iotil_of_ZDerivation d1 hd1
  rw [iotil_zK _ _ _ (iIndReductSeqG_seq d0 d1 a 1), iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 1),
    iseqNaddIdg_iIndReductSeq one_pos, iIndReductSeqG_one,
    iseqNaddIdg_seqCons (seq_empty.seqCons d0), iseqNaddIdg_seqCons seq_empty, iseqNaddIdg_empty,
    inadd_zero_left, iotil_zsubst (Bootstrapping.Arithmetic.numeral_uterm 0) a d1 hd1,
    inadd_comm (ocOadd (iotil d1) 1 0) (isNF_omega_pow hd1nf) (ocOadd (iotil d0) 1 0)
      (isNF_omega_pow hd0nf)]

/-- **RED-FREE Ind descent at `k = 1`** — `iord (zK s' (irk p) ⟨d0, d1[a:=0]⟩) ≺ iord (Ind^{a,t}_F d0 d1)`.
The genuine substituted reduct's `iord` equals the ordinal shadow's (single `inadd`/`max` commute), so the
banked `iord_descent_iIndReduct` (the shadow LH4 descent) transfers. This is the descent half of
`descent_step_Ind` — proven, RED-FREE, axiom-clean. -/
lemma iord_descent_iIndReductSeqG_one {s s' at' p d0 d1 a : V}
    (hd0 : ZDerivation d0) (hd1 : ZDerivation d1) :
    icmp (iord (zK s' (irk p) (iIndReductSeqG d0 d1 a 1))) (iord (zInd s at' p d0 d1)) = 0 := by
  have hd0nf := isNF_iotil_of_ZDerivation d0 hd0
  have hd1nf := isNF_iotil_of_ZDerivation d1 hd1
  rw [iord, idg_zK_iIndReductSeqG_one_eq hd1, iotil_zK_iIndReductSeqG_one_eq hd0 hd1, ← iord]
  exact iord_descent_iIndReduct hd0nf hd1nf one_pos

/-- **`iRedDescent` BUNDLE form of the `k=1` Ind reduct descent (lap 148).** Same content as
`iord_descent_iIndReductSeqG_one` but as the premise-level descent BUNDLE (`idg ≤`, `õ ≺`, NF) that
`descent_step_K_replace` consumes for a `zInd` major premise: the genuine reduct `zK s' (irk p) ⟨d0, d1[a:=0]⟩`
has the SAME degree as `Ind^{a,t}_F d0 d1` (`idg_zK_iIndReduct` via the `_one_eq` transfer) and strictly lower
`õ` (`icmp_iotil_iIndReduct`), with NF premises. This is the interface that lets the §14.254a `Rep` major-premise
replace (`descent_step_K_replace` at `i = majorIdx`) consume the Ind reduct. -/
lemma iRedDescent_iIndReductSeqG_one {s s' at' p d0 d1 a : V}
    (hd0 : ZDerivation d0) (hd1 : ZDerivation d1) :
    iRedDescent (zK s' (irk p) (iIndReductSeqG d0 d1 a 1)) (zInd s at' p d0 d1) where
  dg_le := by rw [idg_zK_iIndReductSeqG_one_eq hd1]; exact le_of_eq (idg_zK_iIndReduct one_pos)
  otil_lt := by
    rw [iotil_zK_iIndReductSeqG_one_eq hd0 hd1, iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 1)]
    exact icmp_iotil_iIndReduct (isNF_iotil_of_ZDerivation d0 hd0)
      (isNF_iotil_of_ZDerivation d1 hd1) one_pos
  nf := by
    refine isNF_iotil_zK (iIndReductSeqG_seq d0 d1 a 1) (fun i hi => ?_)
    rw [iIndReductSeqG_lh, one_add_one_eq_two] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [znth_iIndReductSeqG_zero]; exact isNF_iotil_of_ZDerivation d0 hd0
    · have h := znth_iIndReductSeqG_step d0 d1 a 1 0 one_pos
      rw [zero_add] at h
      rw [h, iotil_zsubst (Bootstrapping.Arithmetic.numeral_uterm 0) a d1 hd1]
      exact isNF_iotil_of_ZDerivation d1 hd1

/-- **Ind root (Buchholz §3.2 case 4 / Def 3.2 clause `Ind`) — the RED-FREE existence-form reduct (lap 144,
named sub-`sorry`).** A `∅→⊥` Ind node `zInd s at' p d0 d1` has a sound, strictly-`iord`-descending
`ZDerivesEmptyR` reduct WITHOUT `red`. The genuine witness is the **corrected substituted chain**
`zK s (irk p) (iIndReductSeqG d0 d1 a k)` (lap-136), `a = π₁ at'` the eigenvariable and `k = value of the
Ind term t = π₂ at'`: premises `⟨d0, d1[a:=0], …, d1[a:=k-1]⟩`, exit premise `k` carrying `F(k) = F(t) = ⊥`.
This REPLACES the lap-141 regression `⟨red d, ZDerivesEmptyR_red hd, …⟩`, whose soundness `ZDerivesEmptyR_red`
routes through the kernel-FALSE `redSoundGen` (:1471) → `zKValidF_iIndReduct_of_zInd` (:80, the lap-136
obstruction: the `k=1` shadow `⟨d1,d0⟩` is NOT valid). Wiring this drops the LAST `red`-soundness dependence
on the live `false_of_ZDerivesEmpty` path (K-case already off `red`, laps 143/144).

**STATUS after lap 145 — DESCENT done, `k=⟦t⟧` blocker DISSOLVED, soundness blocked on a `zIndWff` gap.**
Witness pinned to `k = 1`: `zK s (irk p) (iIndReductSeqG d0 d1 (π₁ at') 1) = ⟨d0, d1[a:=0]⟩` (2-element).

1. **`k = ⟦t⟧` blocker DISSOLVED (lap 145).** On the `∅→⊥` orbit, `zIndWff` gives `seqSucc s = substs1 t p`
   and the orbit gives `seqSucc s = ⊥`, so `substs1 t p = ⊥` ⟹ **`p = ⊥`** (`eq_falsum_of_substs1_falsum`).
   Then EVERY premise of the reduct carries succedent `substs1 _ ⊥ = ⊥`, so the `hexit` clause holds for ANY
   `k` (in particular `k = 1`) — no internal term-evaluation `k = ⟦t⟧` needed. The lap-144 "lone genuine
   prerequisite" was a phantom on the ⊥-orbit.
2. **DESCENT done (lap 145, `iord_descent_iIndReductSeqG_one`, axiom-clean).** `icmp (iord (zK s (irk p)
   (iIndReductSeqG d0 d1 (π₁ at') 1))) (iord (zInd …)) = 0`. The genuine substituted `k=1` reduct's `iord`
   equals the ordinal shadow `iIndReductSeq d0 d1 1 = ⟨d1,d0⟩`'s (single `inadd`/`max` commute — both
   2-element over the same premise-ordinal multiset, `idg/iotil` substitution-invariant; **no `inadd_assoc`**,
   which the repo lacks for general `k`), so the banked shadow LH4 descent `iord_descent_iIndReduct` transfers.
3. **SOUNDNESS — `zIndWff` antecedent-shape gap CLOSED (lap 146, commit `a2b2a3a`).** The lap-145 finding
   (the step clause was MEMBERSHIP `inAnt (F(a)) (seqAnt(fstIdx d1))`, admitting unsound lax nodes whose reduct
   does not thread) has been FIXED: `zIndWff`'s step clause is now SHAPE
   `Seq (seqAnt (fstIdx d)) ∧ seqAnt(fstIdx prem1) = seqCons (seqAnt(fstIdx d)) (F(a))` (faithful Buchholz Ind
   rule; `Seq` bundled like lap-118 `zInegAntWff` for self-preservation under eigensubst). So
   `zDerivation_zInd_inv` now yields, on the ⊥-orbit (Γ=∅, p=⊥ via `eq_falsum_of_substs1_falsum`):
   `seqAnt(fstIdx d1) = seqCons ∅ ⊥ = {⊥}` EXACTLY. **REMAINING = the soundness ASSEMBLY** (the genuine
   remaining work, ~one focused lap). Witness `zK s (irk p) (iIndReductSeqG d0 d1 (π₁ at') 1)`. Mirror the
   `descent_step_K_critical_all` (:2034) template: ZDerivesEmptyR = ⟨⟨ZDerivation via `zDerivation_zK_intro`
   (`hseq=iIndReductSeqG_seq`, premise `ZDerivation`s = d0 + `ZDerivation_zsubst d1` with `maxEigen d1 < π₁ at'`
   from `ZRegular`, `zKValidF` = `isChainInf_telescope` :169 + per-premise iperm `iperm_tp_fstIdx_of_ZDerivation`
   :5784 + the tag-{1,2,5,6} UFormula conds), fstIdx=∅→⊥⟩, `ZRegular_zK_of_premises`, `zfresh_zK_of`,
   `zSeqAnt_zK_of`⟩ + DESCENT `iord_descent_iIndReductSeqG_one` (banked). On the ⊥-orbit the telescope collapses
   (all antecedents `{⊥}`, succedents `⊥`, exit `j0=1` at `⊥`). See `PENDING_WORK.md` lap-146. -/
theorem descent_step_Ind {s at' p d0 d1 : V} (hd : ZDerivesEmptyR (zInd s at' p d0 d1)) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zInd s at' p d0 d1)) = 0 := by
  -- ⊥-orbit data
  have hZ : ZDerivation (zInd s at' p d0 d1) := hd.1.1
  have hant : seqAnt s = (∅ : V) := by have h := hd.1.2.1; rwa [fstIdx_zInd] at h
  have hsucc : seqSucc s = (^⊥ : V) := by have h := hd.1.2.2; rwa [fstIdx_zInd] at h
  obtain ⟨hd0Z, hd1Z, hwff⟩ := zDerivation_zInd_inv hZ
  simp only [zIndWff, zIndEig_zInd, zIndTerm_zInd, zIndP_zInd, zIndPrem0_zInd, zIndPrem1_zInd,
    fstIdx_zInd] at hwff
  obtain ⟨⟨h1a, h1b⟩, ⟨_h2seq, h2a, h2b⟩, h3, h4, _h5⟩ := hwff
  -- the Ind formula collapses to ⊥
  have hp_bot : p = (^⊥ : V) := eq_falsum_of_substs1_falsum h4 (h3 ▸ hsucc)
  subst hp_bot
  have hsubbot : ∀ t : V, substs1 ℒₒᵣ t (^⊥ : V) = (^⊥ : V) := fun t => by
    rw [substs1]; exact substs_falsum _
  -- premise invariants extracted from the regular/fresh/seqAnt-clean Ind node
  have hmaxlt : maxEigen d1 < π₁ at' := by
    have h : zReg (zInd s at' (^⊥) d0 d1) = 0 := hd.2.1
    rw [zReg_zInd] at h; exact ltFlag_eq_zero_iff.mp (nonpos_iff_eq_zero.mp (h ▸ le_max_left _ _))
  have hreg1 : ZRegular d1 := by
    have h : zReg (zInd s at' (^⊥) d0 d1) = 0 := hd.2.1
    rw [zReg_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_right _ _) (le_max_right _ _))
  have hreg0 : ZRegular d0 := by
    have h : zReg (zInd s at' (^⊥) d0 d1) = 0 := hd.2.1
    rw [zReg_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_left _ _) (le_max_right _ _))
  have hfr1 : ZFresh d1 := by
    have h : zFresh (zInd s at' (^⊥) d0 d1) = 0 := hd.2.2.1
    rw [zFresh_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_right _ _) (le_max_right _ _))
  have hfr0 : ZFresh d0 := by
    have h : zFresh (zInd s at' (^⊥) d0 d1) = 0 := hd.2.2.1
    rw [zFresh_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_left _ _) (le_max_right _ _))
  have hsa1 : ZSeqAnt d1 := by
    have h : zSeqAnt (zInd s at' (^⊥) d0 d1) = 0 := hd.2.2.2
    rw [zSeqAnt_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_right _ _) (le_max_right _ _))
  have hsa0 : ZSeqAnt d0 := by
    have h : zSeqAnt (zInd s at' (^⊥) d0 d1) = 0 := hd.2.2.2
    rw [zSeqAnt_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_left _ _) (le_max_right _ _))
  -- the corrected k=1 Ind reduct `⟨d0, d1[a:=0]⟩`
  set ds := iIndReductSeqG d0 d1 (π₁ at') 1 with hds_def
  have hds_seq : Seq ds := iIndReductSeqG_seq d0 d1 (π₁ at') 1
  have hds_lh1 : lh ds = 1 + 1 := by rw [hds_def, iIndReductSeqG_lh]
  have hds_lh : lh ds = 2 := by rw [hds_lh1, one_add_one_eq_two]
  have hz0 : znth ds 0 = d0 := znth_iIndReductSeqG_zero d0 d1 (π₁ at') 1
  have hz1 : znth ds 1 = zsubst d1 (π₁ at') (Bootstrapping.Arithmetic.numeral 0) := by
    have h := znth_iIndReductSeqG_step d0 d1 (π₁ at') 1 0 one_pos
    rw [zero_add] at h; rw [hds_def]; exact h
  have ht0 : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral 0 : V) := by simp
  have hZ1sub : ZDerivation (zsubst d1 (π₁ at') (Bootstrapping.Arithmetic.numeral 0)) :=
    ZDerivation_zsubst ht0 d1 hd1Z hmaxlt
  have hmem : ∀ i < lh ds, ZDerivation (znth ds i) := by
    intro i hi
    rw [hds_lh] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [hz0]; exact hd0Z
    · rw [hz1]; exact hZ1sub
  -- ⊥-orbit collapse of the chain end-sequents
  have hF0 : chainAsucc ds 0 = (^⊥ : V) := by
    simp only [chainAsucc]; rw [hz0, h1b, hsubbot]
  have hExit : chainAsucc ds 1 = (^⊥ : V) := by
    simp only [chainAsucc]
    rw [hz1, fstIdx_zsubst (π₁ at') (Bootstrapping.Arithmetic.numeral 0) hd1Z,
      seqSucc_fvSubstSeqt, h2b, hsubbot, fvSubst_falsum (L := ℒₒᵣ)]
  have hAnt1 : ∀ B, inAnt B (chainAnt ds 1) → B = (^⊥ : V) := by
    intro B hB
    simp only [chainAnt] at hB
    rw [hz1, fstIdx_zsubst (π₁ at') (Bootstrapping.Arithmetic.numeral 0) hd1Z,
      seqAnt_fvSubstSeqt, h2a, hant, hsubbot,
      fvSubstSeq_seqCons seq_empty, fvSubst_falsum (L := ℒₒᵣ)] at hB
    rcases (inAnt_seqCons (fvSubstSeq_seq (π₁ at') (Bootstrapping.Arithmetic.numeral 0) ∅)).mp hB
      with h | h
    · exact h
    · obtain ⟨i, hi, _⟩ := h; rw [fvSubstSeq_lh, lh_empty] at hi; exact absurd hi (by simp)
  have hUbot : IsUFormula ℒₒᵣ (^⊥ : V) := by simp
  -- the chain is `zKValidF`-valid (telescope + uniform leaf side-conditions)
  have hvalidF : zKValidF s (irk (^⊥ : V)) ds := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine isChainInf_telescope (k := 1) hds_lh1 ?_ ?_ ?_ ?_
      · intro B hB; simp only [chainAnt] at hB; rw [hz0, h1a] at hB; exact hB
      · intro i hi B hB
        obtain rfl : i = 0 := by
          rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp (hi.trans one_lt_two)) with h | h
          · exact h
          · exact absurd hi (by rw [h]; simp)
        rw [zero_add] at hB
        exact Or.inr ((hAnt1 B hB).trans hF0.symm)
      · exact Or.inr hExit
      · intro i hi
        obtain rfl : i = 0 := by
          rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp (hi.trans one_lt_two)) with h | h
          · exact h
          · exact absurd hi (by rw [h]; simp)
        rw [hF0]
    · exact fun i hi => iperm_tp_fstIdx_of_ZDerivation (hmem i hi)
    · exact fun i hi => (zKValidF_leafconds_of_ZDerivation (hmem i hi)).1
    · exact fun i hi => (zKValidF_leafconds_of_ZDerivation (hmem i hi)).2.1
    · exact fun i hi => (zKValidF_leafconds_of_ZDerivation (hmem i hi)).2.2.1
    · exact fun i hi => (zKValidF_leafconds_of_ZDerivation (hmem i hi)).2.2.2
    · intro i hi
      rw [hds_lh] at hi
      rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
      · rw [hF0]; exact hUbot
      · rw [hExit]; exact hUbot
    · rw [hsucc]; exact hUbot
    · intro k hk; rw [hant, lh_empty] at hk; exact absurd hk (by simp)
  -- assemble the descending `ZDerivesEmptyR` reduct
  refine ⟨zK s (irk (^⊥ : V)) ds, ⟨⟨zDerivation_zK_intro hds_seq hmem hvalidF, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [fstIdx_zK]; exact hant
  · rw [fstIdx_zK]; exact hsucc
  · show ZRegular (zK _ _ _)
    refine ZRegular_zK_of_premises hds_seq (fun i hi => ?_)
    rw [hds_lh] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [hz0]; exact hreg0
    · rw [hz1]; show zReg _ = 0; rw [zReg_zsubst _ _ d1 hd1Z]; exact hreg1
  · show zFresh (zK _ _ _) = 0
    refine zfresh_zK_of hds_seq (fun i hi => ?_)
    rw [hds_lh] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [hz0]; exact hfr0
    · rw [hz1]; exact zFresh_zsubst (π₁ at') 0 d1 hd1Z hfr1
  · show zSeqAnt (zK _ _ _) = 0
    refine zSeqAnt_zK_of hds_seq
      (seqAntSeqFlag_eq_zero_iff.mpr (by rw [hant]; exact seq_empty)) (fun i hi => ?_)
    rw [hds_lh] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [hz0]; exact hsa0
    · rw [hz1]; exact zSeqAnt_zsubst (π₁ at') _ d1 hd1Z
  · rw [hds_def]; exact iord_descent_iIndReductSeqG_one hd0Z hd1Z

/-- **§14.254a Ind reduct, GENERALIZED off `Γ=∅` (lap 148) — the `ZDerivation`-valued `Γₘ→⊥` Ind reduct.**
The major-premise (`zInd`) generalization of `descent_step_Ind`: a `zInd s at' p d0 d1` deriving `Γₘ→⊥`
(`seqSucc s = ⊥`, `Γₘ = seqAnt s` possibly NONEMPTY), regular/fresh/seqAnt, with the eigenvariable `π₁ at'`
FRESH in the conclusion antecedent (`freshFlag (π₁ at') p Γₘ = 0` — the I∀-style eigenvariable condition the
Ind rule requires; `zFresh_zInd` does not yet carry it, see PENDING_WORK), has its genuine `k=1` reduct
`v = zK s (irk p) ⟨d0, d1[a:=0]⟩` as a SAME-end-sequent (`fstIdx v = s`) strictly-`iord`-descending
(`iRedDescent`) regular/fresh/seqAnt `ZDerivation`. The freshness collapses the reduct's step-premise antecedent
`fvSubstSeq a 0 (seqCons Γₘ ⊥)` to `seqCons Γₘ ⊥` (the telescope threads `Γₘ` faithfully) and supplies the
conclusion-antecedent well-formedness (`freshFlag_wff`). Feeds `descent_step_K_replace` at `i = majorIdx` to
discharge the tag-3 half of `descent_step_K_noncrit_repMajor`. -/
lemma ind_reduct_botSucc_of_fresh {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1))
    (hreg : ZRegular (zInd s at' p d0 d1)) (hfresh : ZFresh (zInd s at' p d0 d1))
    (hseqant : ZSeqAnt (zInd s at' p d0 d1))
    (hsucc : seqSucc s = (^⊥ : V))
    (hfreshΓ : freshFlag (π₁ at') (^⊥ : V) (seqAnt s) = 0) :
    ∃ v, ZDerivation v ∧ ZRegular v ∧ ZFresh v ∧ ZSeqAnt v ∧ fstIdx v = s ∧
      iRedDescent v (zInd s at' p d0 d1) := by
  obtain ⟨hd0Z, hd1Z, hwff⟩ := zDerivation_zInd_inv hZ
  simp only [zIndWff, zIndEig_zInd, zIndTerm_zInd, zIndP_zInd, zIndPrem0_zInd, zIndPrem1_zInd,
    fstIdx_zInd] at hwff
  obtain ⟨⟨h1a, h1b⟩, ⟨_h2seq, h2a, h2b⟩, h3, h4, _h5⟩ := hwff
  have hp_bot : p = (^⊥ : V) := eq_falsum_of_substs1_falsum h4 (h3 ▸ hsucc)
  subst hp_bot
  have hsubbot : ∀ t : V, substs1 ℒₒᵣ t (^⊥ : V) = (^⊥ : V) := fun t => by
    rw [substs1]; exact substs_falsum _
  have hfreshΓeq : fvSubstSeq (π₁ at') (Bootstrapping.Arithmetic.numeral 0) (seqAnt s) = seqAnt s :=
    freshFlag_snd hfreshΓ
  have hmaxlt : maxEigen d1 < π₁ at' := by
    have h : zReg (zInd s at' (^⊥) d0 d1) = 0 := hreg
    rw [zReg_zInd] at h; exact ltFlag_eq_zero_iff.mp (nonpos_iff_eq_zero.mp (h ▸ le_max_left _ _))
  have hreg1 : ZRegular d1 := by
    have h : zReg (zInd s at' (^⊥) d0 d1) = 0 := hreg
    rw [zReg_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_right _ _) (le_max_right _ _))
  have hreg0 : ZRegular d0 := by
    have h : zReg (zInd s at' (^⊥) d0 d1) = 0 := hreg
    rw [zReg_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_left _ _) (le_max_right _ _))
  have hfr1 : ZFresh d1 := by
    have h : zFresh (zInd s at' (^⊥) d0 d1) = 0 := hfresh
    rw [zFresh_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_right _ _) (le_max_right _ _))
  have hfr0 : ZFresh d0 := by
    have h : zFresh (zInd s at' (^⊥) d0 d1) = 0 := hfresh
    rw [zFresh_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_left _ _) (le_max_right _ _))
  have hsa1 : ZSeqAnt d1 := by
    have h : zSeqAnt (zInd s at' (^⊥) d0 d1) = 0 := hseqant
    rw [zSeqAnt_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_right _ _) (le_max_right _ _))
  have hsa0 : ZSeqAnt d0 := by
    have h : zSeqAnt (zInd s at' (^⊥) d0 d1) = 0 := hseqant
    rw [zSeqAnt_zInd] at h
    exact nonpos_iff_eq_zero.mp (h ▸ le_trans (le_max_left _ _) (le_max_right _ _))
  set ds := iIndReductSeqG d0 d1 (π₁ at') 1 with hds_def
  have hds_seq : Seq ds := iIndReductSeqG_seq d0 d1 (π₁ at') 1
  have hds_lh1 : lh ds = 1 + 1 := by rw [hds_def, iIndReductSeqG_lh]
  have hds_lh : lh ds = 2 := by rw [hds_lh1, one_add_one_eq_two]
  have hz0 : znth ds 0 = d0 := znth_iIndReductSeqG_zero d0 d1 (π₁ at') 1
  have hz1 : znth ds 1 = zsubst d1 (π₁ at') (Bootstrapping.Arithmetic.numeral 0) := by
    have h := znth_iIndReductSeqG_step d0 d1 (π₁ at') 1 0 one_pos
    rw [zero_add] at h; rw [hds_def]; exact h
  have ht0 : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral 0 : V) := by simp
  have hZ1sub : ZDerivation (zsubst d1 (π₁ at') (Bootstrapping.Arithmetic.numeral 0)) :=
    ZDerivation_zsubst ht0 d1 hd1Z hmaxlt
  have hmem : ∀ i < lh ds, ZDerivation (znth ds i) := by
    intro i hi
    rw [hds_lh] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [hz0]; exact hd0Z
    · rw [hz1]; exact hZ1sub
  have hF0 : chainAsucc ds 0 = (^⊥ : V) := by
    simp only [chainAsucc]; rw [hz0, h1b, hsubbot]
  have hExit : chainAsucc ds 1 = (^⊥ : V) := by
    simp only [chainAsucc]
    rw [hz1, fstIdx_zsubst (π₁ at') (Bootstrapping.Arithmetic.numeral 0) hd1Z,
      seqSucc_fvSubstSeqt, h2b, hsubbot, fvSubst_falsum (L := ℒₒᵣ)]
  have hAnt1 : ∀ B, inAnt B (chainAnt ds 1) → inAnt B (seqAnt s) ∨ B = (^⊥ : V) := by
    intro B hB
    simp only [chainAnt] at hB
    rw [hz1, fstIdx_zsubst (π₁ at') (Bootstrapping.Arithmetic.numeral 0) hd1Z,
      seqAnt_fvSubstSeqt, h2a, hsubbot, fvSubstSeq_seqCons _h2seq, fvSubst_falsum (L := ℒₒᵣ),
      hfreshΓeq] at hB
    exact ((inAnt_seqCons _h2seq).mp hB).symm
  have hUbot : IsUFormula ℒₒᵣ (^⊥ : V) := by simp
  have hvalidF : zKValidF s (irk (^⊥ : V)) ds := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine isChainInf_telescope (k := 1) hds_lh1 ?_ ?_ ?_ ?_
      · intro B hB; simp only [chainAnt] at hB; rw [hz0, h1a] at hB; exact hB
      · intro i hi B hB
        obtain rfl : i = 0 := by
          rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp (hi.trans one_lt_two)) with h | h
          · exact h
          · exact absurd hi (by rw [h]; simp)
        rw [zero_add] at hB
        rcases hAnt1 B hB with h | h
        · exact Or.inl h
        · exact Or.inr (h.trans hF0.symm)
      · exact Or.inr hExit
      · intro i hi
        obtain rfl : i = 0 := by
          rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp (hi.trans one_lt_two)) with h | h
          · exact h
          · exact absurd hi (by rw [h]; simp)
        rw [hF0]
    · exact fun i hi => iperm_tp_fstIdx_of_ZDerivation (hmem i hi)
    · exact fun i hi => (zKValidF_leafconds_of_ZDerivation (hmem i hi)).1
    · exact fun i hi => (zKValidF_leafconds_of_ZDerivation (hmem i hi)).2.1
    · exact fun i hi => (zKValidF_leafconds_of_ZDerivation (hmem i hi)).2.2.1
    · exact fun i hi => (zKValidF_leafconds_of_ZDerivation (hmem i hi)).2.2.2
    · intro i hi
      rw [hds_lh] at hi
      rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
      · rw [hF0]; exact hUbot
      · rw [hExit]; exact hUbot
    · rw [hsucc]; exact hUbot
    · exact freshFlag_wff hfreshΓ
  refine ⟨zK s (irk (^⊥ : V)) ds, zDerivation_zK_intro hds_seq hmem hvalidF, ?_, ?_, ?_, ?_, ?_⟩
  · show ZRegular (zK _ _ _)
    refine ZRegular_zK_of_premises hds_seq (fun i hi => ?_)
    rw [hds_lh] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [hz0]; exact hreg0
    · rw [hz1]; show zReg _ = 0; rw [zReg_zsubst _ _ d1 hd1Z]; exact hreg1
  · show zFresh (zK _ _ _) = 0
    refine zfresh_zK_of hds_seq (fun i hi => ?_)
    rw [hds_lh] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [hz0]; exact hfr0
    · rw [hz1]; exact zFresh_zsubst (π₁ at') 0 d1 hd1Z hfr1
  · show zSeqAnt (zK _ _ _) = 0
    refine zSeqAnt_zK_of hds_seq
      (by have h : zSeqAnt (zInd s at' (^⊥) d0 d1) = 0 := hseqant
          rw [zSeqAnt_zInd] at h; exact nonpos_iff_eq_zero.mp (h ▸ le_max_left _ _))
      (fun i hi => ?_)
    rw [hds_lh] at hi
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl
    · rw [hz0]; exact hsa0
    · rw [hz1]; exact zSeqAnt_zsubst (π₁ at') _ d1 hd1Z
  · rw [fstIdx_zK]
  · rw [hds_def]; exact iRedDescent_iIndReductSeqG_one hd0Z hd1Z

/-! ### No-redex residual — the §14.254 major-premise dichotomy (lap 148)

With NO redex pair below the exit `j0`, Buchholz §14.25 dispatches on `tp(dₘ)` (the major premise's OWN
reduction type) — equivalently, on its constructor tag (`majorPrem_tag_mem` ⟹ tag ∈ {3,4,5,6}):

- **§14.254a `repMajor` (tags 3,4):** the major premise `dₘ = znth ds m` (`m = majorIdx`) is a `zInd` (tag 3,
  whose Ind-unfolding reduction is `Rep`) or a sub-`zK` (tag 4, `Rep` when its own major premise is `Rep`).
  `tp(dₘ) = Rep`, so `dₘ`'s reduct `dₘ[0]` has the SAME end-sequent `Γₘ→⊥` — feed it to `descent_step_K_replace`
  at `i = m`. (Caveat tag-4: if the sub-chain L-reduces, `tp(dₘ) ≠ Rep` and it falls to §14.254b on the
  cut-partner — handled there.)
- **§14.254b `axMajor` (tags 5,6):** the major premise is an L-axiom `zAxAll`/`zAxNeg` (a `red`-FIXPOINT,
  `tp(dₘ) = Lk_V`). Its active formula `V` (`^∀p`/`inegF p`) is NOT in `Θ = ∅`, so it agrees with the succedent
  of a strictly-earlier premise `i′` (`majorPrem_zAxAll_cutPartner`/`_zAxNeg_cutPartner`). Since there is NO
  redex, `i′` is NOT a direct R-introduction (else `⟪i′,m⟫` is a redex pair `≤ j0`), so `tp(d_{i′}) = Rep` and
  `d_{i′}`'s reduct has the same end-sequent — feed it to `descent_step_K_replace` at `i = i′`.

BOTH bottom out in producing the `Rep`-reduct of a structurally-smaller premise (`dₘ` or `d_{i′}`) deriving
`Γ′→⊥` with `Γ′` possibly nonempty — the GENERAL `Γ→⊥` reduction, closure via strong induction on the
derivation CODE (Buchholz Theorem 2.1; NOT `iord`-recursion — that is PRWO/Gödel-barred). The surrounding
replace plumbing is now discharged by `descent_step_K_replace`; the lone genuine residual of each is the
smaller-premise reduct. -/

/-- **Structured §14.254 reduct certificate (lap-151).** The FAITHFUL conclusion of the general
`Γ→⊥` reduction `genReduct_botSucc`: a `Rep` node `d`'s reduct is EITHER (`Or.inl`) a single
same-end-sequent `õ`-dropping REPLACE reduct `v` (`iRedDescent`; the non-principal cases, spliced via
`descent_step_K_replace`), OR (`Or.inr`) the two FLATTEN halves `a = dⱼ{0} ⊢ Γ→B`, `b = dⱼ{1} ⊢ B,Γ→A`
of `d`'s OWN principal cut (the §14.253 sub-case; spliced via `descent_step_K_spliceHalves`). The flatten
branch is forced when `d`'s reduct degree-trades (`õ` RISES): a bare same-end-sequent replace is then
NON-descending (lap-151 in-kernel finding, judge `E-2026-06-26-JUDGE-splice-flatten-not-seqUpdate.md`).
BOTH branches carry `õ`-STRICT-drop on the spliced object(s) (`iRedDescent`/`icmp (iotil _) (iotil d)=0`),
so the outer splice always lands in the `õ`-fold-drop engine, never the false degree-trade `seqUpdate`
monotonicity. The `∀ B`-threading is in the BOUNDED `∀ k < lh` form to keep the recursion motive `𝚺₁`
(`GenReductCert = certReplace ∨ certFlatten`, split so each branch's definability is provable separately). -/
abbrev certReplace (d : V) : Prop :=
  ∃ v, ZDerivation v ∧ ZRegular v ∧ ZFresh v ∧ ZSeqAnt v ∧
      fstIdx v = fstIdx d ∧ iRedDescent v d

/-- FLATTEN branch: the two principal-cut halves of `d` (cut-pair end-sequents + `õ`-drop). -/
abbrev certFlatten (d : V) : Prop :=
  ∃ a b, ZDerivation a ∧ ZDerivation b ∧
      ZRegular a ∧ ZRegular b ∧ ZFresh a ∧ ZFresh b ∧ ZSeqAnt a ∧ ZSeqAnt b ∧
      seqAnt (fstIdx a) = seqAnt (fstIdx d) ∧ seqSucc (fstIdx b) = seqSucc (fstIdx d) ∧
      (∀ k < lh (seqAnt (fstIdx b)),
          znth (seqAnt (fstIdx b)) k = seqSucc (fstIdx a) ∨
          ∃ i < lh (seqAnt (fstIdx d)),
            znth (seqAnt (fstIdx d)) i = znth (seqAnt (fstIdx b)) k) ∧
      IsUFormula ℒₒᵣ (seqSucc (fstIdx a)) ∧ IsUFormula ℒₒᵣ (seqSucc (fstIdx b)) ∧
      irk (seqSucc (fstIdx a)) + 1 ≤ idg d ∧
      icmp (iotil a) (iotil d) = 0 ∧ icmp (iotil b) (iotil d) = 0 ∧
      idg a ≤ idg d ∧ idg b ≤ idg d

def GenReductCert (d : V) : Prop := certReplace d ∨ certFlatten d

set_option maxHeartbeats 1600000 in
instance certReplace_definable : 𝚺₁-Predicate (certReplace : V → Prop) := by
  unfold certReplace ZRegular ZFresh ZSeqAnt
  simp only [iRedDescent_iff]
  definability

set_option maxHeartbeats 1600000 in
instance certFlatten_definable : 𝚺₁-Predicate (certFlatten : V → Prop) := by
  unfold certFlatten ZRegular ZFresh ZSeqAnt; definability

/-- The structured certificate is `𝚺₁`-definable — each branch isolated (so the motive stays cheap). -/
instance GenReductCert_definable : 𝚺₁-Predicate (GenReductCert : V → Prop) := by
  unfold GenReductCert; exact certReplace_definable.or certFlatten_definable

/-- **Shared FLATTEN-cert assembler from a critical-cut reduct's two principal-cut halves (lap 153).**
The reduct `iRKcCrit (zK s r ds)` is, by construction, `zK s (r−1) (iCritReductSeq a b)` whose two
premises `a ⊢ Γ→C`, `b ⊢ C,Γ→⊥` (`C = cutFormula`, `fstIdx a = seqSetSucc s C`, `fstIdx b = seqAddAnt C s`)
ARE the FLATTEN halves the `GenReductCert`'s `Or.inr` branch wants. The four per-half invariants are
extracted from the reduct's own `ZDerivation`/`ZRegular`/`ZFresh`/`ZSeqAnt` by premise-inversion
(`zDerivation_zK_inv` / `*_zK_premise` at indices `0`,`1` of `iCritReductSeq`); the end-sequent / threading
data fall out of `seqAnt_seqSetSucc` / `seqSucc_seqAddAnt` / `inAnt_seqAddAnt`; the cut formula's wff and
the rank-drop `irk C + 1 ≤ idg d` and the N2 `õ`/`idg` descent facts are supplied by the caller. **Polarity
-agnostic:** the ∀- and ¬-cases (`iRcritG`/`iRcritGNeg`) differ only in which premise each half replaces, but
present identical end-sequent shapes here, so both feed this one assembler. -/
lemma certFlatten_of_critHalves {s r ds a b C : V}
    (hZcrit : ZDerivation (zK s (r - 1) (iCritReductSeq a b)))
    (hregcrit : ZRegular (zK s (r - 1) (iCritReductSeq a b)))
    (hfreshcrit : ZFresh (zK s (r - 1) (iCritReductSeq a b)))
    (hseqantcrit : ZSeqAnt (zK s (r - 1) (iCritReductSeq a b)))
    (ha_fst : fstIdx a = seqSetSucc s C) (hb_fst : fstIdx b = seqAddAnt C s)
    (hSwff : IsUFormula ℒₒᵣ (seqSucc s)) (hSeqs : Seq (seqAnt s))
    (hCwff : IsUFormula ℒₒᵣ C) (hCrk : irk C + 1 ≤ idg (zK s r ds))
    (ha_otil : icmp (iotil a) (iotil (zK s r ds)) = 0)
    (hb_otil : icmp (iotil b) (iotil (zK s r ds)) = 0)
    (ha_idg : idg a ≤ idg (zK s r ds)) (hb_idg : idg b ≤ idg (zK s r ds)) :
    GenReductCert (zK s r ds) := by
  have hseq2 : Seq (iCritReductSeq a b) := iCritReductSeq_seq a b
  have h0lt : (0 : V) < lh (iCritReductSeq a b) := by rw [iCritReductSeq_lh]; exact zero_lt_two
  have h1lt : (1 : V) < lh (iCritReductSeq a b) := by rw [iCritReductSeq_lh]; exact one_lt_two
  have hZa : ZDerivation a := by
    have h := (zDerivation_zK_inv hZcrit).2 0 h0lt; rwa [znth_iCritReductSeq_zero] at h
  have hZb : ZDerivation b := by
    have h := (zDerivation_zK_inv hZcrit).2 1 h1lt; rwa [znth_iCritReductSeq_one] at h
  have hrega : ZRegular a := by
    have h := ZRegular_zK_premise hseq2 hregcrit h0lt; rwa [znth_iCritReductSeq_zero] at h
  have hregb : ZRegular b := by
    have h := ZRegular_zK_premise hseq2 hregcrit h1lt; rwa [znth_iCritReductSeq_one] at h
  have hfresha : ZFresh a := by
    have h := ZFresh_zK_premise hseq2 hfreshcrit h0lt; rwa [znth_iCritReductSeq_zero] at h
  have hfreshb : ZFresh b := by
    have h := ZFresh_zK_premise hseq2 hfreshcrit h1lt; rwa [znth_iCritReductSeq_one] at h
  have hseqanta : ZSeqAnt a := by
    have h := ZSeqAnt_zK_premise hseq2 hseqantcrit h0lt; rwa [znth_iCritReductSeq_zero] at h
  have hseqantb : ZSeqAnt b := by
    have h := ZSeqAnt_zK_premise hseq2 hseqantcrit h1lt; rwa [znth_iCritReductSeq_one] at h
  refine Or.inr ⟨a, b, hZa, hZb, hrega, hregb, hfresha, hfreshb, hseqanta, hseqantb,
    ?_, ?_, ?_, ?_, ?_, ?_, ha_otil, hb_otil, ha_idg, hb_idg⟩
  · -- seqAnt (fstIdx a) = seqAnt (fstIdx d)
    rw [ha_fst, seqAnt_seqSetSucc, fstIdx_zK]
  · -- seqSucc (fstIdx b) = seqSucc (fstIdx d)
    rw [hb_fst, seqSucc_seqAddAnt, fstIdx_zK]
  · -- threading: every antecedent formula of `b` is the cut formula `C = seqSucc (fstIdx a)` or in `Γ`
    intro k hk
    rw [hb_fst] at hk ⊢
    rw [fstIdx_zK]
    have hin : inAnt (znth (seqAnt (seqAddAnt C s)) k) (seqAnt (seqAddAnt C s)) := ⟨k, hk, rfl⟩
    rcases (inAnt_seqAddAnt hSeqs).mp hin with h | h
    · left; rw [ha_fst, seqSucc_seqSetSucc]; exact h
    · right; exact h
  · -- IsUFormula (seqSucc (fstIdx a)) = IsUFormula C
    rw [ha_fst, seqSucc_seqSetSucc]; exact hCwff
  · -- IsUFormula (seqSucc (fstIdx b)) = IsUFormula (seqSucc s)
    rw [hb_fst, seqSucc_seqAddAnt]; exact hSwff
  · -- irk (seqSucc (fstIdx a)) + 1 ≤ idg d
    rw [ha_fst, seqSucc_seqSetSucc]; exact hCrk

/-- **has-redex leaf of the §14.254 chain reduction (`Γ→⊥`, FLATTEN certificate) — NAMED
sub-`sorry`.** A `zK s r ds` chain deriving `Γ→⊥` with a redex pair `⟪i0,j1⟫` below its `isChainInf`
⊥-exit `j0` has the criticality-free principal-cut reduct `iRKcCrit (zK s r ds)` as a SAME-end-sequent
strictly-`iord`-descending regular/fresh/seqAnt `ZDerivation`. ⚠️ **`iord`, NOT `iRedDescent`** (lap-150
in-kernel finding, judge-confirmed): the principal cut drops via the DEGREE
(`idg_zK_iCritReduct_lt`, `idg+1 ≤ idg d`), NOT via `iotil` (`iord_descent_cut`'s `iotil` premise is against
`ω^{õ d}`, weaker than against `õ d`) — so `iRedDescent` (which demands `õ(reduct) ≺ õ d`) is FALSE here.
The descent half is FREE from the EXISTING `iord_descent_iRKcCrit_corr_of_redex`/`_neg_of_redex`
(`:2245`/`:2282`); the residual is soundness `ZDerivation_iRKcCrit_all`/`_neg_botOrbit` (needs
`Seq (seqAnt s)`, the tag-4-chain gap) + `ZRegular/ZFresh/ZSeqAnt_iRKcCrit`. -/
lemma genReduct_chain_hasRedex {s r ds i0 j1 j0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hreg : ZRegular (zK s r ds)) (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (hsucc : seqSucc s = (^⊥ : V))
    (hj0 : j0 < lh ds) (hbot0 : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hij : i0 < j1) (hj1 : j1 ≤ j0) (hpair : isRedexPair ds (⟪i0, j1⟫ : V)) :
    GenReductCert (zK s r ds) := by
  have hvalidF : zKValidF s r ds := zKValidF_of_ZDerivation_zK hZ
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hjlt : j1 < lh ds := lt_of_le_of_lt hj1 hj0
  have hilt0 : i0 < lh ds := lt_trans hij hjlt
  have hex : ∃ c < (⟪lh ds, lh ds⟫ : V), isRedexPair ds c :=
    ⟨⟪i0, j1⟫, pair_lt_pair hilt0 hjlt, hpair⟩
  have hIlt_j0 : redexI (zK s r ds) < j0 := redexI_lt_of_redexPair hij hj1 hj0 hpair
  obtain ⟨hIJ, hJlt, hcase⟩ := redZKReady_of_zKValidF_exists hZ hvalidF hex
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  have hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r := hrank0 _ hIlt_j0
  have hca : ∀ i < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds i) := hvalidF.2.2.2.2.2.2.1
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n; rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  rcases hcase with ⟨sᵢ, sⱼ, a', p, pj, k', d0, hdi, hdj, hirk, hsj⟩ |
      ⟨sᵢ, sⱼ, p, d0, hdi, hdj, hcut, hpUf⟩
  · -- ∀-redex: the principal cut on `^∀ p` (`iRcritG`, halves replace `redexI`/`redexJ`)
    have hZdi : ZDerivation (zIall sᵢ a' p d0) := hdi ▸ hmem _ hIlt
    obtain ⟨_, hssi, hwff⟩ := zDerivation_zIall_inv hZdi
    have hpwff : IsUFormula ℒₒᵣ p := hwff.2.2.isUFormula
    have hregI : ZRegular (zIall sᵢ a' p d0) := hdi ▸ ZRegular_zK_premise hds hreg hIlt
    have heig : maxEigen d0 < a' := maxEigen_lt_of_regular_zIall hregI
    have hSeqsj : Seq (seqAnt sⱼ) := by
      have h := seq_seqAnt_zK_premise hds hseqant hJlt (hmem _ hJlt) (by rw [hdj]; simp)
      rwa [hdj, fstIdx_zAxAll] at h
    have hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)) := by
      have h := hca _ hJlt; rw [chainAsucc, hdj, fstIdx_zAxAll, hsj] at h; exact h
    have hChAI : chainAsucc ds (redexI (zK s r ds)) = (^∀ p : V) := by
      rw [chainAsucc, hdi, fstIdx_zIall]; exact hssi
    have htag1 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) = 1 := by
      rw [zKseq_zK, hdi]; exact zTag_zIall _ _ _ _
    have hZcrit : ZDerivation (iRKcCrit (zK s r ds)) :=
      ZDerivation_iRKcCrit_all hZ hIlt hJlt hIJ hdi hdj heig hfresh hpwff hCwff
        (seq_seqAnt_zK hseqant) hSeqsj hsj
        (fun i' hi' => hthread0 i' (le_of_lt (lt_of_le_of_lt hi' hIlt_j0)))
        (fun i' hi' => hrank0 i' (lt_trans hi' hIlt_j0)) hrankI
    have hregcrit : ZRegular (iRKcCrit (zK s r ds)) := by
      refine ZRegular_iRKcCrit ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZRegular_zK_premise hds hreg hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZRegular_zK_premise hds hreg hIlt
      · rw [zKseq_zK, hdi]; exact Or.inl (zTag_zIall _ _ _ _)
    have hfreshcrit : ZFresh (iRKcCrit (zK s r ds)) := by
      refine ZFresh_iRKcCrit ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZFresh_zK_premise hds hfresh hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZFresh_zK_premise hds hfresh hIlt
      · rw [zKseq_zK, hdi]; exact Or.inl (zTag_zIall _ _ _ _)
    have hseqantcrit : ZSeqAnt (iRKcCrit (zK s r ds)) := by
      refine ZSeqAnt_iRKcCrit ?_ ?_ ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZSeqAnt_zK_premise hds hseqant hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZSeqAnt_zK_premise hds hseqant hIlt
      · rw [fstIdx_zK]; exact seq_seqAnt_zK hseqant
      · rw [zKseq_zK, hdj, fstIdx_zAxAll]; exact hSeqsj
      · rw [zKseq_zK, hdi]; exact Or.inl (zTag_zIall _ _ _ _)
    have hbI : iRedDescent (critReductCorr (zK s r ds) (redexI (zK s r ds)))
        (znth ds (redexI (zK s r ds))) := by
      rw [critReductCorr, if_neg (ne_of_lt hIJ), if_pos rfl, zKseq_zK, hdi,
        zIallPrem_zIall, zIallEig_zIall]
      exact iRedDescent_zsubst_zIall
        (by simp : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral
          (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds)))))) : V)).isUTerm (hdi ▸ hmem _ hIlt)
    have hbJ : iRedDescent (critReductCorr (zK s r ds) (redexJ (zK s r ds)))
        (znth ds (redexJ (zK s r ds))) := by
      rw [critReductCorr, if_pos rfl]
      simp only [zKseq_zK, hdj, fstIdx_zAxAll]
      exact iRedDescent_zAx1_zAxAll_of_irk hirk
    have heqRKc : iRKcCrit (zK s r ds)
        = zK s (r - 1) (iCritReductSeq
            (zK (seqSetSucc s (cutFormula (zK s r ds))) r
              (seqUpdate ds (redexI (zK s r ds)) (critReductCorr (zK s r ds) (redexI (zK s r ds)))))
            (zK (seqAddAnt (cutFormula (zK s r ds)) s) r
              (seqUpdate ds (redexJ (zK s r ds)) (critReductCorr (zK s r ds) (redexJ (zK s r ds)))))) := by
      rw [iRKcCrit_eq_corr htag1 (ne_of_lt hIJ)]
      simp only [iRcritG, iCritReductG, fstIdx_zK, zKrank_zK, zKseq_zK]
    have hCrk : irk (cutFormula (zK s r ds)) + 1 ≤ idg (zK s r ds) := by
      have hlt : irk (cutFormula (zK s r ds)) < r :=
        irk_cutFormula_lt (by rw [zKseq_zK]; exact hmem _ hIlt)
          (by rw [zKseq_zK, hChAI, hdi]; exact tp_zIall _ _ _ _)
          (by rw [zKseq_zK]; exact hrankI)
      exact le_trans (succ_le_iff_lt.mpr hlt) (r_le_idg_zK s r ds hds)
    have ha_otil : icmp (iotil (zK (seqSetSucc s (cutFormula (zK s r ds))) r
          (seqUpdate ds (redexI (zK s r ds)) (critReductCorr (zK s r ds) (redexI (zK s r ds))))))
          (iotil (zK s r ds)) = 0 := by
      refine iotil_zK_lt_replace hds (seqUpdate_seq _ _ _) (seqUpdate_lh _ _ _) hIlt ?_ ?_ hNF ?_
      · rw [znth_seqUpdate_self hIlt]; exact hbI.otil_lt
      · intro n hn; rw [znth_seqUpdate_of_ne hn]
      · intro n; rcases eq_or_ne n (redexI (zK s r ds)) with rfl | hne
        · rw [znth_seqUpdate_self hIlt]; exact hbI.nf
        · rw [znth_seqUpdate_of_ne hne]; exact hNF n
    have hb_otil : icmp (iotil (zK (seqAddAnt (cutFormula (zK s r ds)) s) r
          (seqUpdate ds (redexJ (zK s r ds)) (critReductCorr (zK s r ds) (redexJ (zK s r ds))))))
          (iotil (zK s r ds)) = 0 := by
      refine iotil_zK_lt_replace hds (seqUpdate_seq _ _ _) (seqUpdate_lh _ _ _) hJlt ?_ ?_ hNF ?_
      · rw [znth_seqUpdate_self hJlt]; exact hbJ.otil_lt
      · intro n hn; rw [znth_seqUpdate_of_ne hn]
      · intro n; rcases eq_or_ne n (redexJ (zK s r ds)) with rfl | hne
        · rw [znth_seqUpdate_self hJlt]; exact hbJ.nf
        · rw [znth_seqUpdate_of_ne hne]; exact hNF n
    have ha_idg : idg (zK (seqSetSucc s (cutFormula (zK s r ds))) r
          (seqUpdate ds (redexI (zK s r ds)) (critReductCorr (zK s r ds) (redexI (zK s r ds)))))
          ≤ idg (zK s r ds) := by
      refine idg_zK_le_replace hds (seqUpdate_seq _ _ _) (seqUpdate_lh _ _ _) (fun n => ?_)
      rcases eq_or_ne n (redexI (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hIlt]; exact hbI.dg_le
      · exact le_of_eq (congrArg idg (znth_seqUpdate_of_ne hne))
    have hb_idg : idg (zK (seqAddAnt (cutFormula (zK s r ds)) s) r
          (seqUpdate ds (redexJ (zK s r ds)) (critReductCorr (zK s r ds) (redexJ (zK s r ds)))))
          ≤ idg (zK s r ds) := by
      refine idg_zK_le_replace hds (seqUpdate_seq _ _ _) (seqUpdate_lh _ _ _) (fun n => ?_)
      rcases eq_or_ne n (redexJ (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hJlt]; exact hbJ.dg_le
      · exact le_of_eq (congrArg idg (znth_seqUpdate_of_ne hne))
    exact certFlatten_of_critHalves (C := cutFormula (zK s r ds))
      (heqRKc ▸ hZcrit) (heqRKc ▸ hregcrit) (heqRKc ▸ hfreshcrit) (heqRKc ▸ hseqantcrit)
      (fstIdx_zK _ _ _) (fstIdx_zK _ _ _) (by rw [hsucc]; simp) (seq_seqAnt_zK hseqant) hCwff hCrk
      ha_otil hb_otil ha_idg hb_idg
  · -- ¬-redex: the principal cut on `inegF p` (`iRcritGNeg`, halves SWAPPED across `redexI`/`redexJ`)
    have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ hmem _ hIlt
    obtain ⟨_, hssi, _, hSeqsi, hd0ant⟩ := zDerivation_zIneg_inv hZdi
    have hCwff : IsUFormula ℒₒᵣ (cutFormula (zK s r ds)) := hcut ▸ hpUf
    have hChAI : chainAsucc ds (redexI (zK s r ds)) = (inegF p : V) := by
      rw [chainAsucc, hdi, fstIdx_zIneg]; exact hssi
    have htag2 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) ≠ 1 := by
      rw [zKseq_zK, hdi, zTag_zIneg]; simp
    have hZcrit : ZDerivation (iRKcCrit (zK s r ds)) :=
      ZDerivation_iRKcCrit_neg_botOrbit hZ hIlt hJlt hIJ hdi hdj hcut hd0ant hCwff
        (seq_seqAnt_zK hseqant) hSeqsi hIlt_j0 hj0 hbot0 hthread0 hrank0
    have hregcrit : ZRegular (iRKcCrit (zK s r ds)) := by
      refine ZRegular_iRKcCrit ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZRegular_zK_premise hds hreg hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZRegular_zK_premise hds hreg hIlt
      · rw [zKseq_zK, hdi]; exact Or.inr (zTag_zIneg _ _ _)
    have hfreshcrit : ZFresh (iRKcCrit (zK s r ds)) := by
      refine ZFresh_iRKcCrit ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZFresh_zK_premise hds hfresh hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZFresh_zK_premise hds hfresh hIlt
      · rw [zKseq_zK, hdi]; exact Or.inr (zTag_zIneg _ _ _)
    have hseqantcrit : ZSeqAnt (iRKcCrit (zK s r ds)) := by
      refine ZSeqAnt_iRKcCrit ?_ ?_ ?_ ?_ ?_ ?_
      · rw [zKseq_zK]; intro m hm; exact ZSeqAnt_zK_premise hds hseqant hm
      · rw [zKseq_zK]; exact hmem _ hIlt
      · rw [zKseq_zK]; exact ZSeqAnt_zK_premise hds hseqant hIlt
      · rw [fstIdx_zK]; exact seq_seqAnt_zK hseqant
      · rw [zKseq_zK]
        have h := seq_seqAnt_zK_premise hds hseqant hJlt (hmem _ hJlt) (by rw [hdj]; simp)
        rwa [hdj] at h ⊢
      · rw [zKseq_zK, hdi]; exact Or.inr (zTag_zIneg _ _ _)
    have hbI : iRedDescent (critReductNeg (zK s r ds) (redexI (zK s r ds)))
        (znth ds (redexI (zK s r ds))) := by
      rw [critReductNeg_redexI (ne_of_lt hIJ), zKseq_zK, hdi, zInegPrem_zIneg]
      exact iRedDescent_zIneg
        (isNF_iotil_of_ZDerivation d0 (zDerivation_zIneg_inv (hdi ▸ hmem _ hIlt)).1)
    have hbJ : iRedDescent (critReductNeg (zK s r ds) (redexJ (zK s r ds)))
        (znth ds (redexJ (zK s r ds))) := by
      rw [critReductNeg_redexJ, zKseq_zK, hdj, fstIdx_zAxNeg, hcut]
      exact iRedDescent_zAx1_zAxNeg_gen hpUf
    have heqRKc : iRKcCrit (zK s r ds)
        = zK s (r - 1) (iCritReductSeq
            (zK (seqSetSucc s (cutFormula (zK s r ds))) r
              (seqUpdate ds (redexJ (zK s r ds)) (critReductNeg (zK s r ds) (redexJ (zK s r ds)))))
            (zK (seqAddAnt (cutFormula (zK s r ds)) s) r
              (seqUpdate ds (redexI (zK s r ds)) (critReductNeg (zK s r ds) (redexI (zK s r ds)))))) := by
      rw [iRKcCrit_eq_neg htag2 (ne_of_lt hIJ)]
      simp only [iRcritGNeg, iCritReductG, fstIdx_zK, zKrank_zK, zKseq_zK]
    have hCrk : irk (cutFormula (zK s r ds)) + 1 ≤ idg (zK s r ds) := by
      have hlt : irk (cutFormula (zK s r ds)) < r :=
        irk_cutFormula_lt (by rw [zKseq_zK]; exact hmem _ hIlt)
          (by rw [zKseq_zK, hChAI, hdi]; exact tp_zIneg _ _ _)
          (by rw [zKseq_zK]; exact hrankI)
      exact le_trans (succ_le_iff_lt.mpr hlt) (r_le_idg_zK s r ds hds)
    have ha_otil : icmp (iotil (zK (seqSetSucc s (cutFormula (zK s r ds))) r
          (seqUpdate ds (redexJ (zK s r ds)) (critReductNeg (zK s r ds) (redexJ (zK s r ds))))))
          (iotil (zK s r ds)) = 0 := by
      refine iotil_zK_lt_replace hds (seqUpdate_seq _ _ _) (seqUpdate_lh _ _ _) hJlt ?_ ?_ hNF ?_
      · rw [znth_seqUpdate_self hJlt]; exact hbJ.otil_lt
      · intro n hn; rw [znth_seqUpdate_of_ne hn]
      · intro n; rcases eq_or_ne n (redexJ (zK s r ds)) with rfl | hne
        · rw [znth_seqUpdate_self hJlt]; exact hbJ.nf
        · rw [znth_seqUpdate_of_ne hne]; exact hNF n
    have hb_otil : icmp (iotil (zK (seqAddAnt (cutFormula (zK s r ds)) s) r
          (seqUpdate ds (redexI (zK s r ds)) (critReductNeg (zK s r ds) (redexI (zK s r ds))))))
          (iotil (zK s r ds)) = 0 := by
      refine iotil_zK_lt_replace hds (seqUpdate_seq _ _ _) (seqUpdate_lh _ _ _) hIlt ?_ ?_ hNF ?_
      · rw [znth_seqUpdate_self hIlt]; exact hbI.otil_lt
      · intro n hn; rw [znth_seqUpdate_of_ne hn]
      · intro n; rcases eq_or_ne n (redexI (zK s r ds)) with rfl | hne
        · rw [znth_seqUpdate_self hIlt]; exact hbI.nf
        · rw [znth_seqUpdate_of_ne hne]; exact hNF n
    have ha_idg : idg (zK (seqSetSucc s (cutFormula (zK s r ds))) r
          (seqUpdate ds (redexJ (zK s r ds)) (critReductNeg (zK s r ds) (redexJ (zK s r ds)))))
          ≤ idg (zK s r ds) := by
      refine idg_zK_le_replace hds (seqUpdate_seq _ _ _) (seqUpdate_lh _ _ _) (fun n => ?_)
      rcases eq_or_ne n (redexJ (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hJlt]; exact hbJ.dg_le
      · exact le_of_eq (congrArg idg (znth_seqUpdate_of_ne hne))
    have hb_idg : idg (zK (seqAddAnt (cutFormula (zK s r ds)) s) r
          (seqUpdate ds (redexI (zK s r ds)) (critReductNeg (zK s r ds) (redexI (zK s r ds)))))
          ≤ idg (zK s r ds) := by
      refine idg_zK_le_replace hds (seqUpdate_seq _ _ _) (seqUpdate_lh _ _ _) (fun n => ?_)
      rcases eq_or_ne n (redexI (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hIlt]; exact hbI.dg_le
      · exact le_of_eq (congrArg idg (znth_seqUpdate_of_ne hne))
    exact certFlatten_of_critHalves (C := cutFormula (zK s r ds))
      (heqRKc ▸ hZcrit) (heqRKc ▸ hregcrit) (heqRKc ▸ hfreshcrit) (heqRKc ▸ hseqantcrit)
      (fstIdx_zK _ _ _) (fstIdx_zK _ _ _) (by rw [hsucc]; simp) (seq_seqAnt_zK hseqant) hCwff hCrk
      ha_otil hb_otil ha_idg hb_idg

/-- **§14.254 recursion SPLICE — a reduced premise's `GenReductCert` lifts to a parent `certReplace`
(lap 153).** A `Γ→⊥` chain `zK s r ds` (regular/fresh/seqAnt) with the `isChainInf` exit data, whose premise
`m ≤ j0` carries a `GenReductCert` (the per-premise IH reduct, REPLACE or FLATTEN), reduces to a
SAME-end-sequent `õ`-dropping `certReplace`: splice the IH reduct into `ds` at `m` — `seqUpdate ds m v` for a
single REPLACE reduct, `seqInsert ds m a b` (rank `r' = max r (irk C)`) for the two FLATTEN halves. **BOTH
keep `fstIdx = s` and lower `õ` without raising `idg`** (`iotil_iCritAux_lt`/`iotil_seqInsert_lt` +
`idg_iCritAux_le`/`idg_seqInsert_le'`), so the parent is itself a single same-end-sequent `iRedDescent`
reduct — a `certReplace`, NOT a flatten. **Γ-AGNOSTIC** (the splice validity `ZDerivation_iCritAux_of` /
`isChainInf_seqInsert` never need `seqAnt s = ∅`): this is the Γ-general analog of the orbit
`descent_step_K_replace`/`descent_step_K_spliceHalves` (which conclude `ZDerivesEmptyR` + `iord`-drop). The
genuine §14.254 splice as the recursion re-packages it. -/
lemma certReplace_of_premise_cert {s r ds m j0 : V}
    (hZ : ZDerivation (zK s r ds)) (hreg : ZRegular (zK s r ds))
    (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (hj0 : j0 < lh ds)
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hexit : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hm : m < lh ds) (hmj0 : m ≤ j0)
    (hmcert : GenReductCert (znth ds m)) :
    certReplace (zK s r ds) := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n; rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  rcases hmcert with
    ⟨v, hZv, hregv, hfreshv, hseqantv, hvfst, hdesc⟩ |
    ⟨a, b, hZa, hZb, hrega, hregb, hfresha, hfreshb, hseqanta, hseqantb,
      ha_ant, hb_succ, hb_thr, hfa_a, hfa_b, hrank_b, ha_otil, hb_otil, ha_idg, hb_idg⟩
  · -- REPLACE: swap premise `m` by `v` (`seqUpdate`), Γ-general (ZDerivation_iCritAux_of)
    have hperm_v := iperm_tp_fstIdx_of_ZDerivation hZv
    obtain ⟨hf1, hf2, hf5, hf6⟩ := zKValidF_leafconds_of_ZDerivation hZv
    have hZred : ZDerivation (iCritAux (zK s r ds) m v) :=
      ZDerivation_iCritAux_of hm hZ hZv hvfst hperm_v hf1 hf2 hf5 hf6
    refine ⟨iCritAux (zK s r ds) m v, hZred, ?_, ?_, ?_, ?_, ?_⟩
    · rw [iCritAux_zK]
      exact ZRegular_zK_of_seqUpdate (fun n hn => ZRegular_zK_premise hds hreg hn) hregv
    · rw [iCritAux_zK]
      exact ZFresh_zK_of_seqUpdate (fun n hn => ZFresh_zK_premise hds hfresh hn) hfreshv
    · rw [iCritAux_zK]
      exact ZSeqAnt_zK_of_seqUpdate (seqAntSeqFlag_zK_of_ZSeqAnt hseqant)
        (fun n hn => ZSeqAnt_zK_premise hds hseqant hn) hseqantv
    · rw [iCritAux_zK, fstIdx_zK, fstIdx_zK]
    · exact ⟨idg_iCritAux_le hds hm hdesc.dg_le,
        iotil_iCritAux_lt hds hm hdesc.otil_lt hNF hdesc.nf, isNF_iotil_of_ZDerivation _ hZred⟩
  · -- FLATTEN: splice the two halves `a`,`b` at `m` (`seqInsert`), rank `r' = max r (irk (succ a))`
    have hb_ant : ∀ B, inAnt B (seqAnt (fstIdx b)) →
        B = seqSucc (fstIdx a) ∨ inAnt B (chainAnt ds m) := by
      intro B hB
      obtain ⟨k, hk, hkB⟩ := hB
      rcases hb_thr k hk with h | h
      · exact Or.inl (hkB ▸ h)
      · exact Or.inr (hkB ▸ h)
    have hidgm : idg (znth ds m) ≤ iseqMaxIdg ds := le_iseqMaxIdgAux (lh ds) m hm
    have hrankidg : irk (seqSucc (fstIdx a)) ≤ idg (zK s r ds) := by
      rw [idg_zK s r ds hds]
      exact le_trans (le_pred_of_lt (succ_le_iff_lt.mp (le_trans hrank_b hidgm)))
        (le_max_right r (iseqMaxIdg ds - 1))
    have hr'deg : max r (irk (seqSucc (fstIdx a))) ≤ idg (zK s r ds) :=
      max_le (r_le_idg_zK s r ds hds) hrankidg
    have hci : isChainInf s (max r (irk (seqSucc (fstIdx a)))) (seqInsert ds m a b) :=
      isChainInf_seqInsert hj0 hmj0 hexit hthread0 hrank0
        ha_ant (le_max_right r _) hb_succ hb_ant (le_max_left r _)
    have hZ' : ZDerivation (zK s (max r (irk (seqSucc (fstIdx a)))) (seqInsert ds m a b)) :=
      ZDerivation_seqInsert_of hm hZ hZa hZb hci
        (iperm_tp_fstIdx_of_ZDerivation hZa) (iperm_tp_fstIdx_of_ZDerivation hZb)
        (zKValidF_leafconds_of_ZDerivation hZa).1 (zKValidF_leafconds_of_ZDerivation hZb).1
        (zKValidF_leafconds_of_ZDerivation hZa).2.1 (zKValidF_leafconds_of_ZDerivation hZb).2.1
        (zKValidF_leafconds_of_ZDerivation hZa).2.2.1 (zKValidF_leafconds_of_ZDerivation hZb).2.2.1
        (zKValidF_leafconds_of_ZDerivation hZa).2.2.2 (zKValidF_leafconds_of_ZDerivation hZb).2.2.2
        hfa_a hfa_b
    refine ⟨zK s (max r (irk (seqSucc (fstIdx a)))) (seqInsert ds m a b), hZ', ?_, ?_, ?_, ?_, ?_⟩
    · exact ZRegular_zK_of_seqInsert hm (fun n hn => ZRegular_zK_premise hds hreg hn) hrega hregb
    · exact ZFresh_zK_of_seqInsert hm (fun n hn => ZFresh_zK_premise hds hfresh hn) hfresha hfreshb
    · exact ZSeqAnt_zK_of_seqInsert (seqAntSeqFlag_zK_of_ZSeqAnt hseqant) hm
        (fun n hn => ZSeqAnt_zK_premise hds hseqant hn) hseqanta hseqantb
    · rw [fstIdx_zK, fstIdx_zK]
    · exact ⟨idg_seqInsert_le' hds hm hr'deg ha_idg hb_idg,
        iotil_seqInsert_lt hds hm ha_otil hb_otil hNF
          (isNF_iotil_of_ZDerivation a hZa) (isNF_iotil_of_ZDerivation b hZb),
        isNF_iotil_of_ZDerivation _ hZ'⟩

/-- **no-redex leaf of the §14.254 chain reduction (`Γ→⊥`, recurse via the IH) — NAMED sub-`sorry`.** No
redex pair below the ⊥-exit `j0`; by `majorPrem_tag_mem` the major premise's tag ∈ {3,4,5,6}. tags 3/4
(`Rep` major) → reduce the major premise `znth ds (majorIdx …)` directly by the **IH**; tags 5/6 (L-axiom
major) → identify the upstream `Rep` cut-partner (a tag-3/4 premise) and reduce IT by the IH. Either way,
REPLACE the reduced premise — the genuine Buchholz §14.254 **SPLICE** (`iord`-monotone premise replacement;
a documented bug-magnet, cf. lap87/lap94 ANALYSIS docs). The SPLICE step itself is now banked Γ-general
(`certReplace_of_premise_cert`); the lone residual is the §14.254 major-premise SELECTION at `Γ≠∅` — the
cut-partner lemmas (`majorPrem_*_cutPartner`, `majorIdx_botOrbit_reducible`) currently assume `seqAnt s = ∅`
because a tag-5/6 active formula could sit in `Γ` rather than threading to an upstream R-intro. -/
lemma genReduct_chain_noRedex {s r ds j0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hreg : ZRegular (zK s r ds)) (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (hsucc : seqSucc s = (^⊥ : V))
    (hj0 : j0 < lh ds) (hbot0 : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hnolow : ¬ ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V))
    (IH : ∀ i < lh ds, ZRegular (znth ds i) → ZFresh (znth ds i) → ZSeqAnt (znth ds i) →
        seqSucc (fstIdx (znth ds i)) = (^⊥ : V) →
        (zTag (znth ds i) = 3 ∨ zTag (znth ds i) = 4) →
        GenReductCert (znth ds i)) :
    GenReductCert (zK s r ds) := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  -- Buchholz §14.25 major-premise selection: the LEAST ⊥-exit `jstar ≤ j0`.
  have hP : 𝚺₁-Predicate (fun j => chainAsucc ds j = (^⊥ : V)) := by definability
  obtain ⟨jstar, hjstar, hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hP hbot0
  have hjle : jstar ≤ j0 := by
    by_contra h; exact (hmin j0 (not_le.mp h)) hbot0
  have hjlt : jstar < lh ds := lt_of_le_of_lt hjle hj0
  have hmemZ : ZDerivation (znth ds jstar) := hmem jstar hjlt
  have hregm : ZRegular (znth ds jstar) := ZRegular_zK_premise hds hreg hjlt
  have hfreshm : ZFresh (znth ds jstar) := ZFresh_zK_premise hds hfresh hjlt
  have hseqantm : ZSeqAnt (znth ds jstar) := ZSeqAnt_zK_premise hds hseqant hjlt
  have hsucc' : seqSucc (fstIdx (znth ds jstar)) = (^⊥ : V) := hjstar
  -- The chain is NONEMPTY, so its `õ`-fold is positive — the trivial axiom `zAtom s` (`õ = 0`) strictly
  -- beats it. This is the engine of the leaf escape: if `⊥ ∈ Γ`, `zAtom s` derives `Γ→⊥` directly.
  have hNF : ∀ n, isNF (iotil (znth ds n)) := isNF_iotil_znth_of_ZDerivation_zK hZ
  have hpos : (0 : V) < lh ds := lt_of_le_of_lt zero_le hj0
  have hposlast : iseqNaddIdg ds ≠ 0 := by
    show iseqNaddIdgAux ds (lh ds) ≠ 0
    obtain ⟨M, hM⟩ : ∃ M, lh ds = M + 1 :=
      ⟨lh ds - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
    rw [hM, iseqNaddIdgAux_succ]
    have hg : isNF (iseqNaddIdgAux ds M) := isNF_iseqNaddIdgAux' hNF M
    have hY : isNF (ocOadd (iotil (znth ds M)) 1 0) := isNF_omega_pow (hNF M)
    have hkey : icmp (iseqNaddIdgAux ds M)
        (inadd (iseqNaddIdgAux ds M) (ocOadd (iotil (znth ds M)) 1 0)) = 0 := by
      have h := inadd_left_mono isNF_zero hY (icmp_zero_ocOadd _ _ _) (iseqNaddIdgAux ds M) hg
      rwa [inadd_zero_right _ hg] at h
    intro hzero
    rw [hzero] at hkey
    rcases eq_or_ne (iseqNaddIdgAux ds M) 0 with h0 | h0
    · rw [h0, icmp_zero_zero] at hkey; exact _root_.one_ne_zero hkey
    · rw [icmp_pos_zero h0] at hkey; exact _root_.two_ne_zero hkey
  -- §14.254b residual (lap-155 NARROWED): the tag-5 cut-partner SUB-CASE (b) + all of tag-6. The tag-5
  -- SUB-CASE (a) (`^∀⊥ ∈ Γ`) is now PROVEN inline (the succedent-threading collapse) via the fresh
  -- `zAxAll s ⊥ 0` reduct; this sorry covers only: (b) the tag-5 active `^∀⊥` threading to an upstream
  -- cut-partner `i' < jstar` (a `Rep` node by `hnolow`, NOT a direct R-intro — verified `isRedexPair`
  -- forbids a `zIall ^∀⊥` below j0), and the tag-6 (`zAxNeg`) dual (which lacks the `zAxAllSuccWff`
  -- `p=⊥` collapse and needs BOTH `inegF p, p ∈ Γ` threaded). See `DIRECTION.md`/`PENDING_WORK.md` lap-155.
  have axMajorResidual : GenReductCert (zK s r ds) := sorry
  -- §14.254 leaf escape: `⊥ ∈ Γ` ⟹ the trivial `Γ→⊥` axiom `zAtom s` is a sound `õ`-dropping reduct.
  have leafClose : inAnt (^⊥ : V) (seqAnt s) → GenReductCert (zK s r ds) := fun hbotIn =>
    Or.inl ⟨zAtom s,
      zDerivation_iff.mpr (Or.inl ⟨s, rfl, by rw [hsucc]; exact hbotIn⟩),
      zReg_zAtom s, zFresh_zAtom s,
      (zSeqAnt_zAtom s).trans (seqAntSeqFlag_zK_of_ZSeqAnt hseqant),
      by rw [fstIdx_zAtom, fstIdx_zK],
      ⟨by rw [idg_zAtom]; exact zero_le,
       by rw [iotil_zAtom, iotil_zK s r ds hds]; exact icmp_zero_pos hposlast,
       by rw [iotil_zAtom]; exact isNF_zero⟩⟩
  -- §14.254b SUCCEDENT-THREADING COLLAPSE: an active L-axiom formula `F` at `jstar` either threads to
  -- `Γ` (directly, or after the leaf-chain collapse `leastSucc_in_ant_or_nonleaf`) — the LIVE escape — or
  -- bottoms out at a NON-LEAF premise `m < jstar` concluding `F` (the narrowed residual: an R-intro is
  -- killed by `hnolow`, leaving a `Rep` node, the §14.254b cut-partner). Shared by tag-5 (`F = ^∀⊥`) and
  -- tag-6 (`F = inegF p'` and `F = p'`).
  have collapse : ∀ i, i ≤ j0 → ∀ F, inAnt F (chainAnt ds i) →
      inAnt F (seqAnt s) ∨
      ∃ m, m < i ∧ chainAsucc ds m = F ∧ zTag (znth ds m) ≠ 0 ∧ zTag (znth ds m) ≠ 7 := by
    intro i hi F hF
    rcases hthread0 i hi F hF with hΓ | ⟨i', hi', heq⟩
    · exact Or.inl hΓ
    · rcases leastSucc_in_ant_or_nonleaf hmem hthread0 hj0
        (le_of_lt (lt_of_lt_of_le hi' hi)) heq.symm with hΓ | ⟨m, hmn, hCm, h0, h7⟩
      · exact Or.inl hΓ
      · exact Or.inr ⟨m, lt_of_le_of_lt hmn hi', hCm, h0, h7⟩
  -- General §5 ¬-axiom reduct: from `inegF q, q ∈ Γ` (any `q`) the axiom `zAxNeg s q` derives `Γ→⊥`
  -- directly, õ-dropping (`iotil_zAxNeg = oAtomLk(inegF q)`, finite head; witness index `jw` supplies the
  -- `õ`-value). Reused for both the tag-6 major (`q = p'`, witness `jstar`) and a `zAxNeg` PRODUCER
  -- cut-partner (`q` = its matrix, witness the producer index).
  have axNegCloseGen : ∀ q jw, jw < lh ds → iotil (znth ds jw) = oAtomLk (inegF q) →
      IsUFormula ℒₒᵣ q → inAnt (inegF q : V) (seqAnt s) → inAnt q (seqAnt s) →
      GenReductCert (zK s r ds) := fun q jw hjw hXq hq hΓ_neg hΓ_p =>
    Or.inl ⟨zAxNeg s q,
      zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, q, rfl, hq, hΓ_neg, hΓ_p⟩))))))),
      zReg_zAxNeg s q, zFresh_zAxNeg s q,
      (zSeqAnt_zAxNeg s q).trans (seqAntSeqFlag_zK_of_ZSeqAnt hseqant),
      by rw [fstIdx_zAxNeg, fstIdx_zK],
      ⟨by rw [idg_zAxNeg]; exact zero_le,
       by rw [iotil_zAxNeg, iotil_zK s r ds hds]
          exact finHead_iotil_lt_iseqNaddIdg hjw
            (by simp only [oAtomLk, ocExp_ocOadd]) (by simp only [oAtomLk]; exact (ocOadd_pos _ _ _).ne')
            hXq hNF,
       by rw [iotil_zAxNeg, ← hXq]; exact hNF jw⟩⟩
  -- §14.254b zAxNeg PRODUCER close (factored): a `zAxNeg s'' q` producer (tag 6) is a §5 ¬-axiom
  -- `Γₘ→anything` from `¬q,q ∈ Γₘ`; threading BOTH `¬q` and `q` (`collapse` at `m'`) to `Γ` ⟹ `zAxNeg s q`
  -- derives `Γ→⊥` directly (`axNegCloseGen`). Reused by `tryProducerClose`'s tag-6 case AND the tag-5
  -- climb's zAxNeg landing.
  have closeZAxNeg : ∀ m', m' ≤ j0 → m' < lh ds → zTag (znth ds m') = 6 → GenReductCert (zK s r ds) := by
    intro m' hm'j0 hm'lt h6
    rcases zDerivation_iff.mp (hmem m' hm'lt) with
      ⟨s'', h'', _⟩ | ⟨s'', a'', p'', d0'', h'', _, _⟩ | ⟨s'', p'', d0'', h'', _, _⟩ |
      ⟨s'', at''', p'', d0'', d1'', h'', _, _⟩ | ⟨s'', r'', ds'', h'', _, _, _⟩ |
      ⟨s'', p'', k'', h'', _, _⟩ | ⟨s'', q, h'', hq, hqn, hqp⟩ | ⟨s'', C'', h'', _⟩
    · rw [h''] at h6; simp at h6
    · rw [h''] at h6; simp at h6
    · rw [h''] at h6; simp at h6
    · rw [h''] at h6; simp at h6
    · rw [h''] at h6; simp at h6
    · rw [h''] at h6; simp at h6
    · have hXq : iotil (znth ds m') = oAtomLk (inegF q) := by rw [h'', iotil_zAxNeg]
      have hin_neg : inAnt (inegF q : V) (chainAnt ds m') := by
        simpa only [chainAnt, h'', fstIdx_zAxNeg] using hqn
      have hin_q : inAnt q (chainAnt ds m') := by
        simpa only [chainAnt, h'', fstIdx_zAxNeg] using hqp
      rcases collapse m' hm'j0 (inegF q) hin_neg with hΓ_neg | _
      · rcases collapse m' hm'j0 q hin_q with hΓ_q | _
        · exact axNegCloseGen q m' hm'lt hXq hq hΓ_neg hΓ_q
        · exact axMajorResidual
      · exact axMajorResidual
    · rw [h''] at h6; simp at h6
  -- §14.254b producer dispatch: a NON-LEAF producer `m` concluding the cut formula is reduced by
  -- CONSTRUCTOR. tag 6 (zAxNeg) → `closeZAxNeg`. tag 5 (zAxAll) → the rank-CLIMB
  -- (`climb_to_rep_producer`): its active `^∀ p''` threads UP one rank, so it can only bottom out at a
  -- `zInd`/`zK` (the general-succedent residual `axMajorResidual`), a `zAxNeg` (closed by `closeZAxNeg`),
  -- or a `^∀`-formula in `Γ` (the general escape, residual). The `zAxAll` (tag 5) producer is NO LONGER an
  -- independent gap. tags 3/4 (zInd/zK) directly + the climb's {3,4} landings + the general escape remain
  -- `axMajorResidual` (the genuine general-succedent reduction residual).
  have tryProducerClose : ∀ m, m ≤ j0 → m < lh ds → GenReductCert (zK s r ds) := by
    intro m hmj0 hmlt
    rcases zDerivation_iff.mp (hmem m hmlt) with
      ⟨s'', h'', _⟩ | ⟨s'', a'', p'', d0'', h'', _, _⟩ | ⟨s'', p'', d0'', h'', _, _⟩ |
      ⟨s'', at''', p'', d0'', d1'', h'', _, _⟩ | ⟨s'', r'', ds'', h'', _, _, _⟩ |
      ⟨s'', p'', k'', h'', _, _⟩ | ⟨s'', q, h'', hq, hqn, hqp⟩ | ⟨s'', C'', h'', _⟩
    · exact axMajorResidual
    · exact axMajorResidual
    · exact axMajorResidual
    · exact axMajorResidual
    · exact axMajorResidual
    · -- tag 5 (zAxAll s'' p'' k''): CLIMB its active `^∀ p''`.
      have hjLm : tp (znth ds m) = isymLk k'' (^∀ p'' : V) := by rw [h'', tp_zAxAll]
      have hin' : inAnt (^∀ p'' : V) (chainAnt ds m) := by
        have hinv := zDerivation_zAxAll_inv (h'' ▸ hmem m hmlt)
        simpa only [chainAnt, h'', fstIdx_zAxAll] using hinv.2.1
      rcases climb_to_rep_producer hmem hthread0 hj0 hnolow hmj0 hjLm ⟨p'', rfl⟩ hin' with
        ⟨_, _, _⟩ | ⟨m', hm'j0, hm'lt, hm'tag⟩
      · exact axMajorResidual
      · rcases hm'tag with _ | _ | h6
        · exact axMajorResidual
        · exact axMajorResidual
        · exact closeZAxNeg m' hm'j0 hm'lt h6
    · -- tag 6 (zAxNeg s'' q): close via the factored helper.
      exact closeZAxNeg m hmj0 hmlt (by rw [h'']; simp)
    · exact axMajorResidual
  rcases zDerivation_iff.mp hmemZ with
    ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, hp5, hin5, hsucc5⟩ | ⟨s', p', h, hp6, hin6, hin6_2⟩ | ⟨s', C', h, _⟩
  · -- tag 0 (zAtom): a leaf. Its `⊥`-succedent sits in its own antecedent, and (no earlier ⊥-exit, by
    -- leastness of `jstar`) threads to `inAnt ⊥ (seqAnt s)` — i.e. `⊥ ∈ Γ`. Then the trivial axiom
    -- `zAtom s` collapses the chain (`leafClose`). PROVEN at general Γ (Buchholz §14.254 degenerate case).
    refine leafClose ?_
    have hin : inAnt (^⊥ : V) (chainAnt ds jstar) := by
      have hatom := zDerivation_zAtom_inv (h ▸ hmemZ)
      have hss : seqSucc s' = (^⊥ : V) := by have hc := hsucc'; rwa [h, fstIdx_zAtom] at hc
      rw [hss] at hatom
      simpa only [chainAnt, h, fstIdx_zAtom] using hatom
    rcases hthread0 jstar hjle (^⊥) hin with hh | ⟨i', hi', heq⟩
    · exact hh
    · exact absurd heq.symm (hmin i' hi')
  · -- tag 1 (zIall): succedent `^∀ p'` ≠ `^⊥`, impossible at a ⊥-exit.
    exfalso
    have heq : seqSucc s' = (^∀ p' : V) := (zDerivation_zIall_inv (h ▸ hmemZ)).2.1
    rw [h, fstIdx_zIall, heq] at hsucc'
    exact qqAll_ne_falsum p' hsucc'
  · -- tag 2 (zIneg): succedent `inegF p'` ≠ `^⊥`, impossible.
    exfalso
    have heq : seqSucc s' = (inegF p' : V) := (zDerivation_zIneg_inv (h ▸ hmemZ)).2.1
    rw [h, fstIdx_zIneg, heq] at hsucc'
    exact inegF_ne_falsum p' hsucc'
  · -- tag 3 (zInd): the major premise is a `Rep` node deriving `Γⱼ→⊥`. §14.254a — REDUCE it by the IH
    -- and SPLICE into the parent (`certReplace_of_premise_cert`, Γ-general). PROVEN.
    have htag : zTag (znth ds jstar) = 3 := by rw [h]; simp
    exact Or.inl (certReplace_of_premise_cert hZ hreg hfresh hseqant hj0 hthread0 hrank0 (Or.inr hbot0)
      hjlt hjle (IH jstar hjlt hregm hfreshm hseqantm hsucc' (Or.inl htag)))
  · -- tag 4 (zK): the major premise is a sub-chain `Rep` node deriving `Γⱼ→⊥`. §14.254a — REDUCE by the
    -- IH and SPLICE. PROVEN.
    have htag : zTag (znth ds jstar) = 4 := by rw [h]; simp
    exact Or.inl (certReplace_of_premise_cert hZ hreg hfresh hseqant hj0 hthread0 hrank0 (Or.inr hbot0)
      hjlt hjle (IH jstar hjlt hregm hfreshm hseqantm hsucc' (Or.inr htag)))
  · -- tag 5 (zAxAll): L-axiom `Ax^{k'}_{∀p'}` major (`red`-FIXPOINT). The ⊥-exit + `zAxAllSuccWff` force
    -- `p' = ⊥`, so the cut formula is `^∀⊥`. Thread it (`hthread0`): SUB-CASE (a) `^∀⊥ ∈ Γ` → fresh
    -- `zAxAll s ⊥ 0` derives `Γ→⊥`, õ-dropping (PROVEN); SUB-CASE (b) cut-partner → `axMajorResidual`.
    have hsucc'' : seqSucc s' = (^⊥ : V) := by have hc := hsucc'; rwa [h, fstIdx_zAxAll] at hc
    have heq5 : seqSucc s' = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k') p' := hsucc5
    have hp_bot : p' = (^⊥ : V) := eq_falsum_of_substs1_falsum hp5 (heq5.symm.trans hsucc'')
    have hin_chain : inAnt (^∀ (^⊥) : V) (chainAnt ds jstar) := by
      rw [hp_bot] at hin5
      simpa only [chainAnt, h, fstIdx_zAxAll] using hin5
    have hXval : iotil (znth ds jstar) = oAtomLk (^∀ (^⊥) : V) := by rw [h, iotil_zAxAll, hp_bot]
    -- SUB-CASE (a) reduct, parametrized on `^∀⊥ ∈ Γ`: the ∀-instantiation axiom `zAxAll s ⊥ 0` deriving
    -- `Γ→⊥` (`substs1 0 ⊥ = ⊥`), õ-dropping (`iotil_zAxAll = oAtomLk(^∀⊥)`, finite head).
    have axAllClose : inAnt (^∀ (^⊥) : V) (seqAnt s) → GenReductCert (zK s r ds) := fun hΓ =>
      Or.inl ⟨zAxAll s (^⊥) 0,
        zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, (^⊥ : V), 0, rfl, IsSemiformula.falsum, hΓ,
            by have hsb : substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) (^⊥ : V) = (^⊥ : V) := by
                 rw [substs1]; exact substs_falsum _
               show seqSucc s = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) (^⊥ : V)
               rw [hsucc]; exact hsb.symm⟩)))))),
        zReg_zAxAll s (^⊥) 0, zFresh_zAxAll s (^⊥) 0,
        (zSeqAnt_zAxAll s (^⊥) 0).trans (seqAntSeqFlag_zK_of_ZSeqAnt hseqant),
        by rw [fstIdx_zAxAll, fstIdx_zK],
        ⟨by rw [idg_zAxAll]; exact zero_le,
         by rw [iotil_zAxAll, iotil_zK s r ds hds]
            exact finHead_iotil_lt_iseqNaddIdg hjlt
              (by simp only [oAtomLk, ocExp_ocOadd]) (by simp only [oAtomLk]; exact (ocOadd_pos _ _ _).ne')
              hXval hNF,
         by rw [iotil_zAxAll, ← hXval]; exact hNF jstar⟩⟩
    -- SUB-CASE (a)∨(b) via the succedent-threading collapse: `^∀⊥` threads to `Γ` (→ `axAllClose`) or
    -- bottoms out at a NON-LEAF premise `m < jstar` concluding `^∀⊥`. A RIGHT-symbol producer
    -- (`π₁(tp)=0`) forms an `isRedexPair` with `jstar` (the left ∀-axiom on `^∀⊥`) → killed by `hnolow`;
    -- so the residual is a genuine `Rep` node (tags {3,4,5,6}) concluding `^∀⊥` (narrowed §14.254b target).
    have hjL : tp (znth ds jstar) = isymLk k' (^∀ (^⊥) : V) := by rw [h, tp_zAxAll, hp_bot]
    rcases collapse jstar hjle (^∀ (^⊥)) hin_chain with hΓ | ⟨m, hmjs, hCm, hm0, hm7⟩
    · exact axAllClose hΓ
    · by_cases h0 : π₁ (tp (znth ds m)) = 0
      · exact (rightSym_producer_redex (hmem m (lt_trans hmjs hjlt)) hjL hjlt hjle hmjs hCm h0 hnolow).elim
      · exact tryProducerClose m (le_of_lt (lt_of_lt_of_le hmjs hjle)) (lt_trans hmjs hjlt)
  · -- tag 6 (zAxNeg): dual L-axiom `Ax^0_{¬p'}` major (`red`-FIXPOINT). `zDerivation_zAxNeg_inv` gives
    -- BOTH `inegF p' ∈ Γ'` and `p' ∈ Γ'` (no `zAxAllSuccWff`, so no `p=⊥` collapse). Thread BOTH via
    -- `hthread0`: SUB-CASE (a) `inegF p', p' ∈ Γ` → fresh `zAxNeg s p'` derives `Γ→⊥` directly (the §5
    -- ¬-axiom: `¬p',p' ∈ Γ ⟹ Γ→anything`), õ-dropping; otherwise → `axMajorResidual` cut-partner.
    have hXval : iotil (znth ds jstar) = oAtomLk (inegF p') := by rw [h, iotil_zAxNeg]
    have hin_negp : inAnt (inegF p' : V) (chainAnt ds jstar) := by
      simpa only [chainAnt, h, fstIdx_zAxNeg] using hin6
    have hin_p : inAnt p' (chainAnt ds jstar) := by
      simpa only [chainAnt, h, fstIdx_zAxNeg] using hin6_2
    -- SUB-CASE (a) reduct, parametrized on BOTH `inegF p' ∈ Γ` and `p' ∈ Γ`: the §5 ¬-axiom `zAxNeg s p'`
    -- deriving `Γ→⊥` directly (`¬p',p' ∈ Γ ⟹ Γ→anything`), õ-dropping (`iotil_zAxNeg`, finite head).
    have axNegClose : inAnt (inegF p' : V) (seqAnt s) → inAnt p' (seqAnt s) →
        GenReductCert (zK s r ds) := fun hΓ_neg hΓ_p =>
      Or.inl ⟨zAxNeg s p',
        zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, p', rfl, hp6, hΓ_neg, hΓ_p⟩))))))),
        zReg_zAxNeg s p', zFresh_zAxNeg s p',
        (zSeqAnt_zAxNeg s p').trans (seqAntSeqFlag_zK_of_ZSeqAnt hseqant),
        by rw [fstIdx_zAxNeg, fstIdx_zK],
        ⟨by rw [idg_zAxNeg]; exact zero_le,
         by rw [iotil_zAxNeg, iotil_zK s r ds hds]
            exact finHead_iotil_lt_iseqNaddIdg hjlt
              (by simp only [oAtomLk, ocExp_ocOadd]) (by simp only [oAtomLk]; exact (ocOadd_pos _ _ _).ne')
              hXval hNF,
         by rw [iotil_zAxNeg, ← hXval]; exact hNF jstar⟩⟩
    -- Collapse BOTH `inegF p'` and `p'` to `Γ` (succedent-threading); both in `Γ` → `axNegClose`, else the
    -- narrowed NON-LEAF residual. For the `inegF p'` half, `jstar` is the left ¬-axiom on `inegF p'`, so a
    -- RIGHT-symbol producer is killed by `hnolow` (→ `Rep`-node residual); the `p'` half has no left-axiom
    -- on `p'` at `jstar`, so its non-leaf producer stays a full residual.
    have hjLneg : tp (znth ds jstar) = isymLk 0 (inegF p') := by rw [h, tp_zAxNeg]
    rcases collapse jstar hjle (inegF p') hin_negp with hΓ_neg | ⟨mn, hmnjs, hCmn, hmn0, hmn7⟩
    · rcases collapse jstar hjle p' hin_p with hΓ_p | ⟨mp, hmpjs, hCmp, hmp0, hmp7⟩
      · exact axNegClose hΓ_neg hΓ_p
      · exact axMajorResidual
    · by_cases h0 : π₁ (tp (znth ds mn)) = 0
      · exact (rightSym_producer_redex (hmem mn (lt_trans hmnjs hjlt)) hjLneg hjlt hjle hmnjs hCmn h0
          hnolow).elim
      · exact tryProducerClose mn (le_of_lt (lt_of_lt_of_le hmnjs hjle)) (lt_trans hmnjs hjlt)
  · -- tag 7 (zAx1): a leaf (§5 logical axiom, like zAtom); `⊥ ∈ Γ`. Same trivial-axiom collapse. PROVEN.
    refine leafClose ?_
    have hin : inAnt (^⊥ : V) (chainAnt ds jstar) := by
      have hax := zDerivation_zAx1_inv (h ▸ hmemZ)
      have hss : seqSucc s' = (^⊥ : V) := by have hc := hsucc'; rwa [h, fstIdx_zAx1] at hc
      rw [hss] at hax
      simpa only [chainAnt, h, fstIdx_zAx1] using hax
    rcases hthread0 jstar hjle (^⊥) hin with hh | ⟨i', hi', heq⟩
    · exact hh
    · exact absurd heq.symm (hmin i' hi')

/-- **The §14.254 chain reduction step (tag-4 `zK`) — sorry-FREE DISPATCHER (lap 150), with the per-premise
IH in hand.** A `zK s r ds` chain deriving `Γ→⊥` (`seqSucc s = ⊥`, `Γ = seqAnt s` possibly NONEMPTY),
regular/fresh/seqAnt, whose EVERY premise `znth ds i` already enjoys the `genReduct_botSucc` conclusion when
it is itself a `Rep` node (`IH`, the structural-induction hypothesis), has a SAME-end-sequent (`fstIdx v = s`)
strictly-`iord`-descending regular/fresh/seqAnt `ZDerivation` reduct `v`. Extracts the `isChainInf` ⊥-exit
`j0` from chain validity (`Γ`-agnostic), then `by_cases` on a redex pair below `j0`: YES →
`genReduct_chain_hasRedex` (criticality-free principal cut); NO → `genReduct_chain_noRedex` (recurse the
major premise / cut-partner via `IH`). The Buchholz §14.253/§14.254 dichotomy, `Γ→⊥` and `iord`-DESCENT-valued
— NOT `iord`-recursion (PRWO/Gödel-barred); the IH descends on the derivation CODE only. -/
lemma genReduct_botSucc_chain {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hreg : ZRegular (zK s r ds)) (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (hsucc : seqSucc s = (^⊥ : V))
    (IH : ∀ i < lh ds, ZRegular (znth ds i) → ZFresh (znth ds i) → ZSeqAnt (znth ds i) →
        seqSucc (fstIdx (znth ds i)) = (^⊥ : V) →
        (zTag (znth ds i) = 3 ∨ zTag (znth ds i) = 4) →
        GenReductCert (znth ds i)) :
    GenReductCert (zK s r ds) := by
  obtain ⟨j0, hj0, hAj0, hthread0, hrank0⟩ := (zKValidF_of_ZDerivation_zK hZ).1
  have hbot0 : chainAsucc ds j0 = (^⊥ : V) := hAj0.elim (fun h => h.trans hsucc) id
  by_cases hlow : ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V)
  · obtain ⟨i0, j1, hij, hj1, hpair⟩ := hlow
    exact genReduct_chain_hasRedex hZ hreg hfresh hseqant hsucc hj0 hbot0 hthread0 hrank0 hij hj1 hpair
  · exact genReduct_chain_noRedex hZ hreg hfresh hseqant hsucc hj0 hbot0 hthread0 hrank0 hlow IH

/-- **General `Γ→⊥` one-step reduct CERTIFICATE — the §14.254 crux interface, by CODE-RECURSION
(lap 150 frame, lap-151 `GenReductCert`).** Any `Rep`-node `ZDerivation d` (tag ∈ {3,4}: a `zInd` or a
sub-`zK` chain) deriving `Γ→⊥` with the regular/fresh/seqAnt invariants has a `GenReductCert d`: EITHER a
single `õ`-dropping REPLACE reduct, OR the two FLATTEN halves of `d`'s own principal cut (the structured
certificate that exposes the halves the §14.254 splice needs — see `GenReductCert`). **Proved by
`zDerivation_sigma_induction`** — strong induction on the derivation CODE at the `𝚺₁` level (the certificate
is `𝚺₁`, `GenReductCert_definable`), NOT `iord`-recursion (PRWO/Gödel-barred). The tags ∉ {3,4} are vacuous;
**tag-3 (`zInd`) is PROVEN** as the REPLACE branch via `ind_reduct_botSucc_of_fresh` (`iRedDescent`, `õ`-drop);
**tag-4 (`zK`) delegates to `genReduct_botSucc_chain`**, supplying the per-premise IH the structural induction
provides — the genuine §14.254 recursion isolated WITH its IH in hand. Consumed by the no-redex leaves via
`descent_step_K_replace` (REPLACE) / `descent_step_K_spliceHalves` (FLATTEN). -/
lemma genReduct_botSucc {d : V} (hZ : ZDerivation d) (hreg : ZRegular d) (hfresh : ZFresh d)
    (hseqant : ZSeqAnt d) (hsucc : seqSucc (fstIdx d) = (^⊥ : V))
    (htag : zTag d = 3 ∨ zTag d = 4) :
    GenReductCert d := by
  -- Strong induction on the derivation CODE (the Buchholz §14.254 recursion), at the `𝚺₁` level.
  have key : ∀ d : V, ZDerivation d → ZRegular d → ZFresh d → ZSeqAnt d →
      seqSucc (fstIdx d) = (^⊥ : V) → (zTag d = 3 ∨ zTag d = 4) → GenReductCert d := by
    apply zDerivation_sigma_induction
      (P := fun d : V => ZRegular d → ZFresh d → ZSeqAnt d → seqSucc (fstIdx d) = (^⊥ : V) →
        (zTag d = 3 ∨ zTag d = 4) → GenReductCert d)
    · -- motive definability: `GenReductCert` via its banked instance; the antecedents are `𝚫₁`
      unfold ZRegular ZFresh ZSeqAnt; definability
    · -- the inductive step: dispatch on the rule; the IH `hC` gives `P` on every premise
      intro C hC d hphi
      have hZd : ZDerivation d := zDerivation_iff.mpr (zphi_monotone (fun x hx => (hC x hx).1) hphi)
      intro hreg hfresh hseqant hsucc htag
      rcases hphi with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
        ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, hmem, _⟩ |
        ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C', rfl, _⟩
      · simp at htag                                       -- zAtom (tag 0)
      · simp at htag                                       -- zIall (tag 1)
      · simp at htag                                       -- zIneg (tag 2)
      · -- zInd (tag 3): the general Ind reduct (`õ`-DROP REPLACE, PROVEN lap 148/149)
        rw [fstIdx_zInd] at hsucc
        have hfreshΓ : freshFlag (π₁ at') (^⊥ : V) (seqAnt s) = 0 := by
          have hz : zFresh (zInd s at' p d0 d1) = 0 := hfresh
          rw [zFresh_zInd] at hz
          exact nonpos_iff_eq_zero.mp (hz ▸ le_max_left _ _)
        obtain ⟨v, hZv, hregv, hfreshv, hseqantv, hvfst, hdesc⟩ :=
          ind_reduct_botSucc_of_fresh hZd hreg hfresh hseqant hsucc hfreshΓ
        exact Or.inl ⟨v, hZv, hregv, hfreshv, hseqantv, by rw [hvfst, fstIdx_zInd], hdesc⟩
      · -- zK (tag 4): delegate to the chain step, with the per-premise IH from `hC`
        rw [fstIdx_zK] at hsucc
        refine genReduct_botSucc_chain hZd hreg hfresh hseqant hsucc ?_
        intro i hi hregi hfreshi hseqanti hsucci htagi
        exact (hC (znth ds i) (hmem i hi)).2 hregi hfreshi hseqanti hsucci htagi
      · simp at htag                                       -- zAxAll (tag 5)
      · simp at htag                                       -- zAxNeg (tag 6)
      · simp at htag                                       -- zAx1 (tag 7)
  exact key d hZ hreg hfresh hseqant hsucc htag

/-! ## §14.254 reduction GENERALIZED off `seqSucc = ⊥` (lap 159 — the `axMajorResidual` decomposition)

The residual `axMajorResidual` (`:3417`) and its `Γ=∅` twin `descent_step_K_noncrit_axMajor` (`:3857`) both
reduce to **one** missing piece: the general-succedent reduction `genReduct_anySucc` — a `{3,4}` (`Rep`) node
deriving `Γ→F` for ANY `F` has a `GenReductCert`. The spike (`wip/GenReductAnySucc.lean`, lap 158) settled the
FORK: the recursion threads by the EXISTING CODE-induction (`zDerivation_sigma_induction`), NOT an outer
degree-induction — the `𝚺₁` motive `GenReductCert` never mentions `⊥`, the code-IH threads, and the
`{3,4}`-producer of the cut formula closes by recursing INTO it (the general IH) then splicing via the
already-general `certReplace_of_premise_cert` (`:3283`, its rank-headroom is LOCAL to the premise's own
`irk+1 ≤ idg`, not the chain degree — sidesteps the lap-157 refutation). This block PORTS the spike: the entry
and chain-step are PROVEN; the four genuinely-deep leaves are NAMED sub-`sorry`s (raising the src count = the
decomposition, per CLAUDE.local.md). The leaves:
1. `ind_reduct_anySucc` — the tag-3 Ind reduct off `⊥`: the lap-136 `k`-fold unfolding `⟨d0, d1[a:=0..k-1]⟩`
   (`k = ⟦t⟧`); for a CLOSED succedent (`p` closed) the induction is vacuous and the reduct is `d0`.
2. `genReduct_chain_hasRedex_anySucc` — the §14.253 principal cut off `⊥`: the ∀-redex sub-case now ports
   cleanly (`certFlatten_of_critHalves` generalized off `hsucc → IsUFormula (seqSucc s)`, lap 159); the
   ¬-redex sub-case routes through the `keepTip` (`ZDerivation_corrected_haux0_neg_botOrbit` `:738`) which
   GENUINELY needs the `⊥`-exit (it replaces the succedent by the cut formula, so only a `⊥`-exit re-validates).
3. `genReduct_chain_noRedex_anySucc` — the §14.254 chain recursion off `⊥`: the `{3,4}`-producer + the
   tag-5/6→producer threads CLOSE via the general IH + `certReplace_of_premise_cert` (the lap-158
   `noRedex_producer_closes` wiring, validated); the leaf `C∈Γ` / tag-1/2 R-intro-of-`C` / ex-falso closes
   (currently `Γ→⊥` reducts) need the general-`C` re-construction. -/

/-- **GENERALIZED Ind reduct off `seqSucc = ⊥` — NAMED sub-`sorry` (leaf 1).** The off-`⊥` twin of
`ind_reduct_botSucc_of_fresh` (`:2776`). For `C = ^∀^k⊥` (the residual's dominant shape) the induction is
VACUOUS (`substs1 t p = p`) and the reduct is `d0`; general `C` is the lap-136 unfolding. -/
lemma ind_reduct_anySucc {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1))
    (hreg : ZRegular (zInd s at' p d0 d1)) (hfresh : ZFresh (zInd s at' p d0 d1))
    (hseqant : ZSeqAnt (zInd s at' p d0 d1)) :
    GenReductCert (zInd s at' p d0 d1) := sorry

/-- **GENERALIZED has-redex chain reduct off `seqSucc = ⊥` — NAMED sub-`sorry` (leaf 2).** The off-`⊥` twin of
`genReduct_chain_hasRedex` (`:3048`). ∀-redex sub-case: clean port (certFlatten generalized). ¬-redex
sub-case: the `keepTip` needs the `⊥`-exit — the deep blocker. -/
lemma genReduct_chain_hasRedex_anySucc {s r ds i0 j1 j0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hreg : ZRegular (zK s r ds)) (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hij : i0 < j1) (hj1 : j1 ≤ j0) (hpair : isRedexPair ds (⟪i0, j1⟫ : V)) :
    GenReductCert (zK s r ds) := sorry

/-- **GENERALIZED no-redex chain reduct off `seqSucc = ⊥` — NAMED sub-`sorry` (leaf 3).** The off-`⊥` twin of
`genReduct_chain_noRedex` (`:3365`), with the IH DROPPING the `seqSucc = ⊥` clause (so it fires on a
`{3,4}` producer of ANY succedent — what `axMajorResidual` needs). The `{3,4}`-producer + tag-5/6→producer
threads CLOSE via the general IH + `certReplace_of_premise_cert` (`noRedex_producer_closes`, lap 158); the
leaf `C∈Γ` / tag-1/2 R-intro / ex-falso closes need general-`C` reducts. -/
lemma genReduct_chain_noRedex_anySucc {s r ds j0 : V}
    (hZ : ZDerivation (zK s r ds))
    (hreg : ZRegular (zK s r ds)) (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hnolow : ¬ ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V))
    (IH : ∀ i < lh ds, ZRegular (znth ds i) → ZFresh (znth ds i) → ZSeqAnt (znth ds i) →
        (zTag (znth ds i) = 3 ∨ zTag (znth ds i) = 4) →
        GenReductCert (znth ds i)) :
    GenReductCert (zK s r ds) := sorry

/-- **GENERALIZED chain step off `seqSucc = ⊥` — PROVEN dispatcher.** Off-`⊥` twin of
`genReduct_botSucc_chain` (`:3655`): extract SOME `isChainInf` exit `j0` (`chainAsucc ds j0 ∈ {seqSucc s, ⊥}`,
the `⊥`-exit is the ex-falso fallback) from `zKValidF`, then `by_cases` a redex below `j0` → the generalized
has-redex or no-redex leaves. The IH is the general (no `⊥`-clause) per-premise certificate. -/
lemma genReduct_anySucc_chain {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hreg : ZRegular (zK s r ds)) (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (IH : ∀ i < lh ds, ZRegular (znth ds i) → ZFresh (znth ds i) → ZSeqAnt (znth ds i) →
        (zTag (znth ds i) = 3 ∨ zTag (znth ds i) = 4) →
        GenReductCert (znth ds i)) :
    GenReductCert (zK s r ds) := by
  obtain ⟨j0, hj0, hAj0, hthread0, hrank0⟩ := (zKValidF_of_ZDerivation_zK hZ).1
  by_cases hlow : ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V)
  · obtain ⟨i0, j1, hij, hj1, hpair⟩ := hlow
    exact genReduct_chain_hasRedex_anySucc hZ hreg hfresh hseqant hj0 hAj0 hthread0 hrank0 hij hj1 hpair
  · exact genReduct_chain_noRedex_anySucc hZ hreg hfresh hseqant hj0 hAj0 hthread0 hrank0 hlow IH

/-- **THE general-succedent `Rep`-node reduction `genReduct_anySucc` — PROVEN entry (off `⊥`).** A `Rep` node
`d` (tag ∈ {3,4}) deriving `Γ→F` for ANY `F` has a `GenReductCert d`. Identical CODE-induction structure to
`genReduct_botSucc` (`:3682`), only the `seqSucc (fstIdx d) = ⊥` antecedent is DROPPED from the motive (the
`𝚺₁` motive `GenReductCert` is definable without it; the code-IH threads; tag-3/4 delegate to the
generalized sub-reducts). **This is the single key that closes both `axMajorResidual` and
`descent_step_K_noncrit_axMajor`** (each via recursing into the `{3,4}` cut-partner). -/
lemma genReduct_anySucc {d : V} (hZ : ZDerivation d) (hreg : ZRegular d) (hfresh : ZFresh d)
    (hseqant : ZSeqAnt d) (htag : zTag d = 3 ∨ zTag d = 4) :
    GenReductCert d := by
  have key : ∀ d : V, ZDerivation d → ZRegular d → ZFresh d → ZSeqAnt d →
      (zTag d = 3 ∨ zTag d = 4) → GenReductCert d := by
    apply zDerivation_sigma_induction
      (P := fun d : V => ZRegular d → ZFresh d → ZSeqAnt d →
        (zTag d = 3 ∨ zTag d = 4) → GenReductCert d)
    · -- motive definability: `GenReductCert` banked `𝚺₁`; antecedents `𝚫₁` (no `⊥`-clause to carry)
      unfold ZRegular ZFresh ZSeqAnt; definability
    · -- inductive step: dispatch on the rule; the code-IH `hC` gives `P` on every premise
      intro C hC d hphi
      have hZd : ZDerivation d := zDerivation_iff.mpr (zphi_monotone (fun x hx => (hC x hx).1) hphi)
      intro hreg hfresh hseqant htag
      rcases hphi with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
        ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, hmem, _⟩ |
        ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C', rfl, _⟩
      · simp at htag                                       -- zAtom (tag 0)
      · simp at htag                                       -- zIall (tag 1)
      · simp at htag                                       -- zIneg (tag 2)
      · -- zInd (tag 3): the generalized Ind reduct (no `seqSucc=⊥`)
        exact ind_reduct_anySucc hZd hreg hfresh hseqant
      · -- zK (tag 4): delegate to the generalized chain step, IH WITHOUT the `⊥`-clause
        refine genReduct_anySucc_chain hZd hreg hfresh hseqant ?_
        intro i hi hregi hfreshi hseqanti htagi
        exact (hC (znth ds i) (hmem i hi)).2 hregi hfreshi hseqanti htagi
      · simp at htag                                       -- zAxAll (tag 5)
      · simp at htag                                       -- zAxNeg (tag 6)
      · simp at htag                                       -- zAx1 (tag 7)
  exact key d hZ hreg hfresh hseqant htag

/-- **§14.254 FLATTEN — splice a chain premise's principal-cut halves `dⱼ{0}`,`dⱼ{1}` in place of `dⱼ`
(the genuine Buchholz §14.254 case-(ii) reduct, `iord`-DESCENT) — PROVEN.** A `∅→⊥` chain `zK s r ds`
with the `isChainInf` exit data, whose premise `i ≤ j0` reduces by §14.253 (a principal cut), is reduced
by REMOVING `dⱼ = znth ds i` and SPLICING its two cut-halves `a = dⱼ{0} ⊢ Γⱼ→B`, `b = dⱼ{1} ⊢ B,Γⱼ→Aⱼ`
into the premise sequence (`seqInsert ds i a b`). This is the FLATTEN the bare `seqUpdate`-replacement
canNOT do: when `dⱼ`'s reduct degree-trades (`õ` RISES, `idg` drops), a single same-end-sequent
replacement does NOT lower the outer `iord` (`iotil_zK` is `õ`-only, `idg_zK` pinned `≥ r` — the lap-150
in-kernel finding, judge-convergent `E-2026-06-26-JUDGE-splice-flatten-not-seqUpdate.md`); but the flatten
DESCENDS because both halves have `õ` STRICTLY below `õ dⱼ` (the principal-cut auxiliaries, N1 IH), so the
outer `õ`-fold strictly drops (`iord_descent_seqInsert'`, F2 `ω^{õa}#ω^{õb} ≺ ω^{õ dⱼ}`). Validity is the
genuine ordered-insert object (`isChainInf_seqInsert`/`ZDerivation_seqInsert_of`, the lap-87
order-sensitive object). The cut formula `B = seqSucc (fstIdx a)` now lives at the OUTER level with rank
`r' = max r (irk B) ≤ dg(parent)` (`hr'deg`). This is the genuine §14.254 splice engine; the residual is
only PRODUCING the halves (the reduced premise's principal-cut decomposition, exposed by the structured
genReduct certificate). -/
theorem descent_step_K_spliceHalves {s r r' ds i j0 a b : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hj0 : j0 < lh ds) (hij0 : i ≤ j0) (hbot0 : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ p ≤ j0, ∀ B, inAnt B (chainAnt ds p) →
        inAnt B (seqAnt s) ∨ ∃ p' < p, B = chainAsucc ds p')
    (hrank0 : ∀ p < j0, irk (chainAsucc ds p) ≤ r)
    (hZa : ZDerivation a) (hZb : ZDerivation b)
    (hrega : ZRegular a) (hregb : ZRegular b)
    (hfresha : ZFresh a) (hfreshb : ZFresh b)
    (hseqanta : ZSeqAnt a) (hseqantb : ZSeqAnt b)
    (ha_ant : seqAnt (fstIdx a) = chainAnt ds i)
    (hb_succ : seqSucc (fstIdx b) = chainAsucc ds i)
    (hb_ant : ∀ B, inAnt B (seqAnt (fstIdx b)) →
        B = seqSucc (fstIdx a) ∨ inAnt B (chainAnt ds i))
    (hfa_a : IsUFormula ℒₒᵣ (seqSucc (fstIdx a))) (hfa_b : IsUFormula ℒₒᵣ (seqSucc (fstIdx b)))
    (hrr : r ≤ r') (ha_rank : irk (seqSucc (fstIdx a)) ≤ r') (hr'deg : r' ≤ idg (zK s r ds))
    (ha_otil : icmp (iotil a) (iotil (znth ds i)) = 0)
    (hb_otil : icmp (iotil b) (iotil (znth ds i)) = 0)
    (ha_idg : idg a ≤ idg (znth ds i)) (hb_idg : idg b ≤ idg (znth ds i)) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hi : i < lh ds := lt_of_le_of_lt hij0 hj0
  -- chain validity of the genuine ordered-insert object (lap-87)
  have hci : isChainInf s r' (seqInsert ds i a b) :=
    isChainInf_seqInsert hj0 hij0 (Or.inr hbot0) hthread0 hrank0
      ha_ant ha_rank hb_succ hb_ant hrr
  -- the spliced `ZDerivation`
  have hZ' : ZDerivation (zK s r' (seqInsert ds i a b)) :=
    ZDerivation_seqInsert_of hi hZ hZa hZb hci
      (iperm_tp_fstIdx_of_ZDerivation hZa) (iperm_tp_fstIdx_of_ZDerivation hZb)
      (zKValidF_leafconds_of_ZDerivation hZa).1 (zKValidF_leafconds_of_ZDerivation hZb).1
      (zKValidF_leafconds_of_ZDerivation hZa).2.1 (zKValidF_leafconds_of_ZDerivation hZb).2.1
      (zKValidF_leafconds_of_ZDerivation hZa).2.2.1 (zKValidF_leafconds_of_ZDerivation hZb).2.2.1
      (zKValidF_leafconds_of_ZDerivation hZa).2.2.2 (zKValidF_leafconds_of_ZDerivation hZb).2.2.2
      hfa_a hfa_b
  -- NF facts for the descent
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := isNF_iotil_znth_of_ZDerivation_zK hZ
  refine ⟨zK s r' (seqInsert ds i a b), ⟨⟨hZ', ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [fstIdx_zK]; exact hant
  · rw [fstIdx_zK]; exact hsucc
  · exact ZRegular_zK_of_seqInsert hi (fun m hm => ZRegular_zK_premise hds hd.2.1 hm) hrega hregb
  · exact ZFresh_zK_of_seqInsert hi (fun m hm => ZFresh_zK_premise hds hd.2.2.1 hm) hfresha hfreshb
  · exact ZSeqAnt_zK_of_seqInsert (seqAntSeqFlag_zK_of_ZSeqAnt hd.2.2.2) hi
      (fun m hm => ZSeqAnt_zK_premise hds hd.2.2.2 hm) hseqanta hseqantb
  · exact iord_descent_seqInsert' hds hi hnf hr'deg ha_otil hb_otil ha_idg hb_idg hNF
      (isNF_iotil_of_ZDerivation a hZa) (isNF_iotil_of_ZDerivation b hZb)

/-- **§14.254a — `Rep` major premise (tags 3,4): reduce it and SPLICE — sorry-FREE (lap 151).** No redex below
the exit `j0`; the faithful major premise `dₘ = znth ds (majorIdx)` is a `zInd` (3) or sub-`zK` (4), `tp = Rep`.
`genReduct_botSucc dₘ` returns the structured `GenReductCert`: either (`Or.inl`) a single `õ`-dropping REPLACE
reduct → the banked `descent_step_K_replace`, or (`Or.inr`) the two FLATTEN halves of `dₘ`'s own principal cut
→ the banked `descent_step_K_spliceHalves` at `i = majorIdx`. **This DROPS the false lap-150b
`descent_step_K_splice`** (the single-premise `seqUpdate`+combined-`iord` splice, refuted in-kernel lap 151 —
`õ` rises under a degree-traded premise, the outer `iord` does NOT descend). `majorIdx ≤ j0` because the
`isChainInf` ⊥-exit `j0` is itself a major premise (`isMajorPrem`). -/
theorem descent_step_K_noncrit_repMajor {s r ds j0 : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hj0 : j0 < lh ds) (hbot0 : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hnolow : ¬ ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V))
    (htag : zTag (znth ds (majorIdx (zK s r ds))) = 3 ∨ zTag (znth ds (majorIdx (zK s r ds))) = 4) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨hmlt, hmbot, _, _⟩ := majorIdx_botOrbit_reducible hZ hant hsucc
  have hregm : ZRegular (znth ds (majorIdx (zK s r ds))) := ZRegular_zK_premise hds hd.2.1 hmlt
  have hfreshm : ZFresh (znth ds (majorIdx (zK s r ds))) := ZFresh_zK_premise hds hd.2.2.1 hmlt
  have hseqantm : ZSeqAnt (znth ds (majorIdx (zK s r ds))) := ZSeqAnt_zK_premise hds hd.2.2.2 hmlt
  -- `majorIdx ≤ j0`: the ⊥-exit `j0` is a major premise (`chainAsucc ds j0 = ⊥ = seqSucc s`)
  have hmaj0 : isMajorPrem ds s j0 := by show chainAsucc ds j0 = seqSucc s; rw [hbot0, hsucc]
  have hmj0 : majorIdx (zK s r ds) ≤ j0 := by
    rw [majorIdx, zKseq_zK, fstIdx_zK]
    exact majorIdxAux_le_of_isMajorPrem ds s (lh ds) j0 hj0 hmaj0
  rcases genReduct_botSucc (hmem _ hmlt) hregm hfreshm hseqantm hmbot htag with
    ⟨v, hZv, hregv, hfreshv, hseqantv, hvfst, hdesc⟩ |
    ⟨a, b, hZa, hZb, hrega, hregb, hfresha, hfreshb, hseqanta, hseqantb,
      ha_ant, hb_succ, hb_thr, hfa_a, hfa_b, hrank_b, ha_otil, hb_otil, ha_idg, hb_idg⟩
  · -- REPLACE (`õ`-drop single reduct) → the banked `descent_step_K_replace`
    exact descent_step_K_replace hd hmlt hZv hregv hfreshv hseqantv hvfst hdesc
  · -- FLATTEN (the principal-cut halves) → `descent_step_K_spliceHalves` (PROVEN lap 151)
    have hidgm : idg (znth ds (majorIdx (zK s r ds))) ≤ iseqMaxIdg ds :=
      le_iseqMaxIdgAux (lh ds) (majorIdx (zK s r ds)) hmlt
    have hrankidg : irk (seqSucc (fstIdx a)) ≤ idg (zK s r ds) := by
      rw [idg_zK s r ds hds]
      exact le_trans (le_pred_of_lt (succ_le_iff_lt.mp (le_trans hrank_b hidgm)))
        (le_max_right r (iseqMaxIdg ds - 1))
    refine descent_step_K_spliceHalves hd hant hsucc hj0 hmj0 hbot0 hthread0 hrank0
      hZa hZb hrega hregb hfresha hfreshb hseqanta hseqantb ha_ant hb_succ ?_ hfa_a hfa_b
      (le_max_left r _) (le_max_right r _) (max_le (r_le_idg_zK s r ds hds) hrankidg)
      ha_otil hb_otil ha_idg hb_idg
    · intro B hB
      obtain ⟨k, hk, hkB⟩ := hB
      rcases hb_thr k hk with h | h
      · exact Or.inl (hkB ▸ h)
      · exact Or.inr (hkB ▸ h)

/-- **§14.254b — L-axiom major premise (tags 5,6): replace its upstream `Rep` cut-partner (named
sub-`sorry`).** No redex below the exit; the faithful major premise is `zAxAll`/`zAxNeg` (a `red`-FIXPOINT) with
active formula `V` (`^∀p`/`inegF p`). `V` agrees with the succedent of a strictly-earlier premise `i′`
(`majorPrem_zAxAll_cutPartner`/`_zAxNeg_cutPartner`); since there is no redex, `i′` is NOT a direct R-intro, so
`tp(d_{i′}) = Rep` and `d_{i′}`'s reduct keeps the end-sequent. Closure: produce `d_{i′}`'s strictly-descending
regular/fresh/seqAnt `ZDerivation` reduct (the GENERAL `Γ→⊥` reduction on the smaller premise `d_{i′}`) and feed
`descent_step_K_replace` at `i = i′`. The replace plumbing is banked; the residual is the cut-partner reduct. -/
theorem descent_step_K_noncrit_axMajor {s r ds j0 : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hj0 : j0 < lh ds) (hbot0 : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hnolow : ¬ ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V))
    (htag : zTag (znth ds (majorIdx (zK s r ds))) = 5 ∨ zTag (znth ds (majorIdx (zK s r ds))) = 6) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := sorry

/-- **§5.2 no-redex residual — sorry-FREE major-premise DISPATCHER (lap 148).** No redex pair below the
`isChainInf` exit `j0`. By `majorPrem_tag_mem` the faithful major premise's tag ∈ {3,4,5,6}: routes tag-3/4
(`Rep` major) → `descent_step_K_noncrit_repMajor` (§14.254a replace the major premise), tag-5/6 (L-axiom major)
→ `descent_step_K_noncrit_axMajor` (§14.254b replace the upstream cut-partner). This restores the faithful
Buchholz §14.254a/b split (lap-147 collapsed it into one residual with a docstring that wrongly claimed all
cases replace the major premise — false for the tag-5/6 `red`-FIXPOINT L-axioms, lap-130 finding
`InternalZ:9281`). Both leaves now consume the banked `descent_step_K_replace`. -/
theorem descent_step_K_noncrit_recurse {s r ds j0 : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hj0 : j0 < lh ds) (hbot0 : chainAsucc ds j0 = (^⊥ : V))
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hnolow : ¬ ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V)) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  rcases majorPrem_tag_mem hZ hant hsucc with h | h | h | h
  · exact descent_step_K_noncrit_repMajor hd hant hsucc hj0 hbot0 hthread0 hrank0 hnolow (Or.inl h)
  · exact descent_step_K_noncrit_repMajor hd hant hsucc hj0 hbot0 hthread0 hrank0 hnolow (Or.inr h)
  · exact descent_step_K_noncrit_axMajor hd hant hsucc hj0 hbot0 hthread0 hrank0 hnolow (Or.inl h)
  · exact descent_step_K_noncrit_axMajor hd hant hsucc hj0 hbot0 hthread0 hrank0 hnolow (Or.inr h)

/-- **Non-critical case (Buchholz §3.2 case 5.2) — sorry-FREE has-redex/no-redex DISPATCHER (lap 147).**
Extracts the `isChainInf` exit `j0` (with threading/rank/⊥-exit) from `zKValidF`, then case-splits on whether
a redex pair exists below `j0`: YES → `descent_step_K_hasRedex` (PROVEN, the criticality-free `iRKcCrit` cut);
NO → `descent_step_K_noncrit_recurse` (the general-reduction residual). The has-redex half — Buchholz's §14.253
principal cut — is now DISCHARGED for non-critical chains, leaving only the §14.254 major-premise recursion.
`hncrit` is unused (the split is faithful for any ⊥-orbit chain) but kept to match `descent_step_K_majorIdx`. -/
theorem descent_step_K_noncritical {s r ds : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hncrit : permIdx (zK s r ds) < lh ds) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  have hZ : ZDerivation (zK s r ds) := hd.1.1
  obtain ⟨j0, hj0, hAj0, hthread0, hrank0⟩ := (zKValidF_of_ZDerivation_zK hZ).1
  have hbot0 : chainAsucc ds j0 = (^⊥ : V) := hAj0.elim (fun h => h.trans hsucc) id
  by_cases hlow : ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V)
  · obtain ⟨i0, j1, hij, hj1, hpair⟩ := hlow
    exact descent_step_K_hasRedex hd hant hsucc hj0 hbot0 hthread0 hrank0 hij hj1 hpair
  · exact descent_step_K_noncrit_recurse hd hant hsucc hj0 hbot0 hthread0 hrank0 hlow

/-- **NAMED sub-`sorry` #1 — the per-step K-case math, a sorry-FREE critical/non-critical DISPATCHER
(lap 141).** A regular `∅→⊥` K-node has a SOUND, strictly-`iord`-descending reduct. Case-splits on the
`permIdx` criticality sentinel (Buchholz Def 3.2 case 5): critical (`¬ permIdx < lh ds`) →
`descent_step_K_critical` (CLOSED RED-FREE via `iRKcCrit`, lap 143/144); non-critical →
`descent_step_K_noncritical` (case 5.2). Pure plumbing — the deep content is now the single non-critical
leaf, and the tag-5/6 producer-principal wall is gone (the critical case is fully discharged, off `red`). -/
theorem descent_step_K_majorIdx {s r ds : V}
    (hd : ZDerivesEmptyR (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V)) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord (zK s r ds)) = 0 := by
  by_cases hcrit : permIdx (zK s r ds) < lh ds
  · exact descent_step_K_noncritical hd hant hsucc hcrit
  · exact descent_step_K_critical hd hcrit

/-- **(E') the existence-form one-step descent.** Every regular ⊥-orbit code has a sound, strictly-
descending reduct — Ind root via `descent_step_Ind` (RED-FREE, lap 144), K root via `descent_step_K_majorIdx`
(critical off `red`, laps 143/144). NO `red` anywhere on this path: the dispatch is the `zTag = 3 (Ind)` /
`= 4 (K)` split, both witnessed by genuine reducts. (A cut-free `∅→⊥` is absurd; `majorIdx`/`iIndReductSeqG`
always supply a reducible step.) -/
theorem ZDerivesEmptyR_descent_step {d : V} (hd : ZDerivesEmptyR d) :
    ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord d) = 0 := by
  rcases zTag_Ind_or_K_of_ZDerivesEmpty hd.1 with htag | htag
  · -- Ind root (zTag = 3): witness with the corrected `iIndReductSeqG` reduct, NOT `red`
    rcases zDerivation_iff.mp hd.1.1 with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ |
      ⟨s, p, d0, rfl, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
      ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    · simp at htag
    · simp at htag
    · simp at htag
    · exact descent_step_Ind hd
    · simp at htag
    · simp at htag
    · simp at htag
    · simp at htag
  · rcases zDerivation_iff.mp hd.1.1 with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ |
      ⟨s, p, d0, rfl, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
      ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    · simp at htag
    · simp at htag
    · simp at htag
    · simp at htag
    · have hant : seqAnt s = (∅ : V) := by have h := hd.1.2.1; rwa [fstIdx_zK] at h
      have hsucc : seqSucc s = (^⊥ : V) := by have h := hd.1.2.2; rwa [fstIdx_zK] at h
      exact descent_step_K_majorIdx hd hant hsucc
    · simp at htag
    · simp at htag
    · simp at htag

variable (V) in
/-- **Internal `PRWO(ε₀)` — the crux-1 deliverable, as an explicit hypothesis (lap 137).** No
`𝚺₁`-definable internal sequence `f : V → V` of NF (`ε₀`) codes is everywhere strictly `icmp`-descending
— i.e. there is no infinite `𝚺₁`-definable `ε₀`-descent.

⚠️ This is **NOT** an `𝗜𝚺₁`/`𝗣𝗔` theorem: it is exactly the PA-unprovable principle `PRWO(ε₀)`. Crux 1
(`Reduction`/`StdCor34`, Rathjen §3) derives it *from* `V ⊧ γ` (the Goodstein sentence): an everywhere-
`icmp`-descending `𝚺₁` sequence feeds `bbeta`/`nonterminating_internal` to build a non-terminating
internal Goodstein run, contradicting `V ⊧ γ`. Threading it as a HYPOTHESIS (not a goal) is what makes
the termination half provable — see the `⚠️ TYPE-CORRECTED` note on `prwo_forbids_existence_descent`. -/
def InternalPRWO : Prop :=
  ∀ f : V → V, (𝚺₁-Function₁ f) → (∀ n : V, isNF (f n)) → ¬ (∀ n : V, icmp (f (n + 1)) (f n) = 0)

/-- **(A) NAMED sub-`sorry` (lap 137) — the descending `𝚺₁` STEP function.** From the existence step (E'),
a *total* `𝚺₁`-definable `g : V → V` that, on every `ZDerivesEmptyR` point `w`, returns a strictly-`iord`-
descending `ZDerivesEmptyR`-reduct `g w`. This is the deterministic carrier the orbit iterates.

⚠️ **DEFINABILITY crux (lap-137 finding) + parameter-free strengthening (lap 138):** the conclusion now
demands an **explicit parameter-free graph** `gDef : 𝚺₁.Semisentence 2` for `g` (not just the parametrized
`𝚺₁-Function₁ g`), because the orbit (B0)/`IIter.iIter` needs a `Semisentence` to fill `PR.Blueprint.succ`.
A concrete engine reduct supplies it for free (`iord`/`icmp`/`ZDerivesEmptyR` are all parameter-free).
The natural witness `g w := μ d'. [ZDerivesEmptyR d' ∧ icmp (iord d') (iord w) = 0]` has a `𝚫₁` matrix
(`ZDerivesEmptyR` `𝚫₁`; `iord` `𝚺₁`; `icmp _ = 0` `𝚫₁`), so its *minimality* clause `∀ z < d', ¬P w z` is
`𝚫₁` — BUT the *totality guard* `∃ d', P w d'` is `𝚺₁` (unbounded witness; reducts can be larger codes than
`w`), the wrong polarity for a `𝚺₁` graph. **Fix = a primrec WITNESS BOUND** `∃ d' ≤ B(w), P w d'` (then
bounded-`μ` is `𝚫₁`-total; see `wip/WitnessBound.lean`), OR derive `g` deterministically once
`ZDerivesEmptyR_descent_step`/`descent_step_K_majorIdx` give a *constructive* reduct (Ind = `red d`; K = the
critical reduct) rather than a bare `∃`. Either route delivers the `gDef`. -/
theorem exists_sigma1_descending_step
    (hstep : ∀ d : V, ZDerivesEmptyR d → ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord d) = 0) :
    ∃ (g : V → V) (gDef : 𝚺₁.Semisentence 2), 𝚺₁.DefinedFunction₁ g gDef ∧
      (∀ w : V, ZDerivesEmptyR w → ZDerivesEmptyR (g w) ∧ icmp (iord (g w)) (iord w) = 0) := sorry

/-- **(B0) PROVEN (lap 138) — the reusable internal-iteration linchpin.** Any `𝚺₁`-definable
`g : V → V` *with an explicit parameter-free graph* `gDef : 𝚺₁.Semisentence 2` has a `𝚺₁`-definable
internal iteration `orbit : V → V` with `orbit 0 = z`, `orbit (n+1) = g (orbit n)` over INTERNAL `n : V`.

**Discharge (lap 138):** the generic Foundation iteration combinator the lap-137 baton looked for in HFS
DOES exist — the repo built it for crux-1 in `IIter.lean` (`IIter.iIter gDef g hg x c = g^[c] x`, a genuine
`𝚺₁` `PR.Construction` with `iIter_zero`/`iIter_succ`/`iIter_definable'`). So `orbit n := iIter gDef g hg z n`.
The lap-137 parameter-free SUBTLETY is exactly why the hypothesis is the explicit `DefinedFunction₁ g gDef`
(parameter-free `gDef`) and NOT the parametrized `𝚺₁-Function₁ g`: `PR.Blueprint.succ` needs a `Semisentence`,
which the concrete descending step from (A) (built from `iord`/`icmp`/`ZDerivesEmptyR`, all parameter-free)
supplies. -/
theorem exists_sigma1_iterate (g : V → V) {gDef : 𝚺₁.Semisentence 2}
    (hg : 𝚺₁.DefinedFunction₁ g gDef) (z : V) :
    ∃ orbit : V → V, (𝚺₁-Function₁ orbit) ∧ orbit 0 = z ∧ (∀ n : V, orbit (n + 1) = g (orbit n)) := by
  refine ⟨fun n => IIter.iIter gDef g hg z n, ?_, by simp, fun n => by simp⟩
  exact DefinableFunction₂.comp (F := IIter.iIter gDef g hg)
    (hF := IIter.iIter_definable' (hf := hg) 𝚺) (DefinableFunction.const z) (DefinableFunction.var 0)

/-- **(B) the internal `𝚺₁` ORBIT of a descending step → the `𝚺₁` `ε₀`-descent** — now a composition of the
iteration linchpin (B0) with `𝚺₁`-induction. Given a total `𝚺₁` step `g` descending on `ZDerivesEmptyR`,
`f n := iord (orbit n)` is `𝚺₁`, NF (`isNF_iotower`+`isNF_iotil_of_ZDerivation`, each orbit point a
`ZDerivation`), and `icmp`-descends (`hg_step` at each point). Membership `∀ n, ZDerivesEmptyR (orbit n)` is
internal `𝚺₁`-induction. This internalizes the EXTERNAL-ℕ `iord_iR2_iterate_descends` (`InternalZ:9816`). -/
theorem exists_sigma1_descent_of_sigma1_step
    {z : V} (hz : ZDerivesEmptyR z) (g : V → V) {gDef : 𝚺₁.Semisentence 2}
    (hg : 𝚺₁.DefinedFunction₁ g gDef)
    (hg_step : ∀ w : V, ZDerivesEmptyR w → ZDerivesEmptyR (g w) ∧ icmp (iord (g w)) (iord w) = 0) :
    ∃ f : V → V, (𝚺₁-Function₁ f) ∧ (∀ n : V, isNF (f n)) ∧
      (∀ n : V, icmp (f (n + 1)) (f n) = 0) := by
  obtain ⟨orbit, horbit, horbit0, horbit_succ⟩ := exists_sigma1_iterate g hg z
  -- every orbit point is a regular ⊥-derivation (internal 𝚺₁-induction with the descending step)
  have hmem : ∀ n : V, ZDerivesEmptyR (orbit n) := by
    have hP : 𝚺₁-Predicate (fun n => ZDerivesEmptyR (orbit n)) := by
      haveI : 𝚺₁-Function₁ orbit := horbit
      unfold ZDerivesEmptyR ZDerivesEmpty ZRegular ZFresh ZSeqAnt
      definability
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hP
    case zero => rw [horbit0]; exact hz
    case succ n ih => rw [horbit_succ]; exact (hg_step (orbit n) ih).1
  refine ⟨fun n => iord (orbit n), ?_, fun n => ?_, fun n => ?_⟩
  · -- 𝚺₁-Function₁ (iord ∘ orbit)
    haveI : 𝚺₁-Function₁ orbit := horbit
    definability
  · -- NF: isNF (iord (orbit n)) = isNF (iotower (iotil (orbit n)) (idg (orbit n)))
    exact isNF_iotower (isNF_iotil_of_ZDerivation _ (hmem n).1.1) _
  · -- descent: icmp (iord (orbit (n+1))) (iord (orbit n)) = 0
    show icmp (iord (orbit (n + 1))) (iord (orbit n)) = 0
    rw [horbit_succ]
    exact (hg_step (orbit n) (hmem n)).2

/-- **NAMED sub-`sorry` #2′ (lap 137) — the genuine remaining termination content**, now a sorry-FREE
composition of the descending `𝚺₁` step (A) with the internal `𝚺₁` orbit (B). From the existence step (E'),
build a `𝚺₁`-definable infinite `ε₀`-descent. This is the V-internal analog of `iord_iR2_iterate_descends`
(`InternalZ:9816`) with the EXTERNAL-ℕ iteration internalized as a `𝚺₁` orbit. -/
theorem exists_sigma1_descent_of_step
    (hstep : ∀ d : V, ZDerivesEmptyR d → ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord d) = 0)
    {z : V} (hz : ZDerivesEmptyR z) :
    ∃ f : V → V, (𝚺₁-Function₁ f) ∧ (∀ n : V, isNF (f n)) ∧
      (∀ n : V, icmp (f (n + 1)) (f n) = 0) := by
  obtain ⟨g, gDef, hg, hg_step⟩ := exists_sigma1_descending_step hstep
  exact exists_sigma1_descent_of_sigma1_step hz g hg hg_step

/-- **⚠️ TYPE-CORRECTED (lap 137) — the M3 PRWO contradiction, now with the PRWO hypothesis it needs.**
The lap-135 statement concluded `False` in bare `[V ⊧ₘ* 𝗜𝚺₁]` with NO `PRWO`/`γ` hypothesis — and is
**UNPROVABLE as so typed**: if it AND `hstep` (= `ZDerivesEmptyR_descent_step`, the per-step cut-reduction
descent, a genuine `𝗜𝚺₁` fact) were both `𝗜𝚺₁`-provable, then `𝗜𝚺₁ ⊢ ¬∃z, ZDerivesEmptyR z`, i.e.
`Con(𝗣𝗔)` (via M2 `Z ⊇ 𝗣𝗔`) — Gödel-barred. Since the per-step descent IS `𝗜𝚺₁`, the termination half is
the one carrying the PA-unprovable strength, which must enter as a hypothesis. Now a sorry-FREE composition
of `exists_sigma1_descent_of_step` (the `𝚺₁` descent) with `InternalPRWO` (= crux 1's deliverable). -/
theorem prwo_forbids_existence_descent (hprwo : InternalPRWO V)
    (hstep : ∀ d : V, ZDerivesEmptyR d → ∃ d', ZDerivesEmptyR d' ∧ icmp (iord d') (iord d) = 0)
    {z : V} (hz : ZDerivesEmptyR z) : False := by
  obtain ⟨f, hf, hnf, hdesc⟩ := exists_sigma1_descent_of_step hstep hz
  exact hprwo f hf hnf hdesc

/-- **M3 — the Gentzen `False`, a sorry-FREE composition** of the existence step (E') with the PRWO
obligation, under the `InternalPRWO` (crux-1/`γ`) hypothesis. (Was a bare `sorry`; lap-135 decomposed it,
lap-137 type-corrected the PRWO seam — it concluded `False` in bare `𝗜𝚺₁`, which is Gödel-barred.) -/
theorem false_of_ZDerivesEmpty (hprwo : InternalPRWO V) {z : V} (hz : ZDerivesEmptyR z) : False :=
  prwo_forbids_existence_descent hprwo (fun _ hd => ZDerivesEmptyR_descent_step hd) hz

end GoodsteinPA.InternalZ
