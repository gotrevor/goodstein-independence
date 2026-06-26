import GoodsteinPA.Crux2Blueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote
namespace GoodsteinPA.InternalZ
variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

-- (1) reduct structure: znth 0 = d1, znth 1 = d0, lh = 2
example (d0 d1 : V) : znth (iIndReductSeq d0 d1 1) 0 = d1 := by
  rw [iIndReductSeq, znth_seqCons_of_lt (iRepeatSeq_seq d1 1) _ (by rw [iRepeatSeq_lh]; norm_num),
    znth_iRepeatSeq 0 (by norm_num)]
example (d0 d1 : V) : znth (iIndReductSeq d0 d1 1) 1 = d0 := by
  have := znth_seqCons_self (iRepeatSeq_seq d1 1) d0
  rw [iRepeatSeq_lh] at this; rw [iIndReductSeq]; exact this
example (d0 d1 : V) : lh (iIndReductSeq d0 d1 1) = 2 := by
  rw [iIndReductSeq, Seq.lh_seqCons _ (iRepeatSeq_seq d1 1), iRepeatSeq_lh]
