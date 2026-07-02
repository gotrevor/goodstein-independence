import GoodsteinPA.Hardy
open GoodsteinPA.FastGrowing ONote
-- Does f_α n ≤ f_{ω^α} n hold on small cases?  (α=1: f_ω vs f_1; α=0: f_1 vs f_0)
example : fastGrowing 1 2 ≤ fastGrowing (oadd 1 1 0) 2 := by native_decide
example : fastGrowing 0 3 ≤ fastGrowing (oadd 0 1 0) 3 := by native_decide
example : fastGrowing 2 2 ≤ fastGrowing (oadd 2 1 0) 2 := by native_decide
-- Is there already a Reaches from ω^α to α?  Probe the descent structure.
#check @fastGrowing_le_of_reaches
#check @Reaches
