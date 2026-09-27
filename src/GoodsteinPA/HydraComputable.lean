/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA.ONoteComp
import GoodsteinPA.HydraEscape

/-!
# The canonical hydra battle is computable on codes (stage 2, part B)

Target: `Computable₂ (fun m N => toCode (battle (ofCode m) N))`, from which
`exists_sigma1_battle_def` follows by Foundation's `codeOfPartrec'`.

Everything runs on codes.  A hydra code `c` lists its children's codes (`childC`, inverse `nodeC`,
Cantor pairing as in `ofCode`/`toCode`), and every child code is `< c`, so each hydra function is a
`Computable.nat_strong_rec` on codes — the `ONoteComp.computable_Cnat` pattern.
-/

namespace GoodsteinPA.Hydra

open ONote LeanGallery.Logic.Hydra LeanGallery.Logic.Hydra.Hydra
open GoodsteinPA.Epsilon0Complete GoodsteinPA.ONoteComp

/-! ### (a) Child-code lists -/

/-- The codes of the children of the hydra with code `c`. -/
def childC : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    have := Nat.unpair_right_le n
    (Nat.unpair n).1 :: childC (Nat.unpair n).2
termination_by c => c
decreasing_by omega

/-- The code of the hydra whose children have the given codes. -/
def nodeC : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (nodeC l) + 1

theorem toCode_node (cs : List Hydra) : toCode (node cs) = nodeC (cs.map toCode) := by
  induction cs with
  | nil => rw [toCode]; rfl
  | cons c cs ih => rw [toCode, ih]; rfl

theorem childC_nodeC : ∀ l : List ℕ, childC (nodeC l) = l
  | [] => by rw [nodeC, childC]
  | a :: l => by rw [nodeC, childC]; simp [Nat.unpair_pair, childC_nodeC l]

theorem ofCode_eq (c : ℕ) : ofCode c = node ((childC c).map ofCode) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | n
    · rw [childC, ofCode]; rfl
    · rw [ofCode, childC]
      have := Nat.unpair_right_le n
      rw [ih _ (by omega)]
      simp

theorem childC_toCode_node (cs : List Hydra) : childC (toCode (node cs)) = cs.map toCode := by
  rw [toCode_node, childC_nodeC]

theorem lt_of_mem_childC : ∀ {c a : ℕ}, a ∈ childC c → a < c
  | 0, _, h => by rw [childC] at h; simp at h
  | n + 1, a, h => by
    rw [childC] at h
    have h1 := Nat.unpair_left_le n
    have h2 := Nat.unpair_right_le n
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := lt_of_mem_childC h'; omega

theorem primrec_nodeC : Primrec nodeC := by
  have : nodeC = fun l => l.foldr (fun a acc => Nat.pair a acc + 1) 0 := by
    funext l; induction l with
    | nil => rfl
    | cons a l ih => simp [nodeC, ih]
  rw [this]
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))).to₂

/-! ### A three-way selector on comparison codes (`lt = 0`, `eq = 1`, `gt = 2`) -/

def sel3 (r x0 x1 x2 : ℕ) : ℕ := if r = 0 then x0 else if r = 1 then x1 else x2

theorem primrec_sel3 : Primrec (fun q : ℕ × ℕ × ℕ × ℕ => sel3 q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold sel3
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.fst.comp Primrec.snd)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem computable_sel3 {α : Type*} [Primcodable α] {r x0 x1 x2 : α → ℕ} (hr : Computable r)
    (h0 : Computable x0) (h1 : Computable x1) (h2 : Computable x2) :
    Computable fun a => sel3 (r a) (x0 a) (x1 a) (x2 a) :=
  primrec_sel3.to_comp.comp (hr.pair (h0.pair (h1.pair h2)))

theorem sel3_ordCode (o : Ordering) (x0 x1 x2 : ℕ) :
    sel3 (ordCode o) x0 x1 x2 = match o with | .lt => x0 | .eq => x1 | .gt => x2 := by
  cases o <;> rfl

/-! ### (b) `insertTerm` on ONote codes -/

/-- `insertTerm` transported to ONote codes. -/
def insC (e c : ℕ) : ℕ := encodeONote (insertTerm (decodeONote e) (decodeONote c))

/-- One step of the strong recursion for `insC e`, reading the table of values at codes `< c`. -/
def insStep (e : ℕ) (L : List ℕ) : Option ℕ :=
  if L.length = 0 then some (Nat.pair e (Nat.pair 0 0) + 1)
  else some (sel3 (Cnat (Nat.pair e (Nat.unpair (L.length - 1)).1))
    (Nat.pair (Nat.unpair (L.length - 1)).1
      (Nat.pair (Nat.unpair (Nat.unpair (L.length - 1)).2).1
        ((L[(Nat.unpair (Nat.unpair (L.length - 1)).2).2]?).getD 0)) + 1)
    (Nat.pair (Nat.unpair (L.length - 1)).1
      (Nat.pair ((Nat.unpair (Nat.unpair (L.length - 1)).2).1 + 1)
        (Nat.unpair (Nat.unpair (L.length - 1)).2).2) + 1)
    (Nat.pair e (Nat.pair 0 L.length) + 1))

theorem insStep_spec (e c : ℕ) : insStep e ((List.range c).map (insC e)) = some (insC e c) := by
  simp only [insStep, List.length_map, List.length_range]
  rcases c with _ | m
  · simp only [if_true]
    simp [insC, decodeONote, insertTerm, encodeONote, encodeONote_decodeONote]
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    congr 1
    have hb : (Nat.unpair (Nat.unpair m).2).2 < m + 1 := by
      have := Nat.unpair_right_le m
      have := Nat.unpair_right_le (Nat.unpair m).2
      omega
    rw [List.getElem?_map, List.getElem?_range hb, Option.map_some, Option.getD_some,
      Cnat_pair]
    have hdec : decodeONote (m + 1) = oadd (decodeONote (Nat.unpair m).1)
        ⟨(Nat.unpair (Nat.unpair m).2).1 + 1, Nat.succ_pos _⟩
        (decodeONote (Nat.unpair (Nat.unpair m).2).2) := by rw [decodeONote]
    unfold insC
    rw [hdec]
    rw [sel3_ordCode]
    cases hcmp : ONote.cmp (decodeONote e) (decodeONote (Nat.unpair m).1) <;>
      simp only [insertTerm, hcmp, encodeONote, encodeONote_decodeONote] <;>
      first | rfl | simp [Nat.pair_unpair]

theorem computable_insStep : Computable₂ insStep := by
  have hlen : Computable fun p : ℕ × List ℕ => p.2.length :=
    Computable.list_length.comp Computable.snd
  have hm : Computable fun p : ℕ × List ℕ => Nat.unpair (p.2.length - 1) :=
    Primrec.unpair.to_comp.comp (Primrec.nat_sub.to_comp.comp hlen (Computable.const 1))
  have ha : Computable fun p : ℕ × List ℕ => (Nat.unpair (p.2.length - 1)).1 :=
    Computable.fst.comp hm
  have hmm : Computable fun p : ℕ × List ℕ => Nat.unpair (Nat.unpair (p.2.length - 1)).2 :=
    Primrec.unpair.to_comp.comp (Computable.snd.comp hm)
  have hk : Computable fun p : ℕ × List ℕ => (Nat.unpair (Nat.unpair (p.2.length - 1)).2).1 :=
    Computable.fst.comp hmm
  have hb : Computable fun p : ℕ × List ℕ => (Nat.unpair (Nat.unpair (p.2.length - 1)).2).2 :=
    Computable.snd.comp hmm
  have hpair : Computable₂ Nat.pair := Primrec₂.natPair.to_comp
  have hr : Computable fun p : ℕ × List ℕ => Cnat (Nat.pair p.1 (Nat.unpair (p.2.length - 1)).1) :=
    computable_Cnat.comp (hpair.comp Computable.fst ha)
  have hL : Computable fun p : ℕ × List ℕ =>
      (p.2[(Nat.unpair (Nat.unpair (p.2.length - 1)).2).2]?).getD 0 :=
    Computable.option_getD (Computable.list_getElem?.comp Computable.snd hb) (Computable.const 0)
  have hsucc : Computable Nat.succ := Primrec.succ.to_comp
  have x0 : Computable fun p : ℕ × List ℕ =>
      Nat.pair (Nat.unpair (p.2.length - 1)).1
        (Nat.pair (Nat.unpair (Nat.unpair (p.2.length - 1)).2).1
          ((p.2[(Nat.unpair (Nat.unpair (p.2.length - 1)).2).2]?).getD 0)) + 1 :=
    hsucc.comp (hpair.comp ha (hpair.comp hk hL))
  have x1 : Computable fun p : ℕ × List ℕ =>
      Nat.pair (Nat.unpair (p.2.length - 1)).1
        (Nat.pair ((Nat.unpair (Nat.unpair (p.2.length - 1)).2).1 + 1)
          (Nat.unpair (Nat.unpair (p.2.length - 1)).2).2) + 1 :=
    hsucc.comp (hpair.comp ha (hpair.comp (hsucc.comp hk) hb))
  have x2 : Computable fun p : ℕ × List ℕ => Nat.pair p.1 (Nat.pair 0 p.2.length) + 1 :=
    hsucc.comp (hpair.comp Computable.fst (hpair.comp (Computable.const 0) hlen))
  have hz : Computable fun p : ℕ × List ℕ => decide (p.2.length = 0) :=
    (Primrec.eq.decide).to_comp.comp hlen (Computable.const 0)
  have hmain := Computable.option_some.comp
    (Computable.cond hz (hsucc.comp (hpair.comp Computable.fst (Computable.const (Nat.pair 0 0))))
      (computable_sel3 hr x0 x1 x2))
  have h2 : Computable fun p : ℕ × List ℕ => insStep p.1 p.2 := hmain.of_eq fun p => by
    simp only [insStep]
    by_cases h0 : p.2.length = 0 <;> simp [h0]
  exact h2.to₂

/-- **`insertTerm` is computable on ONote codes.** -/
theorem computable_insC : Computable₂ insC :=
  Computable.nat_strong_rec insC computable_insStep insStep_spec

/-! ### (c) The ordinal of a hydra, on codes -/

/-- The ONote code of `ord (ofCode c)`. -/
def ordC (c : ℕ) : ℕ := encodeONote (ord (ofCode c))

theorem ord_ofCode_succ (n : ℕ) :
    ord (ofCode (n + 1)) = insertTerm (ord (ofCode (Nat.unpair n).1)) (ord (ofCode (Nat.unpair n).2)) := by
  rw [ofCode]
  split
  rename_i cs hcs
  rw [ord_node, List.map_cons, hcs, ord_node]
  rfl

def ordStep (L : List ℕ) : Option ℕ :=
  if L.length = 0 then some 0
  else some (insC ((L[(Nat.unpair (L.length - 1)).1]?).getD 0)
    ((L[(Nat.unpair (L.length - 1)).2]?).getD 0))

theorem ordStep_spec (c : ℕ) : ordStep ((List.range c).map ordC) = some (ordC c) := by
  simp only [ordStep, List.length_map, List.length_range]
  rcases c with _ | n
  · simp only [ordC, ofCode, if_true]
    rw [show ord leaf = 0 from ord_leaf]
    rfl
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have h1 : (Nat.unpair n).1 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_left_le n)
    have h2 : (Nat.unpair n).2 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    rw [List.getElem?_map, List.getElem?_range h1, List.getElem?_map, List.getElem?_range h2]
    simp only [Option.map_some, Option.getD_some]
    simp [insC, ordC, ord_ofCode_succ, decodeONote_encodeONote]

theorem computable_ordStep : Computable ordStep := by
  have hlen : Computable fun L : List ℕ => L.length := Computable.list_length
  have hm : Computable fun L : List ℕ => Nat.unpair (L.length - 1) :=
    Primrec.unpair.to_comp.comp (Primrec.nat_sub.to_comp.comp hlen (Computable.const 1))
  have hA : Computable fun L : List ℕ => (L[(Nat.unpair (L.length - 1)).1]?).getD 0 :=
    Computable.option_getD (Computable.list_getElem?.comp Computable.id (Computable.fst.comp hm))
      (Computable.const 0)
  have hB : Computable fun L : List ℕ => (L[(Nat.unpair (L.length - 1)).2]?).getD 0 :=
    Computable.option_getD (Computable.list_getElem?.comp Computable.id (Computable.snd.comp hm))
      (Computable.const 0)
  have hz : Computable fun L : List ℕ => decide (L.length = 0) :=
    (Primrec.eq.decide).to_comp.comp hlen (Computable.const 0)
  have hmain := Computable.option_some.comp
    (Computable.cond hz (Computable.const 0) (computable_insC.comp hA hB))
  exact hmain.of_eq fun L => by
    simp only [ordStep]
    by_cases h0 : L.length = 0 <;> simp [h0]

theorem computable_ordC : Computable ordC := by
  have := Computable.nat_strong_rec (fun (_ : Unit) c => ordC c)
    (computable_ordStep.comp Computable.snd).to₂ (fun _ c => ordStep_spec c)
  exact this.comp (Computable.const ()) Computable.id

end GoodsteinPA.Hydra
