/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import PAComparator.Hydra.Support.Ordinal
import Mathlib.Logic.Hydra
import Mathlib.Tactic.Abel

/-! Comparator challenge support: the canonical battle and the input coding, verbatim from
`LeanGallery/Logic/Hydra/Canonical.lean`. -/

namespace LeanGallery.Logic.Hydra
open Hydra

/-- Index of the canonical child: the FIRST child of minimal ordinal. -/
def pickIdx : List Hydra → ℕ
  | [] => 0
  | [_] => 0
  | c :: d :: cs =>
    let j := pickIdx (d :: cs)
    match (d :: cs)[j]? with
    | some e => if ONote.cmp (ord e) (ord c) == .lt then j + 1 else 0
    | none => 0

/-- The canonical regrowing chop with `node ds` as the local root (its canonical child is not a
head): descend along canonical children until the canonical child's canonical child is a head,
then regrow `n + 1` copies one level up.  Output shapes are exactly `Chop.grand` / `Chop.deep`'s. -/
def chopC (n : ℕ) : Hydra → Hydra
  | node ds =>
    match hd : ds[pickIdx ds]? with
    | none => node ds
    | some (node es) =>
      match es[pickIdx es]? with
      | none => node ds
      | some (node []) =>
        node (ds.eraseIdx (pickIdx ds) ++ List.replicate (n + 1) (node (es.eraseIdx (pickIdx es))))
      | some _ =>
        have : sizeOf es < sizeOf ds := by
          have hm : node es ∈ ds := List.mem_of_getElem? hd
          have := List.sizeOf_lt_of_mem hm
          simp only [node.sizeOf_spec] at this; omega
        node (chopC n (node es) :: ds.eraseIdx (pickIdx ds))
termination_by h => sizeOf h

/-- **The canonical move at turn `n`.**  The dead hydra stays dead; a canonical child that is a
head is removed (`Step.root`); otherwise `chopC`. -/
def canonStep (n : ℕ) : Hydra → Hydra
  | node cs =>
    match cs[pickIdx cs]? with
    | none => leaf
    | some (node []) => node (cs.eraseIdx (pickIdx cs))
    | some _ => chopC n (node cs)

/-- The canonical battle from `h`, move `j` at turn `j`. -/
def battle (h : Hydra) : ℕ → Hydra
  | 0 => h
  | k + 1 => canonStep k (battle h k)

/-- **Input encoding (a bijection `ℕ ≃ Hydra`).**  `0` is the single head `leaf`;
`n + 1` with `n = ⟪a, b⟫` (Cantor pairing, `Nat.unpair`) is the hydra `ofCode b` with the extra
child `ofCode a` put in front. -/
def ofCode : ℕ → Hydra
  | 0 => leaf
  | n + 1 =>
    have := Nat.unpair_left_le n
    have := Nat.unpair_right_le n
    match ofCode n.unpair.2 with
    | node cs => node (ofCode n.unpair.1 :: cs)
termination_by n => n
decreasing_by all_goals omega

end LeanGallery.Logic.Hydra
