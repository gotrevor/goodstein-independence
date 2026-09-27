/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import PAComparator.Hydra.Support.Basic
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Tactic.Order

/-! Comparator challenge support: `insertTerm`, `sumTerms`, `ord`, verbatim from
`LeanGallery/Logic/Hydra/Ordinal.lean` (same imports, same names). -/

set_option linter.dupNamespace false

namespace LeanGallery.Logic.Hydra

open ONote Hydra

/-- Natural sum with one term: insert `ω^e` into the Cantor normal form `α`. -/
def insertTerm (e : ONote) : ONote → ONote
  | 0 => oadd e 1 0
  | oadd a n b =>
    match ONote.cmp e a with
    | .gt => oadd e 1 (oadd a n b)
    | .eq => oadd a (n + 1) b
    | .lt => oadd a n (insertTerm e b)

/-- Natural sum of `ω^e` over a list of exponents. -/
def sumTerms (l : List ONote) : ONote := l.foldr insertTerm 0

/-- **The Kirby–Paris ordinal of a hydra**: `ord (node cs) = ♯_{c ∈ cs} ω^{ord c}`. -/
def ord : Hydra → ONote
  | node cs => sumTerms (cs.attach.map fun ⟨c, _⟩ => ord c)

end LeanGallery.Logic.Hydra
