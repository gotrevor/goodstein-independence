/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Data.Multiset.Basic

/-! Comparator challenge support: the gallery's `Hydra` and `leaf`, verbatim from
`LeanGallery/Logic/Hydra/Basic.lean` (same import, same names; inductives are generative, so the
challenge re-declares them under the gallery's own names, as the gallery's `Comparator/Hydra` does). -/

set_option linter.dupNamespace false

namespace LeanGallery.Logic.Hydra

/-- A **hydra**: a finite rooted tree. A node carries the list of its child hydras; a
**head** is a leaf, `leaf = node []`. The list carrier is incidental — the whole
development is invariant under permuting children (see the module doc). -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra / a single head: a node with no children. -/
def leaf : Hydra := node []

end Hydra

end LeanGallery.Logic.Hydra
