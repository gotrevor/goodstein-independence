# PORT-V434: goodstein-independence v4.31.0 → v4.34.0

Treadmill brief, branch `v4.34` (local-only: **never push**).  The mechanical part is done by
`lean-bump` (uncommitted in the tree, keep it): `lean-toolchain` = v4.34.0, `lake-manifest.json`
adopted from the `~/.lake-base/4.34.0` store (Foundation `bde9bc28` = FFL master 2026-09-27, mathlib
`5ed29652` = v4.34.0), docbuild + CI satellites re-pinned.  `.lake/packages` is pre-built; there is no
network, so **never** run `lake update` or `lake exe cache get`, and never edit the manifest or lakefile.

## Objective

`lake build` green (whole repo) **and** `lake env lean scripts/AxiomCheck.lean` silent, with every
headline's statement and axiom pin unchanged.  Then commit, log, and **only then** create
`PORT-V434-GREEN.md` holding the last lines of the green `lake build` and of the AxiomCheck run
(the host's stop condition is that file existing; creating it early is a false claim), commit it,
`box done`.

## Where the breakage is

First build: ~83 top-level errors, mostly **Foundation churn between `b47cf44` (our old pin) and
`bde9bc28`**: modules moved/renamed (e.g. `Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1`,
`Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Functions` no longer exist) and presumably
declaration renames behind them, plus mathlib v4.31 → v4.34 and Lean core drift.

Find a moved module or renamed lemma in the new sources under `.lake/packages/Foundation/` (grep the
declaration name you need); mathlib likewise under `.lake/packages/mathlib/`.  Fix imports first, then
build again: the first wave hides the rest.  Work bottom-up through the import graph.

## Rules

- **Frozen:** the statements of every declaration pinned in `scripts/AxiomCheck.lean`, and the pins'
  expected axiom lists.  Fix proofs, imports and helper lemmas; never weaken a headline.
- Prefer a local `Compat.lean` shim (alias / small lemma) over rewriting many call sites when a
  Foundation or mathlib name simply moved.  Never add an `axiom`.
- `native_decide`, deprecation warnings and `set_option maxHeartbeats` bumps are fine.
- Commit green checkpoints as you go (the pre-commit hook builds; a red tree cannot commit, which
  is expected until the build is green).

## Log (required: the migration playbook is built from it)

For every distinct kind of breakage, one line: **symptom → fix → example site**.  E.g.
`bad import Foundation.X.Y → moved to Foundation.X.Z → GoodsteinPA/ToFoundation/FvSubst.lean`.
Group identical renames; name the old and new identifiers exactly.

### Churn patterns

Each line: **symptom → fix → example site**.

#### Foundation (`b47cf44` → `bde9bc28`)

1. `unknown namespace LO` / every `LO.*` name unknown → Foundation's root namespace was renamed
   `LO` → `FFL`; mechanical `LO.` → `FFL.` and `open LO` → `open FFL` across 55 files →
   `GoodsteinPA/ToFoundation/Compat.lean:31`.
2. `Structure` / `Struc` unknown (`invalid binder annotation`, `Tarski.Structure ... is stuck`) →
   the semantics class moved into the `Tarski` namespace: `FFL.FirstOrder.Structure` →
   `FFL.FirstOrder.Tarski.Structure`; likewise `Structure.add_eq_of_lang`,
   `Structure.mul_eq_of_lang`, `Structure.numeral_eq_numeral` →
   `Tarski.Structure.*` → `GoodsteinPA/ToFoundation/Compat.lean`, `GoodsteinPA/ReadoffValueGate.lean:131`.
3. `expected token` at `∀⁰ `/`∃⁰ `/`∀⁰* ` → the first-order quantifier notations are now
   `∀¹ `/`∃¹ `/`∀¹* ` (the superscript numbers the *order*).  685 sites: shimmed, not rewritten —
   `prefix:64 "∀⁰ " => FFL.FirstOrder.UnivQuantifier.all` etc. in `Compat.lean`.
4. `Arithmetic.Hierarchy` unknown → the arithmetical hierarchy was generalised to
   `FFL.FirstOrder.Bounding.Hierarchy ℬ Γ s φ` over a bounding-relation set `ℬ`; the arithmetical
   case is `ℬ[<, L]`.  Shimmed as `abbrev Arithmetic.Hierarchy` + `export` of the lemmas we use
   (`rew exs and_iff or_iff imp_iff sigma_of_sigma_ex`), plus `abbrev DeltaZero` → `Compat.lean`.
   Note `Hierarchy.rew`'s derivation argument is anonymous, so `h.rew _` must become
   `Arithmetic.Hierarchy.rew _ h` → `GoodsteinPA/ReadoffValueGate.lean:432`.
5. `Hierarchy` gained a `bounded` (`ℬ.Closure`) constructor and `ball`/`bexs` now carry
   `R ∈ ℬ` → case-analysis proofs need the extra case and `R = op(<)` inversion →
   `GoodsteinPA/ReadoffValueGate.lean:376` (`sigma1_all_inv`).
6. `𝚺₁`, `Γ-[n]` unknown (`expected token`) → renamed to `𝚺ᴬ₁`, `Γᴬ-[n]` and made `scoped`;
   old spellings restored as global notations in `Compat.lean`.
7. `Γ-Function₃ f via φ` unknown → those notations are `scoped` in `FFL.FirstOrder.Bounding`;
   add `open scoped FFL.FirstOrder.Bounding` → `GoodsteinPA/ToFoundation/FvSubst.lean:21`,
   `GoodsteinPA/Internal.lean`.
8. `FFL.FirstOrder.Arithmetic.HierarchySymbol` unknown → `FFL.FirstOrder.Bounding.HierarchySymbol`
   (and `HierarchySymbol.Semiformula.ball` now takes `hR : R ∈ ℬ`; the arithmetical wrapper is
   `Semiformula.arithmetic_ball` / `val_arithmetic_ball`) → `GoodsteinPA/Kreisel/Statement.lean`.
9. `InductionOnHierarchy.least_number` → `InductionOnBroadHierarchy.least_number`;
   `Definable.ball_le` → `Definable.arithmetic_ball_le` → `GoodsteinPA/Internal.lean:246,473`.
10. `ProvablyProperOn.ofProperOn` → `Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn`
    → `GoodsteinPA/Kreisel/Statement.lean:298`.
11. `Theory.consistent` is now a `𝚷₁.Sentence`; `↑T.consistent` no longer elaborates in an
    implication — use `T.consistent.val` → `GoodsteinPA/Kreisel/Statement.lean:274`.
12. `DeMorgan.neg` → `TildeInvolutive.tilde_involutive` → `GoodsteinPA/Zinfty/Cut.lean:620`.
13. `Derivation2` → `LK2.Derivation` (notation `T ⟹₂ Γ`, scoped); old name restored as an
    `abbrev` in `Compat.lean` → `GoodsteinPA/Zef2TC/Embedding.lean:53`.
14. moved modules: `Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Functions` →
    `Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions`
    (`GoodsteinPA/ToFoundation/FvSubst.lean:16`); `Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1`
    → `Foundation.FirstOrder.Incompleteness.Definability` (`GoodsteinPA/Kreisel/Statement.lean:3`).
15. **content change, not a rename:** PA⁻'s `addEqOfLt` is now
    `∀ x y, x < y → ∃ z <⁺ y, x + z = y` (bounded), so its body is a *conjunction*
    `z < y+1 ⋏ x + z = y`.  The `Zef2TC` derivation for it grew an `andI` node over two
    `trueRel` leaves and the ordinal tower moved up one rung (`ofNat 6` at the root) →
    `GoodsteinPA/Zef2TC/Axm.lean:budgetedEmbedsV3_addEqOfLt`.

#### mathlib v4.31 → v4.34 / Lean core

16. `IsWellFounded α r` deprecated → the class is now `WellFounded r` itself (`attribute [class]`),
    `IsWellFounded.rank`/`rank_lt_of_rel`/`induction` → `WellFounded.*`, and
    `WellFoundedLT α` is `@WellFounded α (·<·)`, so `⟨wf⟩` anonymous constructors must drop the
    brackets → `GoodsteinPA/ToMathlib/Ordinal/WellFoundedRank.lean`,
    `GoodsteinPA/ToMathlib/Hardy/Comparison.lean:16`, `GoodsteinPA/ToMathlib/Ordinal/Epsilon0.lean:110`.
17. **`rw` now checks the target is type-correct at `implicit` transparency.**  A bare anonymous
    constructor in a position of a `def`-wrapped subtype (`ℕ+ = PNat`, `NONote`) elaborates to a
    `Subtype.mk` at the *unfolded* type and fails that check ("not type-correct under the
    `implicit` transparency level"), so `rw`/`simp` stop matching.  Fix: `show ℕ+ from ⟨n, h⟩`
    (resp. `show NONote from ⟨x, h⟩`).  `attribute [reducible] PNat` is refused (not declared
    locally) → `GoodsteinPA/ToMathlib/Goodstein/Domination/Growth.lean`, `.../LowerBound.lean`,
    `.../Ordinal/Epsilon0.lean:125`, `.../ONote/Computability.lean:322`.
    Same root cause when a `simp` lemma keyed on `ℕ+` will not fire: instantiate it by hand
    (`have h_NF := NF_oadd_iff (n := show ℕ+ from ⟨…⟩)`) → `.../ONote/Computability.lean:331`.
18. **the kernel refuses `Nat.pow` with a >32-bit exponent.**  Typechecking a proof mentioning
    `2 ^ (2 ^ 2 ^ 16)` now fails; keep the tower behind an opaque local
    (`obtain ⟨k, hk⟩ : ∃ k, k = 2 ^ (2 ^ 16) := ⟨_, rfl⟩`) →
    `GoodsteinPA/ToMathlib/Goodstein/Domination/BaseCases.lean:594,603`.
19. `Nat.Subtype.denumerable` is `@[no_expose]`, so in module mode `Denumerable.ofEquiv_ofNat`
    can no longer relate `Denumerable.ofNat ↥s` to the *increasing* enumeration
    `Nat.Subtype.ofNat s` — the bridge is unprovable downstream.  Fix: build the coding equiv
    from `Nat.Subtype.ofNat` directly (`codeEnum`, `natCode := Equiv.ofBijective …`, now
    `noncomputable`), which makes the monotonicity read-off `rfl`-close →
    `GoodsteinPA/ToMathlib/Ordinal/Epsilon0.lean:199`, `.../ONote/Computability.lean:enc_strictMono`.
20. `simp` no longer unfolds `n ∈ Nat.rfind p` → use `Nat.mem_rfind` explicitly →
    `GoodsteinPA/ToMathlib/ONote/Computability.lean:rfind_nthNF`.
21. `ORingStructure.zero_eq_zero` gone as a `Semiterm`-level simp lemma; the `0`-operator read-off
    is `rfl` → `GoodsteinPA/Encoding.lean:goodsteinSentence_faithful`.
22. `PNat.add_coe`-style goals: state the arithmetic at `ℕ` (`((x + y : ℕ+) : ℕ) = …`) rather than
    at `ℕ+` so `omega` sees it → `GoodsteinPA/OperatorZeh/Examples.lean:51`.
23. **build-gate note:** `lake env lean <file>` sees *all* oleans, `lake build` restricts to the
    module's declared imports; a file can pass the former and fail the latter (e.g.
    `Structure.numeral_eq_numeral` in `Encoding.lean`).  Trust `lake build`.
24. Deprecations that are warnings only (left alone): `Ordinal.opow_succ` → `opow_add_one`,
    `dif_pos/dif_neg/if_neg` → `dite_eq_*`/`ite_eq_*`, `haveI` → `have` style linter.

## Phase 2: PAComparator (added 2026-09-28)

`lake build` (default target) was green, but `lean-bump --finish` also builds the `PAComparator`
lib, which is still on the old Foundation spellings (`LO.` → `FFL.` is already applied, uncommitted).
Its `*/Challenge.lean` files are the comparator's **trusted statements**: they must stay
self-contained (no import of `GoodsteinPA/ToFoundation/Compat.lean` or any shim) and must state
exactly the same propositions as before, rewritten in current Foundation syntax (`∀¹`/`∃¹`,
`Bounding.Hierarchy ℬ[<, L]`, `𝚺ᴬ₁`, `open scoped FFL.FirstOrder.Bounding`, ...; see the churn
patterns above).  `Support/` files may be fixed freely.

Objective: `lake build PAComparator` and `lake build` both green, AxiomCheck silent.  Log any new
pattern above, commit, then create `PORT-V434-COMPARATOR.md` (tails of both builds) and `box done`.

### Phase-2 churn patterns (PAComparator)

25. `expected token` at `∀⁰ `/`∃⁰ ` and `Unknown identifier Arithmetic.Hierarchy` inside a
    **Challenge** file → the Challenge files must stay shim-free, so they are written in upstream's
    own spelling: `∀¹ `/`∃¹ ` and `Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ` →
    `PAComparator/{PH,Hydra,Wainer}/Challenge.lean`.
26. Consequence of 25: the **development's** headline statements must then use the same upstream
    spelling, or the comparator statement-identity check sees `Arithmetic.Hierarchy` (the `Compat`
    abbrev) on one side and `Bounding.Hierarchy ℬ[<, ℒₒᵣ]` on the other.  `Arithmetic.Hierarchy 𝚺 1 φ`
    → `Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ` in the four pinned hypotheses →
    `GoodsteinPA/PH/Main.lean:30,37`, `GoodsteinPA/HydraEscape.lean:187`,
    `GoodsteinPA/WainerGeneral.lean:237`.  (Same term; `Compat`'s own rule is that *statements* hang
    off upstream directly.)
27. `unknown namespace FFL.FirstOrder.Arithmetic.HierarchySymbol` → `FFL.FirstOrder.Bounding.HierarchySymbol`;
    and `𝚺₁.Semisentence` → `𝚺ᴬ₁.Semisentence` with `open scoped FFL.FirstOrder.Arithmetic
    FFL.FirstOrder.Bounding` (both notation families are now `scoped`) →
    `PAComparator/Goodstein/Support/Internal*.lean`, `PAComparator/Goodstein/Challenge.lean:88`.
28. **pre-existing drift, not toolchain churn:** the development had moved `base`/`bump`/`goodsteinSeq`
    into `namespace Goodstein` (and `goodsteinSentence : ArithmeticSentence`) without updating the
    comparator copy, which still said `namespace GoodsteinPA` / `Sentence ℒₒᵣ`.  Caught by the
    statement-identity harness below → `PAComparator/Goodstein/Support/Defs.lean:17`,
    `PAComparator/Goodstein/Challenge.lean`.

### Statement-identity harness (how 26/28 were caught)

`scratchpad/cmp/{chal,dev}.lean` `#check @<pinned name>` under `pp.explicit`/`pp.notation false`/
`pp.fullNames`, once with the four `PAComparator/*/Challenge.lean` imported and once with the
development's modules; `diff` must be empty.  All 7 comparator-pinned statements are now
expression-identical.  `scratchpad/cmp/defs-{chal,dev}.lean` does the same with `#print` on the
definitions the Goodstein statements reach.
29. **`_proof_N` dedup, the comparator-only trap:** the development had consolidated
    `InternalPow → InternalLog → InternalBump → InternalGoodstein` into a single
    `GoodsteinPA/Internal.lean`, so its `.mkSigma` / `PR.Blueprint` auxiliary proofs dedup *inside
    that one module* (`ibumpTableDef` now reuses `ipowDef._proof_1`, etc.), while the comparator
    support still mirrored the old four-file split and therefore produced its own
    `ibumpTableDef._proof_1`.  Same terms, different `ConstantInfo` names → comparator
    statement-identity would fail.  Fix: one `PAComparator/Goodstein/Support/Internal.lean`, in
    `module` mode (the module system also changes the numbering *within* a declaration), with the
    defs in the development's order (`pow.blueprint, ipowDef, ilogDef, bumpNextDef,
    bumpTable.blueprint, ibumpTableDef, ibumpDef, goodstein.blueprint, igoodsteinDef`).  The
    development's model-side `…construction`s and `𝚺₁-Function` instances need not be reproduced —
    they own no auxiliary proof these defs dedup onto.  Verified by `scratchpad/cmp/defs-*.lean`.
