# Bridge to KT. Wu's `OrdinalAnalysis` (prep for a treadmill)

Source-only survey, 2026-09-27.  No builds run.  OURS = this repo at `kreisel` `7fbd34f`.
WU = `MaxWellApexLab/OrdinalAnalysis` at `origin/main` `87baec7` (fetched 2026-09-27).

## Summary

1. Both repos sit on mathlib's `ONote`/`NONote` and on Foundation; the ε₀ *order* is literally the same (mathlib `<` on `NONote`), only the ℕ-codings differ.
2. WU proves `|PA| = ε₀` in the Π¹₁ sense: `PA[X] ⊢ TI(≺, φ, ā)` for every notation `a`, and `PA[X] ⊬ TI(≺)` with `X` a free predicate.
3. OURS proves Goodstein / Hydra / Paris-Harrington independence by the **Wainer growth route**; no TI(ε₀) statement is used, assumed, or proved in the build (the TI lower bound lives only in `wip/Thm56.lean`, with a `sorry`).
4. So there is no hypothesis on either side for the other to discharge, and Wu's Π¹₁ lower bound **cannot** yield an arithmetical (Π⁰₂) independence like Goodstein on its own.
5. Recommended first target: pin that Wu's coded ordering has order type **exactly ε₀** (cheap, uses our `range_NONote_repr`); headline follow-ons are Wainer's classification (both halves) and `PA + TI(ε₀) ⊢ Goodstein`.

## The two notations side by side

| | OURS | WU |
|---|---|---|
| Notation type | mathlib `ONote` / `NONote` (all headlines quantify `o : ONote, o.NF`) | mathlib `NONote` (`epsilon0Order : CodedOrder NONote`, `Gentzen/CodedOrder.lean:238`) |
| Order | mathlib `<` | mathlib `<`, tied to the internal comparator by `NotationBridge.lt_iff_icmp_modelCode_eq_zero` (`Gentzen/NotationBridge.lean:121`) |
| ℕ-coding (build) | `ONote.encodeONote`: `0 ↦ 0`, `oadd e n a ↦ Nat.pair (enc e) (Nat.pair (n-1) (enc a)) + 1` (`ToMathlib/Ordinal/Epsilon0.lean:158`); also `natCode : ℕ ≃ NONote := (Denumerable.eqv NONote).symm` (`:199`), a non-structural bijection | `NotationBridge.code`: `0 ↦ 0`, `oadd e n r ↦ Nat.pair (Nat.pair (code e) n) (code r) + 1` (`Gentzen/NotationBridge.lean:20`); `nonoteCode` (`:128`) |
| Internal (in-model) coding | build: none for ONote.  `wip/InternalONote.lean:31` has `ocOadd ec n rc := ⟪⟪ec, n⟫, rc⟫ + 1` with `icmp`/`isNFb` course-of-values tables | `Gentzen/InternalONote.lean:20` has the **same** `ocOadd := ⟪⟪ec, n⟫, rc⟫ + 1`, same names (`icmp` `:278`, `isNFb` `:536`, `isNF` `:539`, plus `iadd` `:808`).  Shared lineage with our wip file (inferred from identical names/layout, ~85%) |
| Arithmetized order | build: only `rePred_ltPull_natCode : REPred …` (`ToMathlib/ONote/Computability.lean:489`), an r.e. predicate on `natCode`, no Foundation formula | `precDef : 𝚺₁.Semisentence 2 := “x y. isNF x ∧ isNF y ∧ icmp x y = 0”` (`Gentzen/CodedNotation.lean:21`), lifted to `precCode : Semiformula LX ℕ 2` (`:52`).  ℕ-reading `PrecStandard.precN` (`PrecStandard.lean:32`), `precN_code_iff` (`:43`), range exactly `{n ∣ isNF n}` (`CodeSurj.lean:70,123`) |
| Language | pure `ℒₒᵣ` | `LX = ℒₒᵣ + one unary predicate X` (`Gentzen/Setup.lean:66`); `paLX = EQ LX ∪ PA⁻ ∪ InductionScheme LX univ` (`:91`) |
| TI | Kreisel only: `TI r φ : Sentence ℒₒᵣ := “(∀x, (∀y, r y x → φ y) → φ x) → ∀x, φ x”` (`Kreisel/Statement.lean:102`), `φ` arithmetic | `Prog` / `TI` / `TIupto` over `X` (`Setup.lean:122,126,134`); substituted form `tiUptoAt prec φ a` (`Jump.lean:54`), `closedTI φ a := (tiUptoAt precCode φ a).univCl` (`Order.lean:101`) |
| Abstract interface | none | `structure CodedOrder O` (`CodedOrder.lean:155`): `X`-free closed `prec`, `code : O → ℕ`, `precN`, and two bridges (`eval_precAt_numeral`, `precN_code_iff`).  Lower-bound pipeline is generic over it |

## Headline inventories

**OURS** (all `sorry`-free in the build per `scripts/AxiomCheck.lean`):
- `GoodsteinPA.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence` (`Statement.lean:56`), via `wainer_bound_of_pa_proves_goodstein` (`:42`) and Cichon/Caicedo.  `goodstein_independent` (`:72`).
- `Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing (φ) (hφ : Hierarchy 𝚺 1 φ) (h : 𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ)) : ∃ o : ONote, o.NF ∧ ∃ M, ∀ m ≥ M, ∃ N ≤ fastGrowing o m, ℕ ⊧/![N, m] φ` (`WainerGeneral.lean:236`).  This is the **upper half** of Wainer's classification; the lower half (each `f_o` provably total) is absent.
- `Hydra.pa_not_proves_hydra` (`HydraEscape.lean:186`), `PH.pa_not_proves_ph` (`PH/Main.lean:29`): same Wainer route.
- `consistency_PA : 𝗣𝗔 ⊬ ⊥` (`Result/ConsistencyPA.lean:81`), via `Z∞` cut elimination.
- Kreisel: `kreiselLT_iff_lt` (`Kreisel/Statement.lean:261`), `pa_not_proves_TI_kreisel : 𝗣𝗔 ⊬ ↑(TI kreiselLT good)` (`:270`), `pa_proves_TI_lt` (`:281`), `kreiselLT_delta1` (`:295`), `pa_proves_TI_iff_consistent` (`:304`).
- ε₀-completeness: `exists_NF_repr_eq` (`ToMathlib/Ordinal/Epsilon0.lean:34`), `range_NONote_repr : Set.range NONote.repr = Set.Iio ε₀` (`:92`).
- **What the independence proof needs:** no TI input at all.  `PA ⊬ TI(ε₀)` appears only as `wip/Thm56.lean:113` `peano_not_proves_TI`, outside the build, carrying a disclosed `sorry` (`embed_TI_bounded`, `:95`); `peano_not_proves_goodstein_of_descent` (`:139`) takes the unproved `DescentE` (`:133`) as a hypothesis.  Superseded by the Wainer route.

**WU:**
- `gentzen_upper_bound (φ : Semiformula LX ℕ 1) (a : ONote) (ha : a.NF) : paLX ⊢ closedTI φ (notationTerm ⟨a, ha⟩)` (`Gentzen/UpperBound.lean:113`).
- `gentzen_lower_bound : paLX ⊬ (TI precCode).univCl` (`Gentzen/LowerBound.lean:88`).
- `gentzen_theorem` = the conjunction (`Gentzen/GentzenTheorem.lean:32`).  **Formally, "|PA| = ε₀" means exactly this pair**: TI along `≺` for every `LX`-formula below every standard notation is `paLX`-provable, and TI along all of `≺` for the free `X` is not.  That `≺` has order type ε₀ is carried by `precN_code_iff` plus mathlib's `NONote`, not by a stated `Ordinal.type … = ε₀` theorem (none found).
- `paLX_consistent : paLX ⊬ ⊥` (`Gentzen/Consistency.lean:54`); `epsilon1_theorem` (`Gentzen/Epsilon1Theorem.lean:69`); ACA, `Γ₀`, ramified results beyond scope here.
- Plumbing we would reuse: `paLX_of_peano : 𝗣𝗔 ⊢ σ → paLX ⊢ lMap toLX σ` (`CodedNotation.lean:147`); `models_of_paLX_proof` (`Idiom.lean:71`); `SubstX.lean` (substitute a formula for `X`).
- Wu's README already surveys the FFL `goodstein-independence` repo (our upstream): cites `consistency_PA`, `Zinfty/Cut.lean:49`, and our `wip/Thm56.lean` as the only prior lower bound.  No Lean import either way.  Neither repo proves an `ONote ≃o Iio ε₀` beyond mathlib's `repr` embedding except OURS (`range_NONote_repr`).

## Compatibility

| | OURS | WU |
|---|---|---|
| `lean-toolchain` | `v4.31.0` | `v4.33.0` |
| mathlib | `fabf563` (`v4.31.0`) | `db584cd` (`v4.33.0`) |
| Foundation | `b47cf44` (2026-07-18) | `8c6a5c0` (2026-08-30), `rev = "master"` in lakefile |
| Module system | yes (`module`, `public import`, `@[expose] public section`) | **no** (plain `import`; `grep ^module` finds nothing) |

- Neither can `require` the other today: different toolchains and mathlib.
- Direction is forced even after alignment: a `module` file cannot import a non-module (our `PORT-EPSILON0.md` hit exactly this with LeanGallery on 4.31), while a legacy file *can* import modules (Wu already imports module Foundation).  So the bridge file must be **legacy**, importing Wu and ours.
- No declaration clashes found: Wu's 43 `_root_.LO.FirstOrder.Arithmetic.*Def` names do not meet our 6; Wu's ONote extensions live under `OrdinalAnalysis.NONote`.  (Our `wip/InternalONote.lean` *would* clash, but it is not built.)
- Plan: a **third repo** (legacy, v4.33.0) that `require`s Wu upstream at `87baec7` and our fork at a SHA **after** bumping ours to v4.33.0 + Foundation `8c6a5c0` (a port like `PORT-EPSILON0.md`, est. 3-8 laps).  Target 1 below needs only pure-mathlib facts from us, so it can start in a Wu fork with no port at all.

## Bridge candidates, ranked

1. **Order-type pin for Wu's ε₀ ordering** (value: medium, faithfulness anchor for `gentzen_theorem`; feasibility: high, **1-3 laps**).  From `CodeSurj.isNF_iff_exists_nonote`, `precN_code_iff`, mathlib `NONote.repr` strict monotonicity, and our `range_NONote_repr`.  **Recommended first target:**
   ```lean
   -- the ℕ-reading of Wu's `≺`, on its field, is a well-order of type exactly ε₀
   theorem precN_type_eq_epsilon0 :
       Ordinal.type (α := {n : ℕ // InternalONote.isNF (V := ℕ) n})
         (fun m n => PrecStandard.precN m.1 n.1) = Ordinal.epsilon 0
   -- corollary shape: |PA| = ε₀ with "ε₀" an Ordinal, not a reading
   theorem pa_ordinal_eq_epsilon0 :
       Ordinal.type (…as above…) = Ordinal.epsilon 0 ∧ gentzen_theorem_statement
   ```
   Route: `nonoteCode` is an order iso `NONote ≃o {n // isNF n}`, `NONote.repr` is an order iso onto `Iio ε₀`, `type (Iio ε₀) = ε₀`.  Home: Wu fork `Bridge/` (legacy), with `range_NONote_repr` either re-proved (~100 lines, mathlib only) or imported after the port.
2. **Kreisel in Wu's frame** (value: medium, fits this branch; feasibility: high, **3-6 laps** after co-location).  `kreiselOrder : CodedOrder ℕ` (`prec := lMap toLX kreiselLT`, `code := id`, `precN_code_iff := kreiselLT_iff_lt`) and `paLX ⊬ (TI kreiselOrder.prec).univCl`, by substituting `good` for `X` (`SubstX`) and pulling back to `𝗣𝗔` against `pa_not_proves_TI_kreisel`.  Contrast with `pa_proves_TI_lt` lifted: two `CodedOrder`s of the same ℕ-order type ω with opposite provability, showing the four `CodedOrder` fields do not fix proof-theoretic strength.  Needs a conservation lemma `paLX ⊢ lMap σ → 𝗣𝗔 ⊢ σ` (semantic: expand a PA model with `X := ∅`); not found in Wu.
3. **`PA + TI(≺, arithmetic) ⊢ Goodstein`** (value: medium-high, the true side of "Goodstein sits exactly at ε₀"; feasibility: medium, **10-20 laps**).  Our `Internal.lean` already has `igoodstein` with `igoodstein_nat` (`:961`); needs an internal base-`b` to CNF map onto Wu's `ocOadd` codes (our `wip/InternalONote.lean` `iC`/`ievalNat` is a start, same coding) and the descent `o_{k+1} ≺ o_k`.
4. **Wainer classification, both halves** (value: high; feasibility: low-medium, **20-40 laps**).  Lower half: `∀ o, o.NF → ∃ φ : Semisentence ℒₒᵣ 2, Hierarchy 𝚺 1 φ ∧ (∀ n m : ℕ, ℕ ⊧/![m, n] φ ↔ m = fastGrowing o n) ∧ 𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ)`, from `gentzen_upper_bound` at `φ := lMap "fastGrowing β is total"` plus conservation.  Cost is arithmetizing mathlib's `fundamentalSequence` and `fastGrowing` on Wu's codes inside IΣ₁.  Pairs with our `pa_provable_pi2_eventually_witnessed_below_fastGrowing` for the full theorem.
5. **Derive Goodstein unprovability from Wu** (value: would be high; feasibility: **not as a bridge**).  See risk 1.  Would need Gentzen's consistency proof formalized *inside* PA, or our unfinished `DescentE`.

## Open risks

1. **Π¹₁ vs Π⁰₂ (biggest).**  Wu's lower bound is about `PA[X]` with a free predicate.  Adding a true arithmetic sentence to PA leaves the Π¹₁ ordinal at ε₀, so no argument from `gentzen_lower_bound` alone can show `𝗣𝗔 ⊬ goodsteinSentence`.  The prompt's "Wu's `PA ⊬ TI(ε₀)` discharges what ours uses" has nothing to discharge: ours uses no TI.
2. **Toolchain gap** v4.31 to v4.33 plus 6 weeks of Foundation; ours must move (module-to-legacy import is refused), and Wu tracks Foundation `master`, so pin its SHA.
3. **Three ℕ-codings of ONote** (our `encodeONote`, our `natCode`, Wu's `code`).  Any PA-internal statement should use Wu's coding throughout; a translation to ours is a ℕ-level primrec lemma only.
4. Wu's repo is moving (last commit 2026-09-24); re-fetch and re-read `CodedOrder.lean` before a lap.
5. Target 1 is small enough that Wu might add it themselves; worth a check (and possibly a friendly note) before grinding.
