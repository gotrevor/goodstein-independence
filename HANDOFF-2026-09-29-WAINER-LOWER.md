# HANDOFF 2026-09-29 — WAINER-LOWER, laps 1–6

Branch `wainer-lower`, HEAD `7a310a7`.  Working tree clean.
Build command: `lake build GoodsteinWu` (green; `GoodsteinWu` is out of `defaultTargets`
while it carries the frozen sorry).  Pre-commit runs full `lake build` (1548 jobs) — also green.

## Objective

`GoodsteinWu.fastGrowing_provably_total` in `GoodsteinWu/WainerLower.lean` (frozen statement,
the only `sorry` in the library).  Brief: `WAINER-LOWER.md`.  Full route + rationale:
**`PENDING_WORK.md`** — read that first, it is the live plan and is current.

## Done (all sorry-free, all in `GoodsteinWu/`)

| lap | file | content |
| --- | ---- | ------- |
| 1 | `Conservation.lean` | `peano_of_paLX : paLX ⊢ lMap toLX σ → 𝗣𝗔 ⊢ σ`.  The one ingredient of the route that Wu's package lacks.  `#print axioms` = `[propext, Classical.choice, Quot.sound]`. |
| 2 | `InternalFund.lean` | `ifd c n = ⟪kind, value⟫`, arithmetizing `ONote.fundamentalSequence` in every IΣ₁ model; `ifdNext`/`ifdTable`/`ifd` all `𝚺₁`-defined; `ifd_ocOadd`. |
| 3 | `FundBridge.lean` | `ifd_modelCode`: agreement with mathlib on standard codes (validates the transcription). |
| 4 | `InternalFund.lean` | `icmp_ifdVal_lt`: `ifdVal c n ≺ c` — the internal descent.  Plus `ifd_kind_ne_zero`. |
| 5 | `InternalFund.lean` | `isNF_ifdVal`, with the "leading exponent never increases" strengthening the induction needs.  **`InternalFund` owes nothing further.** |
| 6 | `FastGrowingGraph.lean` | `fgGraph c n y` = the Σ₁ graph of `f_c(n) = y`, with `fgGraphDef : 𝚺₁.Semisentence 3`; witnesses are HFS *sets*, so `fgWit_union` merges them. |

## Remaining (steps 4–6 of `PENDING_WORK.md`)

4. **Progressiveness** — next lap.  `GoodsteinWu/Progressive.lean`:
   `𝗣𝗔 ⊢ Prog(≺, ψ)` for `ψ(c) := isNF c → ∀n ∃y fgGraph c n y`.  Zero and limit cases are
   one step each (lap 4 + `fgWit_union`); the successor case is one `𝚺₁`-induction on `j ≤ n`.
   The exact induction statement is written out in `PENDING_WORK.md` — follow it.
5. **Apply `gentzen_upper_bound`** at `φ := lMap toLX (emb ψ)`, `a := o + 1`; add
   `arithmetic_nonote_prec` for `o ≺ o+1`; come back to `𝗣𝗔` by lap 1's `peano_of_paLX`.
6. **Read off**: only *soundness* at ℕ is needed (`ℕ ⊧ fgGraph (code o) n y → y = fastGrowing o n`,
   well-founded induction on `o`); the other direction of the frozen `↔` is free.

## Notes for the next lap

* `ψ` is X-free throughout (an arithmetic formula pushed through `lMap toLX`), so Wu's
  `SubstX.substX` is never needed — `gentzen_upper_bound` already takes an arbitrary
  `φ : Semiformula LX ℕ 1`.  This is a deliberate simplification of the brief's sketch.
* `ψ` must carry the `isNF c →` guard: `y ≺ x` (Wu's `precDef`) already entails `isNF x`, so a
  non-normal `x` has nothing below it and `Prog` has to prove `ψ x` outright.
* Idiom reminders: `open scoped FFL.FirstOrder.Bounding` and open
  `FFL.FirstOrder.Bounding.HierarchySymbol` or the `𝚺₁-Function₂ … via …` notation will not
  parse.  The DSL has no `-`; use `!subDef`.  A `{n : ℕ} →`-style recursion on `Semiterm` fails
  termination — bind `{n}` before the colon.
* Never edit `OrdinalAnalysis`, never `lake update`, never push.
