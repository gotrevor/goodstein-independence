# HANDOFF — 2026-09-28 — v4.34 port DONE (build + AxiomCheck green)

**Branch** `v4.34` · **HEAD** `dd46a3f` · tree clean · stop sentinel written (`box done --green`).

## State

* `lake build` → `Build completed successfully (1548 jobs)`.
* `lake env lean scripts/AxiomCheck.lean` → silent, exit 0.  Every pinned statement and every
  expected axiom list is byte-identical to the v4.31 tree.
* No `axiom` added; repo is `sorry`-free (no `declaration uses 'sorry'` in the build).
* `PORT-V434-GREEN.md` holds the green evidence; the 24-entry churn playbook (symptom → fix →
  site) is at the end of `PORT-V434.md`.

## What needed real proof work (not renames)

1. **PA⁻ `addEqOfLt` became bounded** (`∃ z <⁺ y, x + z = y`), so the body is a conjunction.
   `budgetedEmbedsV3_addEqOfLt` in `GoodsteinPA/Zef2TC/Axm.lean` grew an `andI` node over two
   `trueRel` leaves (guard `b-a < b+1`, equation `a + (b-a) = b`) and the ordinal tower moved up
   one rung — root is now `ONote.ofNat 6`.
2. **`natCode` was rebuilt on `Nat.Subtype.ofNat`** (`GoodsteinPA/ToMathlib/Ordinal/Epsilon0.lean`).
   mathlib marked `Nat.Subtype.denumerable` `@[no_expose]`, so under the module system there is no
   longer any way to relate `Denumerable.ofNat ↥s` to the increasing enumeration of `s`; the old
   `enc_strictMono` proof was therefore unrepairable.  `natCode` is now `Equiv.ofBijective` over
   `codeEnum = Nat.Subtype.ofNat (range encode)` (hence `noncomputable`, as is `enc`), and
   `enc_strictMono` follows from `codeEnum_strictMono`.  `rePred_ltPull_natCode` is unaffected.
3. `sigma1_all_inv` (`GoodsteinPA/ReadoffValueGate.lean`) had to absorb `Hierarchy`'s new
   `bounded`/`ℬ.Closure` constructor and invert `R ∈ ℬ[<, ℒₒᵣ]` to `R = op(<)`.

## Anti-corruption shim

`GoodsteinPA/ToFoundation/Compat.lean` now also carries: the `∀⁰/∃⁰/∀⁰*/∃⁰*` quantifier notations,
`Arithmetic.Hierarchy` + `DeltaZero` + the `Hierarchy` lemma re-exports, the `𝚺₁`/`Γ-[n]` hierarchy
symbols, and `Derivation2`.  On the next bump, edit that file first.

## Traps to remember

* `lake env lean <file>` sees every olean; `lake build` restricts to declared imports.  A file can
  pass the first and fail the second.  Trust `lake build`.
* Lean 4.34 `rw` checks type-correctness at `implicit` transparency: write `show ℕ+ from ⟨n, h⟩`
  (and `show NONote from ⟨x, h⟩`), never a bare anonymous constructor there.
* The kernel refuses `Nat.pow` at a >32-bit exponent; keep towers like `2 ^ 2 ^ 2 ^ 16` behind an
  opaque local.

## Next

Nothing in this run.  The port is the whole objective and it is met; the math frontier is unchanged
(see `PENDING_WORK.md` / the pre-port handoffs for the Kreisel phase-2 gate and the REBUILD-Z
threads).
