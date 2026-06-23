# HANDOFF (thin pointer)

> **Branch** `plan` · HEAD `c1619f1` · build **green** (`lake build GoodsteinPA`, **1271 jobs**) ·
> headline `GoodsteinPA.peano_not_proves_goodstein` = honest `sorry` (anti-fraud intact).

**Read these, in order:**
- **`STATUS.md`** — the living overview: where it stands, axiom ledger, Outstanding.
- **`HANDOFF-2026-06-23-lap22.md`** — newest per-lap baton (**D' DISCHARGED**; Thm 5.6 clean modulo F-φ).
- **`PENDING_WORK.md`** — open-items / attack-path scratchpad.
- **`DIRECTION.md`** + **`EXPEDITION-PLAN.md`** — frozen charter + the math.

**One-line state:** the entire Buchholz §5 girder is `Thm56.peano_not_proves_TI` (`𝗣𝗔 ⊬ TI_≺(X)`),
now **`#print axioms = [propext, choice, Quot.sound, rePred_ltPull_natCode]`** — `sorryAx` GONE
(**D' closed** lap 22: the embedded ordinal `< ε₀` is machine-checked, `src/GoodsteinPA/EmbeddingBound.lean`).
**Two walls remain: F-φ** (`rePred_ltPull_natCode`, on Aristotle `aris_onotecmp`) and **E** (Goodstein→TI
descent in PA, the deep crux, needs `papers/`). Headline reduced to E via `peano_not_proves_goodstein_of_descent`.
