# E-ARCHITECTURE REVIEW — possible wrong turn at lap 27 (Rathjen §3 is primrec-only)

> **External review, 2026-06-23, Claude Opus 4.8 (fresh session), after reading
> `papers/rathjen-2014-goodsteins-theorem-revisited.pdf` in full (all 17 pp.).**
>
> ⚠️ **VALIDATE, do not trust.** The cited paper facts (§A) are high-confidence. The architecture
> conclusion (§B–C) is *my reconstruction* of this repo's plan from its handoffs + the paper —
> confidence ~75%. **Run the validation checklist (§E) against the actual code before acting.** A
> "How this finding could be wrong" section (§F) is included so you can *refute* it cleanly. Do **not**
> delete the Buchholz §5 / `peano_not_proves_TI` work on the strength of this doc — that result is real,
> correct, and axiom-clean; the question is only whether it is the right *back-end for the Goodstein
> headline*.

## Headline claim
The live E route (lap 27 → present: run Rathjen §3 slow-down on the **X-definable** descent to derive
the **free-predicate** `TI_≺(X)` consumed by `peano_not_proves_TI`) appears **blocked, not merely hard**.
Rathjen's §3 is *intrinsically about primitive-recursive sequences*; it delivers
`Goodstein → primrec-PRWO(ε₀)`, **not** `Goodstein → free-X TI`. The domination obligation Codex and I
both flagged (`∃ l, ∀ n, C(β(n+1)) ≤ F_l n`, i.e. `xDescent_domination`) is **Lemma 3.2 = Grzegorczyk's
theorem, which is true only for primitive-recursive functions and is false for an arbitrary X-definable
descent**. That is not a gap to patch; it is the structural reason Rathjen restricts to primrec sequences.

**The fix is likely Route A — which is Rathjen's actual proof, and which this repo already has scaffolded
(`Reduction.lean` Route-A hook + the *banked* lap-25/26 X-free §3 substrate).**

## §A. What the paper definitively says (high confidence — cited)
1. **All of §3 is primitive-recursive.** Every statement says "primitive recursive":
   - **Lemma 3.2** (p.11): "For every *primitive recursive* function `h` … there is an `n` such that
     `h(x⃗) ≤ f_n(max(2, x⃗))`." This is Grzegorczyk domination. **It is false for non-primrec functions**
     (an oracle/X-definable function can outgrow every fixed `f_l`). This is the exact `hdom`/
     `xDescent_domination` obligation — and it is a *primrec-only* theorem.
   - **Lemma 3.3 (PA)** (p.11–12): builds `g` by diagonalizing the Grzegorczyk hierarchy `f_l`; needs
     `f = f_l` (a fixed level), supplied by Lemma 3.2. So the slow-down is *intrinsically* tied to a
     fixed Grzegorczyk level — you cannot "just pad with the X-definable control function instead."
   - **Cor 3.4 (PA)** (p.12): "From a given **primitive recursive** strictly descending sequence … one
     can construct a slow **primitive recursive** … sequence."
   - **Thm 3.5 (PA)** (p.13), **Lemma 3.6 (PA)** (p.14): all "primitive recursive descending sequence."
2. **Rathjen's back-end is Con(PA) + Gödel II (= Route A).** **Thm 2.8** (p.10): (i) `PRA ⊢ PRWO(ε₀) →
   Con(PA)`; (ii) `PA ⊬ PRWO(ε₀)` *"of course, one invokes Gödel's second incompleteness theorem."*
   **Cor 3.7** (p.14) finishes: *arguing in PA*, assume special-Goodstein-termination `GS`; from
   Lemma 3.6 + Thm 3.5 + Cor 3.4 derive "no infinite primrec descending ε₀-sequence" `= PRWO(ε₀)`; but
   Thm 2.8 says `PA ⊬ PRWO(ε₀)`. Contradiction. **This is exactly the `Reduction.lean` Route-A hook the
   repo set aside.**
3. **The free / "all sequences" version is not PA-formalizable.** Bernays to Goodstein (quoted p.2): `P`
   is `Π¹₁` and "is not a statement that can be formalized in Gentzen's system as it talks about all
   descending sequences." And: *"Gentzen's proof only utilizes primitive recursive sequences of ordinals
   and the equivalent theorem about primitive recursive Goodstein sequences is expressible in the language
   of PA (see Theorem 2.8)."* The general equivalence (Goodstein ⟺ no descending ε₀-seq) is **Thm 2.6,
   over RCA₀** (second-order), *not* over PA.

## §B. The architecture mismatch (my analysis — confidence ~75%)
- **Back-end built:** `peano_not_proves_TI` = `PA(X) ⊬ TI_≺(X)` for the **free predicate** `Xsym`
  (Buchholz §5). Correct + axiom-clean. This is a *free-predicate* statement.
- **Reduction being built (lap 27 →):** §3 slow-down on the **X-definable** descent (`InternalCor34.lean`,
  `hCD`/`nonterminating_of_xDescent`), aiming at `Goodstein → TI_≺(X)`.
- **The break:** §3 only yields `Goodstein → primrec-PRWO(ε₀)`. And
  `free-X TI` is **strictly stronger** than `primrec-PRWO`:
  `PA(X) ⊢ TI_≺(X)` ⟹ (instantiate `X` at any arithmetic `φ`) `PA ⊢ TI_≺(φ)` ⟹ `PA ⊢ primrec-PRWO`.
  Contrapositive: `PA ⊬ primrec-PRWO` ⟹ `PA(X) ⊬ free-X TI`. So your boundedness result is the **weaker**
  unprovability (it is *implied by* Rathjen's Thm 2.8). A reduction landing `primrec-PRWO` therefore does
  **not** discharge the headline against `peano_not_proves_TI`, and the only way to bridge the gap
  (slowing the X-definable descent) needs the primrec-only domination, which fails.
- **This is the same obstruction the repo half-saw at lap 24/27** ("free-X obstruction": X-free PRWO
  can't feed the free-X boundedness theorem). The lap-27 response — "do the reduction on the X-definable
  descent" — moved the obstruction rather than removing it: §3 cannot run on an X-definable descent.

## §C. The proposed fix — Route A (= Rathjen's actual proof), which you are *close* to
- `Goodstein → primrec-PRWO(ε₀)` via §3 on a **primitive-recursive** descent. **Your lap-43/44
  `Grzegorczyk.lean` ℕ-template is already exactly this** (`g`, `g_desc`, `g_C_bound`, Cor 3.4 bricks) —
  it fits Route A with no rework, because it is *already primrec*.
- `primrec-PRWO(ε₀) → Con(PA)` (Thm 2.8(i)) → Gödel II (Foundation `Incompleteness/Second.lean`).
- This is `Reduction.goodstein_implies_consistency` (the `Reduction.lean:52` Route-A hook) fed by the
  **X-free §3 substrate you BANKED at lap 27** (the lap-25/26 internal-V `DescentArith.*` work). That
  substrate may be much closer to closing the headline than the lap-27+ X-definable path.
- **Cost:** the single `PA_delta1Definable` (🟡) Foundation axiom — the stated reason A was set aside.
  Per the repo's own rule "Route A only if B stalls": my read is **B is not stalling, it is blocked**, so
  the fallback condition is met. One documented 🟡 axiom is the honest price of the *elementary* proof;
  it is not fraud and not a `sorry`.

## §D. Why this matters now
`InternalCor34.lean` is grinding toward `xDescent_domination` for an X-definable descent. If §A/§B are
right, that obligation is **false in general** (not just unproven), so the grind cannot terminate in a
proof. Pausing it to validate §E first is high-leverage.

## §E. Validation checklist — confirm or REFUTE against the actual code (do this before acting)
1. **Is `peano_not_proves_TI` genuinely free-X — and can the boundedness *machinery* re-prove
   `PA ⊬ primrec-PRWO`?** Confirm `Xsym` is a fresh, never-instantiated predicate symbol (free-X TI).

   ⚠️ **Precise framing — avoid a false positive.** Do **not** try to "specialize" the *theorem*
   `peano_not_proves_TI` to `PA ⊬ primrec-PRWO`. That move is **logically invalid**: `free-X TI` is
   *strictly stronger* than `primrec-PRWO` (`free-X TI ⊢ primrec-PRWO` by instantiating `X` at the
   descent predicate), so its **un**provability is the *weaker* claim. You cannot derive a stronger
   unprovability (`PA ⊬ primrec-PRWO`) from a weaker one (`PA ⊬ free-X TI`) — instantiating a non-theorem
   does not yield non-theorems (cf. `PA ⊬ Con(PA)` has provable consequences). What §3 needs as its
   back-end is the single X-free arithmetic sentence `PA ⊬ primrec-PRWO(ε₀)`, and that must be **proved
   afresh**, not specialized down.

   So the real question is about the **proof/machinery, not the theorem statement**: *can the Buchholz §5
   boundedness apparatus be re-run to prove `PA ⊬ primrec-PRWO` directly* (e.g. the order-type bound
   applied to a cut-free derivation of the **X-free, arithmetic** `primrec-PRWO` sentence — `X`
   interpreted as a concrete arithmetic level-set, not a fresh symbol)?
   - **If YES** → §B's worry is dissolved *without* Route A: the existing apparatus supplies the needed
     `PA ⊬ primrec-PRWO`, you retarget the reduction's *output* to `primrec-PRWO`, and add **no** axiom.
     (This is the best outcome — verify it can actually be done, don't assume it.)
   - **If NO** (boundedness only yields the free-X version) → you need `PA ⊬ primrec-PRWO` from **Thm 2.8
     / Gödel II = Route A**, accepting the one `PA_delta1Definable` (🟡) axiom.

   Either way the **target is the same** — `PA ⊬ primrec-PRWO` — and your primrec §3 work (`Grzegorczyk.lean`)
   feeds it unchanged. The only fork is *where the back-end unprovability comes from*. **Check this first;
   it is the load-bearing question.**
2. **Is the live obligation actually the primrec-domination?** Inspect what `nonterminating_of_xDescent`
   / `hCD` demands of the extracted `β : M → M`. If it needs `∃ l, ∀ k, iC(β(k+1)) ≤ iF l k` for an
   X-definable `β`, try to **construct a counterexample**: an `X` (oracle) whose induced descent has
   `C(β(k+1))` outgrowing every fixed `F_l`. If refutable, the wall is confirmed real.
3. **Does Route A close from what you already have?** Repoint `Grzegorczyk.lean` (primrec §3) at the
   X-free primrec descent (lap-25/26 banked substrate) → `primrec-PRWO` → `Reduction.lean` Route-A hook →
   Foundation Gödel II. Check whether the headline closes with only `PA_delta1Definable` added (re-run
   `#print axioms`).
4. **Match the contradiction shape to Cor 3.7 (p.14).** Rathjen's contradiction is `PRWO via Con + Gödel
   II`. If your intended contradiction is a *different* shape (`free-X TI via boundedness`), pinpoint
   exactly where you obtain `Goodstein → free-X TI` that Rathjen does not — that step is the suspect.

## §F. How this finding could be wrong (please try to refute)
- **(most likely escape)** If `peano_not_proves_TI` can be specialized to `PA ⊬ primrec-PRWO` (checklist
  #1), the boundedness back-end *is* the right one and only the reduction wiring is off. Then §C is
  overkill — just target `primrec-PRWO`.
- If paLX-internal reasoning supplies a bound on the *specific* constructed descent that I am not seeing
  (some intrinsic control making the X-definable `β` effectively primrec-dominated), the domination might
  hold after all. I could not find such a bound, but you have the construction; check it.
- If you intend the **free-X** result for its own sake, the matching technique is **Kirby–Paris 1982**
  (`papers/kirby-paris-1982-accessible-independence.pdf`, ref [9]) — model-theoretic (nonstandard
  models / indicators), a *completely different* proof from Rathjen §3. Do not expect §3 to deliver it.
  Conflating the two proofs is the trap this doc is warning about.

## §G. Recommended immediate action
1. **Pause** the `InternalCor34` internalization grind.
2. Run **§E checklist #1** (is the back-end free-X or specializable to primrec-PRWO?). This single check
   decides everything.
3. If free-X-only: trigger the **Route-A fallback** (§C) — reuse `Grzegorczyk.lean` + the banked X-free
   §3 substrate + the `Reduction.lean` hook + Gödel II; accept the one `PA_delta1Definable` axiom.
4. Keep the Buchholz §5 `peano_not_proves_TI` work as an independent, axiom-clean result regardless — it
   is a genuine achievement; it just may not be the right back-end for *this* headline.

— end of review —

## §H. VALIDATION RESULT — 2026-06-23 lap 45 (in-box, against the actual code)

Ran the §E checklist. **The finding is CONFIRMED** (independently re-derived before reading this doc,
from the same Rathjen §3 text + the consumer side):

1. **#1 — free-X vs primrec-PRWO: GENUINELY FREE-X.** `Thm56.peano_not_proves_TI :
   IsEmpty (Derivation2 paLX {TI prec})` with `TI prec = Prog prec 🡒 ∀⁰ (Xat #0)`, `Xat` on the
   **free** relation symbol `Xsym` (`LangX.lean:39`), over `paLX` (induction extended to LX-formulas
   incl. X). `prec` is the **concrete** ε₀ order (lMap of a `Semisentence`), not free; the free part is
   the induction predicate `X`, never instantiated on the headline path. ⟹ **escape #1 does NOT
   apply**; the back-end is the *strong* free-X result, and a §3 reduction landing primrec-PRWO cannot
   discharge it. **This is the load-bearing check, and it confirms §B.**
2. **#2 — the live obligation IS the primrec domination, FALSE in general — now MACHINE-CHECKED.**
   `Grzegorczyk.not_dominated_of_diag_le` / `F_diag_not_dominated` (commit `279050d`, pure-ℕ,
   axiom-free) certify: any width/coefficient-growth `w` dominating the diagonal `n ↦ F n n` satisfies
   `¬ ∃ l, ∀ n, w n ≤ F l n` — exactly the negation of `xDescent_domination`. So the X-definable §3
   route is **blocked, not merely hard.** (Realizing a *specific* X-descent with diagonal-fast growth is
   model-theoretic and NOT claimed; the hierarchy fact suffices to refute the obligation.)
3. **#3 — does Route A close from here? NOT for free.** `PA_delta1Definable` is **still an `axiom`** in
   the current Foundation pin (`Incompleteness/Examples.lean:17`). So Route A carries that axiom AND its
   `goodstein_implies_consistency` girder (`Reduction.lean:52`, the Gentzen `TI(ε₀)⊢Con(PA)` direction =
   Thm 2.8(i)) remains an unbuilt deep `sorry` — a *different* girder from the Buchholz §5 boundedness
   built for free-X TI.
4. **#4 — contradiction shape.** Our intended contradiction is `Goodstein → free-X TI via boundedness`,
   which Rathjen does NOT deliver; the suspect step is precisely "slow the X-definable descent"
   (§3-on-X), now refuted.

**Bottom line / the fork (Trevor's strategic call — route switch after sustained effort + the lap-12
anti-fraud stance on Route A's axiom):**
- **(A) Route A** (Rathjen's actual proof): primrec §3 (`Grzegorczyk.lean` already fits) → primrec-PRWO
  → Con(PA) → Gödel II. Cost: the disclosed `PA_delta1Definable` axiom on the headline + still must
  build the `TI(ε₀)⊢Con(PA)` girder (PA∞ cut-elim — NOT the Buchholz §5 work).
- **(B′) Route B via Kirby–Paris 1982** (model-theoretic indicators / nonstandard models): keeps the
  free-X back-end, replaces the (blocked) §3 slow-down with the KP indicator argument inside `M ⊧ paLX`
  (the current wall `no_min_descent_absurd_of_goodstein` is already model-internal, so this is the
  natural continuation). Avoids `PA_delta1Definable`.
- **(iii) Route B via §3-on-X: DEAD** (this §H).

KEEP regardless: `peano_not_proves_TI` (Buchholz §5, axiom-clean) and `Grzegorczyk.lean` (primrec §3) —
real assets reusable by whichever route. Leaf internal bricks (`InternalCor34.ig0`, the general
`ocOadd` descent lemmas) are substrate-agnostic and survive.

— end of review (validated lap 45) —
