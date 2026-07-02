# SPIKE W4 — VERDICT

> Deciding experiment #2 of `MASTERPLAN-2026-07-01-ZERO-AXIOMS.md` §5 (W4). One bounded session.
> Deliverable: typed skeleton `wip/SpikeW4CutElim.lean` + this verdict. See `SPIKE-W4-CONTROL.md`.

## Verdict: **PASS — the control raise IS family-uniform; conditional on ONE mandatory amendment.**

The one open design question — *can the non-principal `allω` traversal of the bounded
rank-lowering recursion re-assemble the ω-node at a single raised control that is a function of
`(α, e)` only, never of the branch index?* — is answered **YES, and not merely at the type level:
the mandated case is proven sorry-free and axiom-clean in the kernel**:

```
'GoodsteinPA.SpikeW4.step_allω' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No branch-dependent control raise is needed, and the `∃K` of `ZekdSomeK` never gets the chance to
break the IH's compositionality (it is opened once, at the root — the amendment below).
**Trigger T-W4 does NOT fire.** The Buchholz fully-operator-controlled fallback is *not* needed
for the traversal — though the verdict locates precisely where the W4 phase may still want it
(the principal ∀/∃ `d`-budget, §"the residual" below — a different slot, outside the mandated
question).

## The explicit transforms (PASS criterion: state them + `< ε₀`)

```lean
def expTower (α : ONote) : ONote := oadd α 1 0     -- ω^α
def raise (e α : ONote) : ONote := e + expTower α  -- e + ω^α
```

Both are literal `ONote`s, so **`< ε₀` holds trivially** (every notation denotes below `ε₀`; NF
is preserved: `expTower_NF`, `raise_NF`). `raise` takes only `(e, α)` — the uniformity
requirement of the mandate — and has the `e + f α` shape that `hardy_add_collapse`
(`H_{e+α} = H_e ∘ H_α`, `Hardy.lean:1686`) collapses, so nested raises across iterated steps stay
one Hardy level. Its two load-bearing properties, both proven (not sorried):

- `raise_lt_raise : β < α → raise e β < raise e α` — strict monotonicity in the ordinal argument
  (via the banked `Zekd.add_lt_add_left_NF`). **This is the whole uniformization mechanism**: the
  per-branch controls `raise e (β n)` all sit strictly below the single `raise e α`, so
  `ZekdProv.mono_e` lifts every branch to the SAME control.
- `norm_raise_le : norm (raise e α) ≤ norm e + max (norm α) 1` (via the banked
  `Zekd.norm_add_le`) — what the amended `+ norm e + 1` budget pays for.

## What was built (evidence)

`wip/SpikeW4CutElim.lean` — elaborates green under the repo toolchain
(`lake env lean wip/SpikeW4CutElim.lean`):

- **12 named case lemmas**, one per `Zekd` rule arm (the cut arm splits keep/principal),
  mirroring the unbounded `cutElimStepAux` (`ZinftyGen.lean:1604`), all stated over the
  norm-carrying `ZekdProv` wrapper with `cutReduceAllAux`'s running-index discipline.
  11 sorried; **`step_allω` proven for real** (the one-case mandate).
- **`operatorCutElimStepAux`** — the step recursion, assembled by a REAL (non-`sorry`)
  induction over `Zekd`; every arm a single `exact` into its case lemma. So the statement's
  coherence under the global recursion — IH shapes, the `c' = c + 1` rank threading, the
  running-index `max k n` discipline, the uniform raise — is machine-checked.
- **`operatorCutElimStep`** — the pinned someK-surface statement (amended, below), a REAL
  corollary (complete proof: root `∃K` unpack, `mono_k` to pay the root norm side condition,
  `ofProv` re-pack).
- Disclosed axioms (real `#print axioms`, in-file):

  ```
  'GoodsteinPA.SpikeW4.operatorCutElimStep' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'GoodsteinPA.SpikeW4.step_allω'           depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  → `sorryAx` + the 3 canonical on the assembly; the mandated case sorry-FREE. **No new `axiom`
  declarations anywhere.** No LOCK file, no `DIRECTION.md` edit, no `Zekd` redesign.

## THE mandatory amendment (candidate statement → pinned statement)

The candidate's conclusion `ZekdSomeK (expTower α) (raise e α) d c Γ` amends in one place:

```lean
theorem operatorCutElimStep {α e : ONote} {d c : ℕ} {Γ : Seq}
    (hα : α.NF) (he : e.NF)
    (h : ZekdSomeK α e d (c + 1) Γ) :
    ZekdSomeK (expTower α) (raise e α) (d + norm e + 1) c Γ
--                                      ^^^^^^^^^^^^^^ was `d`
```

**(a) The `d`-budget must grow by `norm e + 1`.** The per-branch `mono_e` lift is not free: its
side condition is `norm (raise e (β n)) ≤ max k n + d_out`, and `norm (raise e (β n))` can reach
`norm e + norm (β n) + 1` with `norm (β n) < max k n + d` the rule's own bound — so
`d_out = d + norm e + 1` is exactly sufficient, **and uniform in `n`** (`norm e` is structure).
At fixed `d` the lift is unpayable for general `e`. The bump is a function of the *input control
only* — under iteration it compounds through `raise`, which is `hardy_add_collapse`-shaped by
construction; W6-style assembly arithmetic, not a wall.

**(b) The recursion runs at the `Zekd`/`ZekdProv` level; the someK surface is root-only.** The
candidate statement cannot drive its own induction: the ω-case IH would give `∀ n, ∃ Kₙ, …` while
`Zekd.allω` needs the swapped `∃ K, ∀ n, … (max K n) …` — the identical `∀∃ ↛ ∃∀` trap
SPIKE-W3's `all` case hit, resolved by the identical move (concrete base index threaded through
the induction, branch entering only via the running index `max k n`; the `∃K` opened at the root
and re-packed by `ofProv`). This directly answers the FAIL-criterion's parenthetical: the `∃K`
*would* break the IH's compositionality if the induction ran at the someK surface; run one level
down, it never enters the induction.

## Why the mandated case closes (the design answer, 3 moves)

For an ω-node at `(α, e, k, d)` with premises `β n < α` at `(max k n, d)`:

1. IH per branch: reduced derivation at `(expTower (β n), raise e (β n), max k n, d + norm e + 1)`.
2. `ZekdProv.mono_e` lifts branch `n` to the node-uniform `raise e α` — legality from
   `raise_lt_raise` (`β n < α`), budget from `norm_raise_le` + the rule's own `hτ n`.
3. The lifted family re-enters `Zekd.allω` at base index `k`: per-branch ordinals
   `≤ expTower (β n) < expTower α` (strict monotonicity), per-branch norms carried by the
   `ZekdProv` wrapper (the `cutReduceAllAux` norm-threading discipline — the reason the wrapper,
   not bare `Zekd`, is the recursion's surface), node norm `max (norm α) 1 < k + d_out` from the
   threaded `norm α < k + d`.

No `hardy_add_collapse` is needed *in this case* (it is the principal-cut/iteration tool), and
nothing depends on the branch index except through `max k n` — the discipline the calculus was
built for.

## Per-case disposition

| Case | Verdict | Discharging machinery |
|---|---|---|
| `axL`, `verumR` | mechanical | leaf re-formation at witness ordinal `0` (wrapper `≤`-slack) |
| `trueRel`, `trueNrel` | mechanical | keep leaf at original `α ≤ expTower α`; norm rides `hnorm` |
| `wk` | mechanical | `ZekdProv.weakening`, verbatim |
| `weak` | mechanical | `mono_e` (as in `step_allω`) + wrapper `≤`-slack + weakening |
| `andI`, `orI` | mechanical | FINITE instances of the `step_allω` pattern (2/1 branches) |
| **`allω`** | **PROVEN** | the mandated case — sorry-free, axiom-clean |
| `exI` | mechanical* | `mono_e` + witness re-pay `hardy e (k+d) ≤ hardy (raise e α) (k+d_out)` — the same norm-gated hardy raise `Zekd.mono_e` performs internally |
| `cut` (rank `< c`) | mechanical | `mono_e`-unify + re-cut; `ω^α` additively principal absorbs the `osucc` bookkeeping |
| **`cut` (rank `= c`)** | **hard** | banked `Zekd.cutReduceConj/Disj` (∧/∨); ∀/∃ + rank-0 = the W4-phase work (below) |

## Obligations the skeleton SURFACES for the W4 phase (new, precise)

1. **Rank-0 principal twins missing.** `OperatorZinfty` has no bounded analogues of `ZinftyGen`'s
   `atomCut` / `removeFalsum` (grep-verified). Finite, template-driven ports — but they must be
   built, not cited.
2. **`cutReduceAllAux` fixed-family → running-family.** The banked ∀/∃ reduction takes `fam` at a
   FIXED `k₀`; the recursion's `allInv` hands the family at the running index `max k₀ n`. This is
   the *known* scope gap (`OperatorZinfty.lean:764–784`), now located exactly at
   `step_cut_principal`'s ∀/∃ sub-case, with the control raise available (this spike) to pay the
   witness half.

## The residual — the principal ∀/∃ `d`-bump under ω-nodes (located, NOT kernel-verified)

Analysis (not yet a kernel-checked obstruction — the W4 grind must confirm or refute in-kernel):
the banked ∀/∃ reduction bumps `d ↦ d + norm (fam ordinal) + 1`. Inside the recursion the family
ordinal at a cut node is `expTower βφ`, and *under an enclosing ω-node* `norm βφ` is only bounded
by `max k n + d` — **branch-dependent**. A fixed functional `d_out(e, d)` (this statement) cannot
absorb it; neither can the other slot (`Zekd.allω` premises must sit at exactly `max K n`, and
the `d→k` rebalance is provably the wrong direction). Note this is a *different slot* from the
mandated question — the CONTROL raise stays family-uniform regardless; the at-risk quantity is
the numeric norm budget, i.e. the numeric-index shadow of the same scope gap in (2). If it
kernel-confirms, the assessed dodge is exactly the criteria's named fallback: **Buchholz
operator-controlled derivations** — replace the additive `(k, d)` norm budget by a control
FUNCTION/set closed under the reduction's ordinal arithmetic (`+`, `ω^·`, `osucc`), so "premise
norms in budget" becomes "premise ordinals in `H`", which IS stable under the splice. The `e`-side
of this spike carries over unchanged (the raise already lives at the operator level). Sequencing
consequence: **W4's grind must attack `step_cut_principal`'s ∀/∃ sub-case FIRST**, with this risk
pre-registered — it is the phase's genuine hard core; everything else in the table is mechanical.

## Bottom line for the masterplan

W4 is **un-blocked and well-posed at the step level**: the statement is pinned (amended), the
recursion skeleton is machine-checked, and the isolated genuinely-new design piece the spike was
commissioned to decide — the family-uniform control raise through commuting ω-rules — is **proven
in the kernel, not just typed**. Sequence for the ~5–10 lap phase: (1) `step_cut_principal`'s ∀/∃
sub-case (running-family `cutReduceAllAux` + the `d`-bump question — the hard core, fallback
pre-named); (2) rank-0 twins (`atomCut`/`removeFalsum` ports); (3) the seven mechanical
`mono_e`-shaped cases; (4) iterate the step (`hardy_add_collapse` collapses the nested raises)
into the W4 exit artifact `operatorCutElim`. T-W4 does not fire; no re-design of `Zekd` is
needed for the traversal half.
