# SPIKE W4 — the operator cut-elim CONTROL-RAISING design spike (operator-commissioned, 2026-07-01)

> **One bounded session. Deliverable = a typed step-theorem skeleton + ONE case attempted + a binary
> verdict file. NOT a proof campaign.** Deciding experiment #2 of `MASTERPLAN-2026-07-01-ZERO-AXIOMS.md`
> (§5 W4). Everything about bounded cut-elimination is banked EXCEPT one design question; this spike
> answers exactly that question and stops.

## Context (read first)

- `src/GoodsteinPA/ZinftyGen.lean:1547–1694` — the UNBOUNDED `cutElimPrincipal`/`cutElimStepAux`/
  `cutElimStep`/`cutElim` chain (kernel-verified axiom-clean). Your structural template: the bounded
  step theorem is the same recursion with budget bookkeeping.
- `src/GoodsteinPA/OperatorZinfty.lean` — `ZekdSomeK.cutReduceConj/Disj` (:2219/:2239),
  `cutReduceAllAux` (:2262, deliberately FIXED-family) and `cutReduceAllAux_control` (:2283, composes
  with control-raising; kernel-verified clean), `mono_e` (:2078), `allInv` (:2209).
- `src/GoodsteinPA/Hardy.lean` — `hardy_add_collapse` (`H_{e+α} = H_e ∘ H_α`), the control-nesting tool.
- Towsner §19 (esp. 19.6–19.9) + Buchholz–Wainer 1987 (`papers/buchholz-wainer-1987-…`) — the paper
  treatment of witness bounds through cut-elimination. Ground the design in the papers.

## The one open design question

In the global rank-lowering recursion (`cutElimStepAux`'s bounded twin), traversing a NON-principal
`allω` node whose premises sit at running index (`max k n` budgets): the IH hands back, per premise
`n`, a reduced derivation at some raised control `e'ₙ`. Re-assembling the ω-node needs **one uniform
raised control `e'` for the whole family** — an `e'` that is a function of `(α, e, c)` (structure),
NOT of `n`. The fixed-family `cutReduceAllAux_control` dodged this by construction; the spike confronts
it.

## Objective

In `wip/SpikeW4CutElim.lean` (new file, `GoodsteinPABlueprint` root):

1. **Pin the step statement.** Candidate (amend = finding):

   ```lean
   theorem operatorCutElimStep
       {α e : ONote} {d c : ℕ} {Γ : Seq}
       (hα : α.NF) (he : e.NF)
       (h : ZekdSomeK α e d (c + 1) Γ) :
       ZekdSomeK (expTower α) (raise e α) d c Γ
   ```

   with `expTower`/`raise` EXPLICIT ONote functions (ω^-shape and `e + f α`-shape via
   `hardy_add_collapse`) — the uniformity requirement is that `raise` takes only `(e, α)`, never the
   branch index.
2. **Skeleton the recursion** (named sorried lemmas per case, mirroring `cutElimStepAux`'s structure),
   assembled by a real induction.
3. **Attempt ONE case for real: the non-principal `allω` traversal** (the design question above). The
   principal cut cases may cite the banked `cutReduce*` surfaces as sorried obligations — do not
   re-prove them.

## Verdict criteria — write `SPIKE-W4-VERDICT.md`, then STOP

- **PASS** = the step statement + case skeleton elaborate, AND the `allω`-traversal case closes (or
  reduces to lemmas that are transparently `mono_e`/`hardy_add_collapse`-shaped) with a family-uniform
  `raise e α`. State the explicit `expTower`/`raise` and whether they stay `< ε₀` trivially (ONote).
- **FAIL** = the traversal genuinely needs an `n`-dependent control raise (or the `∃K` in `ZekdSomeK`
  breaks the IH's compositionality). Name the obstruction precisely; assess whether Buchholz
  operator-controlled derivations (control as a FUNCTION decorating the derivation, not an index)
  dodge it. This fires trigger **T-W4** — a valuable outcome.
- Either way: real `#print axioms` on the assembled step (expect `sorryAx` + canonical only — NO new
  `axiom` declarations), verdict file written, commit, stop.

## Forbidden

- Grinding principal-cut cases (banked), re-proving inversions, proving beyond the ONE mandated case.
- New `axiom` declarations; LOCK files; `DIRECTION.md`; redesigning `Zekd` (document as FAIL instead).
- Depends-on note: this spike does NOT need SPIKE-W3's result (it works at the someK surface directly),
  but run it AFTER W3's session exits to avoid git races on this repo.
