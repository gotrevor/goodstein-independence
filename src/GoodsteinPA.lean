/-
# GoodsteinPA — Goodstein independence over PA (Kirby–Paris), expedition library

Track 2 of the Goodstein effort: the *syntactic* `𝗣𝗔 ⊬ γ`, built on Foundation's first-order
+ incompleteness apparatus. (Track 1, the mathlib-only growth theory, lives in
`~/src/lean-formalizations`.) See `DIRECTION.md` at the repo root.
-/
import GoodsteinPA.Computability
import GoodsteinPA.Encoding
import GoodsteinPA.Bridge
import GoodsteinPA.Reduction
import GoodsteinPA.Statement
import GoodsteinPA.Zinfty
import GoodsteinPA.ZinftyGen
import GoodsteinPA.LangX
import GoodsteinPA.TruthSem
import GoodsteinPA.XPositive
import GoodsteinPA.Boundedness
import GoodsteinPA.XFreeCutElim
import GoodsteinPA.Hardy

import GoodsteinPA.Domination
import GoodsteinPA.LowerBound
import GoodsteinPA.Embedding
import GoodsteinPA.WainerRoute
-- Route-B growth axiom `wainer_bound_of_pa_proves_goodstein` DISCHARGED into a theorem here
-- (SERIES-4 judge pass): promotes the embedding/RVG/Hardy wip chain into src and splices the witness.
import GoodsteinPA.WainerBound

import GoodsteinPA.EmbeddingX
import GoodsteinPA.EpsilonOrder
import GoodsteinPA.Epsilon0Complete
import GoodsteinPA.ONoteComp
import GoodsteinPA.SeamDefinability

import GoodsteinPA.Thm56
import GoodsteinPA.EmbeddingBound

-- E-core (the Goodstein⟹TI descent, Rathjen §2–3): proof-translation lift + semantic backbone
-- + the arithmetization induction scaffold. Not yet wired into the headline (E = `DescentE` is
-- still a `Prop`), but kept in the build so the §3 bricks stay green.
import GoodsteinPA.DescentLift
import GoodsteinPA.DescentCore
import GoodsteinPA.Grzegorczyk
import GoodsteinPA.DescentArith
import GoodsteinPA.InternalPow
import GoodsteinPA.InternalDigits
import GoodsteinPA.InternalLog
import GoodsteinPA.InternalBump
import GoodsteinPA.InternalONote
-- Natural (Hessenberg) sum `inadd`/`insTerm` on CNF codes — Buchholz §4 pre-ordinal `õ` infra
-- (promoted lap 60; sorry-free, axiom-clean). Order facts F1–F4: strict left-monotonicity,
-- `ω^α#ω^β ≺ ω^γ`, `ω^β·k ≺ ω^{β+1}`, commutativity. Consumed by the (wip) crux-2 descent.
import GoodsteinPA.InternalNadd
-- ω-exponential tower `ω_n(α)` for Buchholz §4 `o(d) = ω_{dg(d)}(õ(d))` (promoted lap 60;
-- sorry-free, axiom-clean). Strict base-monotonicity `icmp_iotower_mono` (Thm 4.2 same-degree
-- descent) + NF preservation. Consumed by the (wip) crux-2 ordinal assignment.
import GoodsteinPA.InternalTower
-- Free-variable substitution on coded terms/formulas (the `zsubst`/RedSound substrate, lap 72).
import GoodsteinPA.FvSubst
-- Crux-2 island: Buchholz-Z ordinal analysis arithmetized in PA (the `PRWO→Con` wall).
-- Promoted from wip/ to src/ (lap 66) so the green-gate type-checks it every lap. Sorry-free;
-- off the headline path until wired into Reduction.lean, but now compiled + axiom-scanned.
import GoodsteinPA.InternalZ
-- Eigenvariable substitution on Z-derivations (rung 1 of the RedSound ladder, lap 72).
import GoodsteinPA.Zsubst
-- Critical-branch K-case ordinal descent for the GENUINE reduct `red` (lap 108; sorry-free, axiom-clean).
-- Ports `iord_descent_iR2_zK_of_valid` to the `red`-ρ via the i/j-side `red` bundles + `iord_iRcritG_eq_iRcrit`.
-- A building block for `iord_descent_red`'s K-case (not yet wired — needs the splice/replace branches + `zKValid`).
import GoodsteinPA.RedZKDescent
import GoodsteinPA.InternalCor34
import GoodsteinPA.IIter
import GoodsteinPA.BlkRec
import GoodsteinPA.BlkRecF
import GoodsteinPA.InternalGrz
import GoodsteinPA.InternalIg
import GoodsteinPA.InternalThm35
import GoodsteinPA.InternalGoodstein
import GoodsteinPA.DescentSlowdown
-- Crux-1 STANDARD-level internal Cor 3.4 global assembly (promoted lap 56; sorry-free, axiom-free,
-- conditional over the Cor-3.4 inputs). Supplies `crux1_internal_run_of_width_dom`, consumed by the
-- (wip) crux-1 bridge in `wip/GentzenCon.lean`. Not yet wired to the headline.
import GoodsteinPA.StdCor34
import GoodsteinPA.StdCor34F
import GoodsteinPA.InternalBridge
import GoodsteinPA.DescentInternal

-- (SERIES-5 cleanup) The Route-A consistency-route apparatus — `DescentSemantic`,
-- `DescentConstruction`, `Crux2Blueprint` — moved to `wip/` after route B carried the headline
-- kernel-clean; they were the abandoned Goodstein⟹Con(PA) route, off the clean summit.
import GoodsteinPA.ReductModel
import GoodsteinPA.XCongruence


-- Front 2 (Foundation's `PA_delta1Definable` axiom) is RESOLVED UPSTREAM: Foundation@e6e1ad1 proves
-- both `PA_delta1Definable` / `ISigma1_delta1Definable` as instances (were bare axioms), so
-- `peano_not_proves_consistency` is now axiom-clean with zero in-repo work. The old `PADelta1.lean`
-- in-repo re-derivation (a sorry'd `(InductionScheme ℒₒᵣ Set.univ).Δ₁`) is deleted as vestigial.
