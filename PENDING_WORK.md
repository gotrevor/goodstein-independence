# Pending work — open obligations & attack paths

## lap 122 — the generalized redex finder is ASSEMBLED; the "L-axiom caveat" is REFUTED
**Build 🟢 1326; new theorem axiom-clean `[propext, choice, Quot.sound]`.** Banked
`inference_critical_pair_of_chain_reroute` (InternalZ, right after `exit_nonRep_of_reroute`).

**THE DELIVERABLE.** The full Sub-lemma A + Sub-lemma B assembly the lap-121 baton scheduled. It is
`inference_critical_pair_of_chain` with its `hnperm` **isymRep clause replaced by a re-route hypothesis**
`hreroute : ∀ i ≤ j0, tp(znth ds i) = isymRep → ∃ i' < i, chainAsucc ds i' = chainAsucc ds i`. It still
produces the genuine `(R_A, L^k_A)` redex with `0 < rk A ≤ r`. So a valid ⊥-chain whose ONLY
criticality-failures are re-routable permissible premises STILL drives the K-descent
(`iord_descent_iRcrit_of_redex`) — the threaded-atom stall dissolved with no engine surgery, **modulo
discharging `hreroute`**. Proof structure: Step A = `exit_nonRep_of_reroute` (non-Rep exit ⟹ left symbol);
Step B = least left symbol `j` (search over `tpSeq ds`, NOT `tp(znth ds ·)` — the latter blows up aesop
depth, see below); Step C = least source `i'` of the cut formula `B` via `least_number` on the definable
`chainAsucc ds · = B`.

**⭐ THE L-AXIOM CAVEAT IS REFUTED (the decisive lap-121 sub-question, settled).** The lap-121 baton flagged
as a genuine risk: "the threading may bottom out at an `isymLk` L-axiom (succ B), not an `isymR(B)`
producer — then the generalized finder FAILS." It does NOT. Step B takes the **LEAST** left-symbol index
`j`; the cut formula `B = A_i` (i < j) is re-routed to its **least** source `i'`, and `i' ≤ i < j`, so
every re-route lands strictly below `j` — where by minimality of `j` there are **no left symbols at all**.
Hence the source can never be an `isymLk` L-axiom. The least source `i'` is non-left (minimality of `j`) and
non-`isymRep` (a re-route would hand back a strictly smaller source, contradicting `i'` least), therefore
`I_{i'} = R_B`. The redex is `(i', j)`. So path (i) is sound on the L-axiom front; the baton's pessimism
was over-cautious.

**THE GENUINE RESIDUAL (sharpened, replaces the refuted caveat) — discharge `hreroute`.** The finder is
banked modulo its one open input `hreroute`, which must hold for **every** `isymRep` premise `≤ j0`.
`chainAsucc_threaded_of_leaf` (lap 121) discharges it for the LEAF isymRep shapes (`zAtom`/`zAx1`, tags
0/7) — their succedent sits in their own antecedent, so chain-threading routes it to an earlier premise.
But `isymRep` ALSO arises from **chain (tag-3) and Ind (tag-4)** premises (`tp_zK`/`tp_zInd`), whose
succedent need NOT appear in their own antecedent — so the leaf lemma does not re-route them. **Decisive
next sub-question:** in a valid ⊥-chain, can a chain/Ind premise (isymRep, succedent = the cut formula `B`,
`0 < rk B`) appear at the least source `i'` (i.e. below the least left symbol)? Two ways to close:
- **(α) exclude / defer them:** likely the right framing — a chain/Ind premise with succ `B` (`0 < rk B`) is
  itself a smaller derivation of `B`, so the *outer* descent recursion (`iord`) covers it; the finder need
  only handle the genuinely-atomic stall. Show the least source ≤ j0 is never tag-3/4, or split the
  descent so tag-3/4 sources route to the IH.
- **(β) re-route them too** — probably FALSE in general (a chain's succedent is free), so (α) is likelier.

**Definability recipe worth remembering (lap 122).** `simp only [isymIsL]; definability` on
`isymIsL (tp (znth ds x))` TIMES OUT at whnf (aesop depth-blowup on the composed `tp`, per memory
`definability-aesop-depth-blowup`). Two fixes were both needed: (i) search over the coded map `tpSeq ds`
via `znth (tpSeq ds) x` (`znth_tpSeq` bridges `= tp (znth ds x)` for `x < lh ds`) instead of `tp(znth ds ·)`;
(ii) `set Is := tpSeq ds with hIs; clear_value Is` BEFORE `definability`, else `definability` recurses into
`tpSeq`'s heavy `PR.Construction` and times out. The whole theorem also needs `set_option maxHeartbeats
1000000`. The `chainAsucc ds · = B` predicate uses the hand-built comp term from `exit_nonRep_of_reroute`.

**NEXT-LAP TARGETS (in order):**
1. **[lap 123] Discharge `hreroute` for chain/Ind premises** — attack path (α): prove that in a valid
   ⊥-chain, the least source of the cut formula is never a tag-3/4 node, OR that such a node is covered by
   the outer `iord` descent recursion rather than the finder. THE remaining gate on path (i).
2. ✅ DONE (lap 122, 3rd commit) — `iord_descent_iRcrit_of_chain_reroute` (InternalZ, right after the
   reroute finder): the reroute twin of `iord_descent_iRcrit_of_chain'`, manufactures the redex via the
   generalized finder and feeds `iord_descent_iRcrit_of_redex`. Stall-free K-descent for valid ⊥-chains,
   modulo `hreroute`. Only target #1 (discharge `hreroute` for chain/Ind) now gates path (i).
3. Re-point the endgame `false_of_ZDerivesEmpty` (M3) strict-descent disjunct onto this stall-free track
   (cf. lap-121 note: `iR2`-track and `red`-track share the ordinal `iord_iRcritG_eq_iRcrit`).
4. Sibling (independent of the stall): `zKValidF_iIndReduct_of_zInd` (lap-120 found it false as stated;
   fix = instance-correct Ind reduct via `zsubst`). Then `foundation_bot_to_Z_empty` (M2) + `gentzenDescentφ`.

## lap 121 — the stall SPLITS: junk-beyond-j0 is provably harmless; only threaded atom ≤ j0 is open
**Build 🟢 1326; new lemma axiom-clean `[propext, choice, Quot.sound]`.** Banked
`iord_descent_iR2_zK_of_validF_critUpTo` (InternalZ, right after `iord_descent_iR2_zK_of_valid`).

**THE FINDING (sharpens lap-120's monolithic stall).** `iord_descent_iR2_zK_of_valid` destructures
`zKValid`'s GLOBAL criticality conjunct `hnperm0 : ∀ i < lh ds, ¬iperm(tp dᵢ) s`, but its proof body
applies it ONLY at indices `i ≤ j0` (the `isChainInf` exit; see InternalZ:8045 in the original). So the
ordinal descent goes through under the strictly weaker `hcrit : ∀ i ≤ j0, ¬iperm(tp dᵢ) s` — that is the
new lemma. **Consequence:** `isChainInf` constrains only premises `0..j0`; therefore a `red`-stall caused
by a **junk** permissible premise (`tp=isymRep`, e.g. a spurious identity atom A→A) at an index `> j0` is
HARMLESS to the genuine `iR2`/redex descent — the redex lives in `0..j0` and the new lemma reduces it
regardless of any junk beyond it. lap-120 conflated this junk case with the genuinely-hard threaded case.

**THE OPEN CORE, now sharp.** The stall is genuinely open ONLY when an atom/`zAx1` premise sits AT an
index `≤ j0` AND is threaded (its antecedent is a real cut formula `B = chainAsucc ds i'`, `i' < idx`).
That breaks `hcrit` at that index, so the redex finder (`inference_critical_pair_of_chain_tp`, needs
`hnperm` up to j0) does not apply, and the atom is a genuine cut against an axiom `B→B` → needs axiom-cut
elimination (the lap-120 prescription stands, but now scoped to a strictly smaller case).

**REACHABILITY of the open core (kernel-grounded structural facts, lap 121).** For a valid ⊥-chain
(`zKValidF s r ds`, `seqAnt s=∅`, `seqSucc s=⊥`) the threading at i=0 (no earlier premises, `seqAnt s=∅`)
FORCES premise 0 to have empty antecedent ⟹ premise 0 is NOT `zAtom`/`zAxAll`/`zAxNeg`/`zAx1` (all need a
formula in their antecedent) ⟹ premise 0 ∈ {I-rule, chain, Ind}. So a threaded atom (`hcrit` breaker) is
always at index `> 0`, with its cut formula `B` produced by an earlier non-isymRep premise (I-rule succ =
`∀p`/`¬A` compound, or L-axiom `zAxNeg` succ = arbitrary incl. `⊥`). Whether a COMPLETE valid ⊥-chain
with a threaded atom ≤ j0 as its first-`isymRep` premise actually exists is STILL unverified — the global
exit-to-⊥ constraint fights it (you must thread the cut formulas all the way to a `⊥`-succedent premise,
and an atom B→B passes B through without progress). lap-120 asserted "reachable" from a LOCAL type-system
argument but never exhibited a full valid witness; this is the decisive sub-question.

**LEVER banked (lap 121, 3rd commit): `iord_descent_iRcrit_of_redex`.** The K-cut descent computation
uses the criticality data (`hwfR/hwfL/hperm/hnperm`) ONLY to run `inference_critical_pair_of_chain` and
manufacture a redex; the actual ordinal descent (`redexCode → iord_descent_iCritReduct_object`) needs
just (a) an EXHIBITED redex pair below the finder sentinel, (b) `1 ≤ r`, (c) the six `ρ`-facts. Extracted
that as `iord_descent_iRcrit_of_redex`; `iord_descent_iRcrit_of_chain'` is now a thin wrapper.
**Significance:** in the threaded-atom stall, `hnperm` is broken (the atom is permissible ≤ j0), so the
finder route is blocked — but if the principal-cut redex can be exhibited ANOTHER way, descent still
fires, IGNORING the atom. So the open core reduces to: *exhibit a `(isymR, isymLk)` redex pair in a
valid ⊥-chain that has a threaded atom*. Probe `ZRegular`: NEGATIVE — `zReg` is eigenvar-freshness
(`zRegNext` atom-branch = 0), orthogonal to the atom-stall; regularity does NOT exclude it.

**CONCRETE NEXT-LAP TARGET (sharpened by the lever):** prove a valid ⊥-chain with a threaded
atom/`zAx1` at index `k ≤ j0` (cut formula `B = chainAsucc i'`, `i' < k`, from `chainAsucc_threaded_of_leaf`)
contains a genuine `(isymR, isymLk)` redex pair within `0..j0`. If the upstream producer `i'` of `B` is
an I-rule (`tp = isymR(B)`, B = `∀p`/`¬A` compound), look for the matching `isymLk` consumer of `B`; the
exit-to-⊥ threading should force one. If found → feed `iord_descent_iRcrit_of_redex` → descent, the atom
is harmless, STALL DISSOLVED with no engine surgery. If genuinely absent → the atom-removal reduction
(lexicographic `(iord, length)` measure) is forced. THREE paths: (i) redex-exhibition [above, cheapest];
(ii) atom-removal reduction + length measure; (iii) re-tag atoms off `isymRep` (deep, wide ripple).

**⭐ COMBINATORIAL CHARACTERIZATION (lap 121, 4th finding — the decisive sub-decomposition).** Read the
redex finder `inference_critical_pair` (InternalZ:507) line by line. Its `hnperm` (criticality up to j0)
has THREE clauses: `¬(isymR(Cmain) ∨ isymLk-at-Γmain ∨ isymRep)`. The proof uses them as:
- **isymR(Cmain) clause** — kills an I-rule at the exit j0 (Step A). For a ⊥-chain this is GENUINE and
  always holds: `isymR(Cmain)=isymR(⊥)` needs succedent `⊥`, but I-rules have compound succ `∀p`/`¬A`. ✓
- **isymLk-at-Γmain clause** — gives `B ∉ Γmain` for the least left-symbol. For a ⊥-chain `Γmain=∅`, so
  this is FREE (nothing is in ∅). ✓
- **isymRep clause** — used at TWO spots: the exit j0 (Step A) and the least-left-symbol's chain-source i
  (line 562). **This is the ONLY clause a threaded atom breaks.**
So the redex finder fails for a threaded-atom ⊥-chain ⟺ an `isymRep` leaf is the exit j0 OR is the
chain-source of the least left-symbol. Everything else goes through unchanged.

**THE FIX (named, buildable next lap): generalize `inference_critical_pair` by REPLACING its `isymRep`
clause with re-routing.** Replace `hnperm`'s isymRep clause with: *every `isymRep` leaf `i ≤ j0` has an
earlier duplicate succedent* `∃ i' < i, Asucc i' = Asucc i` — which is EXACTLY
`chainAsucc_threaded_of_leaf`'s conclusion (already banked). Then:
- **Sub-lemma A (least non-isymRep exit): ✅ DONE lap 121** — `exit_nonRep_of_reroute` (InternalZ, after
  `chainAsucc_threaded_of_leaf`), axiom-clean. The LEAST index `j' ≤ j0` with `chainAsucc ds j' = chainAsucc
  ds j0 ∈ {seqSucc s, ⊥}` is NOT `isymRep` (re-route ⟹ smaller exit ⟹ ⊥ vs minimality). **Definability
  fix worth remembering:** `definability`/aesop LOOPS on `chainAsucc` (depth-3 `seqSucc∘fstIdx∘znth`,
  rule-application-depth cap) — the cure was (i) add the generic instance `chainAsucc_definable' (Γ) :
  Γ-[m+1]-Function₂ := chainAsucc_definable.of_sigmaOne` (mirrors `zsubstTable_definable'`; THIS is what
  lets the comp lemmas fire — bare `𝚺₁-Function₂` literal-1 instance is not found by `Γ-[m+1]` synthesis),
  then (ii) hand-build the predicate def: `apply Definable.and ?_ (by definability); exact DefinableRel.comp
  (by definability) (DefinableFunction₂.comp (F := chainAsucc) (DefinableFunction.const ds)
  (DefinableFunction.var 0)) (DefinableFunction.const c)` after `set c := chainAsucc ds j0; clear_value c`.
- **Sub-lemma B (non-isymRep chain-source):** when the least-left-symbol's source `i` would be `isymRep`,
  re-route via the duplicate to a `< i` index; iterate (least-number) to a non-isymRep source. ⚠️ Caveat:
  that source may be `isymLk` (an L-axiom with succ B), not `isymR(B)` — so the re-routed redex needs an
  `isymR(B)` producer; if the threading bottoms out at an L-axiom, this sub-case still needs care (the
  genuine residual). Premise 0 is an I-rule/chain/Ind (empty antecedent, banked reasoning), which bounds
  the recursion.
- Then feed the exhibited redex to `iord_descent_iRcrit_of_redex` (banked this lap) ⟹ descent, STALL
  DISSOLVED for the threaded-atom case, no engine surgery. This is the concrete program for lap 122.

**NEXT-LAP TARGETS (in order):**
0. **[lap 122] Execute the generalized redex finder** (`inference_critical_pair_of_botChain_reroute`):
   Sub-lemma A first (cleanest, fully provable), then Sub-lemma B. Feeds `iord_descent_iRcrit_of_redex`.
1. **Decide reachability of the threaded-atom-≤-j0 core.** Either (a) prove a valid ⊥-chain's
   first-`isymRep` premise within `0..j0` is reducible (zTag ∈ {3,4}, never atom/`zAx1`) — would DISSOLVE
   the stall and let the endgame run on `iord_descent_iR2_zK_of_validF_critUpTo` + a "critical-up-to-j0
   OR has-reducible-isymRep-≤-j0" dichotomy; or (b) construct the witness ⟹ axiom-cut elimination forced.
   Attack via the exit-to-⊥ threading: does reaching a `⊥`-succedent premise force an isymRep cut/Ind ≤ j0?
2. **Wire the junk case into the endgame.** Use the new lemma: a valid ⊥-chain that is critical-up-to-j0
   (no isymRep premise ≤ j0) descends under `iR2` — independent of `red`'s permIdx stall. This is the
   `Or.inr` (strict-descent) closer of `iord_descent_red`'s analogue on the `iR2` track for the junk case.
   ⚠️ Note: `iR2`-track descent and `red`-track descent share the ordinal (`iord_iRcritG_eq_iRcrit`); the
   endgame `false_of_ZDerivesEmpty` currently routes through `red`/`iord_red_iterate_descends` — consider
   re-pointing the strict-descent disjunct onto the `iR2` track where the junk case is already handled.

---

## Reflection — 2026-06-26 (lap 120, DEEP) — the SELECTION/STALL defect is the genuine open crux
**Build 🟢 1326; headline + girder re-verified in-kernel (`[propext, sorryAx, choice, Quot.sound]`, 0 math
axioms); statement re-audited vs paper — no drift.** Primary deliverable `REFLECTION-2026-06-26-lap120.md`.

**DIRECTION: KEEP** (axiom-free Kirby–Paris, Σ₁ engine `red`/`iord`). **The inversion is SOLVED** — laps
112–119 proved critical-cut soundness on both polarities (Buchholz §5). That was reduct SOUNDNESS.

**THE FINDING — `red` STALLS, so `false_of_ZDerivesEmpty` cannot close.** The endgame
`false_of_ZDerivesEmpty {z} (hz : ZDerivesEmptyR z) : False` (`Crux2Blueprint:1144`) is a bare sorry whose
docstring claims it "closes either way" (fixpoint→cut-free→absurd OR infinite→PRWO). But `red` can be a
FIXPOINT on the ⊥-orbit: `permIdx` selects the first premise with `iperm isymRep`, which is unconditionally
true, so an ATOM (or `zAx1`) leaf can be selected → `red (zK s r ds) = zK s r ds` (banked
`red_zK_fixpoint_of_atom_selected`/`_zAx1_selected`) → a tag-4 K-node that is NOT cut-free. The repo flags
this in `RedZKDescent.lean`'s own docstring ("the orbit STALLS … an atom CAN be the first permissible
premise … fix = `permIdx` refinement OR an atom-free embedding"). **Lap-111's disjunctive `iord_descent_red`
(`red d = d ∨ iord ≺`) did NOT fix the stall — it RELOCATED it** into the unbuilt `false_of_ZDerivesEmpty`
sorry (the stall branches close `Or.inl`). Same defect as laps 104/107, still open 13 laps later.

**KEEP doing:** discharge the inversion → `redSound` (the swap is genuinely needed for the RIGHT disjunct).
**STOP:** treating the atomic engine swap as the SOLE next target before the stall is de-risked; asserting
`false_of_ZDerivesEmpty` "closes either way" while (A)+(B) are unbuilt.

**HIGHEST-VALUE NEXT TARGET — (A) `red w = w ∧ ZDerivesEmptyR w ⟹ False`** (fixpoint-absurdity). Decompose
the endgame into named leaves (mirrors how `redSound` was decomposed):
- **(A) fixpoint-absurdity:** `no_red_fixpoint_of_ZDerivesEmptyR : ZDerivesEmptyR w → red w ≠ w`.
  **⚠️ KERNEL-GROUNDED REFINEMENT (lap-120 scouting): the VACUITY route FAILS — do NOT pursue it.** The
  repo's leaf-soundness (`zTag_reducible_of_emptyAnt`, `zTag_Ind_or_K_of_ZDerivesEmpty`, InternalZ:8377/8480)
  only kills axiom leaves whose WHOLE antecedent is empty. But the *selected premise* of a ∅→⊥ K-node has its
  own sequent `sᵢ`, and `isChainInf` (InternalZ:1177, the chain-validity threading) lets premise antecedents
  contain CUT FORMULAS: `∀ B, inAnt B (chainAnt ds i) → inAnt B (seqAnt s) ∨ ∃ i'<i, B = chainAsucc ds i'`.
  With `seqAnt s = ∅`, premise-antecedent formulas are exactly the `chainAsucc` (cut) formulas. So a selected
  atom `zAtom sᵢ` can be a **valid axiom `B→B`** (`seqAnt sᵢ = {B}`, `seqSucc sᵢ = B = chainAsucc ds i'`,
  satisfying atom-validity `inAnt (seqSucc sᵢ) (seqAnt sᵢ)`). The atom's antecedent need NOT be empty — the
  empty-antecedent contradiction does not fire. **The stall is genuinely reachable in the engine's type
  system; `false_of_ZDerivesEmpty` is unprovable as the engine stands.**
- **THE RESOLUTION (faithful Gentzen; = the deferred lap-104/107 prescription):** a selected axiom premise
  `B→B` means the K-node's cut on `B` is **against an axiom**, which Gentzen ELIMINATES (the cut vanishes,
  leaving the matching `B`-succedent premise). The engine's current Rep-reduce is the IDENTITY here
  (`tpReduce_isymRep`), so it STALLS instead of eliminating the axiom-cut. **Fix = extend `red` to reduce the
  axiom-cut** (when `permIdx` selects a genuine axiom `B→B`, splice in the matching `B`-succedent premise and
  drop the cut), guaranteeing progress. This is the "find+reduce the lowest cut" redesign from laps 104/107,
  now pinned to the precise mechanism (axiom-cut not eliminated). Selection-refinement alone (skip atoms) is
  INSUFFICIENT — the B-cut must still be reduced. An M2 orbit-invariant (axiom-free spine) is fragile (a B→B
  axiom is a normal sub-derivation, hard to exclude globally). PROBE whether `ZRegular w` constrains it, but
  expect the axiom-cut reduction to be the real fix.
- **⚠️⚠️ FURTHER REFINEMENT (lap-120, deeper scouting of `iperm`) — a CONCRETE provable sub-target emerges.**
  At the ⊥-orbit conclusion `s` (`seqAnt s = ∅`, `seqSucc s = ^⊥`), `iperm (tp dᵢ) s` (def InternalZ:976:
  `tp = isymR(seqSucc s) ∨ (isymLk k A ∧ A∈ant s) ∨ tp = isymRep`) holds **iff `tp dᵢ = isymRep`**: the
  `isymR(⊥)` disjunct needs a premise with succedent `⊥` (I-rules have succedent `∀p`/`¬A`, never `⊥`), and
  the `isymLk` disjunct needs the L-formula `∈ ant s = ∅` (impossible). So at a ⊥-orbit K-node the PERMISSIBLE
  premises are exactly the `isymRep` ones (atoms / Ind / K / `zAx1`); I-rules and L-axioms are NON-permissible.
  `permIdx` = first `isymRep` premise. **The decisive sub-question:** can that first-`isymRep` premise be an
  ATOM? If the atom is at **index 0**, the `isChainInf` threading (`∀ B, inAnt B (chainAnt 0) → inAnt B ∅ ∨
  ∃ i'<0, …`) forces its antecedent EMPTY (no earlier cut formulas) ⟹ atom-validity `inAnt (seqSucc sᵢ) ∅`
  FAILS ⟹ **vacuity fires after all.** So the stall requires the atom to be first-`isymRep` at **index > 0**,
  with every earlier premise NON-permissible (I-rules `isymR(C≠⊥)` / L-axioms `isymLk`), and the atom's
  antecedent `= {chainAsucc i'}` for some `i' < permIdx`. **CONCRETE NEXT-LAP TARGET:** prove the first-`isymRep`
  premise of a valid ⊥-orbit chain is forced to index 0 (or otherwise forces the vacuity-firing empty
  antecedent) — via the chain structure / `ZRegular` / the exit `j0` (`chainAsucc j0 = ^⊥`). If provable →
  (A) closes by vacuity, **no engine surgery**. If a genuine index-`>0` atom-stall chain is constructible →
  the axiom-cut elimination is forced. The question is now sharp and in-kernel decidable — attack
  `red_zK_fixpoint_of_atom_selected`'s reachability, not the abstract claim.
- **(B) no cut-free `∅→⊥`:** standard; only needed if (A) routes through "cut-free" rather than direct
  sequent-shape absurdity.
- **(C) descent-internalization:** `gentzenDescentφ` as the real Σ₁ graph of `n ↦ iord(red^[n] z)`. Probably
  routine Σ₁-recursion in IΣ₁ (one fixed function `red`, internally iterable via sequence coding). Lower risk.
- Then assemble `false_of_ZDerivesEmpty` = (A) [the orbit can't fixpoint] composed with descent+PRWO [RIGHT].

**Why (A) over the swap:** hardest-first = attack the piece whose FEASIBILITY is in doubt. The swap wires
banked lemmas (feasible). (A) is a flagged defect with no built resolution (feasibility unknown), it is on
the M3 critical path, it is additive/independent of the swap, and it is DECISIVE: prove it → de-risk the
whole endgame; refute it → forces a selection-architecture fix BEFORE more swap investment.

### ⚠️⚠️⚠️ lap-120 (cont) FINDING — `zKValidF_iIndReduct_of_zInd` is FALSE as stated (Ind-case instance defect, KERNEL-GROUNDED)
Broadened off the stall thread (per `how-to-get-unblocked.md`) to the most self-contained of the 8 sorries —
the Ind-case validity `zKValidF_iIndReduct_of_zInd` (`Crux2Blueprint:79`). It is **false as stated**, for the
SAME structural reason as lap-114's critical-reduct bug (ordinal-invariant reduct that loses the instance):
- **Reduct structure (VERIFIED in-kernel, `scratchpad/indtest2.lean`):** `iIndReductSeq d0 d1 1 = ⟨d1, d0⟩`
  (`znth 0 = d1`, `znth 1 = d0`, `lh = 2`).
- **`zIndWff` succedents (definitional, InternalZ:`zIndWff`):** `seqSucc(fstIdx d1) = F(a+1)` where
  `a = qqFvar(zIndEig)` (a FREE eigenvariable); `seqSucc(fstIdx d0) = F(0)`; `seqSucc s = F(t)` where
  `t = zIndTerm` is a CLOSED term (`IsSemiterm ℒₒᵣ 0`). (`F(·) = substs1 · (zIndP)`.)
- **`isChainInf` exit fails:** the exit needs `chainAsucc j0 ∈ {seqSucc s = F(t), ^⊥}` for `j0 ∈ {0,1}`.
  `chainAsucc 0 = F(a+1)`: can't equal `F(t)` (closed `t` ≠ open `a+1`, different free vars) nor `⊥`.
  `chainAsucc 1 = F(0)`: equals `F(t)` only if `t = numeral 0`. So for any valid `zInd` concluding `F(t)`
  with `t ≠ 0` (e.g. `F(5)` — these exist), `isChainInf s (irk p) ⟨d1,d0⟩` is UNSATISFIABLE ⟹ the theorem
  is false.
- **ROOT CAUSE (= lap-114 pattern):** `iord` is instance-invariant, so the ordinal-DESCENT side
  (`iord_descent_red_zInd`, banked green) never caught this; the VALIDITY side (`zKValidF`) does. The
  verbatim-repeat `iIndReductSeq` (the SAME `d1` each copy, never re-instantiated at 0,1,…,t−1) cannot derive
  `F(t)`. Buchholz's Ind-elimination instantiates the step derivation along `0..t` — but `t` may be NON-
  STANDARD, so the faithful internal reduct is a single substitution-based chain whose validity needs an
  internal (Σ₁-in-V) induction, NOT a verbatim k-fold repeat.
- **FIX (next lap):** re-define the Ind reduct to be instance-correct (the eigenvar-substituted step chain to
  `t`), mirroring lap-114's re-principalization of the critical reduct (`zsubst d0 a (numeral k)`). Likely
  reuses `zsubst`/`ZDerivation_zsubst`. THEN `zKValidF_iIndReduct_of_zInd` (restated on the corrected reduct)
  becomes provable.
- **⚠️ SYSTEMIC HYPOTHESIS:** the "ordinal-invariant but validity-broken reduct" defect now appears in BOTH
  the critical reduct (lap-114, fixed) and the Ind reduct (this finding). **Audit the splice/replace reducts
  (`ZDerivation_red_zK_splice`, axNeg replace validity) for the same latent instance defect BEFORE trusting
  their `zKValidF`/`ZDerivation` obligations** — they may also be mis-stated, not merely hard.
  - **Sharpening:** the lap-114→119 instance-correction campaign (`critReductCorr`/`iRcritG`/`iRcritGNeg` via
    `zsubst d0 a (numeral k)`) corrected the **critical K-cut** reduct only. The **Ind** reduct (`iIndReductSeq`,
    `iRInd`) was NOT touched by that campaign — it kept the original verbatim-repeat shape — which is exactly
    why it retained the instance defect. So the concrete next-lap fix is: **extend the lap-114 re-principalization
    treatment to the Ind rule** (an eigenvar-substituted step chain reaching the conclusion instance `t`). The
    splice reduct CONSUMES the already-corrected critical halves, so it likely inherits the fix (lower risk); the
    axNeg replace ties to the lap-117/118 corrected ¬-inversion. Verify both, but expect the Ind reduct to be
    the genuine second mis-statement.

---

## lap 119 — the engine swap is NOT "pure wiring"; its O1 (regularity) front LANDED
**Build 🟢 green 1326; headline footprint intact (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms).
1 commit. No sorries added.** See `HANDOFF-2026-06-26-lap119.md`.

**Attempted the lap-118 engine swap as prescribed** (`iRK` else-branch → `iRKcCrit`, `iRKDef`/`iRK_defined`
swap, `red_zK_crit ↦ iRKcCrit`). InternalZ compiles green standalone (`scratchpad/lap119-engine-swap.diff`),
but changing `red`'s critical value breaks FAR more than the baton's "2 consumers": the entire **O1 /
`ZRegular` front** (`ZRegular_red_zK_crit`/`_splice_of_chain`, Zsubst) was ABSENT from the lap-118 all-banked
table, and `ZRegular_red` is load-bearing (feeds `ZDerivesEmptyR` → M3). Plus the ~200-line RedZKDescent
descent re-key. Reverted to keep `src/` green; landed the missing O1 front additively.

**THE ADVANCE — regularity of the corrected reduct (all `Zsubst.lean`, all axiom-clean):**
- `zReg_zsubst` ALREADY EXISTED (substitution preserves regularity — the hard piece was done).
- `ZRegular_zsubst_zIallPrem` (I∀ child regular via `zReg_zsubst` + `zReg_zIall`),
  `ZRegular_zInegPrem` (I¬ child via `zReg_zIneg` heredity),
  `ZRegular_iRKcCrit` (whole corrected reduct regular; composes the slot facts; takes `htagI : zTag dᵢ∈{1,2}`).

**Front 1 (O1) now FULLY CLOSED additively (2nd commit):** `ZRegular_iRKcCrit_of_zK` (Zsubst) proves
`ZRegular (iRKcCrit (zK s r ds))` from `hZ`/`hreg`/`hvalid` alone — so once the swap lands,
`ZRegular_red_zK_crit` is `rw [red_zK_crit hcrit]; exact ZRegular_iRKcCrit_of_zK …`. Supplied by new
InternalZ orbit lemmas `isRedexPair_redexCode_of_zKValid` (full redex-pair certificate) +
`zTag_redexI_of_zKValid` (R-redex is an I-rule). All axiom-clean.

**Front 2 (descent) also brought to forms-parity (4th commit):** `iord_descent_iRKcCrit_corr` (∀) /
`_neg` (¬) (RedZKDescent) state the descent on `iRKcCrit (zK s r ds)` directly — via `iRKcCrit_eq_corr`/
`_eq_neg` → the banked `iord_descent_iRcritG_critReductCorr`/`_iRcritGNeg_critReductNeg`. Both axiom-clean.

**ALL THREE fronts now reduce to ONE shared residual — the `redZKReady` orbit bundle.** Regularity
(`ZRegular_iRKcCrit_of_zK`, front 1 ✅ fully self-contained from `hvalid`), descent
(`iord_descent_iRKcCrit_corr`/`_neg`) and soundness (`ZDerivation_iRcritG_critReductCorr`/
`_iRcritGNeg_critReductNeg`) ALL now need only the explicit redex forms: ∀ = `hdi : znth ds redexI =
zIall sᵢ a p d0`, `hdj : … = zAxAll sⱼ pj k'`, `hirk : irk(^∀pj) = irk(cutFormula)+1`; ¬ = `hdi : … =
zIneg sᵢ p d0`, `hdj : … = zAxNeg sⱼ p`, `hcut`, `hp`. (Descent only — regularity needs just `htagI`,
already discharged.)

**⭐ THE orbit bundle `redZKReady_of_zKValid` is EXTRACTED (9th commit) — the central multi-lap residual,
CLOSED.** From `hZ`/`hvalid` it produces `redexI < redexJ < lh ds` + the polarity-dispatched explicit redex
forms: ∀-pair (`zIall sᵢ a p d0` / `zAxAll sⱼ pj k'` + `irk(∀pj) = irk(cutFormula)+1`) ∨ ¬-pair (`zIneg sᵢ
p d0` / `zAxNeg sⱼ p` + `cutFormula = p` + `IsUFormula p`). Built from the banked blocks
(`isRedexPair_redexCode_of_zKValid` → `redexPair_tp` → `zDerivation_isymR_form`/`_isymLk_form`, cross-ruled
on the shared `A`); the `hirk` rank relation via `cutFormula_all`+`irk_substs1`+`irk_all`, the ¬ `pp=p` via
`neg_inj_iff`. Axiom-clean. **This is EXACTLY the `hdi`/`hdj`/`hirk`|`hcut`/`hp` that all three banked fronts
(`ZRegular_iRKcCrit_of_zK`, `iord_descent_iRKcCrit_corr`/`_neg`, `ZDerivation_iRcritG_critReductCorr`/
`_iRcritGNeg_critReductNeg`) consume.**

**NEXT — the atomic engine swap, now genuinely PURE WIRING (all suppliers banked).** Replay
`scratchpad/lap119-engine-swap.diff` (InternalZ: relocate `iRKcCrit`/`iRK`/`iRKcCritDef` before `iRNextG`;
`red_zK_crit ↦ iRKcCrit`; `not_zKCritical_red_zK ↦ _iRKcCrit`). Then re-prove the 3 consumers (build is RED
until all land — atomic):
- `ZRegular_red_zK_crit` (Zsubst): `rw [red_zK_crit hcrit]; exact ZRegular_iRKcCrit_of_zK hds hZ hreg hvalid`
  (the caller `ZRegular_red_zK` hcrit-branch already builds `hvalid`). `ZRegular_red_zK_splice_of_chain`
  reroutes its `iRcritG` premise reads via `iRKcCrit_eq_corr`/`_eq_neg`.
- `iord_descent_red_zK_crit` (RedZKDescent): `rw [red_zK_crit hcrit]`, then `rcases redZKReady_of_zKValid
  hZ hvalid` and dispatch to `iord_descent_iRKcCrit_corr`/`_neg`. (`iCrit_halves_descend` likewise re-keys.)
- `ZDerivation_red_zK_crit` (Crux2Blueprint sorry): restate to `ZDerivation (iRKcCrit (zK s r ds))`, `rcases
  redZKReady_of_zKValid hZ hvalid`, case on ∀/¬ → `iRKcCrit_eq_corr`/`_eq_neg` + the soundness capstones
  (need `hvalid` at the `redSoundGen` zK call site — from `zKValid_iff_zKValidF_and_zKCritical` + criticality).
Full plan in HANDOFF lap-119.

## lap 118 — ¬-case inversion's `hpmem` residual DISCHARGED; capstone now unconditional
**Build 🟢 green 1326; headline footprint intact (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms).
1 commit (4aa7a44). No sorries added.** See `HANDOFF-2026-06-26-lap118.md`.

**Discharged the lap-117 ¬-side residual** `hpmem : inAnt A (seqAnt sⱼ)` (Buchholz 2.2's `A,¬A∈Γ`) by
**strengthening the `zAxNeg` (tag-6) ZPhi disjunct** with a 4th conjunct `inAnt p (seqAnt s)` — faithful to
Buchholz §5 case 2.2 (`Ax^{¬A,0}` genuinely carries both `A,¬A∈Γ`; `buchholz-gentzen.txt:903`). Full ZPhi
ripple done (`ZPhi`/`zphi_monotone`/`_strong_finite`/`zphi_iff`/`zblueprint` σ+π/`zPhi_definable` + rcases/
construction sites in `Crux2Blueprint`/`Zsubst`/`InternalZ`). `zDerivation_zAxNeg_inv` now returns both
memberships; `ZDerivation_corrected_haux0_neg` recovers `hpmem` in-proof; **`ZDerivation_iRcritGNeg_corrected_neg`
drops the `hpmem` hypothesis** (axiom-clean `[propext, choice, Quot.sound]`). The ¬-side twin of lap-115's
`zAx1` 8th-disjunct discharge.

**ALSO banked this lap (3 more commits, all axiom-clean):** (a) **`iord_iRcritGNeg_eq_iRcrit`** descent twin
(`InternalZ`) — the ¬-branch re-point, via `inadd_comm`/`max_comm` on the swapped `seqUpdate` halves; (b)
**`critReductNeg`** (`InternalZ`, red-free) — the concrete ¬-case `ρ` (redexJ ↦ `zAx1 (seqSetSucc sⱼ A) A`,
redexI ↦ `zInegPrem dᵢ` = `d0`, a 𝚺₁ accessor not `red` — arithmetization-ready);
(c) **`ZDerivation_iRcritGNeg_critReductNeg`** (`Crux2Blueprint`) — concrete-`ρ` ¬-soundness, the
`critReductCorr` twin. **Both polarity reduct suppliers now soundness-certified against their concrete engine
`ρ`, and both descent re-points banked.**

**ALSO banked this lap (the dispatched reduct DEFINED + ARITHMETIZED — the hardest re-key piece):**
**`iRKcCrit d`** (`InternalZ`) — the fully-explicit polarity-dispatched critical reduct (`zTag dᵢ=1` → ∀
re-principalized `zsubst`+`Ax^1`-antgrow; else ¬ swapped-slot `Ax^1`-succset+`zInegPrem`), standalone
(table-free, red-free). Bridges `iRKcCrit_eq_corr`/`_eq_neg` → the soundness-certified
`iRcritG (critReductCorr)`/`iRcritGNeg (critReductNeg)`. **`iRKcCritDef` + `iRKcCrit_defined`** — the 𝚺₁
graph (closed first try, `by_cases` on `ti`, reusing `cutFormulaDef`'s `k=π₁(π₂(tp dⱼ))`+`numeralGraph`).
THE arithmetization wall is DOWN.

**ALSO banked this lap — the ¬-case DESCENT** `iord_descent_iRcritGNeg_critReductNeg` (`RedZKDescent`, the
twin of `iord_descent_iRcritG_critReductCorr`) + the sequent-general L-bundle `iRedDescent_zAx1_zAxNeg_gen`.
**ALL corrected-reduct lemmas are now BANKED for BOTH polarities** (arithmetization `iRKcCrit_defined`;
bridges `iRKcCrit_eq_corr`/`_eq_neg`; soundness `ZDerivation_iRcritG_critReductCorr`/`_iRcritGNeg_critReductNeg`;
iord re-points `iord_iRcritG_eq_iRcrit`/`_iRcritGNeg_eq_iRcrit`; descents
`iord_descent_iRcritG_critReductCorr`/`_iRcritGNeg_critReductNeg`). The engine swap is now PURE WIRING.

**NEXT (hardest-first):** the engine SWAP (atomic, one unit, breaks build mid-way — don't commit until green):
(3) re-key `iRK`'s critical branch `else iRKc d s` → `else iRKcCrit d` + `iRKDef`/`iRK_defined`; (4)
`red_zK_crit` SIMPLIFIES to `red (zK s r ds) = iRKcCrit (zK s r ds)`; (5) close `ZDerivation_red_zK_crit`
(restate target to `ZDerivation (iRKcCrit …)`) via `iRKcCrit_eq_corr`/`_eq_neg` + the two soundness lemmas —
the real residual is the `redZKReady` orbit bundle (`hdi`/`hdj`/`hIJ`/`hthread`/`hrank`/… derived at the call
site via `tp`-inversion `redexPair_tp`+`tp_isymR_form_wff`, itself an open sorry); (6) re-prove
`iord_descent_red_zK_crit` via the banked descent twins. Full 6-step list + the all-banked table in
HANDOFF lap-118.

## lap 117 — ¬-case critical-cut inversion SOUNDNESS proven; BOTH critical sub-cases complete
**Build 🟢 green 1326; headline footprint intact (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms).
1 commit (9507db8). No sorries added; the ¬-case lemmas are axiom-clean `[propext, choice, Quot.sound]`.**
See `HANDOFF-2026-06-26-lap117.md`.

**Closed the lap-116 CAVEAT (the I¬ R-redex sub-case).** Buchholz Def 3.2 case 5.1's ¬-subcase SWAPS the two
halves' redex assignment (`d{0}↦`L-redex `j`, `d{1}↦`R-redex `i`; the OPPOSITE of ∀), so `iRcritG` can't
express it ⟹ built a new swapped-half constructor **`iRcritGNeg`** (`InternalZ`) + `ZDerivation_iRcritGNeg_of`.
Proven sound: succedent half `ZDerivation_corrected_haux0_neg` (redexJ=axNeg ↦ §5 `Ax^1_{Γⱼ→A}`, Buchholz
Lemma 5.1 case 2.2) + antecedent half `ZDerivation_corrected_haux1_neg` (redexI=I¬ ↦ child `d0`,
`isChainInf_reduceR_membership` re-points the tip to the `⊥`-endform ⟹ arbitrary conclusion succedent OK) +
capstone `ZDerivation_iRcritGNeg_corrected_neg`.

**THE one residual** (the ¬-side twin of lap-116's `zAx1`-as-ZDerivation gate): `haux0_neg` needs
`hpmem : inAnt A (seqAnt sⱼ)` (Buchholz 2.2's `A,¬A∈Γ`), but the repo's `zAxNeg` ZPhi disjunct pins only
`¬A∈Γ`. **DISCHARGE = strengthen the `zAxNeg` (tag-6) ZPhi disjunct to also require `inAnt A (seqAnt s)`** —
a `ZPhi` ripple (`zphi_monotone`/`_strong_finite`/`zphi_iff`/`zblueprint` σ+π/`zPhi_definable` + ~64
`rcases zDerivation_iff.mp` axNeg arms, each +1 conjunct), mechanically mirroring the lap-116 `zAx1`
8th-disjunct work — OR derive `A∈Γⱼ` from the redex-pair chain context.

**NEXT (hardest-first):** the engine re-key, now de-risked on BOTH polarities — re-key `iRKc` to DISPATCH
(`zTag dᵢ = 1` → `iRcritG`+`critReductCorr`; I¬ → `iRcritGNeg`+ρ_neg) and emit the polarity-correct
constructor. Then `ZDerivation_red_zK_crit` closes via `red_zK_crit` + the two soundness capstones; descent
re-points (need an `iord_iRcritGNeg_eq_iRcrit` twin — short, `#` is commutative). See HANDOFF lap-117 steps.
Suggested sequencing: (a) strengthen `zAxNeg` disjunct (additive, removes `hpmem`), THEN (b) the re-key.

## lap 115 — the inversion's L-half PROVEN; gate = make `zAx1` a sound ZDerivation
**Build 🟢 green 1326; headline footprint intact (`[propext, sorryAx, choice, Quot.sound]`, 0 math
axioms). 1 commit (L-half + finding). No sorries added.** See `HANDOFF-2026-06-25-lap115.md`.

**BOTH inversion halves now proven** (axiom-clean): R-half `ZDerivation_corrected_haux0` (lap 114) +
**L-half `ZDerivation_corrected_haux1`** (this lap). Grounded the L-side in verbatim **Buchholz §5 case 2.1**
(scratchpad `buchholz-gentzen.txt:903` — the missing source): the L-redex `axAll` axiom `Ax^{∀p,k}` (succedent
`F(k)`) reduces to the §5 **logical axiom** `dⱼ[0] = Ax^1_{F(k),Γⱼ→F(k)}` (antecedent gains `F(k)=cutFormula
d`). Engine reduct `v = zAx1 (seqAddAnt (cutFormula d) sⱼ) C`; `haux1` via `ZDerivation_iCritReplaceReduce_general`
(tag-7 ⟹ tag conjuncts vacuous), modulo two named §5 residuals — (O-L1) `hZredL` = `zAx1 …` is a ZDerivation;
(O-L2) `hci` = threading `isChainInf`.

**CRUX FINDING (extends lap-114 to L-side):** the engine reduct `zAxReduct (zAxAll sⱼ p k') = zAx1 sⱼ p` is
unfaithful in THREE ways — payload `p` vs `F(k)`, sequent `sⱼ` vs `seqAddAnt F(k) sⱼ`, and **`zAx1` (tag 7)
is not a `ZPhi` disjunct ⟹ not a ZDerivation at all**. All descent-invariant (why it hid through 108–113).

**NEXT-LAP TARGET (hardest-first — the gate for the whole inversion):** make `zAx1 s C` a sound ZDerivation
leaf — 8th `ZPhi` disjunct `(∃ s C, d = zAx1 s C ∧ inAnt (seqSucc s) (seqAnt s))`, mirroring `zAtom`. Ripple:
`ZPhi`/`zphi_monotone`/`_strong_finite`/`zphi_iff`/`zblueprint` σ+π (mirror `zAxNeg`, `zAx1Graph` exists)/
`zPhi_definable`; ~64 `rcases zDerivation_iff.mp` sites (mostly trailing tag-mismatch arms); +
`zDerivation_zAx1_intro`/`_inv`. Then (O-L1) closes; (O-L2) = lap-113 threading; THEN re-key `red`'s tag-4
critical branch to emit the corrected reducts (R: `numeral k`, L: `zAx1 (seqAddAnt F(k) sⱼ) (F(k))`) and
assemble `ZDerivation_red_zK_crit = ZDerivation_iRcritG_of haux0 haux1`. Full step list in the handoff.

## lap 114 — FRESH-MIND REVIEW: the inversion PRIZE is feasible (re-principalization), not a multi-year wall
**Build 🟢 green 1326; headline footprint intact + re-verified in-kernel (`[propext, sorryAx, choice,
Quot.sound]`, 0 math axioms). 1 commit (building block + finding).** See
`ANALYSIS-2026-06-25-lap114-inversion-instance-mismatch.md`.

**DIRECTION CHANGE (kernel-grounded).** The crux-2 prize `ZDerivation_red_zK_crit` (`Crux2Blueprint:100`)
— the critical-cut SOUNDNESS inversion, framed since lap 110 as "the multi-year cut-elim core, blueprint
`Zinfty.allInv`" — is **FALSE as stated** for a precise, FIXABLE reason. It delegates (via
`ZDerivation_iRcritG_of`, `InternalZ:8336`) to two stripped halves `haux0`/`haux1`; the outer chain's
validity is automatic (`zKValidF_iCritReductGen`). `haux0` concludes `Γ → cutFormula d = Γ → F(k)`, `k`
the L-redex (axAll) instance; its `isChainInf` threading FORCES the redexI premise to derive `F(k)`. But
`red`'s reduct there is `zsubst d0 a (numeral 0)` (instance **0**, `red_zIall`), deriving `F(0) ≠ F(k)`.
**So `red`'s critical reduct is unsound** — it loses the cut instance. (Instance-0 is correct for the
ordinal DESCENT — `iord` is instance-invariant, so `iord_descent_red` survives — which is why this hid in
plain sight through laps 108–113.) This is lap-104's `red_redAllEx_eq` re-principalization finding, now
pinned to the live engine.

**THE FIX (contained, building blocks BANKED):** the critical reduct's R-redex (I∀) premise must be
`zsubst d0 a (numeral k)` (k = `π₁(π₂(tp (redexJ d)))`, the same `k` `cutFormula` reads). Then:
- succedent `= cutFormula d` by **`seqSucc_zsubst_zIall_premise`** (`Zsubst.lean`, BANKED this lap,
  axiom-clean — the linchpin), modulo eigenvariable freshness `hpfresh : fvSubst a (numeral k) p = p` (O3).
- derivability by `ZDerivation_zsubst_zIall_premise` (`Zsubst.lean:1879`, banked), modulo `maxEigen d0 < a` (O1).
- I¬ redex needs no change (`red_zIneg = d0`, no instance).

So the inversion is a `red`-redefinition (re-key the tag-4 critical branch of `iRNextG`/`iRNext` to
substitute the L-redex `k`), NOT new deep machinery.

**NEXT-LAP TARGET (hardest-first, the headline-critical path):**
1. Implement the corrected critical reduct: re-key `iRNextG`/`iRNext` tag-4 so `ρ (redexI)` substitutes
   `numeral k` (k from `tp (redexJ d)`) for the I∀ R-redex, leaving I¬/`zAxReduct` as is. Re-check the
   `red_zK_crit` equation + `𝚺₁`-definability (`iRNextDef`). Descent is instance-invariant ⟹ transfers.
2. Prove `haux0`/`haux1` (the threading reconstruction — `isChainInf` for `seqUpdate ds redexI (corrected
   reduct)` at the new conclusion succedent; inherited from the original chain's `isChainInf` restricted
   to `≤ redexI`, analogous to `ZDerivation_iCritReplaceReduce_of`). Succedent identity is banked.
3. Thread the orbit freshness data (O1/O3) through the `redSound` motive (same obligations the replace
   branch already isolates, lap-99/100).
Then `ZDerivation_red_zK_crit` is REAL → unblocks `redSound`. The chain-REPLACE IH / ⊥-orbit invariant
(lap-113 next step) is the OTHER deep piece, but the inversion is higher-value (it is the cut-elim content
and was the avoided piece per lap-111) and now demonstrably contained.

## lap 113 — splice branch CLOSED; chain-rank invariant PROVEN; NEXT = the iord_descent_red recursion
**Build 🟢 green 1326; headline footprint intact (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms).
4 commits.** The splice `hr'` degree-drop is fully proven and `irk_chainAsucc_redexI_le` (the chain-rank
invariant) is a real axiom-clean proof (NO `isChainInf` refactor — pairing joint-monotonicity bounds the
minimal redex below `j₀`). `iord_descent_red` is down to **ONE** internal sorry.

**THE remaining sorry = the chain-REPLACE strong-induction IH** (`Crux2Blueprint:~595`,
`Or.inr (iord_descent_red_zK_chain_replace … ?_)`): needs `iRedDescent (red dᵢ) dᵢ` for a non-critical
chain premise `dᵢ`, i.e. the recursive IH of `iord_descent_red` on `dᵢ`.

**THE FIX = restructure `iord_descent_red` to conclude `iRedDescent` + strong induction.** Concretely:
1. Prove `iRedDescent_red_of_ZDerivation (d) : ZDerivation d → red d = d ∨ iRedDescent (red d) d` by
   `induction d using ISigma1.sigma1_order_induction` (premises `dᵢ < d` via `znth ds i < ds < zK s r ds`).
   `iord_descent_red` then = a 3-line corollary (`iord_descent_of_iRedDescent` on the RIGHT disjunct).
2. **Per-branch `iRedDescent` bundles** (every K-node reduct factors through `iord_descent_le` =
   `idg_le ∧ iotil_lt ∧ nf`, so the bundles ALWAYS exist):
   - atom / axAll / axNeg: `red d = d` ⟹ LEFT (`red_zAtom`/`red_zAxAll`/`red_zAxNeg`). ✓ trivial
   - I∀ / I¬: `iRedDescent_red_zIall` / (`red_zIneg ▸ iRedDescent_zIneg`). ✓ banked
   - **REPLACE**: `iRedDescent_red_zK_replace_eq` — **DONE this lap** (`RedZKDescent`). chain-replace branch
     feeds it the IH (`dᵢ < d`); if IH gives LEFT (`red dᵢ = dᵢ`) the whole node is a fixpoint (LEFT).
   - **SPLICE**: needs `iRedDescent_red_zK_splice_eq` — TODO: same as `iord_descent_red_zK_splice_eq` but
     also prove the reduct's own NF `isNF (iotil (zK s' r' (seqInsert ds i a b)))` via a case analysis on
     `znth_seqInsert_{pre,at,at1,suf}` (a/b are NF by `hNFa`/`hNFb`, ds-premises by `hNF`). ~15 lines; the
     other two fields = `idg_seqInsert_le'` / `iotil_seqInsert_lt`.
   - **Ind**: needs `iRedDescent_red_zInd` — `iord_descent_iRInd_zInd` goes through `iord_descent_iIndReduct`;
     check it factors through `iord_descent_le`/`iord_descent_iCritAux` to expose the bundle.
   - **critical NODE** (`hcrit` false, `red = iRcritG`): needs the bundle from `iord_descent_red_zK_crit`
     (`RedZKDescent:84`) — same factoring check.
3. **Definability:** `sigma1_order_induction` needs the motive `𝚺₁-Predicate` (`red`/`idg`/`iotil` are
   `𝚺₁-Function₁`, `ZDerivation` is `𝚫₁`); try `definability`, fall back to explicit `.comp₂` per the
   `definability-aesop-depth-blowup` note.

### ⚠️ KEY FINDINGS (lap 113, 2nd half) — the naive `iRedDescent` recursion is WRONG; two real obstacles
Banked all K-node `iRedDescent` bundles (`iRedDescent_red_zK_replace_eq`/`_splice_eq`/`_chain_replace`/
`_chain_splice`; Ind is `iRedDescent_zInd`). But TWO kernel-grounded facts show the general theorem
`ZDerivation d → red d = d ∨ iRedDescent (red d) d` is **FALSE as stated**:

- **(A) The critical-NODE reduct breaks `iRedDescent`.** `red (critical zK) = iRcrit = cut`, whose descent
  is `iord_descent_cut` (`InternalZ:2596`): `idg e + 1 ≤ idg d` (degree DROPS) with
  `icmp (iotil e) (ocOadd (iotil d) 1 0) = 0` (i.e. `õ(e) < ω^{õ(d)}` — `õ` may RISE!). So `iRedDescent`'s
  `otil_lt` (`õ(e) < õ(d)`) FAILS for the cut. ⟹ the theorem must EXCLUDE critical K-chains: condition it
  on `¬ (zTag d = 4 ∧ ¬ permIdx d < lh (zKseq d))`. The recursion preserves this: the IH is only applied
  at chain-REPLACE (`Crux2Blueprint:599`), where the premise `dᵢ` is a NON-critical chain (`h2` true);
  critical premises are SPLICED (`iCrit_halves`, no IH), and splice KEEPS `õ` descending
  (`iotil_seqInsert_lt`) — that's the whole point of splicing-not-cutting.

- **(B) axAll/axNeg-SELECTED premise → neither disjunct holds (the lap-111 selection invariant, now in
  general sub-chains).** If a non-critical node's `permIdx`-selected premise `dᵢ` has `tp = isymLk`
  (tag 5/6 axAll/axNeg, which ARE `red`-fixpoints `red dᵢ = dᵢ`), then `red_zK_rep_nonchain` gives
  `red node = zK (tpReduce (isymLk…) s 0) r ds` — premises `ds` UNCHANGED (so `õ(red node) = õ(node)`,
  `idg` equal ⟹ `iRedDescent.otil_lt` FAILS) but the CONCLUSION is reduced (`tpReduce isymLk ≠ id`, unlike
  `tpReduce_isymRep` for atoms ⟹ NOT a fixpoint either). So a general non-critical node with an L-axiom
  selected satisfies NEITHER `red d = d` NOR `iRedDescent`. For the `∅→⊥` TOP node this is killed by Cor 2.1
  (`tp_selected_isymRep_of_emptyAnt_botSucc`: the selected premise of a `∅→⊥` K-node has `tp = isymRep`,
  never `isymLk`). **The open question: does that selection invariant PROPAGATE through the reduction to
  every sub-chain the recursion visits?** If the reduced sub-chains stay `⊥`-succedent orbits, Cor 2.1
  reapplies and axAll/axNeg are never selected; then the recursion closes. This is the genuine remaining
  content — an INVARIANT (`⊥`-orbit / selected-`tp = isymRep`) threaded through `red`, NOT a mechanical
  strong induction. Likely the right statement: prove the recursion for chains whose conclusion succedent
  is `⊥` (or carries the orbit invariant), so both (A)'s criticality and (B)'s L-axiom selection are
  controlled. Re-examine the lap-107/111 `ZInf`/`ZcOK` prototype inversion cases for the invariant shape.

Once `iord_descent_red` is sorry-free, the open frontier = the PRIZE (`ZDerivation_red_zK_crit` inversion)
+ validity sorries (`zKValidF_iIndReduct_of_zInd`, splice/axNeg validity) + M2/M3.


## lap 111 — DEEP REFLECTION + disjunctive `iord_descent_red` (atom branch CLOSED; SELECTION INVARIANT named)
**Build 🟢 green 1326; headline footprint intact + re-verified in-kernel (`[propext, sorryAx, choice,
Quot.sound]`, 0 math axioms). 2 commits (synthesis + grind).** See `REFLECTION-2026-06-25-lap111.md`.

**Landed (grind):** `iord_descent_red` retyped to the disjunctive `red d = d ∨ icmp (iord (red d)) (iord d) =
0` (and `iord_red_iterate_descends` to the matching per-step dichotomy). Working branches → `Or.inr`. **Atom
branch genuinely closed** via `Or.inl (red_zK_fixpoint_of_atom_selected …)` (a TRUE node-fixpoint:
`tp=isymRep`, `tpReduce_isymRep s 0 = s`).

**axAll/axNeg CLOSED via the SELECTION INVARIANT — which already existed.** axAll/axNeg (tags 5/6) are NOT
clean node-fixpoints (`red dᵢ=dᵢ` but `tp=isymLk` strips the conclusion while `iord` is unchanged ⟹ neither
disjunct holds), so they close ONLY by vacuity. The vacuity is Cor 2.1, **already proved**:
`tp_selected_isymRep_of_emptyAnt_botSucc` (`InternalZ:7163`) — the selected premise of a `∅→⊥` K-node has
`tp = isymRep`, but an L-axiom has `tp = isymLk ≠ isymRep`. Both branches discharged by `exfalso` + that
lemma. No new infrastructure needed.

**⚠ HONESTY CORRECTION:** the disjunctive form resolved `iord_descent_red` but RELOCATED the atom-stall to
M3. The atom branch's `Or.inl` is GENUINELY true — the orbit can reach a `red`-FIXPOINT at an atom(Rep)-
selected ∅→⊥ K-node (atom = Rep, Cor 2.1 PERMITS it; only axAll/axNeg are vacuous). So `false_of_ZDerivesEmpty`
must handle a STALLING orbit (a fixpoint K-node is not cut-free ⟹ neither "infinite descent" nor "cut-free
absurd" fires). True fix is engine/embedding-level: (a) refine `permIdx`/`isPermPrem` to skip Rep premises, or
(b) M2 produces chains with no index-0 Rep/atom. The 2nd grind commit msg's "fully resolved" overstated it.

**Residual `sorry`s in `iord_descent_red` (2, was 5 at lap start) — both deep, confirmed this lap:**
1. **chain-REPLACE IH** — the chain-spine strong induction. Hits **lap-101's wall**: chain premises have
   GROWING antecedents (not ∅→⊥) ⟹ Cor 2.1 doesn't reapply ⟹ inner axAll/axNeg/atom can't use empty-ant
   vacuity. Needs the permIdx-skip-Rep refinement (a).
2. **splice `hr'`** — needs the lap-110 cut-formula strip. CONFIRMED no shortcut: `zKValidF` gives only
   `irk (chainAsucc ds i) ≤ r` (non-strict, `InternalZ:1290/1299`); `idg(parent) = max(r, iseqMaxIdg ds − 1)`
   off by one. Strip is LOCALIZED to `iRcritG`'s cut-formula arg (`InternalZ:6427`: `chainAsucc (zKseq d)
   (redexI d)` = principal → a `cutFormula d` = stripped `A(d)`). Ripples to `ZDerivation_iRcritG_of` /
   `ZDerivation_red_zK_crit` (both already sorry) + splice `irk`; descent lemmas IMMUNE (lap-110). Closes via
   `irk_cut_lt_rank_forall`/`_neg` (`InternalZ:411`). **This strip ALSO unblocks the inversion prize (`:96`).**

**Recommended next-lap order:** cut-formula strip (2) — unblocks `hr'` + the inversion prize; then the
permIdx-skip-Rep refinement (1)+(a) — dissolves the chain-spine wall AND the M3 atom-stall at once.

Then the prize: ∀/¬-INVERSION (`ZDerivation_red_zK_crit`, template `Zinfty.allInv`); then M3
`false_of_ZDerivesEmpty` (fixpoint-or-descent endgame: a `red`-fixpoint ⊥-orbit is cut-free ⟹ absurd; else
infinite ε₀-descent ⟹ PRWO) + M2 embedding; then wire → headline (ONLY when `#print axioms` clean).

## lap 110 — splice branch: 6 of 7 sub-sorries CLOSED; `hr'` isolated as the degree-drop residual
**Build 🟢 green 1326; headline footprint intact (`peano_not_proves_goodstein = [propext, sorryAx, choice,
Quot.sound]`, 0 math axioms).** 1 code commit.

### Banked this lap (`RedZKDescent.lean`, axiom-clean `[propext, choice, Quot.sound]`, green-gated)
- **`iCrit_halves_descend`** — for a valid critical `K^r` chain `dᵢ = zK s r ds`, the two critical-reduct
  halves `a,b = znth (zKseq (red dᵢ)) {0,1}` satisfy the per-half `õ`/`idg`/NF bounds below `dᵢ`
  (`ha`/`hb`/`hag`/`hbg`/`hNFa`/`hNFb`). **Key in-kernel fact:** the critical 5.1 reduct's `õ`-jump lives in
  the OUTER `K^{r-1}` rank-drop, NOT the individual halves — each half is a `K`-chain over
  `seqUpdate ds (redexI/J) (red·)` (i.e. `dᵢ`'s OWN premise sequence with the redex R/L premise swapped for
  its strictly-descending genuine reduct), so each premise-fold descends below `dᵢ` via `iotil_iCritAux_lt` /
  `idg_iCritAux_le` (`iotil`/`idg` ignore the half's reset conclusion/rank). Mirrors `iord_descent_red_zK_crit`'s
  redex extraction.
- **Wired into `iord_descent_red`'s splice branch** (`Crux2Blueprint.lean:595`): feeds the 6 bounds to
  `iord_descent_red_zK_chain_splice`, closing 6 of its 7 residual `sorry`s. **Only `hr'` remains.**

### ⚠️ THE `hr'` RESIDUAL — sharp in-kernel characterization (the splice degree-drop crux)
`hr' : max (irk (seqSucc (fstIdx (znth (zKseq (red dᵢ)) 0)))) r ≤ idg (zK s r ds)`. Established this lap:
`seqSucc (fstIdx (half0)) = chainAsucc dsᵢ (redexI dᵢ) = C`, the redex **principal** formula (the R-premise's
succedent). So `hr' = max (irk C) r ≤ idg(parent)`. The `r ≤ idg(parent)` half is `r_le_idg_zK`. The hard
half is `irk C ≤ idg(parent)`:
- `idg(parent) = max(r, iseqMaxIdg ds - 1)` (the `-1` is one cut-elim degree drop, baked into `idg_zK`).
- `irk C ≤ r'ᵢ` (dᵢ's rank) ONLY (`≤`, from the critical-pair finder `inference_critical_pair_rank`'s
  `hrank`), and `r'ᵢ ≤ idg(dᵢ) ≤ iseqMaxIdg ds`. So `irk C ≤ iseqMaxIdg ds` — **off by one** vs the needed
  `≤ iseqMaxIdg ds - 1`. The bound FAILS in the edge case `irk C = r'ᵢ = idg(dᵢ) = iseqMaxIdg ds` (dᵢ the
  strict-max-degree premise, its rank = its degree = the principal rank) unless `r ≥ iseqMaxIdg ds`.
- `red_zK_splice`'s rank `irk C` (principal `C = A_i`) is CORRECT — splicing `dⱼ`'s halves
  `d{0} ⊢ Θ→C`, `d{1} ⊢ C,Θ→D` flat into the parent makes the parent cut on `C`, so the parent rank must
  be `≥ irk C`. Not a stripping bug.
- **EDGE CASE where `hr'` genuinely FAILS** (in-kernel worked out): `irk C = r'ⱼ = idg(dⱼ) = iseqMaxIdg ds`
  with `dⱼ` the strict-max-degree premise and `r < iseqMaxIdg ds`. Then the splice rank `irk C = iseqMaxIdg ds`
  EXCEEDS `idg(parent) = max(r, iseqMaxIdg ds - 1)` — `iord` goes UP, descent fails. This is the cut-elim
  degree-drop pressure point: reducing the degree-DETERMINING critical premise `dⱼ` ought to drop the parent
  degree, but the spliced rank `irk C` doesn't fall below it. **Two genuine resolution paths (NEXT, hardest-first):**
  1. **Chain-rank invariant ruling out the edge case.** Show a valid chain has `irk(chainAsucc ds i) < idg`
     STRICT (or `r'ⱼ < iseqMaxIdg ds` when `dⱼ` is a chain premise) — i.e. the parent's degree strictly
     dominates any premise's cut-formula rank. Likely from a hereditary `idg`-vs-rank invariant carried by
     `zKValidF`/the embedding. If true, `irk C ≤ iseqMaxIdg ds - 1 ≤ idg(parent)` and `hr'` closes via
     `le_iseqMaxIdgAux` + `idg_zK`.
  2. **Measure refinement.** Adjust `iord`/the splice so the degree-determining premise's reduction is
     reflected (the splice rank should track the halves' reduced degrees, not `dⱼ`'s full pre-reduction rank).
  This shares the cut-rank/degree-drop bookkeeping with `redZKReady`'s motive (`Crux2Blueprint:340/493`).

### ⭐ ROOT CAUSE (lap-110, see `ANALYSIS-2026-06-25-lap110-iCritReductG-cut-formula-strip.md`)
`hr'` AND the critical-case soundness `ZDerivation_red_zK_crit` (`Crux2Blueprint:100`, `hCrk : irk C ≤
zKrank d - 1`) have a SHARED root cause: `iCritReductG`/`iRcritG` cut on the redex **PRINCIPAL** `C =
chainAsucc(redexI)` (`= Aᵢ`), but Buchholz Thm 3.4(a) (`buchholz-gentzen.txt:690/705/808`) cuts on the
**STRIPPED** subformula `A(d)` with `rk(A(d)) < r` STRICT (`= rk(Aᵢ) - 1`). `irk_cut_lt_rank_forall`/`_neg`
(`InternalZ:409/415`) supply the strict drop for the stripped formula. **Fix = redefine `iCritReductG`'s cut
formula to the stripped `A(d)`** (def `cutFormula d` by cases on `Aᵢ = ∀xF`/`¬A` from the redex, via
`substs1 k`/negand). The ordinal-DESCENT lemmas (`iord_descent_red_zK_crit`, `iCrit_halves_descend`) are
IMMUNE — `iotil`/`idg` read only the premise sequence, never `C` — so only `ZRegular`/`ZDerivation` (end-sequent
readers) and the splice rank `irk C` change. **`hr'` closes with ONLY the stripped rank bound (no inversion);
full `ZDerivation_red_zK_crit` additionally needs the ∀/¬-inversion `d{0}⊢Θ→A(d)`/`d{1}⊢A(d),Θ→D` (the deep
cut-elim, blueprint `wip/PathCInf.lean` `Zinfty.allInv`).** NEXT LAP: strip `iCritReductG`'s cut formula →
close `hr'`.

### Full open-sorry inventory (lap-110, headline-path; 3 paths each)
- **`hr'` splice rank** (`Crux2:608`): (1) strip `iCritReductG` cut formula [most promising, above]; (2)
  strict chain-rank-vs-degree invariant from `zKValidF`; (3) measure refinement.
- **chain-REPLACE IH** (`Crux2:594`): (1) `permIdx`/`isPermPrem` engine refinement skipping atom premises
  [lap-109 path 1]; (2) atom-free embedding invariant; (3) secondary lex descent measure.
- **atom/axAll/axNeg fixpoints** (`Crux2:568/610/612`): same atom-fixpoint wall as chain-REPLACE; (1) engine
  refinement; (2) prove ⊥-orbit never selects a normal-form leaf; (3) route atom-selected node to critical.
- **`ZDerivation_red_zK_crit`** (`Crux2:100`): (1) strip cut formula + ∀/¬-inversion [shared root cause];
  (2) port `Zinfty.allInv`/`andInv`/`orInv` from `wip/PathCInf.lean`; (3) abstract the inversions as a
  bundled hypothesis fed by the embedding.
- **`redZKReady` motive** (`Crux2:493`): (1) strengthen the `zDerivation_induction` motive to carry the
  7-field bundle hereditarily; (2) per-node orbit-invariant lemmas; (3) the localized `axNeg` residual
  (`Crux2:404`) needs Buchholz's genuine ¬-axiom cut.
- **`zKValidF_iIndReduct_of_zInd`** (`Crux2:81`): likely FALSE-as-stated (shadow reduct `[d1,d0]` doesn't
  thread to conclusion `F(t)`); (1) confirm vacuity/refute; (2) restate over the genuine eigensubst reduct;
  (3) drop if vestigial.
- **`false_of_ZDerivesEmpty`** (`Crux2:673`) / **`foundation_bot_to_Z_empty`** (`Crux2:661`): the terminal
  PRWO-internalization + Foundation⊥→Z embedding (need `prwoInstance`/Foundation coded-provability API).
- **`goodstein_implies_consistency`** (`Reduction:68`): both Rathjen girders (γ→PRWO + PRWO→Con).

## lap 109 — K-case branch-descent TRIO banked; the recursion wall CHARACTERIZED in-kernel
**Build 🟢 green 1326; headline footprint intact (`peano_not_proves_goodstein = [propext, sorryAx, choice,
Quot.sound]`).** 4 commits: critical sub-branch wired in place (`9e86a26`), replace descent (`8138b91`),
splice descent (`7371573`), baton (`3dc2cb4`).

### Banked this lap (all `RedZKDescent.lean`, axiom-clean, green-gated)
- **`iord_descent_red`'s K-case CRITICAL sub-branch — PROVEN IN PLACE.** Dispatches on the `permIdx`
  sentinel; critical branch fires `iord_descent_red_zK_crit` with `zKValid` = `zKValidF` (from `ZDerivation`)
  + `zKCritical_of_not_permIdx_lt`. **Resolved lap-108's "wire zKValid into ZPhi" worry — criticality is FREE
  from the branch dispatch.**
- **`iord_descent_red_zK_replace_eq`** (5.2.2) — reduces to premise IH `iRedDescent (red dᵢ) dᵢ` via
  `iotil_zK_lt_replace` + `idg_zK_le_replace` + `iord_descent_le`.
- **`iord_descent_red_zK_splice_eq`** (5.2.1) — reduces to the two halves' bounds + rank bound `r'≤dg(parent)`
  via the banked rank-general `iord_descent_seqInsert'`.

### K-branch dispatch — three reducible sub-cases CLOSED in place (lap-109 late)
`iord_descent_red`'s non-critical K-branch now dispatches on the selected premise's tag. CLOSED (banked,
non-recursive `iRedDescent` bundles → `iord_descent_red_zK_replace_eq`): **I¬** (`iRedDescent_zIneg`),
**Ind** (`iRedDescent_zInd`), **I∀** (`iRedDescent_red_zIall`, NEW — eigensubst-invariant, no regularity).
**REMAINING sub-sorries (4):** `atom`/`axAll`/`axNeg` (the FIXPOINT defect — `red dᵢ = dᵢ`, no descent) and
`chain` (the recursive core). The critical branch + I-rule/Ind branches are DONE.

### ⚠️ THE RECURSION WALL — kernel-confirmed obstruction (the gating crux for the `chain` sub-case)
Wiring the two `_eq` lemmas for the `chain` sub-case needs `iord_descent_red` restructured as a strong
induction (mirror `redSoundGen`) to supply the premise IH `iRedDescent (red dᵢ) dᵢ`. **The IH's STRICT `otil_lt` requires the
selected premise `dᵢ = znth ds (permIdx)` to be REDUCIBLE.** Kernel facts established this lap:
- `iperm (isymLk k A) q ↔ inAnt A (seqAnt q)` (`iperm_isymLk_iff`) — axiom leaves CAN be permissible.
- `iperm isymRep q` is ALWAYS true (`iperm_isymRep`) — every Rep premise is permissible ⟹ `permIdx = 0` when
  premise 0 is Rep.
- Cor 2.1 (lap-90, `ANALYSIS-…-lap90`): on the ⊥-orbit (`Γ=∅, C=⊥`) the selected premise is ALWAYS Rep
  (axioms need `A∈Γ=∅`, impossible; I-rules' succedent ≠ ⊥). So NO axiom-leaf selection AT THE TOP.
- **BUT Rep = {atom(0), Ind(3), chain(4)}, and `red(atom) = atom` (atoms are normal forms ⟹ NO strict
  `iord` descent).** If a ⊥-chain's selected (first permissible) premise is an ATOM, the replace reduct
  equals the original ⟹ `iord_descent_red` FIXPOINTS, descent FAILS. The recursion also dives OFF the
  ⊥-orbit (5.2.2 recurses on the Rep chain `dᵢ`, not a ⊥-derivation), where axiom-leaf selection returns.

**Three resolution paths (next lap, hardest-first):**
1. **Prove selected premise on the ⊥-orbit is never a bare ATOM (refine Cor 2.1).** An atom `dᵢ=zAtom sᵢ`
   has `Cᵢ ∈ Γᵢ` (`zDerivation_zAtom_inv`). PARTIAL kernel result worked out this lap: an atom at position
   **0** of a ⊥-chain is IMPOSSIBLE — threading forces `Γ₀ ⊆ seqAnt s = ∅` (no prior premise to thread to),
   but the atom needs `C₀ ∈ Γ₀`. **SUBTLETY (blocks the naive claim):** an atom at i>0 is NOT forbidden by
   threading alone — an earlier I-rule premise i'<i with `chainAsucc ds i' = Cᵢ` supplies the membership, and
   since permissibility = Rep-only (I-rules non-permissible), that atom can still be the FIRST permissible (=
   selected) premise. So path 1 needs MORE than threading: the real fix is that **the `isymRep` tag conflates
   atoms (normal forms) with Ind/chains (reducible)** — `iperm isymRep` always-true wrongly admits atoms as
   "permissible". The genuine engine refinement: make `permIdx`/`isPermPrem` SKIP atom premises (or route an
   atom-selected node to critical), so the selected premise is always Ind/chain (reducible). This is a real
   `red`/`isPermPrem` change — verify it stays faithful to Buchholz (atoms are cut-free, never the reduction
   site). **MOST PROMISING but needs an engine tweak, not just a lemma.**
2. **Secondary descent measure.** Augment `iord` with a lexicographic component (e.g. derivation size / cut
   count) that strictly drops even on an atom-fixpoint replace step, so the orbit measure descends regardless.
3. **Pivot to the Σ₁-Fixpoint ARITHMETIZATION of the ω-rule cut-elim** (lap-108 escalation note) if 1+2 both
   fail — the finitary engine is then genuinely dead. Math doubly-proven (Bryce-Goré Coq + axiom-clean META
   `Zinfty.lean`).

### Other self-contained crux-2 sorries (any can be attacked independently of the wall)
- `zKValidF_iIndReduct_of_zInd` (`Crux2Blueprint:79`) — Ind-reduct chain validity; mirror
  `zKValidF_iCritReductSeq` (`InternalZ:3095`) but for the `iIndReductSeq` shape (need
  `isChainInf_iIndReductSeq` + per-premise wff). Self-contained, ~1 lap.
- `redZKReady` motive (`Crux2Blueprint:340/493`) — the 7-field orbit invariant carried hereditarily; SHARED
  wall with the descent recursion.
- `axNeg` (`ZDerivation_red_zK_nonRep`, `Crux2Blueprint:404`) — ¬-axiom premise reduct is a succedent
  REPLACEMENT (`tpReduce(tp zAxNeg) s 0 = seqSetSucc s p`, `Γ→p`); needs Buchholz's genuine ¬-axiom cut.
- `false_of_ZDerivesEmpty` (`Crux2Blueprint:619`) — internalize `n↦iord(red^[n] z)` as a Σ₁ graph + apply the
  internal PRWO(ε₀) instance (`prwoInstance`, `wip/GentzenCon`). Consumes the proven `iord_red_iterate_descends`.

## lap 108 — `iord_descent_red` NARROWED to the K/cut case + the two-engine map corrected
**Build 🟢 green 1325; `src/` headline footprint intact.** Concrete advance + a correction to the lap-107
diagnosis (which conflated two distinct `red`s):

- **`iord_descent_red` (`Crux2Blueprint.lean`) — Ind branch PROVEN in place.** A `∅→⊥` derivation has top
  tag 3 (Ind) or 4 (K), `zTag_Ind_or_K_of_ZDerivesEmpty`. The Ind branch now closes via the banked
  `iord_descent_red_zInd`; the residual `sorry` is isolated to exactly the **K/cut case** (tag 4). This is
  the headline-WIRED finitary engine (`InternalZ`, tags 0-6), the real crux-2 obligation.

- **K-case CRITICAL branch descent BANKED (`src/GoodsteinPA/RedZKDescent.lean`, NEW, sorry-free, axiom-clean
  `[propext, choice, Quot.sound]`, green-gated 1326).** `iord_descent_red_zK_crit`: for a critical
  (`¬ permIdx < lh ds`) valid `K^r` chain, `icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0`. Ports the
  banked `iord_descent_iR2_zK_of_valid` (`iR2`-ρ) to the genuine `red`-ρ via two new bundle lemmas
  (`iRedDescent_zAxReduct_red_of_tp_isymR/_isymLk`) + `iord_iRcritG_eq_iRcrit` (genuine reduct shares `iord`
  with the ordinal-shadow). The I∀ redex premise's eigensubst (`red = zsubst d0 a 0`) preserves `iotil`/`idg`
  (`iotil_zsubst`/`idg_zsubst`) so the bundle transfers, costing only the regularity `maxEigen d0 < a`
  (`maxEigen_lt_of_regular_zIall`, hence the `hreg` hypothesis). **NOT yet wired into `iord_descent_red`'s
  K-case — two gaps remain:** (a) the **non-critical splice/replace branch descents** (`red_zK_splice`/`_rep`,
  unbanked — the genuine open ordinal core); (b) **`zKValid` availability from the ∅→⊥ orbit** — the bare
  `ZDerivation` `zK` disjunct does NOT carry `zKValid` (`InternalZ.lean:7517`), so even the critical branch
  can't fire from `ZDerivesEmptyR` alone yet (the "wire `zKValid` into `ZPhi`" phase, `InternalZ.lean:7519`).

- **TWO distinct `red`s (lap-107 docs conflated them — corrected here):**
  1. **`src/InternalZ.lean` finitary engine `red` (tags 0-6)** — the HEADLINE-WIRED one
     (`Crux2Blueprint.iord_descent_red`/`redSoundGen`/`false_of_ZDerivesEmpty`/`ZDerivesEmptyR`). Open
     pieces: (a) `iord_descent_red` K/cut case — `red (zK s r ds) = iRK …` dispatches 3 Buchholz branches
     (5.1 critical `iRcritG`, 5.2.1 splice, 5.2.2 replace); only the CRITICAL descent is banked
     (`iord_descent_iR2_zK_of_valid`, for the `iR2`-ρ — needs re-pointing to `red`-ρ); splice/replace descents
     are unbanked. (b) `redSoundGen` K-case needs the `redZKReady` "spine" motive (lap-101 flagged it shaky:
     ∅→⊥ chain premises have growing antecedents ⟹ Cor 2.1 may not reapply down the spine) + the `axNeg`
     sub-residual (`ZDerivation_red_zK_nonRep` tag-6 `sorry`, Buchholz ¬-axiom cut). (c) `foundation_bot_to_Z_empty`
     embedding (`Crux2Blueprint:587`).
  2. **`wip/PathCOmega.lean` prototype `red` (tags 7-10, ω-rule)** — the lap-104 STALL (`red_redAllEx_eq`,
     `sord_red_iterate_stalls_AllEx`) is about THIS one, NOT the finitary engine. It is an external inductive
     (non-load-bearing, lap-107 Finding 2), so it cannot reach the headline regardless.

- **Strategic state (honest).** crux-2 is a genuine multi-month milestone with deep open walls on BOTH the
  finitary engine (K-descent splice/replace + the shaky `redZKReady` spine + axNeg) and the ω-rule prototype
  (non-load-bearing + stall). The mathematically-clean route is the ω-rule (Bryce-Goré + the repo's own
  axiom-clean META `Zinfty.lean`), but it needs Σ₁ ARITHMETIZATION (a Fixpoint predicate over coded
  ω-derivations — the node shapes `zAllOmega s d0 a α` already code the ω-family finitely via `zsubst d0 a t`;
  the deferred work is making the validity predicate a `PR.Blueprint`/`Construction` Fixpoint, not an external
  inductive). **NEXT (hardest-first):** either (A) re-point `iord_descent_iR2_zK_of_valid` to the `red`-ρ and
  bank the splice/replace branch descents to finish `iord_descent_red`'s K case on the finitary engine; or
  (B) start the Σ₁-Fixpoint arithmetization of the ω-rule cut-elimination. (A) is closer to the wired
  headline; (B) is mathematically cleaner. Lean toward (A) first (the finitary engine is what's wired and the
  K-descent is concrete), escalating to (B) if the `redZKReady` spine proves genuinely broken (settle it
  in-kernel like lap-104 settled the prototype stall — don't leave it "shaky" indefinitely).

---

## lap 107 — ⭐⭐⭐ FRESH-MIND REVIEW: the external-inductive prototype track is a DEAD END (kernel-verified); pivot to the Σ₁ engine `red` redesign

**Two in-kernel findings this lap force a direction change (build 🟢 green 1325; `src/` untouched).**

**Finding 1 — `ZInf.allInv` is VACUOUS (verified).** The lap-106 ∀-inversion lemma
(`ZInf Γ → inAnt (^∀φ) Γ → ZInf (seqCons Γ φ(t))`) is provable by a SINGLE weakening
(`ZInf.weaken_top d.seq d`), using neither `ht` nor the membership hypothesis — confirmed by replacing the
whole `induction` and elaborating (`wip/PathCInf.lean`, now renamed `ZInf.allInv_vacuous` with the one-liner
proof + the finding in its docstring). Root cause: the META `Zinfty.allInvAux` content is (1) **ordinal
preservation** (`Provable (o d) c …`) and (2) **erasure** of `^∀φ` (`Γ.erase (∀⁰χ)`); `ZInf : V → Prop`
has **no ordinal index** and the statement **keeps `^∀φ`**, so the conclusion is a mere weakening of `Γ`.
⟹ the lap-106 "principal case proven" + 6 commuting `sorry`s + the planned `permCongr` perf fix were all
work on a content-free lemma. **STOP the `permCongr` fix.**

**Finding 2 — external inductives are NON-LOAD-BEARING for the headline.** `ZInf`/`ZcOK`/`ZcDer` are all
external Lean `inductive … : V → Prop` (PathCOmega.lean:701-702 says so explicitly: "PROTOTYPE the
cut-elimination math … the Σ₁ port … is the deferred final brick"). But the headline needs `IΣ₁ ⊢ Con(PA)`,
i.e. the ε₀-descent must hold in EVERY `V ⊧ IΣ₁`, including non-standard models where the coded ⊥-proof `z`
is **non-standard** — and no external (well-founded) inductive tree exists for a non-standard `z`, so the
embedding `foundation_bot_to_Z_empty` (`Crux2Blueprint.lean:576`) is **unprovable** for such `z`. The
prototypes can guide the inversion combinatorics but can never be wired in. The load-bearing carrier is the
**Σ₁ CODE engine** `red`/`iord` (`InternalZ.lean`), which is already arithmetized and total on all codes
(standard + non-standard) — that's why `iord_red_iterate_descends` builds the ℕ-indexed descent.

**The real obstruction (re-confirmed, lap-104).** Engine `red d = znth (redTable d) d` steps via
`iRNextG d s` (`InternalZ.lean:6915`), which dispatches **only on the conclusion's top `zTag`**
(1→eigensubst, 2→peel, 3→`iRInd`, 4→`iRK`, else→identity). After one K/cut reduction the reduct's top is no
longer a cut, so `red` becomes identity → the orbit STALLS (lap-104: `red_redAllEx_eq`,
`sord_red_iterate_stalls_AllEx`). Hence `iord_descent_red` (`Crux2Blueprint.lean:533`) is **unprovable for
the current `red`**, and it is the true crux of crux-2.

**⏭ NEXT (hardest-first) — the engine `red` redesign (Gentzen's reduction on codes):**
1. **Redesign `red`/`iRNextG` to locate the relevant redex anywhere in the derivation code, not just the top
   node.** For an empty-sequent (∅→⊥) derivation the endsequent has no logical content, so the lowest
   inference must be a cut; reduce THAT cut and the conclusion stays ∅→⊥ with a strictly smaller `iord`.
   This is a Σ₁ tree-search (`redTable`-style) for the lowest/topmost cut + a local key-reduction. The
   prototype inversion cases (which premise to select at the witness `t`, how `#`/`iotower` ordinals combine)
   are the GUIDE — port them onto codes.
2. **Prove `iord_descent_red`** (the K/cut case; the Ind case `iord_descent_red_zInd` is already done) for
   the redesigned `red`: `icmp (iord (red d)) (iord d) = 0` for a regular ∅→⊥ orbit `d`.
3. **`false_of_ZDerivesEmpty`** (`Crux2Blueprint.lean:588`): the ℕ-indexed `iord`-descent (already assembled,
   `iord_red_iterate_descends`) contradicts `PRWO(ε₀)`. Wire crux-1 PRWO + the embedding.
4. Discharge the remaining `Crux2Blueprint` validity `sorry`s (78/95/196/369/455) + `foundation_bot_to_Z_empty`
   (576), then wire crux-1 ∘ crux-2 → `Reduction.goodstein_implies_consistency` → headline (ONLY when
   `#print axioms` clean).

**`wip/PathCInf.lean` + the `ZcDer`/`ZcOK` prototypes stay as a combinatorial sketch — do NOT invest more in
them; they cannot reach the headline.** Keep `InternalZ`/`Crux2Blueprint` (the engine) green in `src/`.

---

## lap 106 — ✅ prerequisite 1 (conclusion-tracking) STARTED: `ZcDer` + conclusion-faithful principal ∀-inversion
**Brick 5o (`wip/PathCOmega.lean`, all axiom-clean `[propext, choice, Quot.sound]`; `lake build GoodsteinPA`
green 1325; `src/` untouched).** Closes lap-105's NEXT prerequisite (1, "conclusion-tracking on the datatype"):
- `fstIdx_zAllOmega`/`fstIdx_zExOmega` — the missing Path-C conclusion projections.
- `inductive ZcDer : V → Prop` — `ZcOK` refined so the ω-∀ node carries its conclusion data (succedent
  `^∀ p`, premise-`t` derives `Γ⟹p(t)` = `seqSetSucc s (substs1 t p)`). Strictly positive ⟹ Lean gives a
  STRUCTURAL recursor incl. an IH over the infinitary ω-premise family — the recursion vehicle for the
  commuting inversion at the PROTOTYPE level (the deferred Σ₁/PRWO transfinite induction is only for the
  arithmetized layer; the inductive itself recurses structurally).
- `ZcDer.toZcOK` — forgetful map (structural induction), so EVERY lap-105 ordinal brick applies to a
  `ZcDer` orbit.
- `zcDer_iff`/`ZcPhiD` — the inversion vehicle (cf. `zcOK_iff`).
- `zcDer_allOmega_inv` — first end-sequent recovery on the Path-C layer (matrix `p`, instance conclusions).
- `zcDer_iord_descent_allOmega` — the principal ∀-inversion step, now CONCLUSION-faithful (new over
  lap-105's `zcOK_iord_descent_zAllOmega`): premise derives `Γ⟹p(t)`, `ZcDer`-preserved, `iord ≺ α`.
- `zIall_realizes_ZcDer` — the embedding's I∀ image realizes a conclusion-tracking ω-∀ `ZcDer` node (so
  `ZcDer` is inhabited by real derivations, not an abstract prototype).

**Calculus pinned this lap (Buchholz Z∞, `scratchpad/buchholz-gentzen.txt:924-972`):** sequents `Γ→C`
(single succedent); inference symbols `R_A` (intro on RIGHT/succedent), `Lk_A` (intro on LEFT/antecedent),
`Cut_D`. Cut on `D`: premise0 = `Γ,D→C` (`Cut_D(Π,0)=Π.D`, D in antecedent), premise1 = `Γ→D`
(`Cut_D(Π,1)=D,Π`). So Path-C `zCutOmega s α dL dR C`: conclusion `s`, cut formula `C`, dL/dR derive the
two Cut premises — NOT the loose "C/¬C" of earlier handoffs. Pin this before extending conclusion-tracking
to ex/cut.

**⏭ NEXT (hardest-first):**
0. **`ZInf.allInv` commuting cases — the bookkeeping `sorry`s (`wip/PathCInf.lean`).** The ∀-inversion
   recursion STRUCTURE + the principal `allω` selection + atomic base cases (`axL`/`verumR`) are PROVEN.
   The commuting cases (`weak`/`andI`/`orI`/`exI`/`cut`/`allω`-side) carry a disclosed `sorry`: their
   `seqCons`-tower permutation/membership bookkeeping triggers pathological HFS `whnf` under `induction`
   (timeout even at 1.6M heartbeats). **Suspected cause:** `seqCons_comm`/`weaken_*` take the consed
   formulas IMPLICITLY, so Lean infers them by unifying `seqCons (seqCons Γ A) B` against the premise type
   — forcing `lh`/`insert` whnf. **Fix (next lap):** (a) give the helpers EXPLICIT formula args (no
   inference), and/or (b) a single `ZInf.permCongr : Seq Δ → (∀ A, inAnt A Γ ↔ inAnt A Δ) → ZInf Γ → ZInf Δ`
   proven ONCE standalone (helpers compile fast OUTSIDE `induction`), each commuting case = one `permCongr`
   with a `tauto`-closed membership `↔`. The math is the verbatim `Zinfty.allInvAux` port; only term-mode
   cost is open. Then: port `andInvAux`/`orInvAux`, then `cutElimStep`, then bridge `ZInf`-height ↔ engine
   `iord` for the PRWO descent, then wire to `false_of_ZDerivesEmpty` (`Crux2Blueprint.lean:588`).
1. **Extend conclusion-tracking to the ∃ and cut nodes** (shapes pinned above) so the commuting ∀-inversion
   is statable on a cut/∃ last rule. Add the conclusion conjuncts to `ZcDer.ex`/`ZcDer.cut`.
2. **The commuting ∀-inversion recursion** over `ZcDer` (structural — the recursor handles the ω-family),
   porting `Zinfty.allInvAux`'s case structure (ω-∀ principal = `zcDer_iord_descent_allOmega` banked).
   BLOCKER: `ZcDer.leaf` wraps an arbitrary engine `ZDerivation`, so a leaf deriving `Γ⟹^∀ p` still needs
   ENGINE-level ∀-inversion — motivates expanding the datatype with explicit ∧/∨/atom constructors (leaves
   become atomic). NEXT_STEPS PRIORITY-1 item 1 ("ADD ∧/∨ intro + atom-axiom") is the same call.

## lap 105 — ✅ the cut-node ORDINAL bookkeeping is CLOSED; ⏭ the structural `hinv` (inversion) is the bottleneck
**See `HANDOFF-2026-06-25-lap105.md`, STATUS lap-105 box.** Build green 1325; `src/` untouched (headline 0
math axioms). This lap CLOSED the lap-104 ordinal obstruction (the `imax`-can't-do-operator-control finding):
the textbook cut ordinal `max(o(dL),o(dR))+1` (`inc (imax …)`, brick 5e) gives operator-control (no
positivity — handles axiom leaves) AND descent against an arbitrary parent (no additive-principality),
UNIFORMLY for both ω-nodes (∀ brick 5e, induction 5g) + the canonical cut constructor `zcOK_cutS`/`_leaf`
(brick 5h) + leaf-NF auto-discharge (5f). All axiom-clean in `wip/PathCOmega.lean`.

**⏭ THE REMAINING BOTTLENECK (next lap, hardest-first) — the STRUCTURAL `hinv`, two genuinely-deep pieces:**
1. **Conclusion-tracking on the datatype.** `ZcOK` currently tracks only ordinal operator-control, NOT the
   conclusion sequent each node derives. Inversion ("from a derivation of `Γ, ∀x F` extract one of `Γ, F(t)`")
   is INEXPRESSIBLE without it. Enrich `ZcOK` (or a paired predicate) so each node carries/constrains its
   conclusion `fstIdx d`. This is the prerequisite for both inversion AND "∅→⊥ has no cut-free proof" (the
   fact that forces `red` to run forever).
2. **General ∀/∧/∨-inversion `redInv*`.** The recursion that RE-PRINCIPALIZES a reduct premise that is NOT
   literally an ω-node (the lap-104 stall: after the ∀/∃ reduction the new left premise `zsubst d0 a t` is an
   engine leaf, tag ≤ 6, so `red` can't fire again). `Zinfty.allInvAux`/`andInvAux`/`orInvAux`
   (`src/Zinfty.lean`) are the axiom-clean META templates to port. Inversion preserves the stored ordinal
   (`≼`), so it composes with the `max+1` descent.

**⭐ Strategic lead (handoff "Strategic finding"):** the engine `iord d = iotower (iotil d) (idg d)` is ALREADY
the `ω_{rank}^{õ}` tower, and `iord_descent_cut` (`InternalZ.lean:2596`) already proves a higher-rank cut node
strictly dominates its lower-rank premises (the rank-mixing the `max+1`/`#` measures cannot do). For the
COMPOUND-cut commuting reductions, relate the cut node's stored ordinal to `iord` and reuse `iord_descent_cut`
rather than re-deriving the tower.

## lap 104 — ⚠ ENDGAME CORRECTION: the naive `red_iterate_descends` `hinv` is unsatisfiable (in-kernel cert)
**See `HANDOFF-2026-06-25-lap104.md`, STATUS lap-104 box, `NEXT_STEPS.md`.** Build green 1325; `src/`
untouched (headline 0 math axioms). Lap 103 packaged crux-2 as `red_iterate_descends {P} (hinv) (hdrop) (hz)`
and framed `hinv` (`∀ w, P w → P (red w)`) as "tractable via premise selection". **This lap proved that
framing false in-kernel** (4 new axiom-clean lemmas in `wip/PathCOmega.lean`):

- `zTag_ne_seven_of_ZDerivation` — every engine `ZDerivation` has tag ∈ {0..6}, never the stored-ω-∀ tag 7.
- `red_redAllEx_eq` — given the ∀-node base premise `d0` is a `ZDerivation`, the ∀/∃-cut reduct `redAllEx`
  is a `red`-FIXPOINT: its new left premise `zsubst d0 a t` has tag `= zTag d0 ≠ 7` (`zTag_zsubst`), so the
  `(9,7,10)` dispatch fails and `red` is the identity.
- `sord_red_iterate_stalls_AllEx` — on a concrete ∀/∃-cut node, `red` fires once then stalls forever, so
  `sord (red^[n+2] w) = sord (red^[n+1] w)`: the stored ordinal is CONSTANT from step 1 — no infinite descent.
- `naive_dispatch_P_not_red_closed` — ANY `P` implying the `(9,7,10)` dispatch shape fails `hinv` on the
  reduct.

**Root cause (the genuine `hinv` content).** Reducing a cut on `∀x F` produces a smaller cut on `F(t)` whose
premises (`zsubst d0 a t` ⊢ `Γ→F(t)`, `zExPrem dR` ⊢ `Γ→¬F(t)`) need NOT be principal nodes for `F(t)`. To
keep the orbit reducible, `red` must RE-PRINCIPALIZE them — i.e. apply Schütte/Tait **inversion** operators
(`redInv∀`/`redInv∧`/`redInv∨`: from any derivation of `Γ, A` extract a derivation of the immediate
subformula instance, stored ordinal `≼`). Inversion is a recursion over the derivation ⟹ it needs the
genuine **Path-C derivation predicate** (datatype). So `hinv` = the Hauptsatz (inversion + reduction), the
irreducible deep content of crux-2. The lap-103 bricks (nodes/`sord`/per-step drops) stay valid; the endgame
*shape* changes. **CORRECTED NEXT (hardest-first): build the `zcOK` datatype, then inversion, then `red`/`hinv`
— NOT more `hdrop` cut-shape cases (easy leaves on an unsatisfiable `hinv`).** See `NEXT_STEPS.md` PRIORITY 1
(updated lap 104).

**Brick 5 STARTED this lap (axiom-clean, `wip/PathCOmega.lean`).** The datatype as a clean Lean
`inductive ZcOK : V → Prop` (constructors: `leaf` wrapping an engine `ZDerivation`, `omegaAll` [INFINITARY
premise family, strictly positive], `ex`, `cut`; each carries Buchholz operator-control `sord ≺ α`). The
inductive-over-`V` `cases` dependent-elim wall is handled exactly as the engine does: `zcOK_iff` (the
`ZcPhi`-disjunction recursion equation, proved by `cases` on a FREE variable) is the inversion vehicle.
Landed `zcOK_cut_inv` / `zcOK_omegaAll_inv` / `zcOK_ex_inv` (node inversions, `zTag`-discriminated) +
`zTag_ne_nine/ten_of_ZDerivation`. This is the prototype on which inversion (`redInv∀`/…) + `red` + `hinv`
get developed; the Σ₁-`Fixpoint` port (so the descent is V-internal for PRWO) is the deferred final brick.
**Brick 5b (axiom-clean):** principal ∀/∃-cut `hinv`, split clean — `zcOK_redAllEx_premises` (the
STRUCTURAL closure: the reduct's two premises `zsubst d0 a tE` / `dE` are `ZcOK`, the genuine soundness
content) + `zcOK_redAllEx_of_ctrl` (full closure GIVEN the reduct's ordinal control). **⚠ 2nd lap-104
finding (in-kernel): the lap-103 `imax` stored-ordinal is INSUFFICIENT for the cut node.** The `cut`
constructor needs `sord premise ≺ stored`, but the reduct stores `imax (sord dL') (sord dR')` and the
max-achieving premise EQUALS `imax` (never `≺`, `icmp` irreflexive). `imax` worked for the parent-cut
*descent* (`sord_redAllEx_lt`) but NOT for the reduct's own *operator-control*. The genuine fix is Gentzen's
RANK-AWARE ordinal assignment (`o(cut) = ω^{rank} ⊕ …`, strictly above premises AND ≺ parent, carrying the
single-step descent) — the deep Gentzen-Hauptsatz content, now isolated to the ORDINAL assignment alone.

**NEXT (two fronts):** (a) the ∀-inversion operator `redInv∀ : V → V → V` + `ZcOK d → ZcOK (redInv∀ d t)`
(the recursion that re-principalizes the GENERAL — non-ω-∀-node — left premise; principal case =
`zcOK_omegaAll_inv`); (b) the rank-aware `sord` (replace `imax`) so the cut node's operator-control + the
single-step descent hold together (`zcOK_redAllEx_of_ctrl`'s `hLctrl`/`hRctrl` + `sord_redAllEx_lt`).

## lap 102 — Probe 2 settled the fork → Path C (stored ordinals); brick 1 landed
**See `HANDOFF-2026-06-25-lap102.md`, `NEXT_STEPS.md` PRIORITY 1.** The crux-2 sub-route fork is resolved
in favour of **Path C** (ω-rule, Buchholz operator-controlled derivations with STORED ordinals). Path X
(finitary `redZKReady`) is disfavoured AND likely broken (hereditary-Rep fails down a nested-chain spine).
Probe 2 lemmas in `wip/InternalZomega.lean` (axiom-clean): `iotil_zK_iIndReduct(_strictMono)`,
`ocOadd_coeff_strictMono`.

**Path-C brick list (`wip/PathCOmega.lean`):**
- **Brick 1 — DONE, FULL (axiom-clean).** `zAllOmega`/`zAllOmegaValid`(+`Full`) — the stored-ordinal ω-∀-node
  + complete validity (premise family valid + conclusion-tracked `Γ→F(t)` + ordinal ≺ stored `α`).
  `zIall_realizes_zAllOmegaValid(Full)` (a regular finitary `zIall` realizes ALL THREE, stored ordinal = the
  node's own `iord`); `zAllOmega_concl` (conclusion computed, not threaded); `zAllOmega_cut_valid`/`_descends`
  (the ∀-cut invariant).
- **Brick 2 (NEXT) — `cutElimStep`** (single rank drop, all node shapes; `Zinfty.cutElimStep`/
  `cutElimPrincipal` template; ∀-cut case = brick 1, others = `cutReduce*` for ∧/∨/atom).
- **Brick 3 — the induction ω-node.** KERNEL DONE (axiom-clean): `indOmegaStoredOrd` (the stored limit
  ordinal `ω_{dg}(ω^{õd1+1} # ω^{õd0})`) + `iord_iIndReduct_lt_storedBound` (it dominates every finite
  unfolding's `iord`, uniformly in `k` — the side-condition the computed `iord` can't compute, discharged).
  Remaining: package as node + validity (premise `ZDerivation`s via `znth_iIndReductSeq_ZDerivation`,
  conclusion-tracking `F(k)`, Σ₁ side-condition), mirroring `zAllOmega`/`zAllOmegaValid`.
- **Brick 4 — `false_of_ZDerivesEmpty` (Path C)**: SKELETON DONE (`stored_ord_iterate_descends`).
  **Endgame design clarified:** Path C uses Buchholz's single-step ordinal-DROPPING `red` (Def 3.2), NOT
  Zinfty's rank-by-rank `cutElimStep` (which raises the ordinal; that's the META proof). Iterating `red`
  on ∅→⊥ = infinite ε₀-descent ⟹ contradicts PRWO(ε₀) (crux-1), exactly the existing finitary formulation
  (`Crux2Blueprint.iord_red_iterate_descends`). Bricks 1/3 ARE the per-node drops feeding it. Remaining:
  `red` on the datatype + wire to `gentzen_descent_of_inconsistent`.
- **Σ₁-definability** of `zAllOmega`/`zAllOmegaValid` (bookkeeping; `⟪…⟫`/`icmp`/`iord` are `𝚺₁`/`𝚫₁`).
- **Cut-tree carrier for the induction node** — brick 3's ordinal bound uses the FINITARY `iIndReductSeq`
  carrier (re-imports the K-chain). The ordinal fact is path-portable (cut-trees use the same `#`-natural
  sum), but the final Path-C induction node's premise must be a cut-TREE deriving `F(k)`, not the chain.
  Build once the cut-node datatype (brick 2) exists.

## Reflection — 2026-06-25 (lap 101 DEEP REFLECTION)
**See `REFLECTION-2026-06-25-lap101.md` + `NEXT_STEPS.md` (the corrected priority list).** Kernel
re-verified in-kernel: headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms),
`peano_not_proves_consistency` clean, faithfulness anchor clean, statement re-audited vs paper — no drift.

**Direction call.** Destination KEEP (`𝗣𝗔 ⊬ Goodstein`, axiom-free, Rathjen/Gentzen). crux-2 target KEEP
(`redSound`). **Sub-route fork REOPENED.** The lap-92 reflection recommended the ω-rule pivot (Path C) with
a de-risk spike to run FIRST; lap-95 overruled to Path X (finitary) **without running the spike** (it was
never written — `find` confirms). Laps 95–100 made real mechanical progress (the `iRK` gate, the
I∀/I¬/axAll non-Rep replace cases) but the wall *relocated* (eigensubst O2 → the `redZKReady`
hereditary-all-Rep motive), exactly the conclusion-tracking the ω-rule retires for free. And the motive's
hard core is shaky: ∅→⊥ chain premises have growing antecedents `{A₀..A_{i-1}}→Dᵢ`, so Cor 2.1 does NOT
reapply down the selected-premise spine ⟹ "hereditary all-Rep" may not hold as stated.

**KEEP:** crux-2 = `redSound` target; the ordinal engine + `zsubst` + `Zinfty` meta template as reusable
assets; `#print axioms`-gated bare-`sorry` headline discipline.
**STOP:** sinking laps into the `redZKReady` motive / axNeg ¬-cut until the spike's verdict — these are
exactly what the ω-rule would retire.
**HIGHEST-VALUE NEXT:** the skipped de-risk spike `wip/InternalZomega.lean` — internal ω-rule ∀-node
(premise family via `zsubst h x (numeral n)`) + substitution-free critical-cut reduct + `iord` assignment
probe. Elaborates clean → PIVOT to Path C (retires the whole finitary obligation list at once; math
doubly-proven by Bryce–Goré + the repo's own axiom-clean meta `Zinfty.lean`). Walls on Σ₁-arithmetization
→ commit to Path X with evidence. Either way the fork stops being re-litigated each reflection lap. Path X
infra stays in `src/` (green, fallback). **Full spike spec + decision rule: `NEXT_STEPS.md` PRIORITY 1.**

---

## 📍 Lap 100 — 3/4 non-Rep replace capstones ASSEMBLED + wiring piece B banked
**Build 🟢 1325. Headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms).** This lap banked,
all axiom-clean `[propext, choice, Quot.sound]`:
- `ZDerivation_zK_replace_zIneg_of` (Crux2Blueprint) — **I¬ non-Rep replace fully assembled** modulo orbit
  invariants. Uses `ZDerivation_iCritReplaceReduce_general` (membership isChainInf, antecedent GROWS by `p`).
  Un-discharged inputs: `hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p` (faithful premise-antecedent,
  the I¬ analogue of I∀'s O3 freshness — `zInegWff` pins only `p ∈ antecedent`), `hSeqs`/`hSeqsi` (Seq-wff),
  `hthread`/`hrank`.
- `ZDerivation_zK_replace_zAxAll_of` (Crux2Blueprint) — **axAll non-Rep replace fully assembled** (cleanest;
  NO threading needed — pure antecedent monotonicity via `ZDerivation_zK_seqAddAnt`). Un-discharged:
  `hSeqs` + `hAwff : IsUFormula (substs1 (numeral k) p)`.
- `thread_rank_restrict_of_le` (InternalZ, after `permIdx_le_of_isPermPrem`) — **wiring piece B**: restrict
  parent threading/rank up-to-`j₀` down to `i ≤ j₀`. Trivial `le_trans`, exactly the capstones' `hthread`/`hrank`.

**STATUS of the four non-Rep cases:** I∀ ✅ (lap 99 `_zIall_of`), I¬ ✅, axAll ✅, **axNeg ❌ OPEN (Path C)**.

### ⚠ axNeg is GENUINELY harder — NOT a simple succedent-replacement (lap-100 finding)
The axNeg reduct (5.2.2, `tp(d):=tp(dᵢ)`) gives conclusion `Γ→p` (`seqSetSucc s p`). But the reduct premise
`red dᵢ = dᵢ` keeps succedent `D = seqSucc sᵢ ≠ p`. So unlike I∀/I¬ (where the reduced premise's succedent
MATCHES the new conclusion succedent, feeding `isChainInf_…_reduceR`'s `hsucc_v`), **for axNeg no premise has
succedent `p`** — the naive `isChainInf (seqSetSucc s p) r ds` is FALSE (`chainAsucc ds j₀' = p` has no
witness). Buchholz handles `¬A` via the CRITICAL pair (5.1: an L⁰_{¬A} redex pairs with an R_{¬A} I¬-intro,
cut on `¬A` → cut on `A`), NOT a standalone 5.2.2 replace. **Two attack paths for axNeg:**
  - *Path C1:* prove axNeg can NEVER be the minimal-permissible non-chain premise on the ⊥-orbit (then the
    `htp`-false dispatch branch for axNeg is vacuous / unreachable). Check `iperm (L⁰_{¬p}) s` reachability.
  - *Path C2:* build a genuine succedent-replacement constructor that re-derives `Γ→p` using the `¬p ∈ Γ`
    side condition + the chain — i.e. follow Buchholz's actual ¬-axiom cut (restructures premises). Read
    `papers/buchholz-on-gentzens…md:80-95` (the `A,Θ→⊥ / Θ→A / Θ→D` triple for `V=¬A`).

### ▶ THE bottleneck remains the motive cascade — now CONSOLIDATED into `redZKReady` (lap 100 close)
`ZDerivation_red_zK`'s TWO replace sorries are GONE — its body is sorry-free, both branches discharged
(chain-Rep via `ZDerivation_red_zK_replace`, non-Rep via `ZDerivation_red_zK_nonRep`). The entire orbit
obligation is consolidated into ONE named predicate **`redZKReady s r ds`** (Crux2Blueprint, a plain `def`,
no definability needed) carrying per selected-premise `dᵢ`: (a) chain-Rep conclusion-tracking; (b) Seq-wff
conclusion; (c) selection-bounded threading/rank; (d) per-tag I∀/I¬/axAll freshness/faithful-ant/wff.
`redSoundGen`'s K-case now has the SINGLE residual `sorry : redZKReady s r ds`. **This is THE motive.**

**⭐ Lap-100 findings that SHARPEN the motive (consume next lap):**
- **The `tp` facts in redZKReady's chain-Rep field are FREE** — `tp_zK = isymRep` UNCONDITIONALLY
  (InternalZ:704), and `red` of a chain is again a chain, so `tp dᵢ = isymRep` and `tp (red dᵢ) = isymRep`
  need NOT be supplied. **redZKReady's chain-Rep field can be SLIMMED to just `fstIdx (red dᵢ) = fstIdx dᵢ`**
  (derive the two tp facts inside `ZDerivation_red_zK` from `tp_zK` + chain-shape-of-`red`). TODO next lap:
  slim the def, derive `htp`/`hredtp` locally via `zTag dᵢ = 4 ⟹ dᵢ = zK …` + `red_zK_rep` form.
- **The genuine hard residuals are exactly TWO:** (i) `fstIdx (red dᵢ) = fstIdx dᵢ` for a non-critical
  chain `dᵢ` — TRUE only when `dᵢ` is "Rep-reducing" (its OWN selected premise is Rep, route B `fstIdx_red`);
  this is HEREDITARY Rep-reduction, the core of Buchholz Thm 3.4's conclusion bookkeeping. (ii) the
  `permIdx ≤ j₀` selection bound feeding the threading/rank (NOT free even on ∅→⊥: `isChainInf`'s `j₀` is the
  Buchholz-non-critical top, and repo-`permIdx` is the GLOBAL least permissible; need the orbit fact
  "∃ permissible premise at index `≤ j₀`", banked half = `permIdx_le_of_isPermPrem`).
- **On a ∅→⊥ chain the non-Rep tag fields are VACUOUS** (Cor 2.1 `tp_selected_isymRep_of_emptyAnt_botSucc`:
  selected premise is Rep, so `znth ds permIdx = zIall/zIneg/zAxAll …` is FALSE → those implications hold by
  contradiction with `tp ≠ isymRep`). And `Seq (seqAnt s) = Seq ∅` is trivial there. So the ∅→⊥ special
  case of `redZKReady` reduces to JUST residuals (i)+(ii) above — a good first sub-lemma
  (`redZKReady_of_emptyAnt_botSucc`) to attempt next lap.

**Motive design (next lap, Path 1 refined):** strengthen `redSound`'s induction (NOT `redSoundGen`, which is
"false in general") to carry, per node, the route-B conclusion-tracking bundle `fstIdx (red d) = …` ∧ chain
Rep-reduction ∧ the threading (from `isChainInf` + `permIdx ≤ j₀`). The hereditary Rep-reduction (i) and the
selection bound (ii) are the genuine cut-elimination content left — this is multi-lap. The capstones +
dispatch + `redZKReady` consolidation mean EVERYTHING downstream of the invariants is now machine-checked.

### ⭐⭐ Lap-100 close: Thm 3.4(b) IS the motive invariant — but the repo `tp` ≠ Buchholz `tp` for CHAINS
Read `papers/buchholz-on-gentzens…md:98-104`. **Theorem 3.4(b): `d[n] ⊢ tp(d)(Π,n)`** — the reduct derives
the REDUCED endsequent, proven by simultaneous induction on build-up. This conclusion-tracking IS the motive
second conjunct: `fstIdx (red d) = ⟨Buchholz-reduced endsequent of d⟩`. **THE key subtlety (settles the
"hereditary Rep" confusion):** the repo's `tp (zK s r ds) = isymRep` UNCONDITIONALLY (`tp_zK`), but
Buchholz's `tp(d)` for a non-critical chain (case 5.2.2) is `tp(dᵢ)` — the SELECTED PREMISE's type. So the
chain reduct's conclusion is `tpReduce (tp dᵢ) (fstIdx d) 0` (reduced by the PREMISE's tp), NOT
`tpReduce (tp(zK)) … = id`. Confirmed by `red_zK_rep_nonchain`: `fstIdx (red (zK)) = tpReduce (tp dᵢ) s 0`.
⟹ **the conclusion-tracking is inherently case-split on the selected premise's tag — which is EXACTLY what
`redZKReady` encodes.** There is no single clean `fstIdx (red d) = f(tp d)` formula; the per-tag structure is
forced. **Lap-100 banked two motive bricks:** `tp_red_isymRep_of_zTag_4` (chain-Rep tp facts free) +
`fstIdx_red_zK_of_selected_Rep` (Rep-reduction off ∅→⊥, reduced to "selected premise Rep-or-critical").

**Next-lap concrete plan:** (1) define the motive predicate `redTracks d : Prop := ZDerivation (red d) ∧
fstIdx (red d) = ⟨per-tag reduced endsequent⟩ ∧ redZKReady-style data`, hereditary; (2) prove its 5 leaf/
non-chain cases (atom/I∀/I¬/Ind/ax) from the banked `red_z*_tpReduce` tracking lemmas; (3) the K-case
consumes the IH's tracking at the selected premise to discharge `redZKReady`'s chain-Rep `fstIdx` field
(`tp dᵢ = Rep ⟹ tpReduce = id`) and routes non-Rep via the capstones — the ONLY genuinely-open inputs left
being the threading selection bound `permIdx ≤ j₀` (orbit fact) + the per-tag freshness (O3) + axNeg.

---

## 📋 Lap 99 — FULL crux-2 sorry inventory + dependency structure (unblock-protocol)
**Build 🟢 1325. Headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms).** Every open crux-2
sorry and how they depend:

| sorry | what | depends on | independent? |
|---|---|---|---|
| `Reduction.lean:68` `goodstein_implies_consistency` | THE headline obligation | crux-1 (DONE, wip) ∘ crux-2; needs WIRING | no — top |
| `Crux2Blueprint:206` chain-replace | non-critical chain dᵢ (Rep) | `red_rep_of_tp_isymRep` hsel = dᵢ's own selected premise is Rep (hereditary ⊥-orbit invariant) | needs orbit invariant |
| `Crux2Blueprint:227` non-Rep replace | I∀/I¬/axAll/axNeg selected premise | **strengthened motive** (Seq-wff + O3-fresh + ∃perm≤j₀); validity-layer infra DONE lap 99 | THE active front |
| `Crux2Blueprint:183` splice | 5.2.1 `iSpliceEnd` validity | `ZDerivation_seqInsert_of` + spliced isChainInf | partial |
| `Crux2Blueprint:80,99` | iIndReduct validity / iRcritG | banked iCrit constructors | partial |
| `Crux2Blueprint:295` `iord_descent_red` | ordinal descent over red | **strengthened motive** (per-premise ordinal IH: iotil/idg); banked `iord_descent_iCritAux`/`_seqInsert`/critical | parallel to :227, SAME motive |
| `Crux2Blueprint:338` `foundation_bot_to_Z_empty` | M2 embedding (Foundation⊥→ZDerivesEmptyR) | Bryce–Goré Peano.v (~1k lines) | **YES — fully independent of redSound** |
| `Crux2Blueprint:350` `false_of_ZDerivesEmpty` | M3 (descent ⟹ False) | iord_red_iterate_descends (= :295) + PRWO well-foundedness | downstream of :295 |

**KEY STRUCTURAL FINDING:** the validity side (:206,:227) AND the descent side (:295) BOTH route through one
strengthened `redSoundGen` induction motive carrying, per premise: (1) conclusion-tracking
(`fstIdx (red dᵢ) = tpReduce …`, banked for all node types), (2) sequent-wellformedness (`Seq (seqAnt s)`
+ wff — NOT in ZDerivation, `seqAnt s = π₁ s`; preservation banked `Seq_seqAnt_seqAddAnt`), (3) O3-freshness
(I∀ eigenvar fresh — NOT in ZRegular/zIallWff), (4) the ordinal IH (`iotil (red dᵢ) ≺ iotil dᵢ`, `idg ≤`).
**THE motive cascade is the single bottleneck for ~5 of the 8 sorries.** The M2 bridge (:338) is the only
genuinely independent deep thread.

### Three attack paths for the motive cascade (the bottleneck)
- *Path 1 (recommended): define `ZGood d : Prop` as a Fixpoint* = hereditary (validity ∧ Seq-wff-conclusion
  ∧ O3-fresh ∧ regular), prove it's `𝚫₁`-definable, the embedding produces it, `red` preserves it. Then
  strengthen `redSoundGen`/`iord_descent_red` motives to `ZGood d → … ∧ ZGood (red d)`. Big (new Fixpoint +
  heredity), but it's THE clean structural object. Validity-layer + descent infra all banked to consume it.
- *Path 2: bundle the invariants into `ZDerivesEmptyR`* (the orbit predicate) as explicit conjuncts and
  thread them as hypotheses through `redSoundGen` WITHOUT a new Fixpoint — discharge the heredity inline
  per node. Less infrastructure, more per-lemma plumbing; risks not being hereditary without the Fixpoint.
- *Path 3: attack M2 (`foundation_bot_to_Z_empty`) instead* — the independent thread. Port Bryce–Goré
  Peano.v's B1–B3 (PA-axioms→Z, modus-ponens→chain-rule, induction→Z-Ind). Doesn't unblock redSound but is
  mandatory and parallelizable; a partial embedding with disclosed sub-sorries is real progress.

---

## 📍 Lap 100 (ordinal side) — iord_descent_red dispatch + Ind leaf banked
`iord_descent_red` (Crux2Blueprint, `icmp (iord (red d)) (iord d) = 0` over `ZDerivesEmptyR`) is the
ORDINAL companion of `redSound`, structurally PARALLEL to `ZDerivation_red_zK`. Orbit `d` is only Ind or K
(`zTag_Ind_or_K_of_ZDerivesEmpty`). **Lap-100 banked `iord_descent_red_zInd`** (the Ind leaf, axiom-clean,
via `iord_descent_iRInd_of_ZDerivation`). **K-case ordinal residual** mirrors the validity dispatch: banked
per-branch descents `iord_descent_iRcrit_of_chain` (5.1 critical), `iord_descent_iCritAux`/`_iCritReduct_
object` (5.2.2 replace), `iord_descent_seqInsert`/`_iSpliceEnd` (5.2.1 splice). NOTE: `iord_descent_iR2_of_
ZDerivesEmpty` (banked) needs `hcrit` (chain critical) — only the 5.1 case; the non-critical K-case descent
is the genuine residual, needing the same selection-bound + per-tag structure as `redZKReady`. Next-lap:
consolidate the K-case ordinal residual into an `iordDescentReady`-style obligation (mirror `redZKReady`),
or attack the shared motive (which feeds BOTH validity + ordinal sides per the lap-99 structural finding).

## 📍 Lap 99 — VALIDITY LAYER + selection bound DONE; remaining = O3-freshness motive + assembly
**Build 🟢 1325. Headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms). Lap-97's
"architectural wall" RESOLVED (the eigensubst rewire landed lap 97; `red (zIall) = zsubst d0 a 0`).**

The two open `sorry`s are `ZDerivation_red_zK`'s replace branches (`Crux2Blueprint.lean:206,214`). Lap 99
built **the entire validity layer** for them, all axiom-clean:
- `ZDerivation_iCritReplaceReduce_of` (R-rule succedent-reduction constructor)
- `ZDerivation_zK_seqAddAnt` (L-rule axAll antecedent-weakening constructor)
- `tpReduce_tp_zAxAll/zAxNeg` (conclusion-tracking, all node types — frontier item 1 DONE)
- `permIdx_le_of_isPermPrem` ⟹ **`permIdx ≤ j₀`** (Buchholz §5.2 selection bound)

### The THREE remaining pieces to discharge the two `sorry`s (attack paths)
**A. O3-freshness invariant + motive strengthening (THE gating residual).** `red_zIall_tpReduce` (the I∀
conclusion-tracking) needs `fvSubst a 0 p = p` and `fvSubstSeq a 0 (seqAnt sᵢ) = seqAnt sᵢ` — the
eigenvariable `a` fresh in the matrix `p` and antecedent `Γ`. **CONFIRMED lap 99: this is NOT in
`ZRegular` (`zReg_zIall` gives only `maxEigen d0 < a`) nor `zIallWff` (gives only `seqAnt(fstIdx d0)=seqAnt s`,
`seqSucc=p(a)`, `IsSemiformula 1 p`).** It is a genuine extra embedding invariant (O3).
  - *Path A1 (recommended):* define a hereditary `ZFresh d : Prop` (eigenvars fresh in their matrices+ants,
    hereditarily) + prove `ZFresh` preserved by `red`/the embedding produces it; thread it as a second
    motive conjunct in `redSoundGen` alongside `ZRegular`.
  - *Path A2:* fold O3 into `ZRegular` itself (extend `zReg_zIall` to also flag `a ∈ FV(p)∪FV(Γ)`), so the
    existing `ZRegular` threading carries it. Cleaner if `zReg`'s definition can name `fvSubst` cheaply.
  - *Path A3 (cheapest unblock):* take O3 as an explicit hypothesis on `redSound`/`ZDerivesEmptyR` (the
    orbit predicate) and discharge it at the M2 embedding (`foundation_bot_to_Z_empty`) where the fresh
    eigenvariable is CHOSEN. Defers the heredity proof to the embedding.

**B. Threading restriction (trivial, ~5 lines).** From the parent `isChainInf` witness `j₀` + `permIdx ≤ j₀`
(via `permIdx_le_of_isPermPrem` given a permissible premise ≤ j₀), restrict `∀i'≤j₀`/`∀i'<j₀` to
`∀i'≤permIdx`/`∀i'<permIdx` by `le_trans`. Feeds `ZDerivation_iCritReplaceReduce_of`'s `hthread`/`hrank`.

**C. axNeg succedent-replacement constructor (medium).** `tpReduce_tp_zAxNeg = seqSetSucc Π p` (succedent
REPLACEMENT, not weakening — distinct from axAll). Needs a `ZDerivation (zK (seqSetSucc s p) r ds)` from
`ZDerivation (zK s r ds)` constructor; Buchholz §5 ¬-axiom cut restructures premises, so read the PDF
(buchholz-on-gentzens md line 90, the `Θ→A` conclusion). Also: confirm axNeg CAN be selected (`¬p ∈ Γ`).

Then: dispatch line 206 (chain dᵢ = Rep) via `ZDerivation_red_zK_replace`; line 214 (non-chain) by node
type — atom/Ind→Rep, I∀/I¬→`ZDerivation_iCritReplaceReduce_of`, axAll→`ZDerivation_zK_seqAddAnt`,
axNeg→(C). Wff side-conditions (hf1_v…) extract from the premise's `ZDerivation` (note `zIallF` wff is
`IsSemiformula 1`, reconcile with `IsUFormula`).

---

## 📍 Lap 97 — ⛔ THE WALL IS ARCHITECTURAL: `red` cannot do the eigenvariable substitution
(SUPERSEDED — the architectural wall was resolved by the lap-97 eigensubst rewire; kept for history.)

**Build 🟢 1325. Headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms). `ZRegular_red` banked
(axiom-clean) — full O1 regularity-preservation, `Zsubst.lean`.**

### The precise diagnosis (settles laps 90–96's stalled route-B)
The genuine cut-elimination residual is `ZDerivation_red_zK` **case 2** (non-chain selected premise,
`Crux2Blueprint.lean:256`). When the selected premise `dᵢ` is an **I∀ node** (the ∀-principal-cut), Buchholz
reduces the conclusion to `Θ→F(0)` (`tpReduce (isymR ∀p) s 0`, `InternalZ.lean:1084`) AND must instantiate
the eigenvariable in the premise: the replacement at position `i` must be **`zsubst d0 a (numeral 0)`**
(`d0(a/0)`), NOT `d0`. But the repo's `red` puts `red(zIall …) = d0` (deriving `Γ→F(a)`, eigenvar `a`),
so `red (chain)` = `zK (Θ→F(0)) r (seqUpdate ds i d0)` is **genuinely unsound** (d0 derives F(a)≠F(0)).
No downstream proof can fix a wrong VALUE — `red`'s value itself must change to do the eigensubst.

### Why it can't be fixed in place (the lap-96 plan is dead)
`red`/`iRNextG`/`iRKr` live in **`InternalZ.lean`**; `zsubst` lives in **`Zsubst.lean`** (imports InternalZ,
strictly downstream). So `iRNextG` literally cannot name `zsubst`. And `red`'s definition block is **tangled**
through InternalZ's tail (lines 6190–7409) with `iR2`, `ZDerivesEmpty` (def at 6935), and the
`zDerivation_*_inv` lemmas — NOT a clean cut to relocate. This is why ~18 laps stalled.

### Heredity check (done, by reasoning): hereditary Cor 2.1 is FALSE
On the ⊥-orbit the TOP chain's selected premise is Rep (Cor 2.1, `tpReduce isymRep = id`), but `red`
recurses into that Rep premise's OWN selected premise, which is permissible for *its* (non-⊥) conclusion —
where I∀/axiom (non-Rep) selected premises DO occur. So the eigensubst case is genuinely reachable.

### ▶ Resolution options (next lap executes — this is a real pivot)
**⭐ RECOMMENDED (NEW, de-risked lap-97): move the `zsubst` DEFINITION upstream, then rewire `iRNextG` in
place.** KEY enabler: **`FvSubst.lean` is independent of `InternalZ`** (imports only Foundation; the 2
"InternalZ/zIall" refs are comments). So `InternalZ` CAN `import GoodsteinPA.FvSubst`. Then:
  - Add `import GoodsteinPA.FvSubst` to InternalZ (line 21 area).
  - Move the zsubst DEFINITIONAL block `Zsubst.lean:34–~400` UP into InternalZ, placed BEFORE `red`
    (line 6190) and after the zIall/zK accessors: `fvSubstSeqAux`/`fvSubstSeq`/`fvSubstSeqt`,
    `tblMapSeqAux`/`tblMapSeq`, `zIallEig`/`zAxAllK` + the per-tag accessors (`zIallF`/`zInegF`/`zIndP`/
    `zIndEig`/`zIndTerm`), `zsubstNext`/`zsubstTable`/`zsubst` + their `*Def`/`*_defined` instances. These
    are DEFINITIONS (+ definability), NOT proofs — low tactic-fragility. The hard THEOREMS
    (`ZDerivation_zsubst`/`iord_zsubst`/`zReg_zsubst`, `Zsubst.lean:1281+/2003+`) STAY in Zsubst and now
    reference the upstream def.
  - Rewire `iRNextG` tag-1 = `zsubst (zIallPrem d) (zIallEig d) (numeral 0)`; re-prove `iRNextG_defined`
    (add `zsubst_defined.iff`/`zIallEig_defined.iff`/`numeralGraph`), `red_zIall = zsubst d0 a (numeral 0)`.
  - Fix the 3 consumers: `ZRegular_red_of_not_zK` zIall case (use `zReg_zsubst _ _ _ hd0`); `redSoundGen`
    zIall case → thread `ZRegular` so `ZDerivation_zsubst` gives `maxEigen d0 < a`; `red_zIall`'s simp uses.
  This is the cleanest path: ~370 lines of DEFINITIONS move up (vs ~1200 tangled lines of red+proofs down).
  Banked `iord_zsubst`/`ZRegular_red`/`zReg_zsubst` transfer unchanged (descent + regularity are
  conclusion-independent). **⚠ scope: a full lap; do NOT leave InternalZ red across a turn — land green or
  stash to wip/.**

Fallbacks (only if the move proves intractable): a PARALLEL downstream reduct `redC` (duplicates the table);
or confine to a ∀-cut-free fragment (too weak for the PA embedding — rejected).

### What lap 97 banked
- `ZRegular_red` (`Zsubst.lean`): `∀ d, ZDerivation d → ZRegular d → ZRegular (red d)`, axiom-clean — the
  full O1 half, ready to transfer to the relocated/parallel reduct (regularity is conclusion-independent;
  `zReg_zsubst` already covers the eigensubst case).

---

## 📍 Lap 95 — FRESH-MIND REVIEW: the wall is a SURGICAL dispatch gate (confirms Path X)

**Build 🟢 1325. Headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), re-verified in-kernel.**
Primary deliverables: `ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md` + `wip/InternalZdispatch.lean`
(de-risk spike, axiom-clean). **Direction KEPT, Path X (lap-92 DECISION) CONFIRMED + SHARPENED.**

**The sharpened picture (corrects the "2–3k-line ω-rule pivot" framing).** Reading the kernel state:
- **O2 DONE** — `ZDerivation_zsubst` (`Zsubst.lean:1855`, axiom-clean) is the benign criticality-free
  eigensubst lemma; route-B reducts consume it. NOT a wall.
- **O1 DONE except one leaf** — `ZRegular_red_zK` (`Zsubst.lean:1788`) is fully proved *modulo the single
  hypothesis `hseltag`* (not a sorry — a clean lemma awaiting one true fact).
- **The wall = ONE false hypothesis.** `hseltag` (splice ⟹ `zTag dᵢ = 4`) is FALSE under the current `iRK`
  (`not_permIdx_lt_zKseq_zAtom`): the splice fires by default on non-chain selected premises.
- **Fix = surgical gate**, NOT a rewrite. Gate `iRK`'s splice on `zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh(zKseq dᵢ)`
  (= dᵢ a *critical chain*); route non-chains to replace (= Buchholz Def 3.2 case 5.2.2). Behaviour is
  identical for chains; only non-chain selected premises change (junk splice → replace). The ω-rule
  *selection* reading is the SOUNDNESS justification, not a reason to rebuild a new node/`Fixpoint`.

**✅ THIS LAP (lap 95) — STEP 1 LANDED IN-KERNEL (green 1325, axiom-clean).** The gate is PORTED IN-PLACE,
not just spiked:
- `iRK` (`InternalZ.lean:6108`) now gates the splice on `zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh(zKseq dᵢ)`;
  `iRKDef`/`iRK_defined` updated (extra `zTag dᵢ` term + a `zTag dᵢ = 4` case in the definability proof);
  `fstIdx_iRK`/`zTag_iRK` re-proved (`split_ifs <;> simp`).
- `red_zK_rep` (proof) / `red_zK_splice` (gains `htag : zTag dᵢ = 4`) + NEW `red_zK_rep_nonchain` (non-chain
  → replace) in BOTH `Zsubst.lean` and the local copies in `Crux2Blueprint.lean`.
- **`ZRegular_red_zK` (`Zsubst.lean`) is now UNCONDITIONAL** — `hseltag` DROPPED, `#print axioms =
  [propext, choice, Quot.sound]`. The lap-94 regularity wall is cleared in-kernel; the obstruction
  docstring is marked RESOLVED (`not_permIdx_lt_zKseq_zAtom` kept as the in-kernel record of *why*).
- `Crux2Blueprint.ZDerivation_red_zK` dispatch restructured to the gated 3+1-way form (the non-chain
  replace case = a disclosed `sorry` = the deep validity residual below). Headline `#print axioms`
  unchanged: `[propext, sorryAx, choice, Quot.sound]` (0 math axioms). Spike `wip/InternalZdispatch.lean`
  REMOVED (superseded — content promoted to src/).

**▶ NEXT (priority order).**
1. **Validity half** (the genuinely deep residual): rewire the replace branch to emit the conclusion-reduced
   `tpReduce (tp dᵢ) Π n` (`tpReduce` Σ₁-def'd `InternalZ.lean:1064`); prove `ZDerivation_red_zK_rep`/`_splice`/
   `_crit` (Crux2Blueprint sorries) on the reduced conclusions. Lap-90 stands: keep-Π `red` is faithful only
   for `tp = Rep`, so conclusion-reduction is mandatory here.
2. **`iord_descent_red`** (`icmp (iord (red d)) (iord d) = 0`, Crux2Blueprint:306) — assemble from the banked
   per-branch descent lemmas under the now-faithful dispatch.
3. **Wire** `Crux2Blueprint → false_of_ZDerivesEmpty → goodstein_implies_consistency → headline`; drop the
   `Statement.lean` headline `sorry`; confirm `#print axioms peano_not_proves_goodstein` is trust-base-clean.

**Aristotle:** idle (all jobs IDLE). Fodder candidate = the in-place `iRKfix_defined` (Σ₁ semisentence,
mechanical port of `iRKDef`) once the gate is ported, or a self-contained `tpReduce` commutation lemma.

---

## 📍 Lap 92 — DEEP REFLECTION: ω-rule pivot (route C) recommended

**Build 🟢 1325. Headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms). No proof code — synthesis lap.**
Primary deliverable: `REFLECTION-2026-06-25-lap92.md`. STATUS lap-92 box + HANDOFF-lap92 updated.

**The call.** crux-2 `redSound` is the right target; the *finitary eigenvariable* sub-route is the source of
the laps-78–91 stall. ⭐ **CORRECTION (later this lap, in-kernel — `ANALYSIS-2026-06-25-lap92-criticality-wall-is-gone.md`):**
`ZPhi` already uses criticality-free **`zKValidF`** (lap-82 re-point is LIVE), and `ZDerivation_zsubst` is green
⟹ **the lap-78 "substitution wall" is GONE** (CE-1/CE-2 attack ONLY the criticality conjunct, no longer in
validity). Lap-91's **O2 is mislabeled** — it is NOT the lap-78 wall. The genuine residual is the **O1↔O2
freshness/eigensubst COUPLING** intrinsic to finitary ∀: eigensubst (O2) needs `aNotEigen` regularity, which
needs freshness tracking in the Wff predicates (O1). TWO honest paths now:
- **Path X (stay finitary):** add eigenvariable-freshness to `zIallWff`/`zIndWff` (O1) + prove
  `ZDerivation_zsubst_eigen` (substitute eigenvariable by closed numeral, `aNotEigen`, preserving `zKValidF`)
  (O2). Lower architectural risk; NO LONGER known-blocked (lap-78's blocker removed).
- **Path C (ω-rule pivot):** Buchholz §6 `Z^∞`, as `Zinfty.lean` (meta, axiom-clean) + Bryce–Goré's Coq do.
  A critical cut *selects* premise `dₙ` instead of substituting ⟹ O1+O2+`tpReduce` all vanish. Higher one-time
  cost, removes the coupling permanently.

**⭐ DECISION (end of lap 92 — `DECISION-2026-06-25-lap92-path-X-favored.md`): Path X favored.** The ω-rule
precedents (`Zinfty.lean`, Bryce–Goré) are META-level (premises = native functions); they do NOT de-risk the
arithmetized ω-rule (Σ₁ `Z*` notations over codes), which is the un-precedented hard part the repo chose
finitary to avoid. Path X completes the invested finitary arithmetization with standard bookkeeping, and O1
is now shown **tractable + maintainable** via the key insight: `zsubst` (closed term) **preserves eigenvariable
indices**, so a freshness invariant phrased on eigenvariable indices (`maxEigen premise < eigenvar`) is
**stable through `red`** (the code-bound `d≤a` was not). Path C is the fallback only if step 4 below walls.

**NEXT — Path X foundation lemmas (concrete, low-risk, reuse the `idg` recursion template):**
1. **✅ DONE (lap 92, `Zsubst.lean`, axiom-clean, green 1325):** `maxEigen d` defined + `𝚺₁`-definable
   (`maxEigenNext`/`maxEigenTable`/`maxEigenDef`) via the `idg`/`PR.Construction` template. `maxEigenNext`
   folds `zIallEig`/`zIndEig` over the premise table; chains use `iseqMaxTab`.
2. **✅ DONE (lap 93, `Zsubst.lean`, axiom-clean, green 1325): recursion equations + stability.**
   (a) `maxEigen_zAtom`/`_zIall`(`= max a (maxEigen d0)`)/`_zIneg`/`_zInd`(`= max (π₁ at') (max …)`)/
   `_zAxAll`/`_zAxNeg`/`_zAx1`/`_zK`(`= iseqMaxEigen ds`) — via the `idg` structural-correctness template
   (`def_maxEigenTable`/`maxEigenTable_seq`/`_lh`/`znth_maxEigenTable_eq_maxEigen`/`maxEigen_eq_maxEigenNext`
   + the `iseqMaxEigen` fold mirroring `iseqMaxIdg`/`idg_zK`). (b) **`maxEigen_zsubst (a t) : ∀ d,
   ZDerivation d → maxEigen (zsubst d a t) = maxEigen d`** — the substitution-stability crux, by
   `zDerivation_induction` + the recursion equations + `zsubst_zIall`/`zInd` preserving the eigenvariable
   + fold congruence `iseqMaxEigenAux_congr` (chain). `#print axioms` = `[propext, choice, Quot.sound]`.
3. **✅ DONE (lap 93, `Zsubst.lean`, axiom-clean, green 1325): `ZDerivation_zsubst` reformulated** from
   `d ≤ a` to `maxEigen d < a`. Relocated the `maxEigen` block above `ZDerivation_zsubst`; added the
   fold-bound `le_iseqMaxEigen` (mirror `le_iseqMaxTab`); each case derives `e ≠ a` + the recursive
   premise bound from the `maxEigen` recursion eqs (`le_max_left/right` for `zIall`/`zInd`, `le_iseqMaxEigen`
   for `zK`). The dead sequent bound `hsa : s ≤ a` is removed (never used). Corollaries
   `ZDerivation_zsubst_zIall_premise`/`_zInd_premise1` retargeted to `maxEigen d0 < a` / `maxEigen d1 < π₁ at'`.
4. **O1 — ARCHITECTURE CHANGED (lap 93): additive `zReg`, NOT a `zIallWff` edit.** Baking freshness into
   `zIallWff` reshapes the `ZDerivation` fixpoint (blueprint/definability/embedding all break — large blast
   radius). Instead, **✅ DONE (lap 93, `Zsubst.lean`, axiom-clean, green 1325):** a standalone `𝚺₁`
   *hereditary-freshness* function `zReg d` (violation count; `0` iff regular), built on the `maxEigen`/`idg`
   table template (`ltFlag`/`zRegNext`/`zRegTable` + recursion eqs `zReg_zAtom`/`_zIall`(`max (ltFlag (maxEigen
   d0) a) (zReg d0)`)/`_zIneg`/`_zInd`/`_zAx*`/`_zK`(`iseqReg ds`)). Predicate `ZRegular d := zReg d = 0`.
   Route-B bridges `maxEigen_lt_of_regular_zIall`/`_zInd` (regular node ⟹ the `maxEigen d0 < a` / `maxEigen d1
   < π₁ at'` that reformulated `ZDerivation_zsubst` consumes). Substitution step `zReg_zsubst` (ZDerivation d ⟹
   `zReg (zsubst d a t) = zReg d`) — regularity preserved by closed-term subst. `#print axioms` clean.
5. **`red` preserves `ZRegular` — structural + Ind cases DONE (lap 93, `Zsubst.lean`, axiom-clean, green
   1325).** `ZRegular_red_of_not_zK` covers atom/zIall(→d0)/zIneg(→d0)/zInd(→`iRInd`)/zAxAll/zAxNeg. KEY
   simplification found: `iRInd (zInd …) = zK s (irk p) (iIndReductSeq d0 d1 1)` is a chain over the
   *literal* premises `⟨d1,d0⟩` — **no substitution at the Ind level** — so its `zReg = max (zReg d1) (zReg
   d0) = 0`. Added the `iseqReg` fold lemmas (`_seqCons`/`_const`/`_iRepeatSeq`/`_iIndReductSeq`,
   `iseqRegAux_znth_congr`) mirroring `iseqMaxIdg`.
6. **`zK` chain case — reusable building blocks DONE (lap 93, `Zsubst.lean`, axiom-clean, green 1325).**
   `ZRegular_zK_of_premises` (a chain all of whose premises are regular IS regular; via `iseqReg_eq_zero_of`)
   and `ZRegular_zAxReduct` (the per-premise atomic reduct preserves regularity — it returns `zAx1`/identity).
   All three `iRK` branches produce a chain over regular reducts, so these are the shared closing lemmas.
7. **`zK`-case reduct-regularity helpers DONE (lap 93, axiom-clean, green 1325):** `le_iseqReg`,
   `ZRegular_zK_premise` (premise of a regular chain is regular), `ZRegular_zK_of_seqUpdate` (5.2.2 `iRKr`
   + each half of 5.1 `iRKc`), `ZRegular_zK_of_iCritReductSeq` (5.1 `iRKc` outer chain). The `iRKr`/`iRKc`
   branches close from these (premises regular via `ZRegular_zK_premise` + IH `ZRegular (red premise)` via
   `znth_redTable_eq_red`; the per-premise reduct regular via `ZRegular_zAxReduct`).
8. **⚠ STRUCTURAL FINDING (lap 93): `red`-preserves-`ZRegular` for the `zK` case is NOT standalone — it needs
   `zKValidF`.** The 5.2.1 splice `iRKs` reads `a,b = znth (zKseq (red dᵢ)) 0/1` where `dᵢ = znth ds permIdx`.
   `zReg a ≤ zReg (red dᵢ)` holds ONLY when `red dᵢ` is a genuine `K`-chain (tag 4) — which requires
   `zTag dᵢ = 4`, a fact that only holds for *valid* derivations (`zKValidF`'s `isChainInf`/criticality
   data), NOT from `ZDerivation`+`ZRegular` alone (a pathological non-tag-4 `dᵢ` would take the `iRKs` branch
   and produce junk halves). **⟹ regularity preservation belongs INSIDE the `redSound` induction** (where
   `zKValidF` is in scope), not as a separate `red_preserves_ZRegular`. The lap-93 helpers are exactly the
   tools that induction will use.
9. **← START HERE: `redSound` with regularity threaded.** Prove "red of a VALID, regular contradiction
   derivation is a valid, regular ZDerivation" by the `redTable`/`zDerivation_induction`, using `zKValidF`
   to pin `zTag dᵢ = 4` in the `iRKs` branch + the lap-93 helpers + the route-B bridges
   (`maxEigen_lt_of_regular_zIall`/`_zInd`) at the I∀/Ind validity steps. Then embedding ⟹ regular, then
   `false_of_ZDerivesEmpty` → headline. Inspect existing `redSound`/`RedSound` scaffolding first (laps 82-90).
2. **(Path X) — ✅ O2 BANKED this lap (`Zsubst.lean`, axiom-clean):** `ZDerivation_zsubst_zIall_premise`
   and `ZDerivation_zsubst_zInd_premise1` discharge the route-B I∀/Ind eigensubst reducts **directly from
   the existing `ZDerivation_zsubst`**, under the freshness bound `d0 ≤ a` / `d1 ≤ π₁ at'`. This
   kernel-certifies the corrected diagnosis: O2 needs NO new substitution lemma. **The entire residual is
   now O1** = produce the bound `premise ≤ eigenvariable`, i.e. add eigenvariable-freshness to
   `zIallWff`/`zIndWff` AND maintain it through `red`. Sharpened next target: decide the freshness predicate
   — a code-bound `d0 < a` (makes the corollary apply directly but is NOT substitution-stable through `red`)
   vs the genuine Buchholz condition `e ∉ FV(ant)` + distinctness (substitution-stable by closed numeral, but
   needs reformulating the corollary's hypothesis from `≤` to that predicate). The maintenance-through-`red`
   of whichever freshness invariant is the real O1 difficulty — and is exactly what Path C (ω-rule) avoids.
3. **(Path C)** `wip/InternalZomega.lean`: ω-rule ∀-node `zAllOmega s g`, premise-n `= appPrem g n` (Σ₁ lookup
   into notation `g`, reusing `zK`/`zKseq`/`iIndReductSeq`); critical-cut reduct = `appPrem g n`, no `substs1`/
   `zsubst`. Then Σ₁-definability of `appPrem`, then port the axiom-clean `iord` engine + `Zinfty` cut-elim
   cases (`orInv`/`allInv`/`cutElimStep` are worked meta templates). ~2–3k-line rebuild.

**STOP:** finitary `tpReduce` conclusion-tracking + new `Zsubst`/`ZDerivation_zsubst` eigenvariable lemmas.
**KEEP (reusable under route C):** `red_zK_rep/_splice`, `tp_*`, `red_rep_of_tp_isymRep`,
`tp_isymRep_of_emptyAnt_botSucc` (the `tp`-dispatch survives; only substitution → selection changes); the
axiom-clean `iord` engine; `Zinfty.lean` as template.

---

## 📍 Lap 91 — route-B keystone `tpReduce` defined + 𝚺₁-definable

**Build 🟢 1325. Headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms). 2 green commits.**

Lap-90 forced route B (faithful Buchholz reduct with conclusion reduction). Step 1 landed:
- ✅ **`tpReduce I s n`** (`InternalZ.lean`, after `inAnt_seqAddAnt`) = Buchholz's reduced sequent
  `I(Π,n)` (from the PDF §2 14.23/14.252): `Rep→Π`, `R_∀xF→Θ→F(n)`, `R_¬A→A,Θ→⊥`,
  `L^k_∀xF→F(k),Θ→D`, `L^0_¬A→Θ→A`. ∀/¬ dispatch on `π₁(A∸1)=6`; ¬-body via `IsUFormula.neg_neg`.
  All 5 per-symbol equations proved axiom-clean (`tpReduce_isymRep` is `@[simp]`).
- ✅ **`tpReduceDef` / `tpReduce_defined` / `_definable` / `_definable'`** (after `seqAddAnt_definable`)
  — `tpReduce` is `𝚺₁`-definable (subDef peels the qq `+1`).

**✅ lap-91 also landed `fstIdx_red_eq_tpReduce_of_Rep`** (`InternalZ.lean`): the route-B conclusion
invariant for the `Rep` case (`zTag ∈ {3,4}`), = the headline ⊥-orbit specialisation, axiom-clean.

**⚠️ TWO OBSTRUCTIONS FOUND (lap 91, the genuine route-B walls — map before grinding):**

**(O1) `zIallWff` does NOT track the eigenvariable freshness `a ∉ FV(Γ)`** (`InternalZ.lean:1542`:
`zIallWff = seqAnt(fstIdx d0)=seqAnt s ∧ seqSucc(fstIdx d0)=substs1 (^&a) p ∧ IsSemiformula 1 p`).
So `ZDerivation (zIall …)` carries no freshness. Route B's I∀ conclusion `Γ→F(0)` needs `Γ[a/0]=Γ`,
i.e. `a ∉ FV(Γ)`. ⟹ **rung-0.5 redux**: strengthen `zIallWff` (and `zIndWff`) with the freshness
conjunct (blast radius: every `zIall`/`zInd` builder must supply it). On the headline ⊥-orbit the
sub-derivations reached have `Γ = ∅` (lap-90), so freshness is MOOT there — a restricted
empty-antecedent I∀ lemma sidesteps O1 for the headline, IF O2 is solved.

**(O2) eigenvariable substitution `d₀(a/n)` is NOT `ZDerivation_zsubst`** (`Zsubst.lean:834`). That
theorem requires `d ≤ a` (substitution variable larger than all codes — fresh, non-clashing). The
route-B I∀ reduct substitutes the *eigenvariable* `e = zIallEig` which genuinely occurs in `d₀`
(small index, `d₀ ⋬ e`), so `ZDerivation_zsubst` does not apply. This is the lap-78 "criticality
substitution wall" again: eigen-subst is a SEPARATE, harder substitution lemma (the eigenvar appears
in the derivation, not a fresh slot). **Genuine next deep target** = an eigenvariable-substitution
ZDerivation lemma (`zsubst d₀ e t` valid when `e` is `d₀`'s genuine eigenvar, freshness from the rule).

**⚠️ (O3) The route-B invariant must be ANTECEDENT-MEMBERSHIP-EQUIVALENCE, not raw `fstIdx =`.**
Buchholz sequents are sets; the repo codes antecedents as `seqCons` sequences with `inAnt` membership,
and the per-rule `…Wff` predicates track the antecedent INCONSISTENTLY: `zIallWff` pins
`seqAnt(fstIdx d0) = seqAnt s` EXACTLY, but `zInegWff` only pins `inAnt p (seqAnt(fstIdx d0))`
(membership). So `fstIdx (red (zIneg …)) = tpReduce (R_¬A) Π 0` FAILS as raw equality (`red zIneg = d0`
has antecedent `Γ'∋p`, not the canonical `seqCons Γ p`). ⟹ state the invariant as: `red d` derives a
sequent with succedent `= seqSucc (tpReduce …)` AND antecedent `≈` (same membership-set as)
`seqAnt (tpReduce …)`. The chain-rule threading already consumes antecedents via `inAnt` only
(`isChainInf`/`chainAnt` at `InternalZ.lean:1157`), so it is robust to this — the invariant equivalence
suffices to rebuild parent chains. **`tpReduce` gives the canonical representative; the invariant is
up-to-`inAnt`-equality to it.** (Headline ⊥-orbit's `fstIdx_red_eq_tpReduce_of_Rep` is EXACT — `Π=∅→⊥`,
no antecedent ambiguity — so O3 only bites in the general structural induction, not the headline rung.)

**⭐ O2 FULLY DECOMPOSED (lap 91) — the route-B I∀ reduct `d₀(a/n) = zsubst d0 a (numeral n)` needs
exactly THREE lemmas, all gated on the eigenvariable freshness (O1, `a ∉ FV(Γ→∀xF)`):**
- **(O2a) eigenvar-plug commutation** `fvSubst a t (substs1 ℒₒᵣ ^&a p) = substs1 ℒₒᵣ t p` under
  `a ∉ FV(p)` — the succedent `F(a)→F(t)` step. NOT in repo/Foundation (only the `a'≠a` variant
  `fvSubst_substs1_fvar` exists, `FvSubst.lean:567`). A Foundation-level formula-induction lemma.
- **(O2b) antecedent freshness** `fvSubstSeq a t Γ = Γ` under `a ∉ FV(Γ)` (= `seqAnt s`). The repo's
  `fvSubst_eq_self_of_le` (`FvSubst.lean:441`) gives this only for the SIZE-fresh `p ≤ a` form; need the
  genuine-freshness `a ∉ FV` form (per-element of the `Γ` sequence).
- **(O2c) eigen-subst validity** `ZDerivation (zsubst d0 a (numeral n))`. `ZDerivation_zsubst`
  (`Zsubst.lean:834`) needs `d₀ ≤ a` (fresh large slot) — FALSE for an eigenvar. Generalize its
  hypothesis from `d ≤ a` to "`a` avoids every nested eigenvariable of `d`" (the only use of `d≤a` is
  deriving `e ≠ a` per nested I∀, `Zsubst.lean:852`); discharge via O1 (distinct eigenvariables).
- The CONCLUSION-TRACKING (`fstIdx (zsubst d0 a (num n)) = tpReduce (tp d) (fstIdx d) n`) then follows
  from `fstIdx_zsubst` (needs only `ZDerivation d0`, `Zsubst.lean:504`) + O2a (succedent) + O2b
  (antecedent). So conclusion-tracking is PURE plumbing once O2a/O2b land.

**NEXT (route-B continuation, in dependency order):**
1. **O1 freshness FIRST** (it gates O2a/O2b/O2c): add `a ∉ FV(seqAnt s) ∧ a ∉ FV(p)` to `zIallWff`
   (and the analogue to `zIndWff`). Blast radius = every `zIall`/`zInd` builder. Then O2a (Foundation
   formula lemma), O2b (per-element `fvSubstSeq` freshness), O2c (generalize `ZDerivation_zsubst`).
2. **O1** (freshness in `zIallWff`/`zIndWff`) — needed for non-empty `Γ`; deferrable if the headline
   ⊥-orbit only reaches empty-`Γ` I∀ sub-derivations (verify via the recursion trace).
3. **Rewire `red`'s I∀/chain/Ind branches to emit `tpReduce (tp dᵢ) Π 0`** (5.2.2 `iRKr`→reduced
   conclusion; Ind→`Γ→F(k)`, `k`=val `t`).
4. **Thm 3.4(b) invariant** `ZDerivation (red d) ∧ fstIdx (red d) = tpReduce (tp d) (fstIdx d) 0` by
   `zDerivation_induction`; the `Rep` cases already done (`fstIdx_red_eq_tpReduce_of_Rep`).
5. Then `iord_descent_red` (ordinal side unaffected), `false_of_ZDerivesEmpty`, M2 bridge → headline.

## 📍 Lap 90 — `redSound` DECOMPOSED + faithfulness finding (`red` faithful only for `Rep`)

**Build 🟢 1325 jobs. Headline still `[propext, sorryAx, choice, Quot.sound]` (0 math axioms).**
3 green commits: (1) `redSound` decomposed into `redSoundGen` skeleton + 2 Thm-3.4 residuals; (2) Ind
residual restated at `zKValidF` (criticality-free); (3) K-core dispatch split into 3 case-5 sub-residuals
with `red_zK_rep`/`red_zK_splice` recursion equations PROVED.

**⭐ MAJOR FINDING (read `ANALYSIS-2026-06-25-lap90-red-faithful-only-for-rep.md`):** the lap-89 tag-4
dispatch + the repo's `red` are **faithful to Buchholz `d[0]` ONLY for `Rep`-reducible chains**
(`tp(d) = isymRep`). Two gaps for non-`Rep` chains: (1) Buchholz 5.2.2 reduces the conclusion to
`tp(dᵢ)(Π,0) ≠ Π`, but `red`/`iRKr` keep `Π` (`fstIdx_iRK = fstIdx d`); (2) the selected minimal-permissible
premise `dᵢ` can be an I-rule/axiom (`iperm` admits `isymR`/`isymLk`), not just a chain, so the
critical-sub-dispatch is ill-typed. ⟹ **`redSoundGen` (∀ ZDerivation) is FALSE**; the K-branch residuals
`ZDerivation_red_zK_replace/_splice` are FALSE as stated (flagged ⚠ in docstrings). **Saving grace —
Buchholz Cor 2.1:** on the ⊥-orbit (`ZDerivesEmpty`, Π = `→⊥`) every selected premise is `Rep`, so
`red = d[0]` faithfully THERE. The TRUE target is `redSound` over `ZDerivesEmpty`.

**⛔ ROUTE A REFUTED (lap 90, later — see analysis doc §UPDATE).** Concrete kill: `red` of a `∅→⊥`
chain recurses into `red d₀` where `d₀` (the selected `Rep` premise) derives `∅→A₀` (threading forces
`Γ₀=∅`, but succedent `A₀ ≠ ⊥`). For `∅→A₀`, `iperm` admits an I-rule premise (`isymR A₀`), so `red d₀`
mis-keeps the conclusion → invalid. The ⊥-condition is NOT preserved one level down, so no ⊥-orbit
invariant closes the recursion. `tp_isymRep_of_emptyAnt_botSucc` (proved) saves only the TOP step.

**NEXT (resume point) — ROUTE B: faithfully port Def 3.2 with conclusion reduction `tp(dᵢ)(Π,n)`:**
1. **Define `tpReduce I Π n` = Buchholz `I(Π,n)`** (the reduced conclusion): `R_∀xF → Γ→F(n)`,
   `R_¬A → …`, `L^k_A → ` left-reduction, `Rep → Π` (identity). Σ₁-definable.
2. **Re-point the reduct's conclusion**: chain branches build `zK (tpReduce (tp dᵢ) Π 0) …` instead of
   keeping `Π`; `iRKr`/the I-rule reducts get the reduced conclusion.
3. **Invariant = Buchholz Thm 3.4(b) verbatim**: `∀ d, ZDerivation d → ZDerivation (red d) ∧
   fstIdx (red d) = tpReduce (tp d) (fstIdx d) 0` — provable by PLAIN structural induction (no orbit
   restriction). Specialise to headline at `tp d = Rep` (⊥-orbit: `tpReduce Rep Π 0 = Π`).
4. **I-rule conclusion-tracking**: `red (zIall) = d0` omits Buchholz's `a/n` substitution `d₀(a/n)`;
   under route B it should derive `Γ→F(0)`. Use `Zsubst.lean` eigen-subst machinery (laps 72–76).
5. **REUSABLE (become route-B's `tp(dᵢ)=Rep` branch):** `red_zK_rep`/`red_zK_splice`,
   `tp_eq_isymRep_of_zTag`, `red_rep_of_tp_isymRep`, `zTag_not_iAx_of_tp_isymRep`,
   `ZDerivation_red_zK_replace` (5.2.2 validity under `tp dᵢ=Rep`), `tp_isymRep_of_emptyAnt_botSucc`.
6. **Independent tractable thread:** `zKValidF_iIndReduct_of_zInd` (Ind reduct validity, unaffected).

## 📍 Lap 89 (FRESH-MIND REVIEW) — endgame SINGLE-FRONT + tag-4 dispatch `iRK` DEFINED

**Build 🟢 1325 jobs, headline `[propext, sorryAx, choice, Quot.sound]` (0 math axioms).**

**⭐ REVIEW FINDING the lap-88 handoff missed:** `PA_delta1Definable` is **discharged UPSTREAM** —
Foundation now proves `𝗣𝗔.Δ₁` as a real `noncomputable instance` (`InductionSchemeDelta1.lean:1379`),
so `peano_not_proves_consistency = [propext, choice, Quot.sound]` (axiom-clean). The whole lap-74/78/81
second-front campaign (`src/PADelta1.lean`) is moot. **The headline has exactly ONE open blocker:**
`goodstein_implies_consistency` (`Reduction.lean:68`) = crux-1 (done lap 57) ∘ crux-2 = `redSound`.
STATUS.md refreshed; memory `pa-delta1-discharged-upstream` written.

**LANDED this lap (3 green commits, all axiom-clean, all in `InternalZ.lean`):**
- ✅ **`permIdxDef`/`permIdx_defined`** — the dispatch index `permIdx` is now Σ₁-definable (was missing).
- ✅ **`iRKr`** (5.2.2 replace) = `iCritAux d (permIdx d) (znth s dᵢ)` + def. ⭐ key insight: the genuine
  reduct halves come from the **recursive table lookup `red dᵢ = znth s dᵢ`**, NOT `inference_critical_pair`
  — so each branch is a CLOSED definable term, no existential.
- ✅ **`iRKs`** (5.2.1 splice) = `zK (fstIdx d) r' (seqInsert (zKseq d) i dᵢ{0} dᵢ{1})`, halves
  `= znth (zKseq (znth s dᵢ)) {0,1}`, **rank `r' = max(irk(seqSucc(fstIdx dᵢ{0})), zKrank d)`** — VERIFIED
  to be exactly the minimal `r'` `isChainInf_seqInsert` requires (`irk(seqSucc(fstIdx a)) ≤ r' ∧ r ≤ r'`).
- ✅ **`iRKc`** (5.1 critical) — standalone extraction of the original tag-4 `iRcritG` branch.
- ✅ **`iRK`** (the dispatch) — 3-way, branching on the **Δ₀ sentinel `permIdx d < lh (zKseq d)`** (=
  criticality, via `permIdxAux_eq_self_of_none`/`_isPermPrem_of_lt`) rather than embedding Δ₁ `zKCriticalDef`;
  sub-dispatch on the same test for the selected premise. `iRK_defined` via nested `by_cases`.

**NEXT (resume point):**
1. **Rewire `iRNextG` tag-4 → `iRK d s`** (`InternalZ.lean:~6011`). Change `iRNextG`'s tag-4 from the inline
   `iRcritG d (…)` to `iRK d s`; replace the tag-4 block in `iRNextGDef` with `!iRKDef y d s`; the
   `iRNextG_defined` proof simplifies (tag-4 case = `!iRKDef`). ⚠ Blast radius: `red_zK` and the lap-86
   `not_zKCritical_*` lemmas (now apply only to the 5.1 sub-case where `permIdx d = lh`). Recheck `red_zK`
   and the descent-bridge lemmas after the rewire.
2. **Semantic dispatch equivalences for `redSound`**: `permIdx d = lh (zKseq d) ↔ zKCritical (fstIdx d)
   (zKseq d)` (both directions banked at `permIdxAux` level) — wire as named lemmas so `redSound`'s tag-4
   case knows which Buchholz branch fired.
3. **`redSound`** = `zDerivation_induction`, tag-4 split via the sentinel into 5.1 (`ZDerivation_iRcritG_of`),
   5.2.1 (`ZDerivation_seqInsert_of_zK` — supply genuine halves from the critical premise's
   `inference_critical_pair`; discharge `isChainInf_seqInsert`'s end-sequent hyps + `r' ≤ dg(parent)` i.e.
   `rk(A(dᵢ)) ≤ dg(parent)`), 5.2.2 (`ZDerivation_iCritAux_of_zK`); then `iord_descent_red` UNCONDITIONAL
   → `iord_red_iterate_descends` → `false_of_ZDerivesEmpty` (`Crux2Blueprint`) → `Reduction.lean:68`.

## 📍 Lap 88 — 5.2.1 GENUINE-OBJECT stack complete (descent + ZDerivation) + 5.2 dispatch index

**Build 🟢 1325 jobs, axiom base clean. 5 green commits.** All new lemmas in `InternalZ.lean`,
`[propext, choice, Quot.sound]`.

**LANDED:**
- ✅ **`iord_descent_seqInsert`** (+ `_of_ZDerivation`/`_of_iSpliceDescent`) — ordinal descent DIRECTLY on
  the genuine `seqInsert` object via rotation kernel `icmp_iseqNaddIdg_seqInsert` (J-shifted induction,
  `isNF` carried; base = F2; suffix folds via `inadd_right_mono`). **No `inadd_assoc`/permutation needed**
  — the lap-87 "needs an `iseqNaddIdg`-reindex" worry was avoidable. + `idg`-side
  `iseqMaxIdg_seqInsert_le`/`idg_seqInsert_le` + `iseqMaxIdgAux_le_of_all`.
- ✅ **`ZDerivation_seqInsert_of`** / `_of_zK` — 5.2.1 validity: spliced chain is a genuine `ZDerivation`
  (analogue of `ZDerivation_iCritAux_of`). + reusable `forall_znth_seqInsert`.
- ✅ **`permIdxAux`/`permIdx`** — 5.2 dispatch index = least permissible premise `i` (`iperm (tp dᵢ) s`);
  full spec stack + Σ₁-def + `permIdx_lt_of_not_zKCritical`.

**⟹ all three dispatch branches (5.1/5.2.1/5.2.2) now object-complete + co-located validity+descent.**

**NEXT (the assembly — not new math; see HANDOFF-lap88 ▶ NEXT):**
1. **Rewrite `iRNextG` tag-4 to DISPATCH** (zKCritical → 5.1; else `permIdx` → sub-dispatch 5.2.1/5.2.2).
   Large blast radius (`iRNextGDef`, `iRNextG_defined`, `red_zK`, `not_zKCritical_*`). Consider a separate
   definable `iRNextGD` to contain it, then swap `redTable`.
2. **Wire genuine halves** `a=dᵢ{0}, b=dᵢ{1}` from `inference_critical_pair` on the critical premise;
   discharge `isChainInf_seqInsert` end-sequent hyps + build `iSpliceDescent`.
3. **`redSound`** via `zDerivation_induction`, tag-4 split → each ZDerivation constructor; then
   `iord_descent_red` unconditional → `false_of_ZDerivesEmpty` → headline.

---

## 📍 Lap 87 — 5.2.1 splice VALIDITY object is ordered insert-at-`i`, NOT the banked end-append model

**Build 🟢 1325 jobs, axiom base clean (headline 0 math axioms).** See
`ANALYSIS-2026-06-25-lap87-splice-order-sensitivity.md`.

**LANDED (axiom-clean `[propext, choice, Quot.sound]`, `InternalZ.lean` after `zKValidF_seqUpdate`):**
splice end-sequent read-outs (`chainAsucc`/`chainAnt`_{`seqCons_seqUpdate_{top,lt}`,`seqUpdate_{self,of_ne}`});
`isChainInf_iSpliceEnd` + `zKValidF_iSpliceEnd` — the order-independent validity REDUCTIONS (take threading
as hypotheses; reusable as the ordinal-side interface + `forall`-premise template).

**FINDING (confirmed vs Buchholz Def 3.2, paper md line 75–76):** the banked ordinal-descent splice model
`seqCons (seqUpdate ds i a) b` (half `a` in place at `i`, half `b` appended at the END) serves the ordinal
`õ` (= order-independent `#`-fold) but is WRONG for `isChainInf` validity, which threads each antecedent
only to STRICTLY-EARLIER succedents. The genuine reduct `K^{r'}_Π(i/dᵢ{0},dᵢ{1})` is the ORDERED
in-place splice `d₀…d_{i−1} dᵢ{0} dᵢ{1} d_{i+1}…dₗ` (insert two halves at `i`, shift tail). So
`zKValidF_iSpliceEnd`'s `isChainInf` hypothesis is generically unsatisfiable for the genuine halves — it's
the ordinal packaging, not the validity object.

**DONE (lap 87, abstract-spec form, axiom-clean, `InternalZ.lean` after `zKValidF_iSpliceEnd`):**
- ✅ **`isChainInf_seqInsert_spec`** — THE hard 5.2.1 threading math. The spliced chain
  `cs = d₀…d_{i−1} a b d_{i+1}…dₗ` is `isChainInf s r' cs` from the original chain's unpacked validity at
  its distinguished `j₀` (`i ≤ j₀`) + the Thm-3.4(a) genuine half end-sequents. New distinguished `j₀+1`;
  full order-sensitive threading by region (worked out + machine-checked).
- ✅ **`zKValidF_seqInsert_spec`** — full faithful validity from the `isChainInf` core + per-half
  well-formedness, via the `forall`-premise `key` over the four insert regions.
Both take the insert read-outs `hpre`/`hai`/`hbi`/`hsuf` as hypotheses (abstract spec).

**DONE (lap 87, concrete op, axiom-clean):**
- ✅ **`seqInsertAux`/`seqInsert`** (`PR.Construction`, `𝚺₁-Function₅`, mirror `seqUpdateAux`) +
  read-outs `seqInsert_lh`, `znth_seqInsert_{pre,at,at1,suf}` (ite-free). NB: `Function₅` Definable
  instance via the explicit `(Γ-[m+1]).DefinableFunction₅` dot form (Foundation lacks bare
  `Γ-Function₅` notation).
- ✅ **`isChainInf_seqInsert`** / **`zKValidF_seqInsert`** — the specs instantiated on the concrete
  `seqInsert` (read-out hyps discharged, given `i < lh ds`). The genuine 5.2.1 reduct's chain-validity +
  faithful validity are now usable object-level facts.

**NEXT (remaining 5.2.1 — connect to the descent + the `red` dispatch):**
2. **Descent transfer**: `õ(seqInsert ds i a b) = õ(seqCons (seqUpdate ds i a) b)` (same `#`-multiset,
   `iseqNaddIdg` permutation-invariant) ⟹ inherit banked `iord_descent_iSpliceEnd`. (Or direct `iord`
   descent on the insert object mirroring `iotil_iSpliceEnd_lt`.)
3. **Wire the genuine halves**: supply `a = dᵢ{0}`, `b = dᵢ{1}` from `inference_critical_pair` applied to
   the critical premise `dᵢ` (the redex finder, L3.1) + the Thm-3.4(a) end-sequent facts to discharge
   `ha_ant`/`ha_rank`/`hb_succ`/`hb_ant`. Then `red`'s tag-4 5.2.1 branch + its `redSound` case.

---

## 📍 Lap 86 (FRESH-MIND REVIEW) — gating criticality question RESOLVED: `red` needs the 5.2 dispatch

**Build 🟢 1325 jobs, axiom base clean. Headline `peano_not_proves_goodstein = [propext, sorryAx,
choice, Quot.sound]` (0 math axioms, honest sorry).** Resolved the lap-85 NEXT-priority-2 gating
question (`ANALYSIS-2026-06-25-lap86-criticality-resolved.md`).

**FINDING (in-kernel, axiom-clean):** a `ZDerivesEmpty` K-chain is NOT always critical. The critical-only
reduct `red (zK s r ds) = iRcritG …` is **itself non-critical** — its `⊥`-half premise (index 1) is a
`K`-chain (`tp = isymRep`, permissible everywhere). New lemmas in `InternalZ.lean` (after `red_zK`):
`not_zKCritical_iCritReductG` / `not_zKCritical_iRcritG` / `not_zKCritical_red_zK`. ⟹ The
iterate-descent's `zKCritical` hypothesis (`iord_iR2_iterate_descends`'s `hcrit`) is **unsatisfiable
after one step**. So the critical-only `red`/`iR2` (Buchholz Def 3.2 case **5.1 only**) cannot drive the
descent; the genuine `red` MUST dispatch the **5.2** cases too.

**Two corrections to the lap-85 plan:**
- Lap-85 priority-1 (`iord (red x) = iord (iR2 x)` unconditional) is necessary but **NOT sufficient** —
  it inherits `iR2`'s descent, which is itself gated on the now-false criticality. Don't close
  `iord_descent_red` via it alone.
- `red`'s tag-4 must DISPATCH 5.1 / 5.2.1 / 5.2.2 (not always `iRcritG`).

**NEXT (the corrected `red` — 5.2 dispatch; descent for each is BANKED, lap-82):**
1. **Decidability — DONE (lap 86):** `zKCritical` is now Δ₁ (`zKCriticalDef` + `zKCritical_defined`/
   `_definable`, axiom-clean, in `InternalZ.lean` after `zKValidF_of_zKValid`). `iRNextG`'s tag-4 can now
   branch on `zKCritical (fstIdx d) (zKseq d)` and stay Σ₁. ⚠ Still to reconcile: `∀ i < lh ds` (repo)
   vs Buchholz's `∀ i ≤ j₀` — the `j₀`-restricted form is the faithful branch; decide whether the
   stronger `∀ i < lh ds` mis-classifies any Buchholz-critical chain (if some i > j₀ has tp(dᵢ) ◁ Π).
2. **5.2.1 splice** — `red d = zK s r' (seqCons (seqUpdate ds i dᵢ{1}) dᵢ{0})`. Descent banked
   (`iord_descent_iSpliceEnd`). ⚠ **The VALIDITY is the next hard piece**: only read-outs are banked
   (`znth_seqCons_seqUpdate_top`/`_lt`, `lh_seqCons_seqUpdate`) — NO `isChainInf`/`zKValidF` for the
   spliced shape yet. Needs the spliced-chain threading proof (the new chain re-establishes `isChainInf`:
   `j₀`, `Γᵢ ⊆ Γ,A₀…` threading with the two spliced halves, rank `≤ r'`). Required because for a CRITICAL
   `dᵢ` the pre-ordinal `õ(red dᵢ)` BLOWS UP (Lemma 4.1(b)), so 5.2.2-replace cannot be used (its descent
   needs `õ(v) ≺ õ(dᵢ)`) — the splice incorporates `dᵢ`'s halves (smaller `õ`) directly.
3. **5.2.2 replace — VALIDITY DONE (lap 86):** `ZDerivation_iCritAux_of` (axiom-clean, next to
   `iord_descent_iCritAux_of_ZDerivation`): replacing premise `i` of a valid chain by a same-end-sequent
   reduct `v` that is a `ZDerivation` (+ its own well-formedness) gives `ZDerivation (iCritAux …)`. With
   the banked descent, the 5.2.2 leaf is complete at the lemma level — both invariants take the same N1
   IH on `v = red dᵢ`. For ⊥-chains the chosen premise is a `Rep`-chain so `tp(dᵢ)(Π,n)=Π` (conclusion
   unchanged) and `v`'s well-formedness hyps are automatic (`tp = isymRep`, I/Ax conjuncts vacuous) — a
   specialized tag-4 corollary collapses them. STILL TODO: the general 5.2.2 conclusion op `tp(dᵢ)(s,n)`
   for the non-⊥ / non-Rep sub-case (only needed if `red` is defined on all d, not just ⊥-chains).
4. **`redSound`** = `zDerivation_induction`, tag-4 split 5.1/5.2.1/5.2.2 → `zKValidF` chain;
   `iord_descent_red` becomes UNCONDITIONAL. (R2 / `zAx1` tag-7 from lap-85 still apply to the 5.1 case.)

## 📍 Lap 85 — R1 DISCHARGED + M1a `red` DEFINED + M1b ordinal bridge (5 green commits)

**Build 🟢 1325 jobs, axiom base clean ([propext, Classical.choice, Quot.sound]).** The keystone
re-point landed and the genuine reduct now exists.

DONE this lap:
- **R1 (the `ZPhi` re-point)** — `ZPhi`'s `zK` disjunct now carries `zKValidF` (faithful, criticality-free
  validity). `zDerivation_zK_intro` is a theorem (was `hZPhiK`). `ZDerivation_iCritReductG_of`/
  `ZDerivation_iRcritG_of` drop the re-point residual. `zKValidF_of_ZDerivation_zK` replaces
  `zKValid_of_ZDerivation_zK`. Dead iR2-orbit descent now takes an explicit `zKCritical` hyp (honest).
- **M1a — `red` DEFINED** (`InternalZ`): `iRNextG` (5-case dispatch, K-case = `iRcritG` on correct reduced
  endsequents), `redTable` PR-recursion, `red := znth (redTable d) d`, 𝚺₁-definable (`redDef`). Per-rule
  recursion eqs `red_zAtom/zIall/zIneg/zInd/zAxAll/zAxNeg/red_zK`. `fstIdx_red_of_tag_Ind_or_K`. Genuine
  endsequent ops definable (`seqSetSuccDef`/`seqAddAntDef`). Blueprint `red`/`fstIdx_red` wired to reals
  (blueprint sorries 6→4).
- **M1b ordinal bridge** — `iord_iRcritG_eq_iRcrit` (via `iotil_zK`/`idg_zK` conclusion-independence). The
  ordinal descent on `red`'s K-case = the banked `iRcrit` descent.

NEXT (M1b `redSound`, the cut-elim nut — priority):
1. **R2 (auxiliary IH)** — discharge the `haux0`/`haux1` hyps of `ZDerivation_iRcritG_of`: the two
   auxiliaries `zK (seqSetSucc (fstIdx d) A(d)) r (seqUpdate ds i (ρ i))` etc. are `ZDerivation`s. Needs:
   (a) premises are ZDerivations — unchanged ones from `d`'s ZDerivation; the replaced one `ρ i =
   zAxReduct (red (znth ds i))` by the `redSound` IH + **`ZDerivation_zAxReduct`** (see ⚠ below);
   (b) the aux chain is `zKValidF` — the banked `zKValidF_iCritReductSeq`/`isChainInf_iCritReductSeq`
   threading (Thm 3.4(a)), establishing the recombination from `d`'s validity + criticality.
2. ⚠ **`zAx1` is TAG 7, NOT a `ZPhi` rule** (tags 0–6). So `zAxReduct` of an axiom premise (tag 5/6 →
   `zAx1`) is currently NOT a `ZDerivation`. Resolve before R2: either (i) the redex premises are never
   tag-5/6 axioms (so `zAxReduct` = identity there — likely, the redex i-premise has `tp = isymR` ⟹ I-rule
   tag 1/2 via `tp_isymR_tag`; the j-premise `tp = isymLk` — CHECK if that forces an L-rule vs an axiom),
   OR (ii) add a tag-7 disjunct to `ZPhi` for `zAx1` (the atomic identity axiom) and re-bless the Fixpoint.
3. **`redSound`** = `zDerivation_induction` over `d`; tags 1,2 (I-rules, but never on ⊥) reuse
   `ZDerivation_iR2_zIall/zIneg` (red=iR2 there); tag 3 (Ind) needs the Ind-reduct `zKValidF` (deep
   residual, parallels old `ZDerivation_iR2_zInd_of_zKValid` but only `zKValidF` now); tag 4 = `ZDerivation_iRcritG_of` + R2.
4. **`iord_descent_red`** — provable on CRITICAL chains: `red_zK` + `iord_iRcritG_eq_iRcrit` + banked
   `iord_descent_iRcrit_of_chain`. ⚠ **GAP: `red` is critical-case-only** (tag-4 always `iRcritG` at
   `redexCode`). Non-critical chains (no redex pair found) need Buchholz 5.2 splice/replace dispatch —
   `red` must branch on `zKCritical`. Decide: does a ZDerivesEmpty chain always have a critical redex
   (positive rank ⟹ L3.1 redex pair)? If yes, critical-only `red` suffices and `iord_descent_red` closes.

## 📍 Lap 84 (FINAL) — RedSound CRITICAL case reduced to TWO named residuals (12 green commits)

**Build 🟢 green, axiom base untouched.** The genuine critical reduct is now named and its validity
isolated. Banked beyond the D₁ interface below:
- `iCritReductG s C rOut rIn0 rIn1 ds0 ds1` — the GENUINE critical reduct
  `K^{rOut}_Π ⟨K^{rIn0}_{Θ→A(d)} ds0, K^{rIn1}_{A(d),Θ→D} ds1⟩`, auxiliaries carrying the real Thm-3.4(a)
  endsequents (`seqSetSucc s C` / `seqAddAnt C s`). Read-outs `fstIdx`/`zTag`/`zKseq`.
- `zKValidF_iCritReductGen` — its outer-chain D₁ validity, **threading AUTOMATIC** from the genuine
  sequent ops (only needs `irk C ≤ rOut` + formula-hood).
- `ZDerivation_iCritReductG_of` — `iCritReductG` is a `ZDerivation` **modulo exactly two residuals**:
  - **(R1) the re-point** `hZPhiK : Seq ds → (∀i<lh, ZDerivation(znth ds i)) → zKValidF s r ds →
    ZDerivation (zK s r ds)` — i.e. `ZPhi`'s `zK` disjunct `zKValid → zKValidF`. ⚠️ INTERLOCKED with the
    descent: `zDerivation_zK_inv` then yields only `zKValidF` (no criticality), breaking
    `iord_descent_iR2_zK_of_valid` (which uses criticality to FIND the redex via
    `inference_critical_pair_of_chain`). So the re-point MUST land together with a descent that dispatches
    criticality as a SEPARATE fact (supply `zKCritical` at the reduction site, where Buchholz case-5
    establishes it — `zKValid_iff_zKValidF_and_zKCritical` is the bridge). Do this as a FOCUSED turn.
  - **(R2) auxiliary IH** — the two auxiliaries are `ZDerivation`s of `Θ→A(d)` / `A(d),Θ→D` (recursive
    Thm 3.4(a)). Needs: extract `A(d)` from the redex (`A_i = chainAsucc ds i`; `A_i = ^∀ p ⟹ A(d) =
    substs1 (num k) p`, `A_i = inegF q ⟹ A(d) = q`) + prove d{0}'s isChainInf with distinguished premise
    `j0' = i` (the replaced premise `dᵢ[k]` carries succedent `A(d)`), threading = original ≤i threading.
    rank drop `irk(A(d)) < irk(A_i) ≤ r` is BANKED (`irk_cut_lt_rank_forall`/`_neg`).

**Recommended next sequencing:** R2 first (independent of re-point, pure Thm-3.4(a) structural content),
then the focused R1 re-point+dispatch turn. Non-critical (5.2.2) is already done (`zKValidF_seqUpdate_iR2`);
splice (5.2.1) prereqs banked. After R1+R2 the critical case closes ⟹ assemble the 5-case `red` +
RedSound structural induction (D₁ ∥ banked D₃).

## 📍 Lap 84 (continued) — D₁ VALIDITY INTERFACE complete for all 3 reduct cases (9 green commits)

**Build 🟢 green, axiom base untouched.** Beyond the 3 preservation lemmas below, banked (all in
`InternalZ.lean`, kernel-checked):
- **Critical (5.1) D₁ — COMPLETE as a hypothesis interface.** `isChainInf_iCritReductSeq` (the 2-element
  recombination chain `⟨d{0},d{1}⟩` is `isChainInf`-valid given Thm 3.4(a) cut-threading) → lifted to full
  `zKValidF_iCritReductSeq` (auxiliaries are `Rep`-chains ⟹ own-perm auto, I/Ax conjuncts vacuous;
  threading + formula-hood supplied). Helpers `znth_iCritReductSeq_one`, `forall_lt_iCritReductSeq`.
  ⭐ **VERIFIED FAITHFUL to Buchholz §2 p.6 / Thm 3.4(a):** `d{0}⊢Θ→A(d)`, `d{1}⊢A(d),Θ→D`, the cut on
  `A(d)`; my hyps `hsucc1`/`hthread0`/`hthread1`/`hrank0` map exactly (hthread1's `B=seqSucc(fstIdx d0)`
  disjunct IS the cut formula `A(d)`).
- **General congruence** `isChainInf_congr` (validity reads `ds` only through `lh`+`chainAsucc`/`chainAnt`).
- **Splice (5.2.1) prereqs**: read-outs `znth_seqCons_seqUpdate_top`/`_lt`, `lh_seqCons_seqUpdate`.
- **Genuine-reduct sequent ops** (replace the ordinal-shadow `iCritAux`'s reuse of `fstIdx d`):
  `seqSetSucc s C` (= `Θ→C`), `seqAddAnt A s` (= `A,Θ→D`), with `inAnt_seqCons`/`inAnt_seqAddAnt`.

**NEXT (genuine reduct, the remaining M1 core — STARTED):** define the genuine critical auxiliaries
`d{0} = zK (seqSetSucc s (A(d))) r (seqUpdate ds i (reduct dᵢ))`, `d{1} = zK (seqAddAnt (A(d)) s) r
(seqUpdate ds j (reduct dⱼ))` — i.e. like `iCritAux` BUT with the correct conclusion sequents from the
new ops. Then `A(d)` is read from the redex via `inference_critical_pair` (∀xF case: `A(d)=F(k)`;
¬A case: `A(d)=A`); prove the auxiliaries derive those sequents (Thm 3.4(a), structural IH) so
`zKValidF_iCritReductSeq`'s hyps are MET. Then re-point `ZPhi` zK disjunct `zKValid→zKValidF` (~6 sites,
`zKValidFDef` banked) and run the D₁/D₃ structural induction = `RedSound`. M1 checkpoint per
`E-CRUX2-ROADMAP`: validity proved IN the same induction as the (banked) descent.

## 📍 Lap 84 — RedSound validity-preservation toolkit BANKED (3 green commits) + judge's parallel-induction unlock

**Build 🟢 green (1324 jobs), axiom base untouched.** Three reusable `RedSound` building blocks landed in
`InternalZ.lean` (the `E-CRUX2 §8` T2/T3 "replace-a-premise stays a valid K^r chain" leaf), right after
the `seqUpdate` read-outs and after `fstIdx_iR2_of_tag_Ind_or_K`:
- `isChainInf_seqUpdate` — chain-validity (`isChainInf`: j₀/threading/rank) is INVARIANT under replacing
  premise `i` by a same-end-sequent reduct `v` (`fstIdx v = fstIdx (znth ds i)`). Helpers:
  `fstIdx_znth_seqUpdate`, `chainAsucc_seqUpdate`, `chainAnt_seqUpdate`.
- `zKValidF_seqUpdate` — full faithful-validity preservation, taking `v`'s own well-formedness
  (own-perm `iperm (tp v)(fstIdx v)` = Lemma 3.3; tag-gated I/Ax formula-hood) as hypotheses.
- `zKValidF_seqUpdate_iR2` — CONCRETE non-critical case (Buchholz 5.2.2): when premise `i` is itself
  `Ind`/`K`-tagged, its `iR2`-reduct is a `Rep`-tagged chain (`iR2_eq_zK_of_tag_Ind_or_K`,
  `zTag_iR2_…=4`, `tp_iR2_…=isymRep`), so own-perm is automatic (`iperm_isymRep`) and the I/Ax
  conjuncts are vacuous; end-sequent invariance from `fstIdx_iR2_of_tag_Ind_or_K`. ⟹ `zKValidF` preserved.

⭐ **JUDGE UNLOCK (Buchholz both papers, validate-don't-trust):** validity is a **PARALLEL invariant**,
NOT post-hoc recovery. Buchholz proves validity (Thm 3.4 / Thm 6.2 = our `zKValidF`/D₁) and
ordinal-descent (Lemma 4.1/4.2 = our banked `iord_descent_*` / D₃) as TWO SIMULTANEOUS inductions over
the SAME primrec reduct `red` (Def 3.2 / Beweistheorie Thm 6.6 — 5-case tag dispatch; only search =
Lemma 3.1 least redex pair = our `inference_critical_pair`). `RedSound`-on-`iR2` was false ONLY because
`iR2` was built ordinal-first. BUILD `red` (the dispatch) and prove its validity IN the same recursion
that gives descent. §7 D₁=`∀n d[n]⊢tp(d)(Π,n)` (=RedSound), D₃=descent — the spec. Sources:
`papers/buchholz-beweistheorie-lecture-notes.md` (red/Thm 6.2), `papers/buchholz-on-gentzens-first-consistency-proof.md`
(Def 3.2 / §7 D₁–D₃). Fallback ONLY if critical case can't be zKValidF-faithful: Siders' Howard vector
(`papers/siders-gentzen-consistency-proofs-arithmetic.md`) — HA/intuitionistic redesign, exhaust Buchholz first.

**NEXT (resume here):** (a) the SUB-CRITICAL splice (Buchholz 5.2.1) validity-preservation analog
`zKValidF_seqSplice` over `seqCons (seqUpdate ds j a) b` — harder (lh+1, threading shift), pairs with banked
`iord_descent_iSpliceEnd`. (b) the CRITICAL case (5.1): `iCritReduct = zK (fstIdx d)(r-1) ⟨d{0},d{1}⟩` —
its two auxiliaries `d{ν}=iCritAux` are `seqUpdate`-replacements, so `zKValidF_seqUpdate_iR2` gives each
auxiliary's validity; the OUTER rank-(r-1) chain validity needs the recombination threading (Thm 3.4(a),
`rk(A(d))<r` already banked as `irk_cut_lt_rank_*`). (c) Re-point `ZPhi`'s zK disjunct `zKValid`→`zKValidF`
(blast radius measured lap-82: ~6 sites; `zKValidFDef` banked) and quantify RedSound + descent over `red`.


## 📍 Lap 83 fresh-mind REFINEMENT (read before executing the lap-82 re-point) — "descent = just wiring" is OVERSTATED

Re-read `iord_descent_iR2_zK_of_valid` (`InternalZ.lean:4755`) end-to-end. The lap-82 KEY FINDING
("step 2 is not new descent math, only wire the banked `iord_descent_iCritAux`/`_iSpliceEnd` into a
dispatch") is **too optimistic on one point**: the K-descent does NOT merely *consume* criticality as a
side fact — it uses `hnperm` (criticality) to **FIND THE REDEX** via `inference_critical_pair_of_chain`,
and then `rw [iR2_zK_eq_iRcrit]` to make `iR2` BE that critical reduct. So:

- In the **non-critical** case there is provably **no such redex** (some premise `i ≤ j₀` has
  `iperm (tp dᵢ) s`), so `inference_critical_pair_of_chain` is inapplicable AND `iRcrit` (= the current
  `iR2_zK`) reduces nothing useful. The banked `iord_descent_iCritAux` descends the reduct
  `zK s r (seqUpdate ds i v)` — but **only if `iR2_zK` actually PRODUCES that reduct**, which it does
  not: `iR2_zK_eq_iRcrit` is unconditional. Wiring the banked descent therefore REQUIRES the reduct
  function `iR2_zK` itself to branch on `zKCritical s ds` (critical → `iRcrit`; non-critical → `iCritAux`
  replace; sub-critical → `iSpliceEnd` splice). That is a **definitional change to the reduct**, not a
  proof-only dispatch — and it breaks `iR2_zK_eq_iRcrit` and everything proved through it (`iR2_zK`,
  the redex-finder route in `iord_descent_iR2_zK_of_valid`, plus the §5 `zAxReduct` bundles which assume
  the iRcrit shape). The lap-82 plan's own step-3 escape hatch ("if `iR2` can't be made to dispatch case
  5.2, define a NEW reduct and re-point `RedSound` + descent onto it") is the realistic route.

- **Net:** the re-point of `ZPhi` → `zKValidF` (step 1) cannot stay green by itself — it forces
  `iord_descent_iR2_zK_of_valid` to take only `zKValidF`, whose non-critical case has no banked
  *producer*. Recommended lap-83 sequencing: **(a)** first build the non-critical reduct + its descent
  capstone as a STANDALONE green lemma `iord_descent_iCritAux_zK_noncrit` (hypotheses: `zKValidF` +
  `¬zKCritical` + the witnessing `i`), reusing banked `iord_descent_iCritAux`; **(b)** likewise the
  sub-critical splice capstone; **(c)** ONLY THEN define the dispatching reduct (new `iR2'` or a guarded
  `iR2_zK`) and re-point — so each step lands green and committable rather than a red all-or-nothing swap.
  This keeps "hardest-first" honest: the genuinely-new math is the non-critical/sub-critical *producers*
  (selecting the witness `i` / splice point from `isChainInf` + ¬criticality), then `RedSound` validity.

## ⭐⭐ Lap 82 (OPERATOR REDIRECT) — crux-2 unblocked: criticality ≠ chain-validity

**Build 🟢 green.** Operator moved Front 2 (`PA_delta1Definable`) to a parallel box — it's a tracked
rest-point; STOP touching `PADelta1.lean` (it merges later). Drive **crux 2 (`RedSound`)** only.
(Lap-82 also banked 3 axiom-clean `PADelta1.lean` code-size bounds before the redirect: `lt_qqAll`,
`self_le_qqAllItr`, `count_le_qqAllItr` — harmless, stay.)

**ROOT CAUSE found + validated against Buchholz (both papers).** `zKValid` bakes a spurious *criticality*
conjunct `(∀ i < lh ds, ¬ iperm (tp (znth ds i)) s)` into chain-validity. Buchholz's `K^r` validity
(§3 clause 5 = `isChainInf`: j₀ + threading + rank) carries NO criticality; criticality is a *reduction*
property (Def 3.2 case 5), not a validity one. Baking it in → `ZDerivation` = only-critical chains →
the genuine reduct's `Rep`-tagged recombined premises fail validity → `RedSound`-on-`iR2` false. See
`ANALYSIS-2026-06-25-lap82-criticality-not-validity.md`.

DONE this lap (axiom-clean, `InternalZ.lean` after `zKValid_definable`):
- `zKCritical s ds` (decoupled criticality), `zKValidF s r ds` (faithful validity = `zKValid` − criticality),
  `zKValid_iff_zKValidF_and_zKCritical` (in-kernel: criticality IS a separable conjunct),
  `zKValidF_of_zKValid`.

⭐ **KEY FINDING (lap 82): DESCENT (D₃, Lemma 4.1/Thm 4.2) is ALREADY FULLY BANKED.** Every Buchholz
reduction case has its closed `iord_descent_*` proved (`InternalZ.lean` 2529–3293): I-rules, Ind (LH4),
non-critical chain `iord_descent_iCritAux` (5.2.2), splice `iord_descent_iSpliceEnd` (5.2.1), critical
`iord_descent_iRcrit_of_chain` (5.1). `iord_iR2_iterate_descends` assembles the ε₀-descent modulo
`RedSound`. So crux-2 is NOT blocked on descent — the wall is purely VALIDITY (RedSound) + the dispatch.

DONE this lap (continued): **`zKValidFDef` + `zKValidF_defined`/`_definable`** — the Δ₁ arithmetization
of `zKValidF` (= `zKValidDef` minus the `¬(!ipermDef ti s)` line), green first try. This is the
prerequisite for re-pointing `zblueprint`'s `zK` disjunct.

⭐ **MEASURED re-point blast radius (lap 82, empirically: re-pointed ZPhi, built, reverted).** Changing
`ZPhi` (`InternalZ.lean:3694`) + `zPhiBounded_iff` (3741, two `rintro`/`exact` spots 3754/3768) +
`zblueprint` (3790/3808: `zKValidDef.sigma/.pi` → `zKValidFDef.sigma/.pi`) + `zPhi_definable` proof.
Then exactly **6 lemma sites** break, all mechanical EXCEPT the descent capstone:
- `zKValid_of_ZDerivation_zK` (~4000): change return type → `zKValidF` (rename).
- forward constructors `ZDerivation_iR2_zInd_of_zKValid` (5094), `ZDerivation_iCritReduct_of` (5125):
  take `zKValidF` instead of `zKValid` (the genuine reduct validates against faithful validity — these
  become PROVABLE where they were vacuous before).
- ⚠️ **`iord_descent_iR2_zK_of_valid` (4780) — THE hard one**: currently UNCONDITIONAL because `zKValid`
  forced criticality (redex always found). With only `zKValidF`, must `by_cases zKCritical s ds`:
  critical → existing `iRcrit` route; non-critical → `iR2` must do the non-critical reduct
  (`iCritAux` replace, descent `iord_descent_iCritAux` BANKED) — needs the `iR2_zK` DISPATCH (step 2).

REDESIGN (revised — hardest-first; descent already done; arithmetization now ready):
1. Re-point `ZPhi`'s `zK` disjunct (`InternalZ.lean:3694`) `zKValid` → `zKValidF` (+ `zPhiBounded_iff` +
   `zblueprint` → `zKValidFDef` + `zPhi_definable`; blast radius measured above).
   `zKValid_iff_zKValidF_and_zKCritical` makes producers mechanical.
2. Make `iR2_zK` DISPATCH (currently always `iRcrit`, `iR2_zK_eq_iRcrit`): critical (5.1, redex exists)
   → `iRcrit`; non-critical (5.2.2, `∃ i ≤ j₀ tp(dᵢ) ◁ Π`) → `iCritAux` replace premise i by `iR2 dᵢ`;
   sub-critical (5.2.1) → splice. Descent for each is ALREADY banked — only wire the selection.
3. **Prove `RedSound` = Thm 3.4(b)/D₁** (THE new content): the reduct is a genuine `ZDerivation`
   (`zKValidF`), by the same `ZDerivation` induction that drives descent. Critical case: recombination
   `K^{r−1}_Π d{0} d{1}` valid via Thm 3.4(a) (`d{0} ⊢ Π·A(d)`, `d{1} ⊢ A(d),Π`, `rk(A(d)) < r`) — the
   `inference_critical_pair` redex + the `zDerivation_z*_inv` peeling primitives are in place. Non-critical:
   `isChainInf s' r (seqUpdate ds i (iR2 dᵢ))` for the reduced end-sequent `s' = tp(d)(Π,n)`.
Fallback: Siders' Howard vector (`papers/siders-gentzen-consistency-proofs-arithmetic.md`, cross-check only).

## ⭐ Lap 81 (FRESH-MIND REVIEW) — criticality crux `not_criticality_aux` PROVED (axiom-clean)

**Build 🟢 green (1324 jobs). Direction KEPT (Δ₁ thread is the actively-movable front; crux 2 stays
DEEP-REFLECTION-blocked).** This lap discharged the criticality crux — the math heart of the
`inductionSchemeUnivDelta1` mem_iff.

DONE (all axiom-clean `[propext, choice, Quot.sound]`, `PADelta1.lean` §Recognizer):
- **`subst_eq_subst_of`** + `isUTermVec_qVec` — formula substitution congruence (`subst` of an
  `n`-ary semiformula depends only on the first `n` entries); via `pi1_structural_induction`.
- **`subst_fvarSeq_quote`** — `subst (fvarSeq k) ⌜F⌝ = ⌜F ⇜ (&·)⌝` (mirrors `subst_fvarSeq_fixitr`).
- **`fvar?_substs_lt`** — fv-free `k`-ary `F` ⟹ `(F ⇜ (&·)).FVar? x → x < k` (via `Semiformula.fvar?_rew`).
- **`freeVariables_eq_empty_of_shift`** — shift-fixpoint ⟹ fv-free (strong-induction descent on free vars).
- **`subst_fvarSeq_le` / `subst_fvarSeq_succ`** — `subst (fvarSeq m) F = subst (fvarSeq k) F` for
  `k ≤ m` / `m = k+1`; stated at GENERIC V to dodge the `V = ℕ` order diamond. ⚠️ KEY GOTCHA: V's `+`
  on `ℕ` IS native, but its `≤`/`-` are NOT (`instLE_foundation ≠ instLENat`); bundle order bounds at
  generic V (where `le_self_add` picks V's order), invoke at `V := ℕ` (then `+` is native, omega-friendly).
- **⭐ `not_criticality_aux`** — THE crux: `0 < ψ.fvSup → ¬(IsSemiformula ℒₒᵣ (ψ.fvSup-1)
  ⌜fixitr 0 ψ.fvSup ▹ ψ⌝ ∧ shift ⌜..⌝ = ⌜..⌝)`. Pins `m = fvSup` in the recognizer. Route:
  `IsSemiformula.sound` → F (m-1)-ary, ⌜F⌝=body; F fv-free; `subst (fvarSeq m)` both sides
  (`subst_fvarSeq_fixitr` rhs, `subst_fvarSeq_succ`+`subst_fvarSeq_quote` lhs) ⟹ `ψ = F⇜(&·)`,
  free vars <m-1, contradicting `ψ.FVar?(m-1)`. ⚠️ `Semiformula.quote_inj_iff` needs `(V:=ℕ)(L:=ℒₒᵣ)`
  explicit (ambiguous with `Bootstrapping.Semiformula.quote_inj_iff`); `natCast_nat` normalizes the
  `(k:V)` cast; `rw [← heq] at hfv` rewrites ψ in the INDEX too — use `apply ... ; rw [heq]` instead.

REMAINING (priority order):
1. **mem_iff (⇐)** — `∃ p₀, χ = univCl (succInd p₀)` ⟹ `IsInductionAxiomCode (⌜χ⌝:ℕ)`. Canonical
   witness p=⌜p₀⌝, m=`(succInd p₀).fvSup`, body=⌜fixitr 0 m ▹ succInd p₀⌝, ψ:=succInd p₀. Conjuncts:
   `⌜χ⌝=qqAllItr body m` (`quote_univCl_eq_qqAllItr`); body fv-free m-ary (`quote_isSemiformula` +
   `shift_quote_fixitr`); criticality m=0∨¬(..) — m>0 case is **`not_criticality_aux`** (DONE);
   subst-eq `subst (fvarSeq m) body = succIndCodeRaw ⌜p₀⌝` via `subst_fvarSeq_fixitr` + `succIndCodeRaw_quote`.
2. **mem_iff (⇒)** — `IsInductionAxiomCode (⌜χ⌝:ℕ)` ⟹ `∃ p₀, χ = univCl (succInd p₀)`. Decode p,m,body
   (`IsSemiformula.sound` on p ⟹ p₀; succIndCodeRaw-inversion); from subst-eq + fv-free + criticality
   ⟹ body=⌜fixitr 0 m ▹ succInd p₀⌝, m=fvSup, χ=univCl(succInd p₀). Reuses the same machinery.
3. **`ch : 𝚫₁.Semisentence 1`** + `Defined IsInductionAxiomCode ch` — INDEPENDENT of (1)/(2), pure
   assembly via `HierarchySymbol.Semiformula` combinators (`bexs`/`ball`/`⋏` + `ProperOn.*`/`val_*`)
   over the component graphs (`succIndCodeRawGraph`, `qqAllItrGraph`, `fvarSeqGraph`, `substsGraph`,
   `isSemiformula`). Then `isDelta1 := ProvablyProperOn.ofProperOn`. **Tractable; no deep reflection.**
4. Assemble `inductionSchemeUnivDelta1 := { ch, mem_iff, isDelta1 }`; rewire `Reduction.lean`
   (`peano_not_proves_consistency := @consistent_unprovable 𝗣𝗔 paDelta1 _ _`) ONLY when sorry-free
   (anti-fraud). Headline ALSO needs crux 2 — still DEEP-REFLECTION-blocked.

## ⭐ Lap 80 — `inductionSchemeUnivDelta1`: recognizer is 𝚫₁; mem_iff blocked on bv-reflection

**Build 🟢 green; 6 green commits this lap.** All `PADelta1.lean` lemmas `#print axioms`-clean
`[propext, Classical.choice, Quot.sound]`. Lone sorry still = `inductionSchemeUnivDelta1`.

DONE this lap (all axiom-clean, in `PADelta1.lean`):
- **3a `quote_univCl_eq_qqAllItr`**: `⌜univCl ψ⌝ = qqAllItr ⌜fixitr 0 fvSup ▹ ψ⌝ fvSup`. The forward
  bridge for mem_iff (⇐).
- **`succIndCodeRawGraph`** (`𝚺₁.Semisentence 2`) + `succIndCodeRaw.defined` — concrete model-indep
  graph chaining numeral/substs1/qqBvar/qqAdd/imp/qqAll graphs (needed to reference inside `ch` DSL).
- **`IsInductionAxiomCode`** (the recognizer predicate over V) + `isInductionAxiomCode_definable :
  𝚫₁-Predicate` (via `definability`). ⟹ **the recognizer being Δ₁ is machine-checked** — the math
  heart. `IsFVFree` inlined as `IsSemiformula ∧ shift=self` so definability sees only 𝚫₁ atoms.
- **mem_iff (⇐) conjunct lemmas**: `freeVariables_fixitr_eq_empty`, `shift_quote_fixitr` (fv-free
  body's quote is shift-fixed), `fvar?_fvSup_pred` (fvSup tight: var `fvSup-1` is free when fvSup>0).

REMAINING (the genuine wall — DEEP Foundation-internal reflection):
1. **CRITICALITY (⇐), the crux**: for canonical witness m=`(succInd ψ).fvSup`>0, body=⌜fixitr 0 m ▹
   succInd ψ⌝, must show `¬ IsSemiformula ℒₒᵣ (m-1) body`. Via `IsSemiformula.def`
   (`IsSemiformula L n p ↔ IsUFormula L p ∧ bv L p ≤ n`, `Formula/Basic.lean:1208`) this is
   `m ≤ bv ℒₒᵣ ⌜φ''⌝`. **BLOCKED**: no Foundation lemma computes `bv ℒₒᵣ ⌜φ⌝` from φ's syntactic
   bound-var usage; `fvar?_fvSup_pred` gives the syntactic fact (φ''=fixitr uses `^#(m-1)`) but
   reflecting "`^#(m-1)` occurs ⟹ bv ≥ m" through the quote needs a NEW structural-induction lemma
   `bvQuote : bv ℒₒᵣ ⌜φ⌝ = <syntactic max-bv+1 of φ>` (or a lower-bound version). Aristotle CANNOT
   help (Foundation not in its mathlib-v4.28 env). Attack: induct on φ with `quote_rel/all/...` +
   `bv_all/bv_rel/...` structural lemmas; OR the subst-truncation route (if body were (m-1)-ary,
   `subst (fvarSeq m) body = subst (fvarSeq(m-1)) body` so result lacks free var m-1, contradicting
   `succInd ψ` having free var m-1 — but this ALSO needs a `subst`-ext-on-first-n lemma +
   free-var-occurrence reflection, equally deep).
   **⭐ KEY UNLOCK FOUND (lap 80): `IsSemiformula.sound`** (`Formula/Coding.lean:323`):
   `IsSemiformula L n (φ:ℕ) → ∃ F : SyntacticSemiformula L n, ⌜F⌝ = φ` — internal semiformula codes
   at ℕ ARE quotes. **Criticality route via sound** (avoids building `bvQuote` from scratch):
   work at V=ℕ. Suppose `IsSemiformula ℒₒᵣ (m-1) ⌜φ''⌝` (φ''=fixitr 0 m ▹ succInd ψ, m=fvSup>0).
   `sound` ⟹ ∃ F:(m-1)-ary, `⌜F⌝ = ⌜φ''⌝` (ℕ). Apply internal `subst ℒₒᵣ (fvarSeq m)` to both:
   RHS = `⌜succInd ψ⌝` (subst_fvarSeq_fixitr). LHS: F is (m-1)-ary so the length-m vector's entry m-1
   is unread ⟹ `subst (fvarSeq m) ⌜F⌝ = subst (fvarSeq(m-1)) ⌜F⌝` [**needs subst-congruence lemma**,
   below] `= ⌜F ⇜ (fun i:Fin(m-1)↦&i)⌝` (typed_quote_substs + fvarSeqVec_val). So syntactically
   `succInd ψ = F ⇜ (&·)`; but the opened (m-1)-ary F has free vars ⊆ {0..m-2} ⟹ `(succInd ψ).fvSup
   ≤ m-1 = fvSup-1`, contradicting fvSup>0. The ONE reusable lemma to build:
   **`subst_eq_subst_of` (formula subst congruence)**: `IsSemiformula ℒₒᵣ n p → (∀ i<n, w.[i]=w'.[i])
   → subst ℒₒᵣ w p = subst ℒₒᵣ w' p` — mirror `subst_eq_self` (`Functions.lean:710`,
   `IsSemiformula.pi1_structural_induction`); needs a term-level `termSubst_eq_termSubst_of` too
   (mirror `termSubst_eq_self`, `Term/Functions.lean:145`). Plus `freeVariables (F⇜(&·)) ⊆ {0..m-2}`
   (free vars of an open of an (m-1)-ary formula by &0..&(m-2)) — likely via `Rew`/`freeVariables`
   structural simp on `⇜`.
2. **mem_iff (⇒)**: decode p,m,body; from `subst (fvarSeq m) body = ⌜succInd ψ⌝` + body fv-free m-ary +
   criticality ⟹ body = ⌜fixitr 0 m ▹ succInd ψ⌝ and m=fvSup (fixitr-inversion injectivity). Uses
   `subst_fvarSeq_fixitr` (banked) + `IsSemiformula.sound` (same unlock) + `subst_eq_subst_of`.
3. **`ch : 𝚫₁.Semisentence 1`** + `Defined IsInductionAxiomCode ch`: INDEPENDENT of (1)/(2) — build via
   the `HierarchySymbol.Semiformula` combinators `bexs`/`ball`/`⋏` (have `ProperOn.bexs/.ball/.and` +
   `val_bexs/...` for free ProperOn+eval) over the component graphs (`succIndCodeRawGraph`,
   `qqAllItrGraph`, `fvarSeqGraph`, `substsGraph`, `isSemiformula`, graphDelta of each). Then
   `isDelta1 := ProvablyProperOn.ofProperOn` + `Defined.proper`; `mem_iff` at ℕ via `Defined.iff` +
   the (1)+(2) bridge. **This is the next tractable chunk** (no deep reflection; pure assembly).

## ⭐ Lap 79 — `PA_delta1Definable` front A: brick 2a (`qqAllItr`) DONE; next = free→bound rewrite

Front A (`inductionSchemeUnivDelta1`) decomposes the internal `univCl'` recognizer `closeAll` into
TWO independent pieces. **`closeAll p = qqAllItr (freeToBound m p) m` where `m = fvSup p`**, mirroring
`univCl' φ = ∀⁰* (Rew.fixitr 0 φ.fvSup ▹ φ)` (`Basic/Syntax/Rew.lean:420`).

- ✅ **brick 2a DONE (lap 79, axiom-clean): `qqAllItr p k = ^∀^[k] p`** — PR.Construction, `𝚺₁-Function₂`,
  `qqAllItr_succ'` (front-peel) + `qqAllItr_quote` (`qqAllItr ⌜φ⌝ n = ⌜∀⁰* φ⌝`). `PADelta1.lean §Brick 2a`.
- ✅ **brick 2b DONE (lap 79, axiom-clean): `freeToBound`** (the forward `Rew.fixitr 0 m` analog) —
  term-level `termFreeToBound d t` (`^&x↦^#(x+d)`, `TermRec`) + formula-level `freeToBound d p`
  (`UformulaRec1`, depth-threaded, full rel/nrel/⊤/⊥/∧/∨/∀/∃ simp set), both `𝚺₁-Function₂`.
  **BANKED ASSET — but the recognizer below does NOT use it** (see pivot).
- ⚠️ **PIVOT (lap 79): the recognizer goes BACKWARD via existing `subst`, not forward via `freeToBound`.**
  Matching `freeToBound ⌜φ⌝ = ⌜Rew.fixitr 0 m ▹ φ⌝` hits a dependent-arity wall: `(Rew.fixitr n m).q =
  Rew.fixitr (n+1) m` is ILL-TYPED (codomains `n+m+1` vs `n+1+m`, not defeq) — Foundation omits it on
  purpose. Cleaner recognizer reusing **existing** Foundation lemmas (`subst_comp_fixitr`,
  `typed_quote_substs`):
  `ch(y) := ∃ p ≤ y, IsSemiformula 1 p ∧ ∃ m ≤ y, ∃ body ≤ y, y = qqAllItr body m ∧ L.IsFVFree m body ∧`
  `(m = 0 ∨ ¬ L.IsFVFree (m-1) body) ∧ subst ℒₒᵣ (fvarSeq m) body = succIndCodeRaw p`
  where `fvarSeq m = ⟨^&0,…,^&(m-1)⟩` (internal). KEY BRIDGES (all from existing Foundation):
  · `qqAllItr_quote` (DONE) gives `⌜univCl(succInd ψ)⌝ = qqAllItr ⌜fixitr 0 m ▹ succInd ψ⌝ m`, m = fvSup.
  · `subst (fvarSeq m) ⌜fixitr 0 m ▹ ψ⌝ = ⌜(fixitr 0 m ▹ ψ)⇜(&·)⌝ = ⌜ψ⌝` via `typed_quote_substs` +
    `subst_comp_fixitr` (`Basic/Syntax/Rew.lean:412`, `(fixitr 0 m ▹ φ)⇜(&·) = φ`). Soundness: `body`
    fv-free m-ary ⟹ `subst (fvarSeq·)` is injective (inverse of fixitr), so `body` is pinned.
  · `IsFVFree`-pin replaces the need for an internal `fvSup` function (m forced = fvSup, max bound +1).
  DONE pieces (lap 79, all axiom-clean): (1) ✅ `fvarSeq` (brick 2c) `.[i]=^&i`, `IsSemitermVec`;
  (2) ✅ `subst_fvarSeq_fixitr` (brick 2d) = `subst ℒₒᵣ (fvarSeq m) ⌜fixitr 0 m ▹ φ⌝ = ⌜φ⌝` via
  `fvarSeqVec_val` + `typed_quote_substs` + `subst_comp_fixitr`. **THE crux bridge is banked.**
  REMAINING assembly pieces:
  · (3a) the univCl↔qqAllItr bridge: `(⌜univCl ψ⌝ : V) = qqAllItr ⌜Rew.fixitr 0 ψ.fvSup ▹ ψ⌝ ψ.fvSup`
    — combine `qqAllItr_quote` (`qqAllItr ⌜φ'⌝ n = ⌜∀⁰* φ'⌝`) with `coe_univCl_eq_univCl'`
    (`(univCl ψ : SyntacticFormula) = univCl' ψ = ∀⁰* (fixitr 0 ψ.fvSup ▹ ψ)`) + `Sentence.quote_def`.
  · (3b) build `ch : 𝚫₁.Semisentence 1` as the bounded-∃ recognizer (see ch formula above; uses
    `succIndCodeRaw`, `subst ℒₒᵣ (fvarSeq ·)`, `qqAllItr`, `IsFVFree`/`IsSemiformula`-pin graphs).
  · (4) `mem_iff` at ℕ. (⇐) χ=univCl(succInd ψ): witness p=⌜ψ⌝, m=fvSup, body=⌜fixitr..⌝, close with
    (3a)+(3b)+`succIndCodeRaw_quote`+`subst_fvarSeq_fixitr`. (⇒) decode p=⌜ψ⌝ (IsSemiformula 1), m,body;
    from `subst (fvarSeq m) body = ⌜succInd ψ⌝` + body fv-free m-ary ⟹ body=⌜fixitr 0 m ▹ succInd ψ⌝
    (injectivity / inverse — the one nontrivial sub-argument left), then y=⌜univCl(succInd ψ)⌝∈scheme.
  · (5) `isDelta1` (`ProvablyProperOn.ofProperOn` + properness of the bounded ∃).
  Then rewire `Reduction.lean`: `peano_not_proves_consistency := @consistent_unprovable 𝗣𝗔 paDelta1 _ _`.

Front B (crux-2 criticality redesign) stays DEEP-REFLECTION-blocked — see lap-78 box below.

## ⭐⭐⭐ Lap 78 (FRESH-MIND REVIEW) — crux-2 rung-2 is ARCHITECTURE-BLOCKED; pivot to `PA_delta1Definable`

**Read `ANALYSIS-2026-06-24-lap78-criticality-substitution-wall.md` FIRST.** The lap-77 plan ("front A:
generalize `ZDerivation_zsubst` to `aNotEigen d` + `a ∉ FV(conclusion)`") is **insufficient** — proven by
two explicit counterexamples:
- **CE-1**: inner chain conclusion `s'` containing `^&a` ⟹ `aNotEigen`-only does NOT rule out the
  criticality collapse (`^∀(^&a=^&a)` vs `^∀(0=^&a)` both → `^∀(0=0)` under `a↦0`).
- **CE-2**: even with **full Buchholz regularity** (`^&a` only in `F(·)`-occurrences), a substituted
  numeral `i` coinciding with a conclusion term `F(i)` collapses criticality. Rung 2 substitutes the
  whole range `i=0…k-1`, so any inner chain concluding `F(j)`, `j<k`, is hit.

⟹ `ZDerivation_zsubst` cannot be the exact-validity-preserving lemma rung 2 needs. **The chain-rule
criticality design (formula-inequality `tp dᵢ ≠ seqSucc s`, `InternalZ.lean:1204`) is the problem.**
Fork (a DEEP-REFLECTION decision, NOT a grind snap-pick): (1) re-reduction semantics; (2) **structural
criticality** — track the principal premise by index/rank not syntactic inequality (most principled,
matches Buchholz operator-control; largest rewrite); (3) restrict + discharge a side-condition (cheapest,
likely false). **Recommend option 2 when this is next revisited at altitude.**

**This lap pivots to the second front `PA_delta1Definable`** (mandatory for the axiom-free headline; the
operator's literal instruction). Status: `𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`. Foundation has
`Theory.Δ₁` combinators for `∅`/`{φ}`/`T+U`/`insert` (so FINITE theories are reachable) but **NO**
`InductionScheme.Δ₁` (the infinite scheme — the real wall). `𝗣𝗔⁻` is finite (`= 𝗘𝗤 ∪ {17 axioms}`) but
has no `Δ₁` instance yet either. Attack order: (a) `𝗣𝗔⁻.Δ₁` via the finite combinators (tractable brick);
(b) `(InductionScheme ℒₒᵣ Set.univ).Δ₁` = build internal `succInd`/`univCl` recognizer (the multi-lap
arithmetization). `ZDerivation_zsubst` (`d≤a` form) stays banked + axiom-clean.

## ⭐ Lap 76 — rung-1 `ZDerivation_zsubst` 6/7; zK case + a DESIGN OBSTRUCTION (read first)

`ZDerivation_zsubst` (`Zsubst.lean`, end) is proven for atom/zIall/zIneg/zInd/zAxAll/zAxNeg; the **zK
case is a `sorry`** (the lone open hole in the file). Groundwork bricks landed this lap:
- `irk_fvSubst` — `irk (fvSubst a t A) = irk A` (rank invariance; the `isChainInf` rank ingredient). ✅
- `iperm_tp_zsubst` — the **positive** permissibility transfer (Lemma 3.3 conjunct of `zKValid`):
  `iperm (tp d) q → iperm (tp (zsubst d a t)) (fvSubstSeqt a t q)` for `ZDerivation d`. ✅

**⚠ OBSTRUCTION found while proving `iperm_tp_zsubst` (design-level, needs a decision):**
The `zKValid` **criticality** conjunct `¬ iperm (tp di) s` does **NOT** transfer under `fvSubst` the way
the positive `iperm` does. `iperm`'s R-case asks `principalFormula = seqSucc q`; `fvSubst` is *not*
injective on formulas (it collapses `^&a`→`t`), so a chain that was critical (`^∀F(^&a) ≠ seqSucc s`) can
become NON-critical after substitution if `seqSucc s = ^∀F(t)`. I.e. substitution can manufacture a
spurious permissibility match against the conclusion `s`. So the `zK` case of `ZDerivation_zsubst` as
*currently stated* (arbitrary `a`, only `d ≤ a`) is likely **not provable / not true** without an
**eigenvariable-freshness hypothesis** `a ∉ FV(s)` (or `a ∉ FV` of every chain conclusion in `d`).
Three resolutions to weigh next lap (likely needs a fresh-mind judgement, see how-to-get-unblocked):
1. **Add a freshness hypothesis** to `ZDerivation_zsubst` (`a` not occurring free in `d`'s sequents).
   Buchholz's actual reduct substitutes a numeral for the *eigenvariable*, which by the eigenvariable
   side-condition is fresh for all surrounding sequents — so a freshness hypothesis is FAITHFUL, not a
   cheat. Then criticality transfers (no spurious match: `^&a` absent from `s`). The cost: thread
   freshness through the I∀/Ind premises (an inner eigenvariable may equal `a` — but those are
   bound-and-renamed; `zIndWff`/`zIallWff` already pin `e`-freshness). **Recommended — matches the math.**
2. Restrict `ZDerivation_zsubst` to derivations with **no `zK` nodes** (does rung 2's Ind reduct ever
   substitute into a `d1` that contains chains? if chain-free this suffices — CHECK what rung 2 feeds).
3. Define a Δ₁ freshness predicate `aFreshIn d` and carry it; heavier but fully general.

Next lap: pick (1), add `(hfresh : ...)`, redo the zK case using `iperm_tp_zsubst` (positive) + a
`¬iperm` transfer that now goes through because `^&a ∉ s`. The other 6 cases are freshness-agnostic
(already proven) — only the statement gains a hypothesis they ignore.

## Reflection — 2026-06-24 (lap 74, DEEP) — direction KEPT; three sharpenings

Full write-up: `REFLECTION-2026-06-24-lap74.md`. Synthesis for the grind:

**Direction call: KEEP, re-validated from altitude.** crux 2 (internalized finitary-Buchholz-Z
cut-elimination) is the right, *unavoidable* target — PROVED this lap: the banked free-X
`peano_not_proves_TI` is the wrong shape (`γ` can't imply free-`X` TI), the specific-instance route
still needs Gentzen, and the meta-level monument can't be reused internally. No ε₀-strength-free proof
of an ε₀-strength independence result exists. A future lap must NOT re-litigate "resurrect the monument."

**KEEP doing:** the RedSound rung ladder (0.5 ✅ → 1 `zsubst` → 2 Ind reduct → 3 K/cut reduct → 4
dispatch); the reusable `iord`/ω-tower ordinal *assignment* machinery; the lap-71 cascade recipe for
ZPhi side conditions; banking (not deleting, not resurrecting) the Thm-5.6 monument.

**STOP doing:** (1) extending `iR2`/`iCritReduct` infrastructure — lap 70 proved that reduct is NOT
validity-preserving; it is SUPERSEDED by the genuine Option-A reduct. Every new `iR2`-shaped lemma is
on the dead path. The genuine reduct re-fits BOTH validity (RedSound) AND its own descent
`o(R d)≺o(d)`; reuse the C3 templates, not the `iord_iR2_iterate_descends` assembly. (2) treating
`PA_delta1Definable` as an acceptable disclosed residual (operator: axiom-free or abandoned).

**Highest-value next target (re-endorsed):** finish **`ZDerivation_zsubst`** (rung-1 step 2) — see the
lap-73 box below for the resolved plan (freshness via `d ≤ a` code-bound; close the well-formedness gap
by adding `IsSemiformula`/`IsUFormula` to `zIallWff`/`zIndWff`/`zInegWff`, start `zInegWff`). It unblocks
the genuine Ind reduct (rung 2), the more tractable of the two genuine reducts.

**SECOND FRONT (advance when the ladder blocks — design soak / build wait):** `PA_delta1Definable`
(Foundation `Incompleteness/Examples.lean:17`, still an `axiom` upstream + in our pin; arithmetize PA's
induction-scheme Δ₁-definability). Independent of crux 2, mandatory for axiom-free, untouched by any lap
— the biggest non-cut-elimination risk to the endpoint. Bounded (no deep math) but substantial.

**Deferred (after RedSound):** the C0.5 Foundation→Z bridge (`¬Con(PA)` ⟹ a Z ⊥-derivation); blueprint
= Bryce–Goré `Peano.v` 3-layer shape in `archive/findings/ON-LINE-FINDINGS-2026-06-24-bryce-gore-gentzen.md`.

## ⭐⭐⭐ Lap 74 (grind) — WELL-FORMEDNESS GAP (B) CLOSED + Δ₁-motive finding for `ZDerivation_zsubst`

**Landed (green 1323, axiom-clean):** the lap-73 blocker (B) is discharged. Strengthened all three
I-rule `…Wff` predicates with principal-formula formula-hood, via the lap-71 cascade recipe (body +
`…WffDef` σ/π + `_defined` simp; the `isUFormula`/`isSemiformula` splice auto-discharges under
`HierarchySymbol.Semiformula.val_sigma`, no extra `.iff` needed — confirmed by `zKValid` + Foundation's
`IsFormulaSet` precedents):
- `zInegWff p d0` += `IsUFormula ℒₒᵣ p` (σ: `!(isUFormula ℒₒᵣ).sigma p`).
- `zIallWff s a p d0` += `IsSemiformula ℒₒᵣ 1 p` (σ: `!(isSemiformula ℒₒᵣ).sigma 1 p`).
- `zIndWff d` += `IsSemiformula ℒₒᵣ 1 (zIndP d)` (same, on the bound matrix var `p` already in scope).
The strengthened inversions (`zDerivation_zIneg_inv`/`_zIall_inv`/`_zInd_inv`) now surface this for free;
no construction site existed, so zero ZPhi-cascade churn. These feed `fvSubst_inegF` (`IsUFormula`),
`fvSubst_all` (`IsUFormula` via `.isUFormula`), `fvSubst_substs1_fvar` (`IsSemiformula 1`).

**⚠ KEY FINDING for `ZDerivation_zsubst` (the motive must NOT carry unbounded ∀a/∀t).** The naive motive
`P d := ∀ a, d ≤ a → ∀ t, IsSemiterm 0 t → ZDerivation (zsubst d a t)` is **Π₁, not Δ₁** — so it fails
`zDerivation_induction`'s `𝚫₁-Predicate P` requirement. **FIX: fix `a t` OUTSIDE the induction.** State
```
theorem ZDerivation_zsubst {a t : V} (ht : IsSemiterm ℒₒᵣ 0 t) :
    ∀ d, ZDerivation d → d ≤ a → ZDerivation (zsubst d a t)
```
with motive `P d := d ≤ a → ZDerivation (zsubst d a t)` — now Δ₁ (`d ≤ a` Δ₀ + `ZDerivation` Δ₁ ∘ `zsubst`
Σ₁-function, params `a t` fixed). IH threads: child `d0 < d ≤ a ⟹ d0 ≤ a`; eigenvar `e < d ≤ a ⟹ e ≠ a`
(zIall: `a_lt_zIall`; zInd: `e = π₁ at' ≤ at' < zInd` via `pi₁_le_self`+`at_lt_zInd`) discharges
`fvSubst_substs1_fvar`'s `a'≠a`. Build per case via `zDerivation_iff.mpr` 7-tag (mirror
`isNF_iotil_of_ZDerivation`'s rcases at `InternalZ.lean:3792`). Definability of `P`: `ZDerivation`'s
fixpoint-definable instance ∘ `zsubst_definable` + `≤`/`→` combinators (try `definability`).
zK case = the hard one (per-premise IH via `znth_zsubstTable_eq_zsubst` + `zKValid` transfer under subst,
needs `tp`/`iperm` subst-invariance — CHECK). Caveat (lap 73): rung 2's `zsubst d1 at' j` may need a true
`a∉eigenvars(d)` predicate, not just `d ≤ a` — prove the `d ≤ a` version first.

## ⭐⭐⭐ Lap 73 — RUNG 1 STEP 1 DONE + STEP 2 SUBSTRATE COMPLETE (`fstIdx_zsubst`, full subst-commutation)

**Landed (green 1323, all axiom-clean `[propext, Classical.choice, Quot.sound]`):**
- **Step 1 DONE** (`Zsubst.lean`): `zsubst` table structural correctness (`zsubstTable_seq/_lh`,
  `znth_zsubstTable_eq_zsubst`, `zsubst_eq_zsubstNext`), the 7 per-rule recursion equations
  (`zsubst_zAtom`…`zsubst_zAxNeg`), and **`fstIdx_zsubst : ZDerivation d → fstIdx (zsubst d a t) =
  fvSubstSeqt a t (fstIdx d)`** (7-way `zDerivation_iff` case split).
- **Step 2 SUBSTRATE COMPLETE** (`FvSubst.lean` general-`L`, + 2 lemmas in `Zsubst.lean`):
  `IsUTerm.termFvSubst`/`IsUTermVec.termFvSubst` (UTerm preservation), `IsUFormula.fvSubst`,
  `fvSubst_neg`, `inAnt_fvSubstSeq`, `fvSubst_inegF`, `termBShift_eq_self_of_closed`,
  `termFvSubst_termBShift`, `termFvSubstVec_qVec`, **`termFvSubst_termSubst`** (term subst lemma),
  **`fvSubst_subst`** (formula subst lemma, `pi1_structural_induction`, mirror `substs_substs`), and
  **`fvSubst_substs1_fvar : a'≠a → fvSubst a t (substs1 ^&a' p) = substs1 ^&a' (fvSubst a t p)`**
  (Buchholz regularity; the zIall/zInd succedent transfer). `t` always closed (`IsSemiterm ℒₒᵣ 0 t`).

**NEXT — `ZDerivation_zsubst` assembly (rung-1 step 2 proper). Two findings (design RESOLVED):**

**(A) Freshness = the `d ≤ a` code-bound (no tree predicate needed).** Every internal eigenvariable
`e` of a node `n ≤ d` satisfies `e < n ≤ d` (zIall: `a_lt_zIall : a' < zIall…`; zInd: `e = π₁ at' ≤ at'
< zInd…` via `pi₁_le_self` + `at_lt_zInd`). So state
`ZDerivation_zsubst : ZDerivation d → d ≤ a → IsSemiterm ℒₒᵣ 0 t → ZDerivation (zsubst d a t)`
with motive `P d := ∀ a, d ≤ a → ∀ t, IsSemiterm ℒₒᵣ 0 t → ZDerivation (zsubst d a t)` over
`zDerivation_induction`. Children `< d ≤ a` ⟹ IH applies (`d0 < d ≤ a → d0 ≤ a`); eigenvariables
`e < d ≤ a ⟹ e ≠ a` (`ne_of_lt`), discharging `fvSubst_substs1_fvar`'s `a'≠a`. Build via
`zDerivation_iff.mpr` (one-step) → `ZPhi {ZDerivation} (zsubst d a t)`, 7-tag.
⚠ CAVEAT: rung 2 invokes `zsubst d1 at' j` (eigenvariable `at'`, numeral `j`) — needs `d1 ≤ at'`,
NOT guaranteed by `at' < zInd` alone. So `d ≤ a` may need generalizing to a genuine
"a ∉ eigenvars(d)" tree predicate for the rung-2 USE (a fixpoint/cov predicate). Prove the `d ≤ a`
version first (correct + provable), generalize only if rung 2 forces it.

**(B) WELL-FORMEDNESS GAP — the real blocker.** The commutation lemmas need principal-formula
formula-hood that `ZPhi` does NOT currently carry: `fvSubst_all` needs `IsUFormula p` (zIall/zInd
succedent), `fvSubst_inegF` needs `IsUFormula p` (zIneg), `fvSubst_substs1_fvar` needs
`IsSemiformula ℒₒᵣ 1 p` (zIall/zInd matrix). `zAxAll`/`zAxNeg` disjuncts ALREADY carry `IsUFormula p`;
I∀/I¬/Ind do NOT. **Fix = lap-71 cascade**: add `IsSemiformula ℒₒᵣ 1 p` to `zIallWff`/`zIndWff` and
`IsUFormula ℒₒᵣ p` to `zInegWff` (both `𝚫₁`: `isSemiformula L`/`isUFormula L` Defs exist). Blast radius
is SMALL — the `ZPhi` plumbing (`zphi_monotone`/`_strong_finite`/`zphi_iff`/blueprint σ-π/`zPhi_definable`)
threads `…Wff` OPAQUELY; only the `…WffDef` + `_defined` proof change, and the `_inv` lemmas return more
(callers unaffected). Risk: the `_defined` 𝚫₁ proof (mirror how `zKValidDef` embeds `(isUFormula ℒₒᵣ).sigma/.pi`
under `val_sigma`). Start with `zInegWff` (binary, fewest sites: def 1264, Def 1269, _defined 1279, σ-core
3709, π-core 3727, definable 3747, inv 4853), validate the recipe, then zIall/zInd.

**Assembly per-case sketch (after B):** atom→`inAnt_fvSubstSeq` (no fresh/IH); zIall→IH(d0)+`fvSubst_all`+
`fvSubst_substs1_fvar`(a'≠a)+`seqAnt` via `fvSubstSeq`; zIneg→IH+`fvSubst_inegF`; zInd→2×IH+numeral/qqAdd
commutation (`termFvSubst` of `numeral 0`/`qqAdd (^&a) (numeral 1)` — numerals closed so fixed; need
`termFvSubst_numeral`/`_qqAdd` helpers); zK→per-premise IH via `znth_zsubstTable_eq_zsubst`+`zKValid`
transfer (iperm/tp invariance under subst — likely needs `tp_fvSubst`/`iperm` subst-invariance, CHECK);
zAxAll/zAxNeg→`IsUFormula.fvSubst`+`inAnt_fvSubstSeq`. Then step 3 `iotil_zsubst = iotil` (õ subst-inv).

## ⭐⭐⭐ Lap 72 — RUNG 1 `zsubst` DEFINED (eigenvariable substitution on Z-derivations)

**Landed (green 1323, axiom-clean), see `HANDOFF-2026-06-24-lap72.md` for the full ledger:**
- `src/GoodsteinPA/FvSubst.lean` (new `module`): `termFvSubst a t u` (term-level free-var subst
  `^&a↦t`, `Language.TermRec`) + `fvSubst a t p` (formula-level, `UformulaRec1`, param `⟪a,t⟫`,
  identity `allChanges` since `t` closed) + definability + `fvSubst_isSemiformula` (preservation,
  closed `t`). Resolves PENDING's open "free-var subst is not `substs1`" design question.
- `src/GoodsteinPA/Zsubst.lean` (new): `fvSubstSeq`/`fvSubstSeqt` (seq/sequent subst), `tblMapSeq`
  (zK premise table-map), `zsubstNext` (7-tag table step), `zsubst d a t` (course-of-values
  `<`-recursion, mirror `iRTable`/`iR2`), all `𝚺₁`-definable. Added `zIallEig`/`zAxAllK` accessors.

**NEXT — rung 1 CORRECTNESS (the def is in place; prove it does the right thing):**
1. `fstIdx_zsubst : fstIdx (zsubst d a t) = fvSubstSeqt a t (fstIdx d)` (diagonal table read-out, mirror
   `iR2`'s `znth_iRTable` lemmas in `InternalZ.lean` ~4380+, then 7-tag `fstIdx (z* s' …) = s'`). EASIEST.
2. `ZDerivation_zsubst` (rung-1 correctness): child `<` bounds + per-rule subst-commutation + likely an
   eigenvariable-freshness hyp; drive by `ZDerivation`-induction + lap-70 `zDerivation_z*_inv`.
3. `iotil_zsubst = iotil` (õ subst-invariance; shape+rank based, `irk` subst-invariant — prove
   `irk_fvSubst` analog of `irk_substs1`). Likely EASIEST after (1).
Then **rung 2** (genuine Ind reduct) reachable. Cut-elim shape blueprint: `~/src/Gentzen/.../cut_elim.v`.

## ⭐⭐⭐ Lap 71 — FRESH-MIND REVIEW + rung-0.5 I¬ wired (cascade de-risked)

**Review:** direction KEPT (Option A forced lap 70, kernel re-verified: headline 0 math axioms; lap-70
landmarks clean; build green 1321). STATUS refreshed off stale lap-59/62 framing.

**Landed (green 1321, axiom-clean):** the rung-0.5 cascade is now PROVEN OUT on the simplest disjunct.
Moved `zInegWff` up before `ZPhi`, gave it `zInegWffDef : 𝚫₁.Semisentence 2` + `zInegWff_defined`
(`𝚫₁-Relation`, mirrors `zKValidDef` — all 𝚺₀ pieces: `fstIdx`/`seqSucc`/`seqAnt`/`^⊥`/`inAnt`), and wired
`∧ zInegWff p d0` into the I¬ disjunct across the WHOLE cascade: `ZPhi` def, `zphi_monotone`,
`zphi_strong_finite`, `zphi_iff` (both directions), `zblueprint` σ-core (`!(zInegWffDef.sigma) p d0`) +
π-core (`!(zInegWffDef.pi) p d0`), `zPhi_definable` simp (`+zInegWff_defined.iff`). **Only 2 inversion
sites broke** (the rest use `_` tails) — fixed `zTag_Ind_or_K_of_ZDerivesEmpty` (`hsc → hsc,_`) and
**STRENGTHENED `zDerivation_zIneg_inv`** to return `ZDerivation d0 ∧ seqSucc s = inegF p ∧ zInegWff p d0`
(the payoff: I¬ inversion now hands the premise-sequent data the genuine reduct reads).

**Cascade recipe (now battle-tested for I∀/Ind next):** (1) def the `…Wff` + `…WffDef : 𝚫₁.Semisentence n`
+ `_defined` instance ABOVE `ZPhi` (placed after `zKValid_definable`, ~line 1252); (2) add `∧ …Wff …` to
the `ZPhi` disjunct; (3) propagate the binder through `zphi_monotone`/`_strong_finite`/`zphi_iff` (×4
patterns); (4) `∧ !(…WffDef.sigma) …` into zblueprint σ-core, `∧ !(…WffDef.pi) …` into π-core; (5)
`+…Wff_defined.iff` to `zPhi_definable`'s second simp; (6) `lake build`, fix the ≤2 inversion sites that
name the disjunct's last conjunct — strengthen the corresponding `_inv` lemma to surface the `…Wff`.

**I∀ DONE (this lap too, green 1321, axiom-clean):** wired `zIallWff s a p d0` identically — moved up,
`zIallWffDef : 𝚫₁.Semisentence 4` (`substs1Graph ℒₒᵣ` for `seqSucc(fstIdx d0)=substs1 (^&a) p`, `qqFvarDef`
for `^&a`), `zIallWff_defined : 𝚫₁-Relation₄` (the σ/π simp needs `(substs1.defined (L := ℒₒᵣ)).iff` — `L`
must be pinned or instance synth fails), wired through the full cascade, and **STRENGTHENED
`zDerivation_zIall_inv`** to return `… ∧ zIallWff s a p d0` (recover the eigenvariable `a` via
`congrArg (fun d => π₁ (zRest d)) h` — there is no `zIallEig` accessor; `zRest (zIall s a p d0)=⟪a,p,d0⟫`).

**Ind DONE (this lap too — RUNG 0.5 COMPLETE, green 1321, axiom-clean):** `zIndWff` built as a UNARY
predicate on the whole node `d` (sidesteps the missing `𝚫₁-Relation₅` notation AND lets its body be
strengthened later WITHOUT re-running the cascade). Added accessors `zIndEig`/`zIndTerm` (`= π₁/π₂ (π₁
(zRest d))`, the `at'=⟪a,t⟫` decode) + their `𝚺₀` Defs; `zIndWffDef : 𝚫₁.Semisentence 1` +
`zIndWff_defined : 𝚫₁-Predicate`. Term-codes from Foundation `Bootstrapping.Arithmetic`: `numeral`
(`numeralGraph`; `numeral 0 = 𝟎`), `qqAdd` (`qqAddGraph`; `Sa = qqAdd (^&a) (numeral 1)`). Conditions:
`d0 ⊢ Γ→F(0)` (`seqAnt(fstIdx d0)=seqAnt s`, `seqSucc(fstIdx d0)=substs1 (numeral 0) p`), `d1 ⊢
F(a),Γ→F(Sa)` (`inAnt (substs1 (^&a) p) (seqAnt(fstIdx d1))`, `seqSucc(fstIdx d1)=substs1 (Sa) p`),
conclusion `seqSucc s = substs1 t p`. Wired `∧ zIndWff d` into the Ind disjunct across the cascade;
strengthened `zDerivation_zInd_inv` to return `… ∧ zIndWff (zInd s at' p d0 d1)` (recovering all 5
components from `h`). Gotchas: `numeral`/`qqAdd`/`numeralGraph`/`qqAddGraph` live in
`LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic` (not the bare `…Arithmetic`); the `𝚫₁-Predicate`
instance simp needs `and_assoc` to reconcile the right-nested core with `zIndWff`'s grouping.

⚠️ **`zIndWff` deliberately OMITS the `Γ ⊆ ant(d1)` threading** (the bounded-∀ `∀ i < lh(seqAnt s),
inAnt (znth (seqAnt s) i) (seqAnt(fstIdx d1))`) the genuine Ind reduct's `isChainInf` will need. Because
`zIndWff` is unary, ADDING that conjunct later only re-proves `zIndWffDef`/`zIndWff_defined` — it does NOT
touch the ZPhi cascade. Add it when building rung 2.

**NEXT — rung 1+ (the genuine reduct, the deep crux-2 core):**
- **rung 1 `zsubst d a n`** — Σ₁ eigenvariable substitution on Z-derivations (numeral `n` for free var `a`),
  `ZDerivation`-preserving + `iotil`-invariant + `fstIdx`-computing. Σ₁ recursion over the tree applying
  `substs1`/`Rew` per node. Multi-lap brick. (See lap-70 LADDER below for the full plan + sub-bricks.)
- **rung 2** genuine Ind reduct (most tractable — premises genuine, not `Rep`); **rung 3** genuine K/cut
  reduct; **rung 4** `RedSound` tag-dispatch → closes the descent → `Reduction.lean:68`.

## ⭐⭐⭐ Lap 70 — Option B REFUTED in-kernel; Option A (genuine reduct) ladder

**Finding (kernel-checked, `not_zKValid_iCritReduct`):** the ordinal-faithful `iR2` can NEVER preserve
`zKValid` — `iCritReduct`'s premises are chains (`iCritAux = zK …`, `tp = isymRep`, permissible
everywhere), breaking `zKValid`'s criticality conjunct, which the L3.1 redex finder requires. So lap-69's
**Option B is dead**; **`RedSound` is false for the current `iR2`**. (Cross-checked vs Bryce–Goré: their
`cut_elimination` is genuinely validity-preserving + shape-dispatched — `~/src/Gentzen/.../cut_elim.v`.)

**Buchholz genuine reductions (Def 3.2 / 14.23–14.25, `scratchpad/buchholz-gentzen.txt:184-265`):**
- **I¬ (14.23):** `d[0] := d0`. No substitution. ✅ `ZDerivation_iR2_zIneg` (lap 70, clean).
- **I∀ (14.23):** `d[n] := d0(a/n)` — eigenvariable `a` replaced by numeral `n` throughout `d0`.
- **Ind (14.24):** `d[0] := K^r⟨d0, d1(0), d1(1), …, d1(k−1)⟩`, `k = ⟦induction term⟧` (a numeral since
  `d` closed). Premises: `d0 : Γ→F(0)`, `d1(i) : F(i),Γ→F(i+1)`. **Valid chain** because each premise
  `d1(i)`'s antecedent formula `F(i)` is the PRIOR premise's succedent (threading ✓). Needs the
  substituted copies `d1(a/i)` + count `k`.
- **Chain/K (14.25):** the cut-elimination proper — shape-dispatched on the cut formula (atom/neg/∀).

**THE foundational brick = eigenvariable substitution on Z-derivations `zsubst : V→V→V→V`** (substitute
numeral `n` for free variable `a` throughout derivation `d`), Σ₁-definable + `ZDerivation`-preserving.
Building blocks in hand: Foundation's coded-formula substitution `substs1 ℒₒᵣ t p` (used already in
`irk_substs1`), rank-substitution-invariance `irk_substs1`, the peeling inversions
`zDerivation_zIall_inv`/`_zIneg_inv`/`_zAxAll_inv`/`_zAxNeg_inv` (lap 70). `zsubst` is a Σ₁ recursion over
the derivation tree applying `substs1` at each sequent — mirror the `iRTable`/`iCritReduct` blueprint
recursions. Multi-lap; build incrementally.

**LADDER (hardest-first within Option A; the Ind case is the more tractable wall — its reduct premises are
genuine sub-derivations, NOT `Rep`, so not definitionally blocked like the K-case):**
0.5. **PREREQUISITE — strengthen `ZPhi`'s I∀/Ind disjuncts with the premise-sequent + eigenvariable side
   conditions** (a Σ₁/Δ₁ Fixpoint cascade, exactly like laps 66/69's leaf + K cascades). The CURRENT
   `ZPhi` zIall disjunct is `d = zIall s a p d0 ∧ d0 ∈ C ∧ seqSucc s = ^∀ p` — it does NOT say `d0` derives
   `Γ→F(a)` (Buchholz I∀ requires `fstIdx d0 = mkSeqt (seqAnt s) (substs1 (^&a) p)` + `a ∉ conclusion`).
   Likewise the Ind disjunct omits `fstIdx d0 = Γ→F(0)` / `fstIdx d1 = F(a),Γ→F(Sa)`. **Without these the
   genuine reduct's THREADING (isChainInf) is unprovable** — after substitution `σi = zsubst d1 a i` you
   can't compute its sequent `F(i),Γ→F(i+1)`. (This under-constraining does NOT break the descent
   direction — the C0.5 bridge produces a genuine derivation that still satisfies the weaker `ZPhi`, and
   the ordinal descent uses only NF facts — but it DOES block `RedSound`.) Building block landed lap 70:
   `isChainInf_of_last` (reduces chain-validity to premise-local threading).
   ⚠️ **DESIGN DECISION needed first (lap-70 finding):** `at'` in `zInd s at' p d0 d1` is currently
   **opaque/unused** (never decoded; the Ind semantics F(0)/F(Sa)/F(t)/eigenvar/term are entirely
   unencoded). The cascade must DECODE it — recommend `at' = ⟪a, t⟫` (eigenvariable `a`, induction term
   `t`), accessors `zIndEig := π₁ at'` / `zIndTerm := π₂ at'`. Exact Buchholz Ind conditions (rules read
   lap 70, `scratchpad/buchholz-gentzen.txt:140-152`):
   - `seqAnt (fstIdx d0) = seqAnt s ∧ seqSucc (fstIdx d0) = substs1 ℒₒᵣ ‘0’ p`  (d0 ⊢ Γ→F(0))
   - `seqSucc (fstIdx d1) = substs1 ℒₒᵣ (S(^&a)) p ∧ inAnt (substs1 ℒₒᵣ (^&a) p) (seqAnt (fstIdx d1))`
     ∧ Γ-threading of `seqAnt (fstIdx d1)`  (d1 ⊢ F(a),Γ→F(Sa))
   - `seqSucc s = substs1 ℒₒᵣ t p`  (conclusion ⊢ Γ→F(t))
   Verify the term constructors first: `^&a` = `qqFvar a`; the successor term `S(^&a)`; `‘0’` numeral
   (used in `IRk.blueprint:312`). `substs1`/`inAnt` already Δ₁ — so the cascade is mechanical once the
   conditions + at'-decode are pinned. I∀ analog: `seqSucc (fstIdx d0) = substs1 ℒₒᵣ (^&a) p` with
   `at' → a` the eigenvariable (zIall already has the `a` slot).
1. **`zsubst d a n`** — Σ₁ derivation substitution. Sub-bricks: per-node sequent substitution (apply
   `substs1`/`Rew` to `fstIdx`), recurse on `zIallPrem`/`zInegPrem`/`zIndPrem0/1`/`zKseq`. Prove
   `ZDerivation_zsubst` (preserves validity) + `iotil_zsubst = iotil` (õ substitution-invariance — the
   ordinal side already assumes this; make it a theorem) + `fstIdx_zsubst` (the reduced end-sequent).
2. **Genuine Ind reduct `iRInd'`** = `zK s (irk p) ⟨d0, zsubst d1 at' 0, …, zsubst d1 at' (k−1)⟩` with
   `k = ⟦induction-term-of d⟧`. Build the substituted-block sequence (Σ₁ recursion reading `zsubst d1 at' i`
   at index `i`; mirror `iRepeatSeq`). Prove `zKValid` of it — the **threading** is the genuine content
   (premise `i+1`'s antecedent `F(i)` = premise `i`'s succedent; rank `irk(F(i)) ≤ r` via `irk_substs1`).
3. **`RedSound` for tag 3 (Ind)** falls out: `ZDerivation (iRInd' …)` from step 2's `zKValid` +
   `znth_…_ZDerivation`. Re-fit `iord_descent` to `iRInd'` (õ-side survives via `iotil_zsubst`).
4. **Genuine critical reduct (K-case, tag 4)** = the cut-elimination, shape-dispatched (Bryce–Goré
   `cut_elimination_atom`/`_neg`/`_lor`). Hardest. Peel R-redex (`zDerivation_zIall_inv` → `d0`, then
   `zsubst` for I∀) + L-redex (`zDerivation_zAxAll_inv`/`_zAxNeg_inv`) and splice into a chain whose
   premises are genuine (non-`Rep`) sub-derivations. Prove `zKValid` + re-fit `iord` descent.
5. **`RedSound`** (`∀ d, ZDerivesEmpty d → ZDerivation (iR2 d)`) = tag-dispatch on 3 (Ind) + 4 (K).
   Then `iord_iR2_iterate_descends` (already assembled) closes the descent → C0.5 bridge → `Reduction:68`.

**Banked lap 70 (all axiom-clean, green 1321):** `zDerivation_zIall_inv`/`_zIneg_inv`/`_zAxAll_inv`/
`_zAxNeg_inv`/`_zAtom_inv` (peeling), `not_zKValid_of_zK_premise`/`not_zKValid_iCritReduct` (obstruction),
`ZDerivation_iR2_zIall`/`_zIneg` (clean I-rule `RedSound` fragment), `isChainInf_of_last` (chain-validity
from premise-local threading), `iCritReductSeq_lh`/`znth_iCritReductSeq_zero`.

**Foundation substitution API (for `zsubst`):** `subst L w p` (vector subst, `Functions.lean:429`),
`substs1 L t p := subst L ?[t] p` (`:759`), `shift L p` (`:276`), `free p := substs1 L ^&0 (shift L p)`
(`:784`); free vars are `^&i` (`qqFvar`). Eigenvariable subst (free var `a` → numeral) is NOT `substs1`
(that's for bound var 0); needs a free-var replacement built from `subst`/`shift` — investigate next.

## ⭐⭐ Lap 67 — THE tag-4 K-case descent ASSEMBLED (`iord_descent_iR2_zK_of_valid`, axiom-clean)

The crux-2 ordinal nut for the chain/cut rule is machine-checked. `iord_descent_iR2_zK_of_valid`
(end of `src/GoodsteinPA/InternalZ.lean`) proves `o(iR2 (zK s r ds)) ≺ o(zK s r ds)` for a valid
`K^r` chain whose premises are `ZDerivation`s, **conditional on `zKValid s r ds`** (the Buchholz K^r
side conditions). Axiom-clean `[propext, Classical.choice, Quot.sound]`, green 1321 jobs.

Banked substrate this lap (all axiom-clean, all in `src/`):
- `tp_cases` (tp-trichotomy) + `tp_eq_isymR_of_pi₁_zero`/`tp_eq_isymLk_of_pi₁_one` + `isymIsR`/
  `pi₁_isym*` (π₁-discriminant 0/1/2) ⟹ `redexPair_tp`: read `tp(redexI)=R_A` ∧ `tp(redexJ)=L^k_A`
  (shared cut) off the bare `isRedexPair` finder least-pair.
- `iRedDescent_zAxReduct_of_iRedDescent` (wrap collapse via `icmp_trans`, handles the I-rule
  sub-derivation being an axiom leaf) + `iRedDescent_zAxReduct_iR2_of_tp_isymR` (i-side) /
  `_isymLk` (j-side) ⟹ the six ρ-facts of `iord_descent_iRcrit_of_chain'` at `ρ = zAxReduct∘iR2`.
- `zKValid s r ds` Prop bundle = `isChainInf` ∧ per-premise `iperm`(perm) ∧ `¬iperm`(crit) ∧ per-tag
  principal-formula `IsUFormula` (tags 1,2,5,6).

### ▶ NEXT PHASE (the one remaining structural gap): wire `zKValid` into the `ZPhi` `zK` disjunct
The bare `zK` disjunct is `Seq ds ∧ ∀ i<lh ds, premise ∈ C` — it does NOT carry `zKValid`, so a
genuine `ZDerivation`'s K-node doesn't yet hand you validity. Strengthen the `zK` disjunct to
`… ∧ zKValid s r ds` (faithful: an unconstrained premise sequence is NOT a valid system-Z `K^r`
inference). This is a Σ₁/Δ₁ **Fixpoint cascade** (one focused atomic pass, build only at the end):
1. **Definability of `zKValid` ingredients** (currently MISSING, all bounded/Δ₁ — build as blueprint
   `Def`s or inline): `seqAnt`/`seqSucc` (=π₁/π₂, trivial), `inAnt` (bounded ∃), `iperm` (Or of
   isym-equalities + `inAnt`), `chainAsucc`/`chainAnt` (=seqSucc/seqAnt∘fstIdx), `isChainInf`
   (bounded ∃ j0 + bounded ∀'s over `irk`/`inAnt`), `zAxAllF`/`zAxNegF` (=π₁∘zRest / zRest).
   `irk` is Σ₁ (`irkDef`), `IsUFormula` is Δ₁ (`(isUFormula ℒₒᵣ).sigma/.pi`).
2. Add `zKValid` (as Δ₁) to BOTH zblueprint Σ and Π cores (mirror how `IsUFormula` embeds
   `.sigma`/`.pi`), update `ZPhi` def + `zphi_monotone`/`zphi_strong_finite`/`zphi_iff`/`zPhi_definable`
   (the zK disjunct gets the extra conjunct; `zKValid` has no `C`-dependence so monotone/strong_finite
   are trivial on it), and the ~6 `rcases zDerivation_iff.mp` sites (zK pattern gains `hvalid`).
3. Then `zDerivation_zK_inv` yields `zKValid`; **extend `iord_descent_iR2_struct` tag-4 case** to
   `exact iord_descent_iR2_zK_of_valid hds hmem hvalid` (replacing the current `simp [zTag_zK] at htag`),
   dropping the `htag` restriction ⟹ the UNCONDITIONAL `ZDerivation d → icmp (iord (iR2 d)) (iord d)=0`.
NB: this cascade is sizeable but the pattern is known (lap-66 did the §5-leaf cascade). The descent
MATH is now entirely banked — only this faithfulness/definability wiring remains before the
no-infinite-descent → `ZDerivesEmpty d → False` → C0.5 bridge → `Reduction.lean:68`.

## ⭐ Lap 66 — crux-2 island promoted to src/ + green-gated; K-case j-side architecture pinned

**Done this lap:** (P0+P1a) Farmed goodstein-ab-xhigh's recursive-iR2 spine (3937 lines, the
architectural keystone) and PROMOTED it out of the un-built `wip/` island into
`src/GoodsteinPA/InternalZ.lean`, imported by the aggregator. `lake build GoodsteinPA` (1321 jobs)
now type-checks it every lap AND the sorry-gate scans it (it is sorry-free). Capstones verified
axiom-clean. Then banked the j-side §5 atomic-reduct bundle `iRedDescent_zAx1_zAxAll/_zAxNeg`.

**P1b (med graft) — NOT mergeable as-is.** goodstein-ab-med used an INCOMPATIBLE symbol encoding
(`iRsym C = ⟪0,C,0⟫+1`, `iLsym A k = ⟪1,A,k⟫+1`, `isymKind/isymFml` via `π₁(I-1)`) vs xhigh's
(`isymR A = ⟪0,A⟫`, `isymLk k A = ⟪1,k,A⟫`). med's atomic chain (`ZDerivesEmpty_descends_critical_atomic`,
60-decl closure) bottoms out on med's `tp`/`ZPhi`/`ZDerivation` over that encoding, so it does not
compile against the xhigh spine — grafting it = re-deriving against xhigh's layer, i.e. NEW work, not
a merge. xhigh ALREADY has the §5 atomic layer (`zAxAll`/`zAxNeg`/`zAx1`/`oAtom1`/`icmp_oAtom1_oAtomLk`),
so med's value is largely duplicated; do NOT spend laps porting med's encoding.

**THE pinned crux-2 frontier (the genuine remaining math, K-case = tag 4):**
`iord_descent_iR2_struct` proves the descent `o(iR2 d) ≺ o(d)` UNCONDITIONALLY for I-rules (tags 1,2)
and Ind (tag 3). The K-rule (tag 4) reduces — via `iord_descent_iRcrit_of_chain'` — to six `ρ`-facts
about the two redex premises (`ρ = iR2(znth ds ·)`):
  - **i-side (R-redex, an I-rule): DONE** concretely (`iRedDescent_iR2_of_tp_isymR`).
  - **j-side (L-axiom redex, tags 5/6): the BLOCKER.** `iR2` is the IDENTITY on atomic axioms
    (`iR2_zAxAll`/`iR2_zAxNeg` proven), so `ρ(redexJ)=znth ds j` and the required strict drop
    `icmp (iotil (ρ j)) (iotil (znth ds j)) = 0` is FALSE (irreflexive). The §5 reduct `zAx1`
    (strict drop, banked as `iRedDescent_zAx1_z*` this lap) cannot enter through the `iR2` table.
**Path 2 (weaken j-side to `≤`) RULED OUT** (lap 66, verified): the K-case descent
`iord_descent_iCritReduct` proves `o(d[0]) ≺ o(d)` via `iord_descent_cut` = (degree drop N3a) ∧
(õ-side N3b). N3b is `icmp_omega_pow_nadd_lt h0o h1o` = `ω^{õd{0}} # ω^{õd{1}} ≺ ω^{õ(d)}`, which
genuinely needs BOTH `õ(d{ν}) ≺ õ(d)` STRICT (a `#` of two ω-powers is `≺ ω^c` only if both exponents
`< c`). And `õ(d{1}) ≺ õ(d)` traces back (via `iotil_iCritAux_lt`) to strict drop on the replaced
j-premise. With `vj = iR2(atom) = atom`, `õ(d{1}) = õ(d)` — descent FAILS. **So the current `iR2` does
NOT achieve descent on tag-4; the §5 j-reduct is genuinely required, not optional.**

**Done lap 66:** defined the §5 reduct FUNCTION `zAxReduct : V → V` (`zAxAll s p k ↦ zAx1 s p`,
`zAxNeg s p ↦ zAx1 s p`, identity off tags 5/6) + rewrite lemmas `zAxReduct_zAxAll/_zAxNeg` + the
j-side bundles `iRedDescent_zAxReduct_zAxAll/_zAxNeg` (axiom-clean). This is the function the critical
reduct must install on the j-side.

**DONE path-1 steps 1+2 (lap 66):**
  1. ✅ `zAxReductDef` (Σ₁-definability of `zAxReduct`) — axiom-clean.
  2. ✅ **Rewired `iRNext` tag-4** (the `iR2` table step) so BOTH premise reducts are wrapped in
     `zAxReduct`: `iCritReduct d i j (zAxReduct (iR2 premᵢ)) (zAxReduct (iR2 premⱼ))`. `zAxReduct` is the
     identity off atomic-axiom tags (so harmless on the i-side I-rule sub-derivation, which is a
     `ZDerivation` ⟹ tag ∈ {0..4} ⟹ never 5/6) and is the §5 `Ax^1` reduct on the j-side L-axiom redex.
     `iRNextDef` re-proven; `iR2_zK` + `iR2_zK_eq_iRcrit` updated to `ρ = fun n ↦ zAxReduct (iR2 (znth ds n))`.
     All axiom-clean, green (1321 jobs). **The reduction `iR2` now genuinely descends on tag-4 in
     principle** — the j-premise õ strictly drops.

**NEXT-LAP ATTACK (assemble the unconditional K-case, then the whole induction):**
  3. **`zAxReduct_of_ZDerivation`** (`ZDerivation d → zAxReduct d = d`): from `zDerivation_iff`, a
     ZDerivation's tag ∈ {0,1,2,3,4} (zAtom/zIall/zIneg/zInd/zK), never 5/6, so `zAxReduct` is the
     identity. Needed to collapse the i-side wrap `zAxReduct (iR2 premᵢ) = iR2 premᵢ` in the descent.
  4. **Tag-5/6 inversion + UFormula** (`zTag d = 5 → ∃ s p k, d = zAxAll s p k`, similarly tag 6): to
     apply `iRedDescent_zAxReduct_zAxAll/_zAxNeg` to a redexJ premise known by `tp = isymLk k A`. The
     `IsUFormula p` side comes from the chain's `hwfL`/`zKWff` well-formedness data — locate it.
  5. **Assemble `iord_descent_iR2_struct` for tag 4**: feed `iord_descent_iCritReduct_object` with
     `v = zAxReduct (iR2 premᵢ)` (= `iR2 premᵢ` via step 3, descent from `iRedDescent_iR2_of_tp_isymR`)
     and `w = zAxReduct (iR2 premⱼ)` (= `zAx1` via `iR2_zAxAll`+`zAxReduct_zAxAll`, descent from
     `iRedDescent_zAxReduct_zAxAll`). The redex `(i,j)` + `tp` facts come from
     `inference_critical_pair_of_chain` (already used inside `iord_descent_iRcrit_of_chain'`). Likely
     route: discharge the six `ρ`-facts of `iord_descent_iRcrit_of_chain'` at `ρ = zAxReduct ∘ iR2`,
     then `rw [← iR2_zK_eq_iRcrit]`.
  NOTE: atomic axioms (tags 5/6) are NOT standalone `ZDerivation` constructors — they appear only as
  chain premises, so the j-side lemma keys off the premise CODE being `zAxAll`/`zAxNeg`.
Then the UNCONDITIONAL `ZDerivation d → icmp (iord (iR2 d)) (iord d) = 0` (all tags), the
no-infinite-descent → `ZDerivesEmpty d → False`, C0.5 bridge, wire `Reduction.lean:68`.

## ✅ RESOLVED lap 66: ZPhi extended with the §5 axiom base cases (the structural gap is closed)

`ZPhi`/`ZDerivation` now has 7 disjuncts: zAtom/zIall/zIneg/zInd/zK **+ zAxAll (tag 5) + zAxNeg
(tag 6)**, each carrying `IsUFormula ℒₒᵣ p`. Full cascade fixed & axiom-clean, green (1321 jobs):
ZPhi def, zphi_monotone, zphi_strong_finite, zphi_iff, zblueprint (Σ/Π cores embed
`(isUFormula ℒₒᵣ).sigma`/`.pi`), zPhi_definable, isNF_iotil_of_ZDerivation (new leaves via
`isNF_iotil_zAxAll/_zAxNeg`), and all 6 `rcases zDerivation_iff.mp` sites (+2 patterns each).
`zAxReduct_of_ZDerivation` → `zAxReduct_of_tp_isymR` (the ZDerivation form is now false since axioms
are leaves; the i-side redex premise has `tp = isymR` ⟹ tag 1/2, so `zAxReduct = id`). Added
`k_lt_zAxAll`. **The redex finder can now fire on a genuine `ZDerivation` — the K-case is reachable.**

**NEXT: assemble `iord_descent_iR2_struct` for tag 4 (the K-case), then the full induction.**
The pieces are all banked & axiom-clean:
  - chain inversion `zDerivation_zK_inv` (premises are ZDerivations OR §5 axioms now),
  - `iR2_zK_eq_iRcrit` (ρ = zAxReduct ∘ iR2), the nut `iord_descent_iRcrit_of_chain'`,
  - i-side: `iRedDescent_iR2_of_tp_isymR` + `zAxReduct_of_tp_isymR` (collapse the wrap),
  - j-side: `iRedDescent_zAxReduct_zAxAll/_zAxNeg` (needs `IsUFormula p`, now carried by the leaf).
  Route: from `ZDerivation (zK s r ds)` derive the chain hyps (hchain/hrank/hwfR/hwfL/hperm/hnperm
  from the chain validity — CHECK what `zDerivation_zK_inv` + the zK ZPhi disjunct give vs what the
  nut needs; the chain-validity predicates `chainAsucc`/`chainAnt`/`isChainInf` may need a bridge from
  the bare `∀ i < lh ds, znth ds i ∈ ZDerivation`), then discharge the six ρ-facts at redexI/redexJ.
  ⚠️ GAP TO CHECK: the nut needs `hchain`/`hAj0`/`hrank` (chain-structure predicates). The ZPhi zK
  disjunct only gives `Seq ds ∧ ∀ i<lh ds, premise ∈ ZDerivation` — NOT the chain antecedent-threading
  (`chainAnt`/`chainAsucc`) the redex finder consumes. Either (a) the zK ZPhi disjunct must be
  strengthened to a genuine `isChainInf`-style condition, or (b) those predicates are derivable from
  the premise sequents. Resolve this before the final assembly.

## (historical) THE blocking structural gap (lap 66): ZPhi lacks the §5 axiom base cases — RESOLVED above

`ZPhi` (line ~3165) — the `ZDerivation` fixpoint — has exactly 5 disjuncts: zAtom / zIall / zIneg /
zInd / zK. **No tag-5/6 disjunct.** So every chain premise (`znth ds i ∈ C` = a `ZDerivation`) has tag
∈ {0..4}, NEVER 5/6. But `tp` assigns the L-symbol `isymLk` ONLY to tags 5/6 (`zAxAll`/`zAxNeg`), and
the redex finder (`inference_critical_pair_of_chain`) needs a premise with `tp = isymLk` at the j-end.
⟹ **on a genuine `ZDerivation`, the redex finder never fires** — the K-case is unreachable, not just
unproven. The §5 L-axioms are Buchholz logical-axiom LEAVES (the only source of left symbols, tp
comment p.12) and MUST be `ZPhi` base cases. (med's arm added them via `ZDerivation_zAxInst/_zAx1`.)

**EXTENSION PLAN (atomic change — nothing compiles until the whole cascade is fixed; do it in one
focused pass, build at the end):** add two base-case disjuncts AT THE END of the `ZPhi` Or-chain (after
the zK disjunct) so existing rcases patterns only need 2 appended cases:
```
  ∨ (∃ s p k, d = zAxAll s p k ∧ IsUFormula ℒₒᵣ p)   -- ∀-axiom leaf (tag 5)
  ∨ (∃ s p,   d = zAxNeg s p   ∧ IsUFormula ℒₒᵣ p)   -- ¬-axiom leaf (tag 6)
```
(IsUFormula in ZPhi so a rcased premise gives `IsUFormula p` for the §5 descent — `IsUFormula` is a
`𝚫₁-Predicate` in Foundation, `via isUFormula ℒₒᵣ`, usable in the blueprint.) Cascade to fix:
  - `ZPhi` def (~3165); `zphi_monotone` (~3173 rintro: +2 trivial leaf patterns, no `C` use);
    `zphi_strong_finite` (~3185: +2, leaves have no premise so `by simp`); `zphi_iff` (~3198, BOTH
    directions, bounded `∃ s<d,…`); `zblueprint` Σ AND Π cores (~3227, add `!zAxAllGraph d s p k ∧
    !isUFormula …` style disjuncts); `zPhi_definable` (~3247, add `zAxAll_defined.iff`,
    `zAxNeg_defined.iff`, `IsUFormula.defined.iff` to the simp).
  - 6 `rcases zDerivation_iff.mp` sites: lines ~3355, 3379, 3568, 3954 (`iord_descent_iR2_struct`),
    3972 (`iRedDescent_iR2_of_tp_isymR`), 4014 (`zAxReduct_of_ZDerivation`). Each: append 2 patterns
    `| ⟨s, p, k, rfl, hp⟩ | ⟨s, p, rfl, hp⟩`. For the descent lemmas the new leaf cases are tag 5/6:
    in `iord_descent_iR2_struct` they're NF (no descent needed — but htag excludes them, so `simp at
    htag`); in `iRedDescent_iR2_of_tp_isymR` tp=isymLk≠isymR so `absurd`; in `zAxReduct_of_ZDerivation`
    `zAxReduct (zAxAll…) = zAx1…` is NOT `= d`, so that lemma must WEAKEN — see below.
  - ⚠️ `zAxReduct_of_ZDerivation` becomes FALSE for the new leaves (`zAxReduct (zAxAll s p k) = zAx1 s p
    ≠ zAxAll s p k`). Restrict it to `tp d = isymR A → …` or to tags {0..4}, OR only use it on the
    i-side premise (which has `tp = isymR`, tag 1/2). Re-scope to `(htp : tp d = isymR A)`.
Then: with axioms now reachable as premises, assemble the K-case (steps 3–5 above) and the
unconditional descent.

## ⭐⭐⭐ Reflection — 2026-06-24 (lap 62, DEEP) — priorities reset

> Full synthesis: `REFLECTION-2026-06-24-lap62.md`. Direction **KEEP** (genuine forward motion — crux 1
> landed lap 57, 58–61 correctly built crux-2's axiom-clean ordinal engine). Three sharpenings below.

**Endpoint HARDENED (operator directive, binding):** axiom-free (trust base only) **or abandoned**. No cited
`PRWO→Con` axiom on the headline; `PA_delta1Definable` must also be discharged. Crux 2 reclassified
🟠-generational → **🟡 must-fully-discharge frontier** (feasibility settled: Bryce–Goré Coq, Feb 2026).

**KEEP:** Route A; crux 2 via **Buchholz-Z + C0.5 bridge** (fork B, judge-endorsed); the axiom-clean
`InternalZ` engine; `GentzenCon` SEAM guards; the banked `peano_not_proves_TI` monument (do NOT touch).

**STOP:** crux-2-as-cited-axiom as an endpoint (forbidden); refining `#`/tower/template algebra *before* the
OBJECTS exist; the `GentzenCon` footer's "arithmetize over Foundation's `Theory.Derivation`" plan (superseded
by Buchholz-Z — re-point that footer next edit).

**HIGHEST-VALUE NEXT (objects-first, in order):**
1. **Fixpoint `ZDerivation : V → Prop`** — THE unblocker (lap-61 NEXT #1, confirmed). Mirror Foundation's
   `Theory.Derivation` via `HFS/Fixpoint.lean`'s `Fixpoint.Construction` over the `z*` codes
   (`InternalZ.lean`). Unblocks structural induction (`isNF (iõ d)`), `iR` well-definedness, the
   ⊥-characterization, and per-rule C3 instantiation.
2. **`iR : V → V`** (C2 reduction `d ↦ d[0]`) — needed to state the per-rule descent on concrete reducts.
3. **C0.5 Foundation→Z bridge** — `(𝗣𝗔).DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z` (M-internal). Type written
   in `InternalZ.lean` footer; blueprint = Bryce–Goré `Peano.v` (filed `ON-LINE-REQUEST` for the source).
4. **C3 descent — REORDERED per judge `E-CRUX2-DECOMPOSITION-2026-06-24.md` (2026-06-24).** The difficulty
   is NOT spread across iR+C3; it is concentrated in **ONE case (5.1, critical/cut-elim)**, gated behind two
   currently-unlisted prereqs. Plow in this order (most are low-hanging `#`-bookkeeping the algebra exists for):
   - **iR skeleton** (rule-by-rule dispatch on `zTag`, Def 3.2) — minimal, enough for the easy rules.
   - **LOW-HANGING descent cases first** (each ~1 lap; debugs the engine end-to-end before the nut):
     LH1 I¬ (`self_lt_iadd_one`), LH2 I∀ (+ subst-invariance `õ(d(a/t))=õ(d)`), LH3 chain-non-crit (**F1**),
     LH4 Ind (**F3** `ω^β·k≺ω^{β+1}`), LH5 chain-crit (**F1+F2**).
   - **THEN two prereqs (build before the nut — without them C3-critical can't be STATED truthfully, only
     smuggled as a `rk(A(d))<dg(d)` hypothesis = hidden gap):** **L3.1** Lemma 3.1 critical-pair existence
     (pure Σ₁ combinatorics on premise list, NO ordinals); **T3.4** Theorem 3.4 `rk(A(d))<r` + the `d{0}`/`d{1}`
     auxiliary derivations. ⚠️ CHECK FIRST (judge pt-7): if the box's rank encoding makes `rk<r` definitional,
     T3.4 collapses to an unfolding — don't over-build it.
   - **THE NUT (case 5.1, Lemma 4.1(b)(ii)):** mostly OBJECT construction (build `d{0}`/`d{1}` as ZDerivations
     per 3.2(5.1)) + a 3-step ordinal tail: F2 (`õ(d[0])<ω^{õ(d)}`) + degree-drop (`dg(d[0])<dg(d)` via T3.4)
     + the tower combine. ✅ **The tower step is BANKED:** `InternalTower.iotower_omega_pow`
     (`ω_m(ω^α)=ω_{m+1}(α)`, proved lap 62) + `icmp_iotower_lt_succ_of_le` give exactly the §4 combine.
   - **Thm 4.2** = ~3-line tower combine over LH-cases + nut.
   - Lit map: nut → `papers/buchholz-beweistheorie-lecture-notes.pdf` + `buss-handbook-ch2`; L3.1/T3.4 → [6] pp.8–9.

**PARALLEL FRONT (when crux-2 blocks):** discharge `PA_delta1Definable` upstream (now mandatory) — check the
Foundation pin first (still an `axiom` in `Incompleteness/Examples.lean`?). Also **C0.5 bridge** decomposes
into B1 (PA axioms→Z) / B2 (PA rules→Z, **induction via Z's native `Ind` rule — the key shortcut**) / B3
(compose, M-internal). ⭐ Judge §5 (2026-06-24): the `Ind` shortcut SKIPS Bryce–Goré's induction→ω-rule
sub-tower (~half their `Peano.v`) ⟹ **C0.5 is <1k lines**, not ~1215. Do NOT port their `cut_elim.v`
(infinitary, not the primrec `R` PRWO needs); only `Peano.v` transfers. Run in a worktree when descent stalls.

> **Lap-62 progress (this lap):** C0 Fixpoint `ZDerivation` ✅ DONE (structural skeleton + `case` +
> `induction`, axiom-clean `wip/InternalZ.lean`); nut tower step `iotower_omega_pow` ✅ banked (`src/`).
> NEXT = `iR` rule-by-rule skeleton → 5 low-hanging cases.

**HYGIENE (low, non-blocking):** off-path `DescentSemantic.lean` free-X `sorry` + deps → `wip/` candidates.

---

## ⭐⭐ Lap 59 — natural-sum `#` NF + order foundations DONE; ORDER>iC reprioritization

`wip/InternalNadd.lean` (the lap-58 brick 1) now carries, all `lake env lean` green + axiom-clean
`[propext,choice,Quot.sound]`:
- **NF preservation:** `isNF_insTerm` (`isNF e→n≠0→isNF b→isNF (insTerm e n b)`), `isNF_inadd`
  (`isNF a→isNF b→isNF (inadd a b)`). Order-induction; the `isNF_ocOadd` side-condition (lead-exp `≺`
  head) discharged through the 3 `insTerm_ocOadd` branches via `icmp_two_iff_swap_zero` / `icmp_eq_imp_eq`
  / `ocExp_insTerm`.
- **Unit/prepend laws:** `insTerm_prepend` (`insTerm e n b = ocOadd e n b` when `b=0 ∨ icmp (ocExp b) e=0`),
  `inadd_zero_right` (`#` right-unit on NF).
- **ω-power layer:** `thenV_one_right`, `icmp_omega_pow` (`icmp (ω^α)(ω^β)=icmp α β`; `ω^c=ocOadd c 1 0`),
  `inadd_omega_pow` (`ω^α # b = insTerm α 1 b`).

**⚠️ REPRIORITIZATION (this lap's finding):**
1. **ORDER, not iC, is what the descent consumes.** Buchholz Thm 4.2 (`o(d[n]) ≺ o(d)`) via Lemma 4.1
   (`dg`/`õ` monotonicity) needs `#`'s ORDER laws. `iC (a#b) ≤ iC a + iC b` is for ε₀-width control
   (crux-1 Grzegorczyk levels) and is NOT on the crux-2 descent path; at most it serves C4 bounds.
2. **`iC_inadd` does NOT follow from the naive `insTerm`-fold.** `iC (insTerm e n b) ≤ max(iC e)(n+iC b)`
   (or `n+max(iC e)(iC b)`) is provable, but folding it over `a`'s terms over-counts: `inadd (ocOadd ec nc
   rc) b = insTerm ec nc (inadd rc b)` adds `nc` to the WHOLE accumulator `iC(inadd rc b) ≥ iC rc`,
   giving `nc+iC rc` where `iC a` only has `max(iC ec)nc` maxed with `iC rc`. The TRUE bound needs the NF
   fact `ec ≻ (every exp of rc)` so the `nc`-merge can only hit a `b`-coefficient (≤ iC b), never an
   rc-term. ⟹ a real NF-aware proof, deferred until/unless C4 needs it.

**Buchholz §4 inequalities NOW PINNED** (read `scratchpad/buchholz-gentzen.txt:781-822`). Lemma 4.1 /
Thm 4.2: every descent case rewrites `õ(d)=ω^{α0}#…#ω^{αl}` by replacing ONE summand `ω^{αi}` with a
strictly-smaller block, then concludes the whole `#` drops. The `#`-facts actually consumed:
- **(F1) `#` strict left-cancellation/mono** — replacing a summand by a smaller one decreases the sum.
- **(F2) two-powers-below** — `αi0,αi1 ≺ αi → icmp (ω^{αi0} # ω^{αi1}) (ω^{αi}) = 0`  (case 5.1, 5.2.1).
- **(F3) `ω^β·k ≺ ω^{β+1}`** — `icmp (ocOadd β k 0) (ω^{β+1}) = 0`, finite k (case 4, the Ind rule).
- **(F4) commutativity** of `#` (to move the changed summand to the cancellable end) + assoc for the fold.

**NEXT deep target (hardest-first) = (F1), now SHARPLY ISOLATED.** This lap recast it:
`#` strict-mono ⟺ **left-cancellation `icmp (inadd g X) (inadd g Y) = icmp X Y`** (NF g,X,Y), which by
order-induction on `g` (using `inadd_ocOadd` + `inadd_single_term`, banked) reduces to the **single-term
insertion embedding**:
> **`icmp_insTerm_congr` (NF A, NF B): `icmp (insTerm e n A) (insTerm e n B) = icmp A B`.**  ← THE nut.
Proof plan = pair order-induction on `m=⟪A,B⟫` (mirror `icmp_swap_aux`/`icmp_eq_imp_eq`), motive
`isNF (π₁ m)→isNF (π₂ m)→ …`. Case grid on `icmp e (ocExp A)`×`icmp e (ocExp B)` (∈{0,1,2}) + A/B=0:
  - both-prepend (e≻ both leads): heads `ω^e·n` equal, tails are A,B ⟹ `icmp_ocOadd` + `icmp_self` +
    `cmpV_self` collapse to `icmp A B`.
  - both-merge (e=both leads): coeffs `n+ca`,`n+cb`; **`cmpV_add_left`** (banked) ⟹ `cmpV ca cb`; tails
    `ra,rb` unchanged ⟹ `icmp A B` directly (`icmp_pos_pos`).
  - both-recurse (e≺ both leads): heads `ω^{la}·ca` vs `ω^{lb}·cb` decide unless la=lb∧ca=cb, then
    **IH on ⟪ra,rb⟫** (both `< m`). Heads match `icmp A B`'s head exactly.
  - mixed (e relates differently to la vs lb): then la≠lb (NF + e between them), so BOTH `icmp A B` and the
    inserted comparison are decided by the lead-exponent comparison la-vs-lb — they agree. (Lean: case on
    which of the 6 mixed combos; each resolves at the head via `icmp_pos_*`/`icmp_finHead_infHead`-style.)
  - base A=0 (B≠0, so `icmp A B=0`): need `icmp (ω^e·n) (insTerm e n B)=0`, i.e. ω^e·n ≺ insertion into a
    nonzero NF B. Sub-lemma `insTerm_ge_term` (dominance). Symmetric for B=0.
Then **(F1)** `inadd_left_cancel` (induct g) ⟹ strict-mono corollary `icmp X Y=0 → icmp(g#X)(g#Y)=0`.
**(F2)/(F3)** are short once `icmp_omega_pow` + `icmp_ocOadd` are in hand (F3 = exponent compare `β≺β+1`;
F2 = both exps `≺ αi` ⟹ 2-term CNF below `ω^{αi}`). **(F4)** commutativity = the other hard nut (NF
canonical-form uniqueness); defer behind (F1) since (F1)+reorder often suffices per-case.
- ALT (worktree, parallel if a lap stalls): start C0 (arithmetize system Z `ZDerivation : V→Prop`),
  independent of the `#` order algebra.

## ⭐⭐⭐ Lap 58 — crux 2 REFRAMED to model-theoretic route + Buchholz ord/R GROUNDED from source

**(a) `gentzen_reduction_internalized` is now a THEOREM** (`21a7318`). Was an opaque object-level axiom
`𝗣𝗔 ⊢ (prwoInstance gentzenDescentφ 🡒 Con(𝗣𝗔))`; now proved via `provable_of_models 𝗣𝗔` +
`Semantics.Imp.models_imply` + `Bootstrapping.consistent.defined`, from the clean **per-model semantic
axiom** `gentzen_descent_of_inconsistent` (Gentzen eq-(5) at model level: `¬𝗣𝗔.Consistent M` ⟹ the
gentzen descent everywhere `icmp`-descends in `M`). Same axiom COUNT (4) but the deep one is now in the
proven crux-1 shape. Assembly `#print axioms` = `[propext,choice,Quot.sound,PA_delta1Definable]` + 4.

**(b) Buchholz `ord`/`R` extracted VERBATIM** → `CRUX2-ORD-ASSIGNMENT-2026-06-24.md` (text in
`scratchpad/buchholz-gentzen.txt`). `o(d) := ω_{dg(d)}(õ(d))`; `õ`/`dg` recursions (I∀/I¬/Ind/K rules);
consistency = ⊥-derivation ⟹ `tp=Rep` ⟹ infinite `o`-descent (Thm 4.2) ⟹ ¬PRWO.

**(c) ⚠️ LOAD-BEARING FINDING — calculus mismatch.** Buchholz's `ord`/`R` are over **his system Z**
(chain rule `K^r`, `Ind`, `Rep`/`tp`/`d[n]` ω-simulation), NOT Foundation's **Tait+cut** calculus
(`Theory.Derivation`: `axL`/`andIntro`/…/`cutRule`/`axm`). Foundation's `Hauptsatz` is **meta-level**
(Type `⊢ᵀ Γ` realizability, no arithmetized ordinals) — no shortcut. ⟹ **Route A** (recommended):
arithmetize system Z + a translation `𝗣𝗔-Tait-⊥-deriv → Z-⊥-deriv`. Route B (Schütte on Tait+cut directly)
fails because PA-induction is an `axm` schema that blocks finite cut-elim. Full analysis in the doc.

**NEXT (hardest-first, concrete + checkable, all Route A):**
1. **InternalONote natural (Hessenberg) sum `#`** — the ONE genuinely-missing ordinal primitive `õ` needs
   (`ω^c` = `ocOadd c 1 0`; ω-tower `ω_n` = meta-iterate of `c↦ocOadd c 1 0`; `iadd`/`iomul`/`ibigMul`
   already exist). Source-independent, bounded — the best first brick. Build `inadd a b` (CNF merge of
   exponents summing coeffs) + `isNF_inadd`/`icmp_inadd`/`iC_inadd` (mirror `iadd`).
2. **C0 — arithmetize system Z** as `ZDerivation : V → Prop` (`Fixpoint.Construction`, mirror
   `Theory.Derivation`); coded `zI∀`/`zI¬`/`zInd`/`zK`+atomic, `fstIdx`/subterm-`<` lemmas; formula `rk`.
3. **C1 — `iõ`/`idg`/`iord`** by `<`-strong-recursion on Z-codes (recursion combinator: build the
   derivation analog of Foundation `Language.TermRec.Construction` (`Term/Basic.lean:301`), or graph-Fixpoint).
4. **C2/C3** — `iR := d↦d[0]`, preserves-⊥; Thm 4.2 internalized (Lemma 4.1 `dg`/`õ` monotonicity). Deep.
5. **C5** — `gentzenDescentφ` graph + `d₀` via the Route-A translation of `𝗣𝗔.Proof _ ⌜⊥⌝`.
First action next lap: build brick 1 (`inadd`) in a new `src/GoodsteinPA/InternalNadd.lean` (or extend
`InternalCor34`), sorry-free + axiom-clean, mirroring the existing `iadd` lemma set.

**BRICK 1 EQUATIONAL CORE DONE (lap 58, `wip/InternalNadd.lean`, `lake env lean` green, axiom-clean
`[propext,choice,Quot.sound]`).** Natural sum factored into two single-arg course-of-values recursions
(mirroring `iomul`/`iadd`): `insTerm e n b` (insert `ω^e·n` into NF `b`; `insTerm_ocOadd` 3-way `icmp`
recursion) and `inadd a b = insTerm (ocExp a)(ocCoeff a)(inadd (ocTail a) b)` (`inadd_ocOadd`,
`inadd_zero_left`). Both `𝚺₁`-definable (full `*_defined`/`*_definable`/`*_definable'` instances + tables).
Gotchas banked: open `LO.FirstOrder.Arithmetic.HierarchySymbol` for `DefinableFunction₂/₃.comp`/
`Definable.comp₁`/`ball_le`; for a 2-param `PR.Blueprint`, `resultDef` natural order is
`(result, index, param₀, param₁)` so `insTermTableDef := …resultDef.rew (Rew.subst ![#0,#3,#1,#2])`
(index↦last). **NEXT for brick 1 (the property lemmas, then promote to `src/`):** `isNF_insTerm`/
`isNF_inadd` (NF preservation), `icmp`-monotonicity (`# ` is commutative + strictly-monotone in each arg
on NF), `iC_inadd` (`iC (a # b) ≤ iC a + iC b` or similar), and `inadd`-commutativity. These are what
`õ`'s descent (Lemma 4.1) consumes. Mirror the `iadd`/`iomul` `isNF_*`/`icmp_*`/`iC_*` proof style
(`InternalONote.lean` ~1820–2100).

**HELPERS DONE (lap 58 cont., `wip/InternalNadd.lean` green):** `icmp_tri` (comparison code is always
`0`/`1`/`2`, order-induction via `cmpV_tri`/`thenV_tri`) + `icmp_eq_zero_of_ne`; `insTerm_pos`/
`insTerm_ne_zero`; `ocExp_insTerm` (head exp `= e` unless `e ≺ lead-exp b`, then `ocExp b`). V-numeral
disequalities (`0≠1`,`0≠2`,…) discharge by `simp`. **NEXT: `isNF_insTerm`** (`isNF e → n≠0 → isNF b →
isNF (insTerm e n b)`) by order-induction on `b`: the `e≺e'` branch needs `icmp (ocExp(insTerm e n r')) e'
= 0`, supplied by `ocExp_insTerm` (lead-exp is `e` or `ocExp r'`, both `≺ e'`). Then `isNF_inadd`,
`icmp`-monotonicity, `iC_inadd`.

## ⭐⭐ Lap 57 — TWO findings: (a) seqDescent_dominated was FALSE, fixed; (b) width-code wall

**(a) Soundness fix (DONE, committed `38c6de0`).** Lap-56's `seqDescent_dominated` was **false at ℕ**
(conclusion `SeqDominated` asserts an infinite ε₀-descent; hyps vacuously met by empty seq). Fixed by
threading an explicit realizer `SeqRealized seq M = ∃ β:M→M, (∀n, M⊧/![β n,n] seq) ∧ NF ∧ ≠0 ∧ 𝚺₁`,
discharging the β-parts of `SeqDominated` directly. New disclosed axiom `gentzenDescentφ_realized`. See
memory `seqdominated-vacuity-needs-realizer`.

**(b) THE sharpened crux-1 target — `BlkRec`-over-function refactor (see
`ANALYSIS-2026-06-23-lap57-width-code-wall.md`).** The remaining `seqDescent_dominated` gap is NOT
"build a finite width code `wseq`" — **no finite `wseq` works**. `nonterminating_of_slowdown` needs the
slow-down NF+`iC≤k+1`+descent for ALL `k:V`; a finite `wseq` gives `znth=0` past `lh` ⟹ `blk wseq j ∼ j`
⟹ `iC(β(blk j)) ≤ Cβ+j` fails for complexity-growing descents (exactly Cor 3.4's case). **Fix:** width as
a `𝚺₁` FUNCTION `W := fun t => iC(β(t+1))` (mirrors `Grz.corW`). Refactor steps:
1. `src/BlkRec.lean`: add `blkF W`/`offF W` (𝚺₁ `boState` recursion reading `W (π₁ ih)`), re-prove the 4
   bookkeeping facts + width-sum facts + internal `C_le_wsumc` (= `Grz.C_le_wsum_corW`). Additive → green.
2. `src/StdCor34.lean`: `crux1_internal_run_of_width_dom` etc. switch `BlkRec.blk wseq`→`blkF W`; width
   hyp becomes `∀n, W n ≤ iF l₀ n`; `hβC` via `C_le_wsumc`.
3. `wip/GentzenCon.lean` `SeqDominated`: `wseq Cβ : M` → `W : M→M`; `seqDescent_dominated` then discharges
   fully (`Cβ:=iC(β 0)`, `l₀':=l₀+1`, width-dom from `hβbound`). No remaining width gap.

This is hardest-first crux-1 work; the descent half is already general (works for any width).
**Step 1 DONE (`21d1856`):** `src/GoodsteinPA/BlkRecF.lean` — `blkF`/`offF`/`wsumcF` over a width
FUNCTION, sorry-free + axiom-free. **Step 2 DONE (`2f8f72e`):** `src/GoodsteinPA/StdCor34F.lean` —
`crux1_internal_run_F` drives the internal run over the width function, C-bound + within-block
domination discharged internally (`iC_le_wsumcF`, `one_le_iC_of_ne_zero`); no `hβC`/`Cβ`/`wseq`.
**Step 3 DONE (`2199982`) — CRUX 1 CLOSED.** `wip/GentzenCon.lean` `nonterminating_of_seq_descent` calls
`StdCor34F.crux1_internal_run_F` directly (clean `[propext,choice,Quot.sound]`); dead finite-`wseq` girder
gone. `SeqRealized` carries explicit `βDef`; `SeqStdBounded` width form. **The crux-1 sorry is gone.**

## ⭐⭐ WHOLE Gentzen chain now SORRY-FREE (`abece0f`). NEXT = crux 2 = 4 disclosed axioms (🟠 generational)
`wip/GentzenCon.lean` sorry-free; `goodstein_implies_consistency_via_gentzen` `#print axioms` =
`[propext, choice, Quot.sound, PA_delta1Definable]` + 4 crux-2 axioms. Crux 1 axiom-clean. The remaining
4 (all the Gentzen ordinal-analysis arithmetization, interlocked):
- `gentzenDescentφ` (ℒₒᵣ graph of `n↦ord(Rⁿd₀)`), `gentzenDescentφ_realized` (total 𝚺₁ NF branch +
  explicit `βDef`), `gentzenDescentφ_dominated` (Rathjen 3.2 width bound) — discharge once `ord`/`R` exist.
- `gentzen_reduction_internalized : 𝗣𝗔 ⊢ (prwoInstance gentzenDescentφ 🡒 Con(𝗣𝗔))` — Gentzen's
  `PRWO(ε₀) → Con(𝗣𝗔)` internalized; the deep `TI(ε₀) ⊢ Con(PA)` content.
Attack: (a) read Buchholz (`papers/buchholz-on-gentzens-first-consistency-proof.pdf`) + `papers/siders-*`,
decompose eq-(5) `ord(R d) ≺ ord d` lemma-by-lemma; (b) state `ord`/`R` as `ℒₒᵣ` primrec functions over
Foundation's `Theory.Derivation` (`Bootstrapping/Syntax/Proof/Basic.lean`); (c) certificates then
discharge from `ord`/`R`'s fixed build tree. Multi-lap. Headline stays `sorry` until all 4 real.

## Lap 56 — crux-1 redirect: natCode↔NF bridge DISSOLVED (transparent icmp); over-generality sharpened

**FRESH-MIND REVIEW. Build green 1315; headline honest sorry; M1+Phase 1 done; faithfulness clean.
Direction VALIDATED** (crux 1 right hardest-but-tractable target; crux-2 eq-5 stays 🟠 parked). Two
crux-1 findings, both acted on (`wip/GentzenCon.lean`, verified `lake env lean` green; memory
`prwo-transparent-icmp-not-opaque-precphi`):

**(1) DONE — opacity dissolved.** Lap-55 built `prwoInstance` on `SeamDefinability.precφ` =
`codeOfREPred₂ (natCode a < natCode b)`, Foundation's **opaque r.e. blob** whose spec is std-model-ONLY;
in nonstandard `M`, `M⊧/![z,y]precφ` is an opaque Σ₁ search, NOT cleanly `z≺y` — re-creating the wall-B
opacity lap 36 dissolved. **Fix (mirrors lap 36):** rebuilt on the transparent internal `icmp`:
- `prec_internal : Semisentence ℒₒᵣ 2 := “z y. ∃ c, !icmpDef c z y ∧ c = 0”`
- `eval_prec_internal : M⊧/![z,y]prec_internal ↔ icmp z y = 0` (every `M⊧IΣ₁`; `simp [prec_internal,
  Semiformula.eval_substs, icmp_defined.iff]`).
- `prwoInstance`/`prwoInstance_models_iff`/`prwoInstance_faithful` (now `M=ℕ` corollary) all on `icmp`,
  axiom-clean `[propext,choice,Quot.sound]` — `_faithful` even SHED its F-φ `native_decide` artifact.
- `ord_R_descends`/`gentzenDescent_descends` switched to `icmp` form for coherence.
⟹ **the natCode↔NF order bridge (lap-55's "new sub-target") DISSOLVES**: `nonterminating_of_seq_descent`'s
descent hyp is ALREADY `∀ n y z, seq[y,n]→seq[z,n+1]→icmp z y=0`, the exact `icmp`-descent form
`StdCor34.crux1_internal_run_of_width_dom` consumes (`hβdesc`). PRWO + `igoodstein` now share ONE coding.
`goodstein_implies_prwo` clean modulo the lone bridge sorry.

**(2) THE concrete next target — standard-level domination certificate.** `nonterminating_of_seq_descent`
for *arbitrary* `seq` (no domination hyp) is **UNPROVABLE on the built standard girder**:
`crux1_internal_run_of_width_dom` needs a STANDARD `l₀:ℕ` with `∀ n, znth wseq n ≤ iF l₀ n`, but
`Grz.F_diag_not_dominated` kills standard domination of a diagonal-fast descent (lap-55 flagged this;
confirmed). **Attack paths (do one next lap):**
- **(A, recommended) Thread the certificate.** Add to `nonterminating_of_seq_descent` a hypothesis
  packaging the Cor-3.4 slowdown inputs derived from `seq` — concretely `∃ (β:M→M)(wseq Cβ:M)(l₀:ℕ),
  0<l₀ ∧ (∀n,isNF(β n)) ∧ (∀n,β n≠0) ∧ (∀n,icmp(β(n+1))(β n)=0) ∧ (∀j,iC(β(blk wseq j))≤Cβ+j) ∧
  𝚺₁-Function₁ β ∧ (∀n,znth wseq n≤iF l₀ n)`. Then the proof is `obtain ... ; exact
  crux1_internal_run_of_width_dom ...` — **discharges the sorry**. (Requires `wip/GentzenCon` to import
  `wip/StdCor34`.) Thread the certificate up through `prwoInstance_models_of_goodstein` /
  `goodstein_implies_prwo`; supply it at `gentzenDescentφ` in the assembly as a disclosed axiom (Lemma 3.2,
  discharged once `ord`/`R` exist). This makes the chain HONEST (no unprovable general lemma).
- **(B) Construct β from seq's value-graph.** The β for the girder = `seq`'s value function (the unique `y`
  with `seq[y,n]`); needs `seq` functional/total + NF nonzero values. Then `hβdesc` = the descent hyp
  directly. This is the seq→β extraction half of the construction; pairs with (A) for the wseq half.
- **(C) Build the seq→wseq Cor-3.4 slowdown** (the deep half: `InternalCor34.ibigMul`-standard lead +
  `Grzegorczyk.lean` blueprint; item 1 below). This is what eventually discharges the certificate for
  `gentzenDescentφ` rather than axiomatizing it.

**DONE later this lap (attack path A + honest threading):** Promoted `StdCor34` → `src/` (1316 jobs).
Wired `SeqDominated` + `nonterminating_of_dominated` (**axiom-clean** — certificate→girder seam type-checks
end-to-end). Then made the chain HONEST: `seqDescent_dominated` was a FALSE-for-arbitrary-seq sorry (its
conclusion `SeqDominated M` is seq-free, so "any descent ⟹ a standard-dominated descent exists" is false —
`F_diag`). Fixed by threading the seq-specific **`SeqStdBounded seq M := ∃ l₀:ℕ, ∀ n y, seq[y,n] → iC y ≤
iF l₀ n`** (Rathjen Lemma 3.2) through `seqDescent_dominated` / `prwoInstance_models_of_goodstein` /
`goodstein_implies_prwo` (now `(hstdom : ∀ M⊧IΣ₁, SeqStdBounded seq M) → 𝗣𝗔⊢γ → 𝗣𝗔⊢prwoInstance seq`),
supplied at `gentzenDescentφ` by the disclosed axiom `gentzenDescentφ_dominated`. **Result:**
`seqDescent_dominated` is now a TRUE conditional lemma; its sorry = the genuine Cor-3.4 construction (β from
seq's descending branch + the standard-level slowdown using `hstdom`). **THE crux-1 next target** = prove
`seqDescent_dominated` (paths B/C above). NB its hardest input (`hstdom` for `gentzenDescentφ`) is gated on
crux 2's `ord`/`R` arithmetization, so the independent crux-1 work is the GENERAL construction
(`seqDescent_dominated` for an abstract `SeqStdBounded` descent).

## ⭐ Lap 55 — crux-1 frontier collapsed to TWO clean inputs + the model-theoretic route for `goodstein_implies_prwo`

**Done this lap (all axiom-clean `[propext, choice, Quot.sound]`, src build green 1315):**
- **`hdef` (definability) FULLY DISCHARGED.** `src/InternalIg`: `ig0_definable`, `ig_definable`
  (meta-induction on level, proved at `𝚺₁`), `igtTot_definable`. `wip/StdCor34`: `bbtail_definable`,
  `bbeta_definable`, `salpha_definable`, then **`hdef_of_beta_definable`** (the whole `bbeta∘salpha`
  tower is `𝚺₁`-definable from a single `𝚺₁-Function₁ β` premise) and **`crux1_internal_run_of_beta_def`**.
- **`hdom` reduced to clean WIDTH-domination.** `BlkRec.off_succ_lt_width_of_blk_eq` (within a block the
  offset is strictly below the width) + `StdCor34.hdom_of_width_dom` + **`crux1_internal_run_of_width_dom`**:
  the domination premise is now just `∀ n, znth wseq n ≤ iF l₀ n` (the concrete instance of Rathjen
  Lemma 3.2).
- **iF growth bricks (Lemma 3.2 substrate), `src/IIter`:** `self_le_iIter`/`self_le_iF` (inflationary
  `n ≤ iF l n`), `le_iIter_add` (iterate monotone in count), `iF_le_succ_level`/`iF_mono_level`
  (`l ≤ l' ⟹ iF l n ≤ iF l' n`, n≥1), `iF_one` (`iF 1 n = n + n`).

**Crux-1 frontier is now EXACTLY two inputs to `crux1_internal_run_of_width_dom`:**
  (a) a **definable ≺-descending NF `β`** and (b) **width-domination** `∀ n, znth wseq n ≤ iF l₀ n`.

**THE ROUTE for `goodstein_implies_prwo` (model-theoretic — ungates it from arithmetizing ord/R):**
Foundation has `LO.FirstOrder.complete_iff : T ⊨ φ ↔ T ⊢ φ` (`Completeness/Completeness.lean:69`). So
`𝗣𝗔 ⊢ prwoInstance seq` ⟺ `prwoInstance seq` holds in **every** model `V ⊧ 𝗣𝗔`. Proof of
`goodstein_implies_prwo`: from `𝗣𝗔 ⊢ γ` get (soundness) `𝗣𝗔 ⊨ γ`; for any `V ⊧ 𝗣𝗔`, `V ⊧ γ`; if
`V ⊭ prwoInstance seq` there is an internal infinite `seq`-descent ⟹ build `β` (NF ordinal codes from
the descent) + width-domination ⟹ `crux1_internal_run_of_width_dom` gives an internal non-terminating
Goodstein run = `V ⊭ γ`, contradiction. Hence `V ⊧ prwoInstance seq` ∀V ⟹ `𝗣𝗔 ⊢ prwoInstance seq` by
`complete_iff`. **No ord/R arithmetization needed for this skeleton** — the deep content moves into the
single per-model obligation "internal `seq`-descent ⟹ (NF `β` + standard-`l₀` width-domination)".
- The **width-domination is where the primrec-only restriction bites** (an arbitrary `seq`-descent may be
  diagonal-fast, undominable — `Grz.F_diag_not_dominated`). For the headline we only need the ONE concrete
  instance `seq = gentzenDescentφ`, whose width `C(ord(Rⁿd₀))` IS standard-`l₀` dominated by Lemma 3.2
  (see [[crux1-headline-needs-only-standard-level]]). So either (i) thread a standard-`l₀` domination
  hypothesis through `goodstein_implies_prwo`, or (ii) specialize it to descents with a domination
  certificate. NEXT LAP: set up the `complete_iff` skeleton in `wip/GentzenCon.lean`, isolating the
  per-model descent→β+domination obligation as the lone sorry.

## Reflection — 2026-06-23 (lap 53, DEEP) — direction KEEP; honest endpoint named
Full synthesis: `REFLECTION-2026-06-23-lap53.md`. Kernel re-verified (headline 0 math axioms, faithful
bridge clean, build green 1313). Route A **re-derived from the mathematics and KEPT** (Goodstein⟹PRWO,
not free-X-TI — §3 is primrec-only, the free-X bridge is the *wrong direction*, not merely hard).

- **DIRECTION CALL: KEEP.** Route A (Rathjen Cor 3.7) is correct and standard. The lap-52 NEXT (assemble
  `ig` + port g-properties + wire `StdCor34`) is the right next move.
- **KEEP doing:** drive **crux 1** (`goodstein_implies_prwo`, 🟡 tractable, ~80% built) to a clean
  axiom-free assembly — this is the hardest-first move among *resolvable* doubts and lands `γ→PRWO`
  axiom-clean, the next real milestone. Keep the `wip/GentzenCon.lean` scaffold + SEAM guards. Keep the
  banked Thm-5.6 monument (do not touch/resurrect/delete).
- **STOP doing:** (1) open-ended crux-1 substrate that isn't on the `ig → StdCor34.salpha →
  InternalThm35 → nonterminating_internal → goodstein_implies_prwo` critical path — every brick must
  answer "does this bring the `goodstein_implies_prwo` *body* closer?" (lap-49's generic-V `icorAlpha`
  tower failed that test and was banked). (2) Further crux-2 investment beyond the existing scaffold:
  crux 2 (`PRWO→Con`) is **🟠 GENERATIONAL** — arithmetizing Gentzen's `ord`/`R`/eq-(5) inside PA, with
  **no upstream shortcut** (confirmed lap 53: Foundation's `Hauptsatz.main` is meta-level; no arithmetized
  ordinal analysis in Foundation/mathlib; the meta-level Thm-5.6 machine can't be reused). The scaffold
  already isolates it to the single cited `ord_R_descends` axiom; chip only opportunistically.
- **HIGHEST-VALUE NEXT TARGET:** finish crux-1's `goodstein_implies_prwo` (the lap-52 NEXT list).
  Reasoning: it is the *resolvable* feasibility doubt, it de-risks half the headline with a concrete
  checkable win, and it crystallizes the honest endpoint — *crux-1 built + crux-2 cited eq-(5) +
  `PA_delta1Definable` upstream*, best-case headline `[propext, choice, Quot.sound, PA_delta1Definable]`.
- **FLAGGED FOR OPERATOR:** that best-case is NOT DIRECTION rule #1's strict trust base; the
  `PA_delta1Definable` cost is inherent to Route A's Gödel II. Recommendation: accept the single disclosed
  upstream axiom (orthogonal to the Goodstein mathematics). Needs a review/operator call before the
  headline `sorry` is ever discharged.

## ⭐⭐⭐ Lap 54 (cont.) — Cor 3.4 → Thm 3.5 internal chain ASSEMBLED end-to-end (modulo named hyps)
`wip/StdCor34.lean` now imports the promoted `GoodsteinPA.InternalIg` and assembles the real
internal-Grzegorczyk tail into the Thm-3.5 sequence (both axiom-clean `[propext, choice, Quot.sound]`,
`lake env lean wip/StdCor34.lean` green; src build green 1315):
- **`salpha_igtTot_spec l₀ (hl₀ : 0 < l₀) …`** — instantiates `salpha (↑l₀) β blk off (igtTot l₀)` and
  proves the NF + (∃K, tight C-bound) + ≺-descent triple. The four unconditional `igtTot` props discharge
  `salpha_isNF`/`salpha_C_le` outright; `salpha_desc` reduces to the **single domination input** `hdom`
  (`∀ j, blk(j+1)=blk j → off j + 1 < iF l₀ (blk j)`) via `igtTot_within`.
- **`bbeta_of_igtTot …`** — feeds that triple into `InternalThm35.bbeta_isNF`/`bbeta_C_le`/
  `bbeta_desc_exists`, producing `∃ K s, 0<K ∧ NF ∧ iC(β'ᵣ)≤r+1 ∧ ≺-descent` — the complete Thm 3.5
  output (the input `DescentArith`/Lemma 3.6 consume).
- **`bbeta_of_igtTot_blkRec …`** — specializes `blk/off := BlkRec.blk/off wseq`, discharging the
  bookkeeping (`hblk_dich`/`hoff_adv`/`hnm`) directly from the src `BlkRec` laws. So the whole Cor 3.4
  → Thm 3.5 girder is now built from a single width code `wseq` + **just two deep inputs**: the input
  ≺-descending NF `β` and the domination `hdom` (`∀ j, blk(j+1)=blk j → off j + 1 < iF l₀ (blk j)`).

**`crux1_internal_run` — WHOLE girder chained to the non-terminating run (axiom-clean):** added the
seam to the Lemma-3.6 consumer. `nonterminating_of_bbeta_facts` repackages the `bbeta` triple as
`DescentSlowdown.nonterminating_of_slowdown`'s input (`iCanon (r+1) = iC ≤ r+1`, definitional).
`crux1_internal_run l₀ (0<l₀) wseq …` chains `igtTot → salpha → bbeta → Lemma 3.6` to
`∃ m₀, ∀ k, 0 < igoodstein m₀ k` (internal Goodstein run never terminates — the contradiction).
The ENTIRE internal-Grzegorczyk crux-1 girder is now machine-checked end-to-end, with the remaining gaps
isolated to exactly **three named hypotheses**:
1. **input `β`** (`hβNF`/`hβ0`/`hβdesc`/`hβC`) — the gentzen ε₀-descent as a ≺-descending NF V-sequence;
2. **`hdom`** — domination (Lemma 3.2): `off j + 1 < iF l₀ (blk j)`;
3. **`hdef`** — `𝚺₁`-definability of `bbeta K s (salpha (↑l₀) β (BlkRec.blk wseq) (BlkRec.off wseq)
   (igtTot l₀))` (∀ K s; uniform construction). STARTED (lap 54): the leaf instances
   **`iblk_definable`/`iblockIdx_definable`/`iblockOff_definable`** are now in `src/InternalIg` (explicit
   `DefinableFunction₂/₃.comp` terms — `definability` aesop blows its depth on the nested `ocOadd`/`iwseq`,
   per memory). **KEY UNLOCK still owed: an `ite`-definability lemma** (`fun x => if P x then f x else g x`
   definable from definable `P`,`f`,`g`) — Foundation has NO direct helper; build it via the graph
   disjunction `z = ite ↔ (P ∧ z=f) ∨ (¬P ∧ z=g)` as a `Defined` Semisentence. That unlocks
   `ig0`/`ig`(meta-induction on `l`)/`igtTot`/`bbtail` already-comp/`bbeta`/`icorAlpha`/`salpha`
   definability — the rest of the chain. NB `bbtail` is `iadd`/`iomul`/`ocOadd`/`/`/`%` comp (no ite);
   `bbeta` and `ig0`/`igtTot` are the ite ones; `ig` also needs meta-induction `∀ l, Function₂ (ig l)`.

**REMAINING crux-1 frontier (hardest-first), all now isolated as named hypotheses of `bbeta_of_igtTot`:**
1. **`hdom` = domination (Rathjen Lemma 3.2)**: `off j + 1 < iF l₀ (blk j)` — the within-block offset
   stays below the Grzegorczyk width. THE deep arithmetic brick; needs the specific input `β`/level `l₀`.
2. **`blk`/`off` bookkeeping + input `β`**: the `blk`/`off`/`hblk_dich`/`hoff_adv`/`hnm` come from
   `BlkRec` (in src); the raw ≺-descending NF `β` (`hβNF`/`hβ0`/`hβdesc`/`hβC`) is the gentzen-descent
   instance encoded as ε₀-codes — needs the descent-graph → V-internal-β bridge.
3. **Reflection lift**: from the V-internal descending sequence to the PA-provability statement
   `𝗣𝗔 ⊢ prwoInstance seq` (`wip/GentzenCon.lean:137` `goodstein_implies_prwo` `sorry`) via
   `DescentArith.nonterminating_internal` (needs Σ₁-definable `m`,`b` + internalized `ineq6_step`).
Inspect `src/GoodsteinPA/Domination.lean` (Dom ns) + `DescentSlowdown.lean` + `DescentArith` for (1)/(3).

## ⭐⭐ Lap 54 (cont.) — TOTALIZED `igtTot` (unconditional NF/≠0/exp/C), in-range within-descent
After the 5 raw `ig` props, built `igtTot l n m := if m < iF l n then ig l n m else ig0 0 0` and its
interface (all axiom-clean, `lake env lean wip/InternalIg.lean` green): `isNF_igtTot`, `igtTot_ne_zero`,
`higt_exp_igtTot`, `iC_igtTot_bound` are now **UNCONDITIONAL** (resolving the lap-53-flagged `higt0`
reconciliation — the `salpha_*` interface demands these ∀ n m, but raw `ig` is 0 out of range; the fixed
nonzero finite default `ig0 0 0 = ω^0·2` totalizes them). The within-block descent `igtTot_within`
(`m+1 < iF l n → icmp (igtTot (m+1))(igtTot m) = 0`) STAYS in-range — this is the single seam where
**domination (Lemma 3.2)** enters when wiring `salpha_desc`'s `higt_within` (offsets `< block width ≤
iF l (blk)`). So `igtTot` now satisfies ALL of `salpha_isNF`/`salpha_C_le` unconditionally, and
`salpha_desc` modulo the domination-backed within condition.

**NEXT (crux-1, hardest-first = DOMINATION):** the remaining deep brick is Rathjen **Lemma 3.2**: the
block-width `iC(β(t+1)) ≤ iF l₀ (blk)` for the specific `β` from `InternalThm35.bbeta` / the gentzen
descent, at a STANDARD level `l₀`. This is what makes every `salpha` offset in-range (feeds
`igtTot_within`). Until domination lands, the `salpha → bbeta → nonterminating_internal →
goodstein_implies_prwo` chain cannot close. Also still owed: the reflection/Δ₁ lift from the V-internal
`nonterminating_internal` machinery to the PA-provability statement `𝗣𝗔 ⊢ prwoInstance seq`
(`wip/GentzenCon.lean:137` `goodstein_implies_prwo` `sorry`) — a large separate layer. Inspect
`src/GoodsteinPA/Domination.lean` (`Dom` namespace, ℕ-level `toOrdinal`/`bump` bounds) + `InternalThm35`
for the β/level interface before attacking.

## ⭐⭐ Lap 54 — ALL 5 `igt`-interface props BUILT (`higt_within` + `higt0`, axiom-clean, wip)
The two remaining `StdCor34.igt` bricks landed in `wip/InternalIg.lean` (`lake env lean` green, full
`lake build GoodsteinPA` still green 1314; all axiom-clean `[propext, choice, Quot.sound]`):
- **`higt_within` — THE deep brick** (`m < iF l n → icmp (ig l n (m+1)) (ig l n m) = 0`, internal
  `Grz.g_desc`). Meta-induction; base `icmp_ig0_desc`; step decomposes `m`'s block via the **new
  `iblock_step` dichotomy** (within: `iblockOff↦+1`, index fixed ⟹ `icmp_iblk_within` + IH with offset
  `< iF l (iIter…)` from `iblockOff_lt_width`; boundary: `iblockOff↦0`, index `+1` ⟹ coeff strict drop
  via `iblockIdx_lt` + monus arithmetic ⟹ `icmp_iblk_boundary`; exhaustion: `ig(m+1)=0 ≺` positive
  `iblk` via `icmp_zero_ocOadd`).
- Supporting generic bricks added (all in the `Support` section, generic `f`/`fDef`/`hf`):
  `iblockIdx_common`/`iblockOff_common` (prefix-invariance re-express `m`-state on the longer common
  code `iwseq…(m+1+1)` so the `BlkRec` step laws apply — the `m` vs `m+1` codes differ otherwise),
  `iblock_step` (`BlkRec.blk_off_within`/`_boundary`), `ipsum_le_add`/`ipsum_le_of_le` (monotonicity),
  `iter_le_ipsum_diag` (`Grz.F_succ_le_psum`), `iblockIdx_lt` (`Grz.blockIdx_lt`, by contradiction).
- **`ig_ne_zero` = `higt0`** (`m < iF l n → ig l n m ≠ 0`): `ig0`/`iblk` are `ocOadd…≠0`.

**5 of 5 igt props DONE: `isNF_ig`(higtNF), `higt_exp_ig`(higt_exp), `iC_ig_bound`(higtC),
`higt_within`, `ig_ne_zero`(higt0).** NEXT crux-1 step (no more `ig`-internal bricks): wire them into
`wip/StdCor34.lean` — `igt n m := ig l₀ n m`, supply the 5 hyps to `salpha_isNF`/`salpha_desc`/
`salpha_C_le`, then `salpha_*` → `InternalThm35.bbeta` → `DescentArith.nonterminating_internal`
(Lemma 3.6) ⟹ `goodstein_implies_prwo`. ⚠️ STILL OWED before claiming crux 1: (a) the `habove`/`iAbove`
input the `salpha_*` lemmas want (relate `ocExp (ig …)` to `iVbigMul (β…) (l+1)` — `higt_exp_ig` gives
the `< ω^(l+1)` shape; need the `iAbove` packaging); (b) reconcile the `salpha` `higt0` hyp being stated
UNCONDITIONALLY vs `ig_ne_zero` being in-range only (guard `igt` or weaken `salpha`); (c) the DEFERRED
`icmp`-code ↔ `natCode`-order seam; (d) the `off j < iF l₀ (blk j)` within-block hypothesis feeding
`higt_within` at the StdCor34 level.

## ⭐ Lap 53 (post-reflection grind) — `ig` recursion + structural invariants BUILT (axiom-clean)
Started the crux-1 `ig` assembly (the lap-52 NEXT). Two deliverables:
- **Promoted `InternalGrz` → `src/`** (sorry-free, axiom-clean since lap 52; charter says completed
  proofs live in `src/`). Build green **1314 jobs**. Added to the `GoodsteinPA.lean` aggregator.
- **NEW `wip/InternalIg.lean`** (compiles clean via `lake env lean`, all lemmas axiom-clean
  `[propext, choice, Quot.sound]`):
  - `iF_pos : ∀ l x, 1 ≤ x → 1 ≤ iF l x` — positivity preservation of every meta-level (the `hfpos`
    input the `InternalGrz` decomposition laws need), by meta-induction via `iIter_pos`.
  - **`ig : ℕ → V → V → V`** — the internal Grzegorczyk `g` (mirror of `Grz.g`), meta-recursion on the
    standard level: `ig 0 = ig0`; `ig (l+1) n m = iblk (l+1) (max 1 (n - iblockIdx)) (ig l (iIter … n
    iblockIdx) iblockOff)` for `m < iF(l+1) n` else `0`. **Coefficient `max 1 (n - iblockIdx)` is the
    faithful internal mirror of Rathjen's `(n-blockIdx).toPNat'`** (`Grz.g` uses an `ℕ+` coeff) — equal
    to `n - iblockIdx` in the live regime, clamped to `1` out of range ⟹ NF holds unconditionally
    (sidesteps needing `iblockIdx < n` up front). Recurrence eqns `ig_zero`/`ig_succ_of_lt`/`ig_succ_of_ge`.
  - **`higt_exp_ig`** (internal `Grz.g_lt`, the `< ω^(l+1)` shape): `ocExp (ig l n m) = 0 ∨ ∃ j ≤ l,
    ocExp = ocOadd 0 j 0` — a DIRECT case analysis on the outermost constructor (NO induction; the top
    exponent is read off `ig0`/`iblk l`/`0`). This is the `StdCor34.habove_of_igt_exp` input (`higt_exp`).
  - **`isNF_ig : ∀ l n m, isNF (ig l n m)`** (internal `Grz.g_NF`, unconditional) — meta-induction;
    base `isNF_ig0`, step `isNF_iblk` (live coeff + NF tail via IH + tail nests below `ocOadd 0 (l+1) 0`
    via `higt_exp_ig`, discharged by `icmp_zero_ocOadd`/`icmp_ocOadd_lt_coeff`).

**`higtC` DONE (2nd lap-53 commit, axiom-clean):** `iC_ig_bound : ∀ l, ∃ Kg>0, ∀ n m, iC (ig l n m) ≤
Kg·(n+m+1)` (internal `Grz.g_C_bound`). Meta-induction; base `Kg=2` via `iC_ig0_le`, step `Kg=max ↑(l+1) K`
with the three `iC_iblk` pieces each `≤ Kg·(n+m+1)` — the clamped coeff `max 1 (n-bi) ≤ n+1` is FREE
(monus, no `iblockIdx < n` needed), the tail via the new supports `iIter_le_add_ipsum` +
`iter_add_iblockOff_le` (`tn+tm ≤ n+m`, internal `Grz.iter_add_blockOff_le`). The in-range branch derives
`1 ≤ n` (since `iF(l+1)0 = 0`). So 3 of 5 igt-interface props are built: **`higtNF`=`isNF_ig`,
`higt_exp`=`higt_exp_ig`, `higtC`=`iC_ig_bound`**.

**NEXT crux-1 bricks (remaining `StdCor34.igt` interface, hardest-first):**
1. **`higt_within` — `m < iF l n → icmp (ig l n (m+1)) (ig l n m) = 0`** (internal `Grz.g_desc`,
   `Grzegorczyk.lean:599`). The deep recursive within-block descent; meta-induction with within-block
   (`iblockOff → +1`, IH via `icmp_iblk_within`) vs block-boundary (`iblockOff → 0`, coeff drops via
   `icmp_iblk_boundary`) vs exhaustion (`ig (m+1) = 0`) cases. The hard port — needs internal
   `iblockIdx`/`iblockOff` step laws (`BlkRec.blk_succ_dich`/`off_succ_of_blk_eq` are the substrate).
2. **`higt0` — nonzero in range** (`m < iF(l+1)n → ig l n m ≠ 0`): `iblk`/`ig0` are `ocOadd … ≠ 0`.
   NB the `StdCor34` `higt0` hyp is stated unconditionally — reconcile (either guard `igt` to be nonzero
   everywhere, or weaken the `salpha_*` hyp to in-range; design call when wiring).
Then `igt n m := ig l₀ n m`, port the five into `higtNF`/`higt0`/`higt_within`/`higtC`/`higt_exp`, wire
`StdCor34.salpha_*` → `InternalThm35.bbeta` → `nonterminating_internal` ⟹ `goodstein_implies_prwo`.

## ⭐⭐⭐ Lap 52 — crux-1 bricks 1 + 2-core BUILT (green, axiom-clean, wip)
Discharged the two `wip/StdCor34` interface obligations' substrate (lap-51 designated NEXT):

- **Brick 1 DONE — `wip/BlkRec.lean`** (axiom-clean): the definable block bookkeeping `blk`/`off` as a
  single internal `𝚺₁` primitive recursion (`boStep` state machine: advance offset within a block,
  roll to next block when `off+1 ≥ W(blk)`) over an **abstract width sequence code `wseq`** (read by
  `znth wseq (blk j)`) — sidesteps internal `findGreatest`. Proves exactly the `StdCor34.salpha`
  bookkeeping hyps: `blk_succ_dich` (= `hblk_dich`), `off_succ_of_blk_eq` (within-block off-advance,
  behind `higt_within`), `blk_add_off_le` (= `hnm`) ⟹ `blk_le` (for `hβC`). Independent of β.

- **Brick 2 CORE DONE — `wip/IIter.lean`** (axiom-clean): the reusable internal-iterate primitive
  `iIter fDef f hf x c = f^[c] x` for a **fixed** `𝚺₁`-function `f` (graph `fDef`) at an **internal**
  count `c : V`, as a `PR.Construction` with both recurrence laws + `𝚺₁`-definability of `(x,c) ↦ f^[c]x`
  + `iIter_natCast` (standard `k` ⟹ meta-iterate `f^[k]`). This is the engine `iF (l+1) n = (iF l)^[n] n`
  needs (internal iteration at standard meta-level l ⟹ NO internal Ackermann).

**Brick 2 — `iF` + `ipsum` substrate DONE (`wip/IIter.lean`, axiom-clean); REMAINING = block-decomp + `ig`:**
- ✅ `iF : ℕ → (V → V)` built by meta-recursion (Subtype bundle `iFwith` carries function+Def+proof):
  `iF_zero`/`iF_succ`/`iF_defined` + `iF_natCast` (standard agreement `iF l ↑k = ↑(Grz.F l k)`).
- ✅ `ipsum f n i = Σ_{t=1}^i f^[t] n` (`Grz.psum` internalized): `ipsum_zero`/`ipsum_succ`/`ipsum_defined`
  + monotonicity. Generic over the fixed `𝚺₁`-fn `f`, so it serves every `iF l`.
- ✅ `wsumc` + `wsumc_blk_le` (`wip/BlkRec.lean`, codex review lap 52): the elapsed-WIDTH invariant
  `wsumc (blk j) ≤ j` that `salpha_C_le`'s `hβC` actually needs — `blk_le` (block count) alone was an
  OVERCLAIM. `wsumc_blk_add_off : wsumc(blk j) + off j = j` (exact, under positive widths).
- ⚠️ **wseq SEAM (codex lap 52):** `BlkRec.blk/off` read the width from a finite sequence CODE `wseq`
  (`znth wseq b`); the IIter substrate (`ipsum`) reads it from a definable width FUNCTION. For crux-1
  integration these must meet. Two routes: (a) build a concrete definable global width `W t = iC(β(t+1))`
  and thread its Def (couples `BlkRec` to β); (b) **prefix-invariance** — prove `blk wseq j` depends only
  on `znth wseq b` for `b ≤ blk j` (≤ j), so a *long-enough prefix code* of the true widths gives the
  correct `blk/off`. Route (b) keeps `BlkRec` abstract; add `blk_prefix_congr`/`off_prefix_congr` next.
- ⏭ NEXT: `iblockIdx`/`iblockOff` over `iF l` (level sets of `ipsum (iF l) n`). Mirror `Grz.blockIdx`/
  `blockOff` but AVOID internal `findGreatest` — use the `BlkRec.boStep` state-machine idiom (a width
  recurrence whose width at block `i` is `iIter (iFDef l) (iF l) (iF_defined l) n (i+1)`), giving
  `psum_blockIdx_le`/`blockOff_lt_width`/`psum_add_blockOff` internally. Needs `ipsum` monotonicity +
  a `≤ n` cap (blocks `< n`). Then `iF l`/`ipsum`/block-decomp standard-agreement lemmas as needed.
1. `ig : ℕ → V → V → V` meta-recursion: `ig 0 = ig0` (built), `ig (l+1) n m = iblk (l+1) (n - iblockIdx…)
   (ig l (iF l^[…] n) (iblockOff…))` for `m < iF (l+1) n` else 0 (mirror `Grz.g`). Port `g_NF`/`g_lt`/
   `g_desc`/`g_C_bound`/`g_exp` ⟹ the `StdCor34` `igt` interface (`higtNF`/`higt0`/`higt_within`/`higtC`/
   `higt_exp`). Then `igt n m := ig l₀ n m` for the Lemma-3.2 standard level `l₀`.
Then wire `BlkRec.blk/off` + `igt` into `StdCor34.salpha_*` → `InternalThm35.bbeta` → `DescentArith.
nonterminating_internal` (Lemma 3.6) ⟹ `goodstein_implies_prwo` body (crux 1).
⚠️ Then verify the DEFERRED DEEPER SEAM (`icmp`-code ↔ `natCode`-order) before claiming crux 1.

## ⭐⭐⭐ Lap 51 — SEAM CHECKS (operator-directed): crux-1↔crux-2 chain VERIFIED at statement level
Added 3 machine-checked guards to `wip/GentzenCon.lean` (compile iff the seams hold; green modulo the
2 disclosed crux sorries):
- **Seam 1 (ONE shared PRWO):** crux 1 *outputs* `𝗣𝗔 ⊢ prwoInstance gentzenDescentφ`, crux 2 *consumes*
  the same — the composition `gentzen_prwo_implies_consistency (goodstein_implies_prwo gentzenDescentφ ·)`
  type-checks ⟹ both reference the **identical** `prwoInstance` def (same `precφ` ε₀-order). ✓
- **Seam 2 (Con is Foundation's `Con[𝗣𝗔]`):** `example (hγ) : False := peano_not_proves_consistency
  (goodstein_implies_consistency_via_gentzen hγ)` type-checks ⟹ the assembly's `↑𝗣𝗔.consistent` is
  **definitionally** the object Gödel II (`consistent_unprovable 𝗣𝗔`) forbids — not a lookalike. ✓
- **Seam 3 (end-to-end = the girder):** `not_proves_of_implies_consistency
  goodstein_implies_consistency_via_gentzen : 𝗣𝗔 ⊬ ↑goodsteinSentence` — same type as `Reduction.lean`'s
  `goodstein_implies_consistency` girder; the assembly drops in once both crux sorries are real. ✓

**⚠️ ONE DEEPER SEAM STILL DEFERRED (verify when crux-1's BODY is wired):** the above guard seam 1 only
checks the prwoInstance *def* is shared between the two crux STATEMENTS. The crux-1 *proof*
(StdCor34 slow-down → `goodstein_implies_prwo`) works on `InternalONote` codes ordered by `icmp`/`isNF`;
but `prwoInstance`/`precφ` order the descent by `natCode` (`precφ_spec : ℕ⊧![m,n] precφ ↔ natCode m <
natCode n`). So wiring crux-1's body needs the bridge **`icmp a b = 0 ↔ natCode-order`** (and
`isNF`-code ↔ valid CNF notation) — i.e. that the StdCor34 descent β (icmp-code form) IS the descent
`prwoInstance gentzenDescentφ` quantifies over. This is the F-φ-flavoured code↔order seam; check it the
moment `goodstein_implies_prwo`'s sorry starts getting filled (ANTI-FRAUD: re-`#print axioms` the route).

## ⭐⭐⭐ Lap 51 — standard-level Cor 3.4 global assembly BUILT (green); crux-1 reduced to 2 concrete bricks
Followed the lap-50 designated next action. Two deliverables, both green:
- **`isNF_iadd_clean` + `isNF_icorAlpha`** (`src/InternalCor34.lean`, axiom-clean, in the build) — the
  missing NF sibling of `icmp_iadd_clean`/`iC_iadd_clean`. Completes the `icorAlpha` brick set: the
  slowed term `ω^(l+1)·β + g` now has ALL FOUR Cor-3.4 properties (within/boundary/C-bound/NF).
- **`wip/StdCor34.lean`** (type-checks at 400k heartbeats, off the build target) — the internal
  **global** Cor-3.4 assembly: `salpha_isNF` / `salpha_desc` / `salpha_C_le` prove that the slowed
  sequence `α j = ω^(l+1)·β_{blk j} + igt(blk j)(off j)` has `isNF` + global `icmp`-descent +
  `iC(α j) ≤ K·(j+1)` — **exactly the input `InternalThm35.bbeta` (Thm 3.5) consumes** — by composing
  the `icorAlpha_*` bricks. This is NEW non-vacuous content (the ℕ-template `Grz.corAlpha_*` only has
  the per-step lemmas; the global ∀j descent is vacuous in ℕ but real inside `V ⊧ 𝗜𝚺₁`).
  GOTCHA banked: `iadd`/`icorAlpha` are semireducible → `isDefEq` whnf-loops on variable-level args
  even on identical terms; `attribute [local irreducible] iadd icorAlpha` makes defeq structural.
  And `habove`'s 3rd arg feeds `β (blk a)`, so boundary leads `β(blk(j+1))`/`β(blk j)` need `a=j+1`/`a=j`
  (NOT `blk j+1`), keeping `salpha(j+1)` un-`hb`-rewritten.

**Crux 1 now reduces to discharging the `wip/StdCor34` interface hypotheses (2 concrete bricks):**
1. **Block bookkeeping `blk`/`off`** = internal `iwsum`/`iwidx`/`iwoff` (partial sums + `findGreatest`
   over the width fn `t ↦ iC(β(t+1))`), giving the dichotomy `blk(j+1) ∈ {blk j, blk j+1}`, the offset
   relations, and `blk j + off j ≤ j`. MECHANICAL `𝚺₁` recursion (mirror `Grz.wsum`/`widx`/`woff` +
   the PR.Construction idiom in `InternalCor34.iAboveTable`). Self-contained, axiom-clean-achievable.
2. **The `ig`-tail recursion `igt n m`** = internal Grzegorczyk `g` (`Grz.g`) at STANDARD level: NF /
   `≠0` / within-block descent / `iC ≤ Kg·(n+m+1)` / `iAbove(ocExp(igt n m)) (ω^(l+1)·…)`. Bottoms at
   `ig0`/`iblk` (built); the deep part is the meta-l recursion over the F-block decomposition, needing
   internal `iF_l` (standard l ⟹ fixed primrec, IΣ₁-total — NO internal Ackermann).
Then wire `salpha` → `bbeta` → `DescentArith.nonterminating_internal` (Lemma 3.6) → contradicts γ =
`goodstein_implies_prwo` (crux 1). **THE remaining hard wall stays crux-2 eq (5)** `ord(R d) ≺ ord d`.

## ⭐⭐⭐⭐ Lap 50 KEY INSIGHT — crux 1 for the HEADLINE needs only STANDARD level (internal-Ackermann wall is OFF-path)
Re-derived + paper-validated (Rathjen `scratchpad/rathjen.txt:401`, Lemma 3.2). Memory
`crux1-headline-needs-only-standard-level`. **This re-frames the project's hardest crux.**

- `goodstein_implies_consistency = crux2 ∘ crux1` uses crux 1 at the **single instance**
  `seq = gentzenDescentφ` (= graph of `n↦ord(Rⁿd₀)`), NOT for all primrec descents (PRWO is a schema).
- `H(n,d)=ord(R^[n]d)` is a **concrete** primrec function ⟹ Lemma 3.2 gives a **STANDARD** Grzegorczyk
  level `n₀` (PA-provable bound, independent of the internal arg `d₀`). `f_{n₀}` is then a fixed primrec
  fn, IΣ₁-total, evaluable at internal `d₀`. **No internal Ackermann.** The laps-45→49 internal-`l`
  conclusion was correct only for FULL PRWO (∀ internal-index descent) — the headline never needs that.
- ⟹ **crux 1 downgraded from generational to tractable engineering.** Build STANDARD-level internal
  Cor 3.4 (abstract over a descent with a STANDARD-l domination hyp `∃ l:ℕ, ∀n, C(β(n+1))≤f_l n`):
  * Reuse the ABANDONED standard lead `InternalCor34.ibigMul (k:ℕ)` + `ig0`/`iblk` (the lap-49 generic-V
    `iVbigMul`/`icorAlpha` tower was unneeded effort for the headline — keep banked, not on the path).
  * Blueprint = sorry-free ℕ-template `Grzegorczyk.lean` (`corAlpha`/`corAlpha_C_bound`/`_within`/`_boundary`,
    `g`/`g_desc`/`g_C_bound`, `F`).
  * Downstream DONE: internal Thm 3.5 (`InternalThm35.bbeta_*`), Lemma 3.6 (`DescentArith.nonterminating_internal`).
  * Discharge the standard-l domination for the gentzen descent via Lemma 3.2 once `ord`/`R` exist.
- **THE remaining hard wall is now crux 2's eq (5)** `ord(R d) ≺ ord d` (Gentzen reduction, Buchholz [6];
  Foundation Hauptsatz is meta-level only ⟹ from-scratch arithmetization). Crux 1 is no longer the bottleneck.
- ⚠️ NOT yet built/verified — validate the standard-level internal Cor 3.4 type-checks + `#print axioms`
  clean before relabeling crux 1 done.

**NEXT-LAP first action:** start `wip/StdCor34.lean` (or extend `InternalCor34`) — the standard-level
abstract Cor 3.4 over `ibigMul`, mirroring `Grz.corAlpha_*`. Then wire to `InternalThm35` + Lemma 3.6.

## ⭐⭐⭐ Lap 50 (2026-06-23) — REVIEW + crux-2 PRWO formulation BUILT & faithfulness-certified
Fresh-mind review. **Direction KEEP** (Route A = Rathjen Cor 3.7). Crux-1 step-3 (internal `ig`
f-recursion → internal Grzegorczyk `F`, Ackermann-level) is **blocked on infra Foundation lacks** —
so this lap advanced the *unblocked* **crux 2** (Gentzen `PRWO→Con`), per the lap-49 handoff.

**Foundation map (Explore, lap 50):** NO universal evaluator / Kleene-T predicate (`code`/
`codeOfPartrec'`/`codeOfREPred` all encode a *meta* function into a *fixed* formula). ⟹ **PRWO must be
a per-formula schema**, which is exactly what the proof needs (crux 1 proves all instances; crux 2 uses
the one for `n↦ord(Rⁿd₀)`). `Con(𝗣𝗔)` = `Theory.consistent : 𝚷₁.Sentence`; Gödel II =
`consistent_unprovable [T.Δ₁][𝗜𝚺₁⪯T][Consistent T]`; arithmetized derivations =
`Theory.Derivation : V→Prop` (`Bootstrapping/Syntax/Proof/Basic.lean:459`); Hauptsatz is **meta-level
only** (not arithmetized — no shortcut for eq 5). See memory `crux2-prwo-schema-no-universal-evaluator`.

**DONE this lap (`wip/GentzenCon.lean`, type-checks, 2 disclosed crux sorries):**
- `prwoInstance seq := “¬∀ n y z, (!seq y n ∧ !seq z (n+1)) → !precφ z y”` — reuses `SeamDefinability.precφ`
  (the ε₀-ordering ℒₒᵣ-formula); no `isNF` needed (`natCode : ℕ ≃ NONote` bijects onto all CNF).
- **`prwoInstance_faithful` PROVED** (`ℕ⊧prwoInstance seq ↔ ¬∀n y z, seq[y,n]→seq[z,n+1]→natCode z<natCode y`;
  axioms = trust base + 1 🟢 F-φ native_decide) — the formulation is **kernel-certified faithful**.
- `gentzenDescent_descends`/`derivesEmpty_iterate` PROVED (the `n↦ord(Rⁿd)` descent from `ord_R_descends`).
- assembly `goodstein_implies_consistency_via_gentzen` = `crux2 ∘ crux1` type-checks = the `Reduction.lean`
  girder interface (validates the architecture).

**NEXT — crux-2 deep cores (hardest-first), all in `wip/GentzenCon.lean`:**
1. **`ord_R_descends` (eq 5)** — THE Gentzen reduction ordinal-descent. Ground in Buchholz [6]
   (`papers/buchholz-on-gentzens-first-consistency-proof.pdf` + `siders-…pdf`). Hardest.
2. **`ord`/`R` as arithmetized primrec functions** over `Theory.Derivation` + `R_preserves_empty` +
   `gentzenDescentφ` (the ℒₒᵣ graph of `n↦ord(Rⁿd₀)`, `d₀`=least ⊥-proof).
3. **`gentzen_prwo_implies_consistency` (crux 2)** — assemble: `¬Con ⟹` derivation `d₀` of ⊥ ⟹ the
   `gentzenDescent` is an infinite ≺-descent ⟹ contradicts `prwoInstance gentzenDescentφ`. Needs the
   reasoning INSIDE 𝗣𝗔 (the `prwoInstance` must be applied to the internal `d₀`).
4. (crux 1, separate girder) **`goodstein_implies_prwo`** — Rathjen §3 internal Cor 3.4 (blocked, see below).

## ⭐⭐⭐ Lap 49 (2026-06-23) — generic-route Cor 3.4 lead bricks + crux-2 grounded
Confirmed **M1 (`goodsteinTerminates_re`) and Phase-1 reduction (`not_proves_of_implies_consistency`)
are already complete & axiom-clean** — the operator's named M1 target was done by a prior lap; the only
open obligation is the deep Phase-2 girder `Reduction.goodstein_implies_consistency` (crux 1+2 below).

**CRUX 2 grounded this lap (Rathjen 2014 Thm 2.8, read pp. 8–11) → `CRUX2-GENTZEN-2026-06-23.md`.** The
Phase-2 Gentzen girder `PRWO(ε₀)→Con(PA)` decomposed lemma-by-lemma over Foundation's ARITHMETIZED
`Theory.Derivation : V → Prop` (located): `prwoSentence` (the hinge — formulate PRWO, highest confab risk),
primrec `ord`/`R` on coded derivations, `ord(R D) ≺ ord D` (Gentzen reduction, the deep core), assemble
via primrec descent `n ↦ ord(R^[n] d)` vs PRWO. Independent of crux 1; NOT blocked on Ackermann. Next-lap
candidate if crux-1's Ackermann-`F` infra stays blocked. Keep crux-2 scaffold sorries in `wip/`.

**Done this lap (`InternalCor34.lean`, axiom-clean, green 1311):** the generic Cor 3.4 lead at a
*non-standard* level `l : V` (the meta-`ibigMul (k:ℕ)` was only the standard-level special case).
- `oadd1iter_eq_succ` / `iAbove_ibigMul_finCode` — cast the `MinExpGe` threshold iterate to finite-code
  form (standard level).
- **`iVbigMul β l = (ω·)^l β`** — V-indexed `ω^l·β` as a genuine `𝚺₁` primitive recursion (`PR.Construction`,
  mirror of `iAboveTable`), with `isNF_iVbigMul`/`icmp_iVbigMul`/`iC_iVbigMul_le` by `sigma1_succ_induction`.
- **`iAbove_finCode_iVbigMul`** — V-indexed MinExpGe: `ω^(l+2)·β` clean above finite code `l+1`.
  (Motive-definability needed an EXPLICIT `Definable.comp₂` term — aesop blows up on the `iAbove` rule;
  see memory `definability-aesop-depth-blowup`.) Plus `iVbigMul_ne_zero`, `isNF_finCode`, `iadd_one_finCode`,
  `iAbove_zero_iVbigMul`.

**DONE — steps 1 & 2 of the prior plan (this lap, all green/axiom-clean):**
1. ✅ **Generic clean-append on `iVbigMul`** — `iAbove_code_iVbigMul`, `iAbove_ocExp_iVbigMul_fin/_inf`
   discharge `iAbove (ocExp g) (iVbigMul β (l+1))` for finite or infinite-top-exponent `g < ω^(l+1)`.
2. ✅ **`icorAlpha` assembly** — `icorAlpha β g l := iadd (iVbigMul β (l+1)) g` with the three portable
   Cor-3.4 properties: `icorAlpha_within` (`icmp_iadd_clean_within`), `icorAlpha_boundary`
   (`icmp_iadd_clean_boundary`+`icmp_iVbigMul`), `icorAlpha_C_le` (`iC_iadd_clean`+`iC_iVbigMul_le`).
   Validated end-to-end at level 0 with concrete `ig0` (`icorAlpha_ig0_within`). NB: `iVbigMul` is now
   `irreducible` (its `construction.result` never reduces on a variable level → whnf blow-up); the full
   4-hyp `icmp_iadd_clean` also blows up on unification — use the `_within`/`_boundary` wrappers.

**NEXT — two genuinely deep, isolated remaining pieces (crux 1 step 3):**
3a. **The internal `ig` f-recursion over level `l:V`** — `ig (l+1) n m = iblk (l+1) (…) (ig l (f^[blk] n)
   (off))` bottoms out at the internal Grzegorczyk `F` (Ackermann-level, NOT IΣ₁-total ⟹ needs the FULL-PA
   reduct `reduct_models_PA`, a different layer than this `V ⊧ 𝗜𝚺₁` file). Abstract-`ig` interface (provide
   `isNF`, `ocExp(ig) = code j ∨ 0` with `j ≤ l`, `ig ≠ 0`, `iC(ig) ≤ K(n+m+1)`, within/boundary descent as
   hyps — exactly what `icorAlpha_*` consume) defers the F-construction; discharge `f` separately.
3b. **The X-definable block bookkeeping** (`corBlk`/`corOff` over the raw descent's C-widths `corW β t =
   iC(β(t+1))`) — assembles the global slow sequence `α : V → V`. **KEY FINDING this lap: this is NOT cleanly
   IΣ₁** — `W = corW β` is X-definable (β lives in the LX descent layer, `DescentConstruction`), so `iwsum`/
   `iwidx`/`iwoff` must be built X-definably THERE (mirror `Grz.wsum`/`widx`/`woff`, lines 159-217), not in
   this generic-`V` file. The resulting α feeds `InternalThm35.bbeta` (Thm 3.5, DONE) → `nonterminating_of_xDescent`.

## ⭐⭐⭐ Lap 47 (2026-06-23) — internal Thm 3.5 COMPLETE; the two §3/Gentzen cruxes are next
Discharged lap-46 item 4's remaining input: **ω-tower cofinality** `iwtower_cofinal : ∀ c, ∃ s, icmp c
(iwtower s) = 0` (`InternalThm35`, axiom-clean), proved with NO NF hypothesis (`icmp_ocOadd_lt_exp` reads
only the leading exponent, so `sigma1_order_induction` at `ocExp c < c` decides the whole code; witness
`s` = the iterated-exponent depth). ⟹ `bbeta_desc_exists` gives the full Thm 3.5 descending sequence
**unconditionally** (no `hbdry`). **Internal Thm 3.5 is now hypothesis-free and route-independent.**

**The two open deep cruxes (hardest-first), both multi-lap — the live work:**
1. **Internal Cor 3.4** (THE harder). Produce the slow internal descent `α : V → V` (`iC(αₙ)≤K(n+1)`,
   `isNF`, `icmp`-descent) from a raw primrec ε₀-descent. Internal level `l:V` ⟹ Ackermann ⟹ needs the PA
   substrate. **Recommended first attack (lap-45 path #2): parameterize over an abstract internal `f`**
   (recursion eqns + Lemma-3.2 domination as hypotheses); build `ig`/`icorAlpha`/descent+bound relative to
   it; discharge `f`'s existence separately. Blueprint = `Grzegorczyk.lean` ℕ-template. The standard-`l`
   `InternalCor34` (`ig0`/`iblk`/`ibigMul`) is reusable bricks (special case), NOT the generic route.
2. **Gentzen Thm 2.8(i) `PRWO(ε₀)→Con(𝗣𝗔)`** + formulate **`PRWO(ε₀)` as a `Sentence ℒₒᵣ`**. Primrec `ord`
   + reduction `R`, `ord(R D)<ord D`, over Foundation `Derivation`. THE deep ordinal-analysis girder.

**Decision for next lap:** start crux 1 via the abstract-`f` parameterization (path #2) — it lets the
genuine `g`-padding math land green now without first building internal Ackermann. See `Reduction.lean`
docstring + STATUS "Where it stands" for the full chain.

**Crux-1 PROGRESS (lap 47, `InternalCor34.lean`, axiom-clean):** Cor 3.4's slowed term
`αⱼ = ω^(l+1)·βₙ + g(l,n,m)` needs a GENERAL clean append (`g` is a genuine ordinal `< ω^(l+1)`, not the
finite tail the `betaTail` lemmas handle). Built the internal analog of `Grz.AllExpAbove`/`C_add_clean`:
- `iadd_clean_step` — the `gt`-branch recursion of `iadd` under the clean head condition.
- `iAbove e0 a` (Σ₁-flag predicate via a parameterized course-of-values table, + `iAbove_zero`/`iAbove_ocOadd`
  recursion) — "every leading exponent down `a`'s spine `≻ e0`" (internal `MinExpGe`).
- **`icmp_iadd_clean_within`** — two clean appends onto the SAME head compare by their tails:
  `icmp (iadd a b₁)(iadd a b₂) = icmp b₁ b₂` (= internal `corAlpha_within`, the `g`-descent through the
  fixed lead). Plus `ocExp_iadd_clean` (head exponent preserved).
**Crux-1 NEXT (hardest-first):**
1. **`icmp_iadd_clean_boundary`** — `icmp a₁ a₂ = 0 → icmp (iadd a₁ b₁)(iadd a₂ b₂) = 0` (head drops; =
   internal `corAlpha_boundary`). Needs the shared-prefix recursion; cleanest with `isNF a₁/a₂` + the
   `icmp = 1 ⟹ equal-code` fact (so equal exponents are literal, enabling `icmp_ocOadd_same_head`). For
   Cor 3.4 use `icmp_ibigMul` gives `icmp a₁ a₂ = icmp β' β`. A unified `icmp (iadd a₁ b₁)(iadd a₂ b₂) =
   thenV (icmp a₁ a₂)(icmp b₁ b₂)` would subsume within+boundary.
2. **`iC_iadd_clean`** — `iC (iadd a b) ≤ max (iC a)(iC b)` under `iAbove (ocExp b) a` (= internal
   `C_add_clean`, the slowness C-split). Also `iAbove`-preservation lemmas for `ibigMul`/`iomul` (the head
   `ω^(l+1)·βₙ` satisfies `iAbove (ocExp g) ·` since `g < ω^(l+1)`) = internal `MinExpGe_bigMul`/`AllExpAbove_bigMul`.
3. Then the abstract-`ig` interface (recursion eqns + descent + `iC ≤ K(n+m+1)` + `ig < ω^(l+1)` as hyps),
   `icorAlpha`, and the internal `ig` recursion on level `l:V` (the f-recursion; the genuinely deep last step).

## ⭐⭐⭐ Lap 46 (2026-06-23) — ROUTE RESOLVED: PRWO(ε₀)→Con(PA)+Gödel II (Rathjen Thm 2.8)
Operator-directed Route A. Lap-45's fork is **settled** (memory `route-resolved-prwo-gentzen`):
- **Headline path** = Rathjen Cor 3.7: `𝗣𝗔⊢γ →(§3, primrec) 𝗣𝗔⊢PRWO(ε₀) →(Gentzen Thm 2.8(i)) 𝗣𝗔⊢Con(PA)`,
  then Gödel II. This IS `Reduction.goodstein_implies_consistency` (now decomposed in its docstring).
- **The free-X β-wall (`DescentSemantic:582`) is the WRONG target**: §3 is primrec-only; an oracle X
  descent isn't dominated (machine-checked `not_dominated_of_diag_le`). But a **PRWO** descent is
  *internally* primrec ⟹ Lemma 3.2 applies internally ⟹ unblocked. `peano_not_proves_TI` (free-X)
  does NOT chain (free-X-TI ⊢ PRWO, wrong direction) — banked asset, off-path.
- **DONE this lap (axiom-clean):** `InternalThm35.bbtail_isNF/_C_le/_desc` — the model-internal Thm 3.5
  block-tail (`r ≥ K`): from a slow internal descent α produce βᵣ = ω·α_{(r-K)/K}+(K-(r-K)%K) with
  strict ≺-descent and the TIGHT `iC(βᵣ) ≤ r+1`, via internal division. Route-independent.
- **Open cruxes (hardest-first), both deep / multi-lap:**
  1. **Internal Cor 3.4** — Grzegorczyk hierarchy `f:V→V→V` over `V ⊧ 𝗣𝗔` (internal level `l:V`,
     Ackermann, not IΣ₁-total ⟹ needs the PA substrate `reduct_models_PA`). Produces the slow α that
     `bbtail_*` consumes. lap-45 path #2 (parameterize over abstract f) recommended first.
  2. **Gentzen Thm 2.8(i) `PRWO(ε₀)→Con(PA)`** — primrec `ord` + reduction `R`, `ord(R D)<ord D`,
     arithmetized in PA over Foundation's `Derivation`. The deep ordinal-analysis girder.
  3. **Formulate `PRWO(ε₀)` as a `Sentence ℒₒᵣ`** (∀ primrec-code descent → finite); gates both 1,2.
  4. Thm 3.5 **prefix + full β — DONE (modulo one cofinality input)**. `bbeta K s α` (`InternalThm35`)
     is the complete Thm 3.5 sequence indexed from `0`: ω-tower prefix for `r<K` (SIMPLIFIED to single
     towers `βⱼ = ω_{s+K−1−j}` — valid since `C` is the max coeff, not term count, so `C=1≤j+1`),
     block-tail `bbtail` for `r≥K`. Axiom-clean: `bbeta_isNF`, `bbeta_C_le : iC(βᵣ)≤r+1` (all r),
     `bbeta_desc` (prefix→prefix / seam / block→block). **Remaining = ONE disclosed hypothesis**
     `hbdry : icmp (bbtail K α K) (iwtower s) = 0` (i.e. `β_K ≺ ωₛ`): ω-tower **cofinality** in ε₀
     — `∀ NF code c, ∃ s, c ≺ iwtower s`, with a concrete `s = σ(α₀,K)`. Next lap: prove cofinality.
     Supporting: `iwtower` (ω-tower on codes), `icmp_iwtower_succ`, `icmp_ocOadd_lt_exp`.
- Foundation `PA_delta1Definable` axiom rides Gödel II (separate residual; lap-6 noted upstream burndown).


## ⭐⭐ Lap 45 (2026-06-23) — VALIDATED PIVOT: §3-on-X is BLOCKED; route is now Trevor's call
**Read `E-ARCHITECTURE-REVIEW-2026-06-23.md` §H + `HANDOFF.md`.** Independently re-derived in-box AND
confirmed against the external review. The lap-27→44 plan (run Rathjen §3 slow-down on the X-definable
descent → free-X `TI_≺(X)`) is **structurally blocked, not merely hard**:
- `peano_not_proves_TI` is genuinely **free-X** (checklist #1: `Xsym` free, `prec` concrete) — the
  *strong* back-end; a §3 reduction to primrec-PRWO cannot reach it.
- The §3 domination `∃ l, ∀ n, C(β(n+1)) ≤ F_l n` is **FALSE for an X-definable descent** — now
  MACHINE-CHECKED (`Grz.not_dominated_of_diag_le`/`F_diag_not_dominated`, commit `279050d`): the
  Grzegorczyk hierarchy's diagonal escapes every fixed level, so domination is primrec-only.
- Root cause of the misalignment: a non-standard / X-definable descent needs an **internal** (V-level,
  Ackermann) Grzegorczyk level — NOT a fixed meta-l — and `f_l` for `l:V` is NOT IΣ₁-provably total.
  So the lap-40→44 meta-iterate `ibigMul` / meta-recursion `ig` design cannot produce the needed β.

**THE FORK (Trevor decides — do NOT pick unilaterally; lap-12 forbade Route A's axiom on the headline):**
1. **Route A** (Rathjen's actual proof): primrec §3 → primrec-PRWO → Con(PA) → Gödel II.
   `Grzegorczyk.lean` already fits (primrec). Cost: disclosed `PA_delta1Definable` (still an `axiom` in
   the pin) + the unbuilt `TI(ε₀)⊢Con(PA)` girder (`Reduction.lean:52`; PA∞ cut-elim — distinct from
   Buchholz §5). Attack paths: (a) check if a Foundation pin-bump discharges `PA_delta1Definable`
   upstream (lap-6 noted a session was on it); (b) build the Gentzen ordinal-analysis girder.
2. **Route B via Kirby–Paris 1982** (model-theoretic indicators): keep free-X; replace §3-on-X with
   the KP indicator argument inside `M ⊧ paLX` (the wall `no_min_descent_absurd_of_goodstein` is already
   model-internal — natural continuation). Avoids the axiom. Read `papers/kirby-paris-1982-…pdf`.
   Attack paths: (a) formalize indicators / the Σ₁-definable "gap" function; (b) the
   Paris–Harrington-style density argument adapted to Goodstein.
3. **§3-on-X: DEAD** — `InternalCor34` meta-l grind must NOT resume.

**Survives regardless:** `peano_not_proves_TI` (axiom-clean), `Grzegorczyk.lean` (primrec §3, Lemma 3.3
complete + the obstruction lemma), `InternalONote` code arithmetic, `InternalCor34.ig0` + general
`ocOadd` descent lemmas (substrate-agnostic leaves).

### SHARPENED (lap 45, end) — the crux is localized to Cor 3.4; Thm 3.5 + Lemma 3.6 are done/tractable
Grounded the Route-A back-end against Rathjen pp.13–14 (Lemma 3.6, Cor 3.7, Thm 2.8). Precise map:
- **Lemma 3.6** (the special-Goodstein run never terminates, given `C(βₙ) ≤ n+1`) = repo's **DONE**
  `DescentArith.nonterminating_internal` / `DescentSlowdown.slowdown_run_facts` (axiom-clean).
- **Thm 3.5** (slow `α` → `β`, `C(βᵣ) ≤ r+1`) is **level-agnostic, no Ackermann, IΣ₁-tractable**: finite
  tails + `r = K(n+1)+i` *division* indexing. Internal C-bound `iC_betaTail_le` LANDED (lap 45); descent
  = `icmp_betaTail_within/_boundary`, NF = `isNF_iadd_finite` (built). Remaining: the `β:V→V` assembly
  (internal division reindex + the `j<K` ω-tower prefix) — mechanical, route-agnostic.
- **Cor 3.4** (raw descent → slow `α`, the Grzegorczyk `g`-padding) = **THE deep crux, common to both
  routes.** Needs the Grzegorczyk level `l`; for ANY *quantified/generic* descent (Route A's ∀-primrec
  PRWO, or Route B's oracle X-descent) `l` is **internal (`l:V`)** ⟹ `f_l` is Ackermann ⟹ **NOT
  IΣ₁-provably-total** ⟹ needs a **PA substrate** (`V ⊧ₘ* 𝗣𝗔`), not the IΣ₁ `PR.Construction` toolkit.
  CORRECTION to the lap-45 mid-note: the meta-`l` `InternalCor34` design (`ig0`, `iblk`, `ibigMul`) is
  NOT outright dead — it is the **standard-`l`** special case (correct when the descent's level is a
  fixed standard natural), and `ig0` + the general `ocOadd` lemmas are reused by the internal-`l` version.
  But the *generic* slow-down needs internal `l`.

**3 attack paths for the Cor 3.4 crux (internal-`l` `g`-padding):**
1. **Build internal Ackermann/Grzegorczyk `f : V→V→V` over `V ⊧ 𝗣𝗔`** (Σ₁-graph + PA-totality by
   induction on the level), then `ig`/`icorAlpha` by PA-induction on `l:V`. Most direct, heaviest.
2. **Parameterize over an abstract internal `f`** (take `f`'s recursion eqns + Lemma-3.2 domination as
   hypotheses / a structure supplied by `M ⊧ 𝗣𝗔`), build `ig`/`icorAlpha`/descent+bound relative to it,
   and discharge `f`'s existence separately (disclosed). Lets the genuine `g`-math land green now; most
   tractable. ⟸ RECOMMENDED first.
3. **Restructure `g` to avoid `f_l`**: define blocks by the descent's *actual* widths (incremental V
   recursion) and prove the linear `C`-bound directly. Risk: the linear bound may genuinely need the
   Grzegorczyk recursion (Rathjen's `g` is built that way precisely for the linear bound) — may be false.

**Route decision still open** (Trevor): (A) Rathjen Con(PA)+Gödel II [carries `PA_delta1Definable`; reuses
Cor 3.4 + Buchholz §5 for Thm 2.8] vs (B′) Kirby–Paris model-theoretic indicators [axiom-clean back-end;
fresh technique]. Cor 3.4 (internal-`l`) is needed by (A); (B′) replaces §3 entirely with indicators.


## ⭐ Reflection — 2026-06-23 (lap 44, DEEP) — the wall `sorry` is framed on a DEAD path; rewire it FIRST

Full synthesis in `REFLECTION-2026-06-23-lap44.md`. Two findings:

- **(A) `DescentSemantic.no_min_descent_absurd_of_goodstein` (`:574`) routes through the DEAD 𝚺₁ path.**
  The literal `sorry` lives inside `hCD`, which uses `hbound` (`∃ m₀ b, 𝚺₁-Function₁ b ∧ …`) +
  `DescentArith.nonterminating_internal`. But the bound `b` is built from the **X-definable** descent, so
  it is genuinely **X-dependent** ⟹ no 𝚺₁ `b` exists in a general model ⟹ the `hbound` 𝚺₁ shape is
  **UNACHIEVABLE / FALSE**, not just hard. **Action (next lap, do first):** rewire `hCD` to the in-file
  **`nonterminating_of_xDescent`** (lap 41, X-essential `lx_succ_induction`). It needs `β : M → M` with
  `∀k isNF (β k)`, `∀k iCanon (k+1) (β k)`, `∀k icmp (β(k+1)) (β k)=0`, and the LX-definable run comparison
  `hPdef`. The residual `sorry` then becomes the HONEST "produce `β`" obligation. The 𝚺₁ engine
  (`nonterminating_internal`/`hbound_of_slowdown`/`nonterminating_of_slowdown` in `DescentSlowdown`) is
  sorry-free + axiom-clean — KEEP as a banked asset (charter: never delete completed proofs), just stop
  routing the live wall through it.

- **(B) `Grzegorczyk.lean` collapses Rathjen's length `|·|` (Lemma 3.3(2)/Cor 3.4) onto C.** Self-consistent
  on paper (`C ≤ |·|`; the absolute `C(βᵣ)≤r+1` is Thm 3.5, built in `DescentCore.C_betaTail_le` via
  `C_omega_mul_le`) but UNVERIFIED until the ℕ Cor 3.4 assembly (item 1 below) typechecks. If the C-bound
  won't close, define `len : ONote → ℕ` (the symbol-count `|·|`), prove `C ≤ len`, redo Lemma 3.3(2) on
  `len`, and bound `C` via `C ≤ len` at the end.

**Status of the run/consumer side (all DONE):** `nonterminating_of_xDescent`, `slowdown_run_facts`,
`ineq6_step_internal`, `DescentCore` Thm 3.5 reindex + `lemma36_nonterminating`, the unconditional descent
`descentR`/`descent_iterate_seq_total`. The ONLY remaining content = produce the M-internal `β`.

## ⭐ Lap 43 — **Rathjen Lemma 3.3 COMPLETE in the ℕ-template** (`Grzegorczyk.lean`, 6 axiom-clean commits, green 1309)

The genuine combinatorial heart of the slow-down wall (Lemma 3.3, the Grzegorczyk `g`) is now fully
machine-checked in the self-contained ℕ-template `src/GoodsteinPA/Grzegorczyk.lean`:
- `F` (the hierarchy `F 0 n=n+1`, `F (l+1) n=(F l)^[n] n`); `g0` base case.
- `blk k c x = ω^k·c+x` + Rathjen's two ordinal descent cases (`repr_blk_within`, `repr_blk_boundary`).
- Block decomposition `blockIdx`/`blockOff` (via `Nat.findGreatest`) + full correctness specs
  (`psum_blockIdx_le`, `blockIdx_lt`, `lt_psum_blockIdx_succ`, `blockOff_lt_width`, `blockIdx_eq`).
- **`g`** recursion (`g (l+1) n m = blk (l+1) (n-i) (g l (F_l^i n) j)` for `m<F(l+1)n`, else 0).
- Invariants `g_lt` (`repr (g l n m) < ω^(l+1)`), `g_NF`.
- **`g_desc`** (Lemma 3.3(1) DESCENT — the hard property; within/boundary/exhausted case split).
- **`g_C_bound`** (Lemma 3.3(2) BOUND `C(g l n m) ≤ K_l·(n+m+1)`).

**REMAINING toward `hbound` (hardest-first):**
1. **(ℕ-template Cor 3.4 assembly)** — from a descending `β:ℕ→ONote` + a **domination** `∃ l, ∀ n, |β_{n+1}| ≤ F l n`,
   build `αⱼ = ω^ω·βₙ + g l n m` (`j = Σ_{t≤n}|βₜ| + m`, `m<|β_{n+1}|`): descent (within-block via `g_desc`,
   across-block via `βₙ ≻ β_{n+1}` + `ω^ω` absorbing `g<ω^ω`), slowness `C(αⱼ)≤K(j+1)` (via `g_C_bound`).
   Needs a `|·|`-length/`C` measure on `ONote` for the block widths + block-finding on the β side
   (mirror of `blockIdx`). NOTE: the domination hypothesis is where "β primitive recursive" bites
   (Lemma 3.2 = `exists_lt_ack_of_nat_primrec`, + `ack ≤ F l` relation); state Cor 3.4 abstractly over
   the domination so the M-internal version supplies its own.
2. **(Thm 3.5 reindex)** — feed the slow α into the EXISTING `DescentCore` template
   (`C_betaTail_le`, `repr_betaTail_within/_boundary`) ⟹ β' with `C(β'ᵣ)≤r+1` ⟹ `lemma36_nonterminating`.
3. **(M-internalization)** — port the whole ℕ-template chain onto `InternalONote` M-codes; the M-internal
   subtlety is whether the domination holds for the X-dependent descent's block-length function.

## ⭐ Lap 42 (REVIEW) — `IterPrefix_lxDef` DISCHARGED; the descent EXISTS unconditionally; **the real crux is now the Rathjen §3 SLOW-DOWN**

**Done lap 42 (1 commit, axiom-clean, green 1308):** `IterPrefix_lxDef` + `minClause_lxDef`
(`DescentConstruction.lean`) — the lap-41 "lone wall" (`hPdef`). The membership-form trick
(`isDescent_iff_mem`: X-atom on a *bound* variable) that `DescentConstruction.descent_seq_exists`
already used for the `Mlt`-descent applies verbatim to the **`descentR`** route. So `IterPrefix`'s four
clauses (`skel`/`descentMlt`/`minClause`/`xclause`) are each binary-`LX`-definable; the only new one is
`minClause` (the `descentR` minimality `∀ z<x', ¬(Mlt f z x ∧ ¬MX z)` via Foundation `ballLT`). Result:
**`descent_iterate_seq_total : ∀ k:M, IterPrefix hM f a₀ k` is UNCONDITIONAL** — the canonical
`Mlt`-descent prefix exists at every length, no hypotheses. (Lap 41 over-rated this as "genuine
multi-lap infra"; it was one membership-form clause.)

**⚠️ FRESH-MIND COURSE-CORRECTION — the prior `hbound` decomposition under-specified the SLOWNESS.**
The lap-41 plan (piece 1) claimed the extracted descent `α` comes "with `iC(α k) ≤ K(k+1)` (Rathjen
`|αₖ|≤K(k+1)`)". **That is NOT automatic.** `descentR` picks the `<`-least `¬MX` code `≺ αₖ`; its
coefficient `C` is uncontrolled. Rathjen gets the bound only via **Corollary 3.4** (read `papers/
rathjen-2014…pdf` p.11–12): pad an arbitrary descent into a *slow* one (`|αᵢ|≤K(i+1)`) using the
Grzegorczyk function `g` from **Lemma 3.3** (`g(n,m)>g(n,m+1)` for `m<f(n)`, `|g(n,m)|≤K(n+m+1)`).
**Only then** does **Theorem 3.5**'s reindex `β_{K(n+1)+i}=ω·αₙ+(K-i)` give `C(βᵣ)≤r+1`. The lap-41
`InternalONote` toolkit (`iC_iomul`/`iC_iadd_finite`/`icmp_betaTail_*`) is the **Thm-3.5** code
arithmetic; **Cor 3.4 (the `g`/Grzegorczyk padding) is NOT started and is the genuine remaining wall.**

**Also flag (stale code):** `no_min_descent_absurd_of_goodstein`'s `hbound` `sorry`
(`DescentSemantic.lean:569`) still demands a `𝚺₁-Function₁ b`. That is UNACHIEVABLE — `b` is
`X`-dependent (derived from `no_min`/`MX`). The correct route is lap-41's `nonterminating_of_xDescent`
(the `lx_nonterminating`/`X`-essential path). When β is built, **refactor `hCD` to go through
`nonterminating_of_xDescent`**, deleting the dead `𝚺₁` `hbound`+`DescentArith.nonterminating_internal`.

**REMAINING for `hbound`, hardest-first (revised lap 42):**
1. **(HARD CRUX — Rathjen Cor 3.4 slow-down)** — internalize the `g`/Lemma 3.3 Grzegorczyk padding on
   `M`-codes: from an `icmp`-descent of ε₀-codes, produce a SLOW `icmp`-descent with `iC(αᵢ)≤K(i+1)`.
   Lemma 3.2 = mathlib `exists_lt_ack_of_nat_primrec` (ack ≈ Grzegorczyk fₙ). **This is multi-lap.**
   Decompose: (a) ℕ-template `g : ℕ²→ONote` + descent/bound lemmas (Aristotle-eligible, self-contained);
   (b) internalize as `M`-code recursion.
2. ✅ **(DONE lap 42) Extract `α : M → M`** — `descent_alpha_exists` (`DescentConstruction.lean`):
   `α 0=a₀`, `∀k ¬MX(α k)`, `∀k descentR f (α k)(α(k+1))`. Coherence via `IterPrefix_agree` (prefix
   agreement by X-free `sigma1_succ_induction` + `descentR_functional`). Axiom-clean. ⟹ `Mlt`-descent +
   each `¬MX` (`descentR_descends`). NOTE: `α` is NOT yet known slow — that's piece 1 (Cor 3.4).
3. **(plumbing) Decode `Mlt`→`icmp`** on codes (the route-b seam): `Mlt f y x` (`=prec`, X-free) ⟺
   `icmp y x = 0` on the ε₀-code reading; `isNF (α k)`. Needs the `prec`↔`icmp` bridge in `M`.
4. **(ARITH, toolkit ready) Thm 3.5 reindex** `α(slow) → β`, `βᵣ=ω·αₙ+(K-i)` — `iCanon(r+1)`
   (`iC_iomul`+`iC_iadd_finite`), `icmp`-descent (within+boundary), `isNF` (`isNF_iadd_finite`).
5. **`hPdef'` + close** — LX-def of `ievalNat(k+1)(βₖ)≤igoodstein m₀ k` (`lxDef_of_reduct` on the 𝚺₁
   `ievalNat`/`igoodstein` graphs + β's LX-formula); `nonterminating_of_xDescent` ⟹ `hCD` ⟹ `hbound`.
   ANTI-FRAUD: re-`#print axioms` headline (must stay `sorryAx` until the WHOLE chain is real) + girder.

## ⭐ Lap 41 — slow-down toolkit + run engine COMPLETE; `hbound` reduced to "build the X-definable β"

The lone wall is still `hbound` (`DescentSemantic.lean`, now ~line 460). Lap 41 closed the ENTIRE
code-level + run-level half (8 axiom-clean commits, green 1308):
- ✅ `icmp_iomul`, `icmp_betaTail_boundary`, `isNF_iomul`, `isNF_iadd_finite` (`InternalONote.lean`) —
  the slow-down's order/NF lemmas. Toolkit now complete: `iadd`/`iomul`, `iC_iomul`/`iC_iadd_finite`
  (⟹ `C(βₖ)≤k+1`), within+boundary descent, NF preservation, `ineq6_step_internal` (the (6) step).
- ✅ `DescentSlowdown.lean` (NEW): `slowdown_run_facts` (X-agnostic base/step/hpos core),
  `hbound_of_slowdown` (𝚺₁ path), `nonterminating_of_slowdown`.
- ✅ `DescentSemantic.nonterminating_of_xDescent` — **the reduction**: given `β:M→M` with the 3 arith
  facts (NF/iCanon(k+1)/icmp-descent) AND `hPdef` (LX-definability of `T̂^{k+2}(βₖ)≤mₖ`), the run from
  `T̂²(β₀)` never terminates. Via `slowdown_run_facts` + `lx_nonterminating` (X-essential). ⚠ The
  descent is X-DEPENDENT so the run MUST go through `lx_nonterminating`, NOT the 𝚺₁ path.
- ✅ `DescentSemantic.descentR` — the LX-definable functional descent-step relation to iterate:
  `descentR_exists` (=descent_step), `descentR_descends`, `descentR_lxDef`.

**REMAINING for `hbound` — three pieces, hardest-first:**
1. **(HARD CORE) M-internal X-definable iteration `α : M → M`** — `α 0 = a₀`, `α (k+1) = descentR-image`,
   for `k : M`. Build via an **LX recursion theorem**: `lx_succ_induction` over the LX-formula
   `Pk := ∃ s, Seq s ∧ lh s = k+1 ∧ znth s 0 = a₀ ∧ ∀ i<k, descentR (znth s i)(znth s (i+1)) ∧ ∀ i≤k ¬MX(znth s i)`
   (Seq/znth/lh are reduct-𝚺₁ → bridge via `lxDef_of_reduct`; `descentR` clause via `descentR_lxDef`).
   Then `α k := znth (the s) k` extracted via uniqueness. PREREQ: `descentR_functional` (uniqueness —
   needs reduct `<`-trichotomy; M⊧PA⁻ via `ReductModel.reduct_models_PA`, port `lt_trichotomy`).
   Gives `α`: `Mlt`-descending, each `¬MX`, with `icmp (α(k+1))(α k)=0` (decode `Mlt`=`prec`→`icmp` on
   codes — the route-(b) seam) + `isNF (α k)` + a coeff bound `iC(α k) ≤ K(k+1)` (Rathjen `|αₖ|≤K(k+1)`).
2. **(ARITH) Rathjen reindexing `α → β`** — `βᵣ = ω·αₙ + (K−i)`, `r = K(n+1)+i`, `i<K` (block n via
   `r/K`, offset `r%K`). Gives `iCanon(r+1) βᵣ` (`iC_iomul`+`iC_iadd_finite`, ℕ-template
   `DescentCore.C_betaTail_le`), `icmp`-descent (within `icmp_betaTail_within` + boundary
   `icmp_betaTail_boundary`), `isNF` (`isNF_iadd_finite`). Pure code arithmetic, 𝚺₁-definable in r.
3. **`hPdef`** — `T̂^{k+2}(βₖ)≤mₖ` is LX-definable: `lxDef_of_reduct` on the 𝚺₁ `ievalNat`/`igoodstein`
   graphs + the LX-formula for `β` (from 1+2). Then `nonterminating_of_xDescent` ⟹ `hCD` ⟹ close `hbound`.
   ANTI-FRAUD: re-`#print axioms peano_not_proves_TI` (must stay clean) AND `peano_not_proves_goodstein`
   (must stay `sorryAx` until the WHOLE chain is real) after any edit near the girder/headline.

## ⭐ Lap 40 — internal ordinal arithmetic for the slow-down STARTED (2 axiom-clean commits)

Read Rathjen 2014 §3 ("Slowing down", Thm 2.6 proof + Def 3.1) on disk — confirmed the slow-down
(arbitrary ε₀-descent → sequence feeding the **special** Goodstein `igoodstein`) is irreducible and
fundamentally needs `ω·α` multiplication + CNF addition on codes. Built the two foundational internal
ops in `InternalONote.lean` (both `#print axioms`-clean, build green 1307):
- ✅ **`iadd`** (`47c267b`) — internal CNF ordinal addition `a+b` on codes, CofV table indexed by the
  first summand (param = b), 3-way leading-exponent `icmp` branch. Lemmas `iadd_zero_left`,
  `iadd_ocOadd`.
- ✅ **`iomul`** (`1af80bc`) — internal ω-multiplication `ω·c`, exponent bump `e↦1+e = iadd (ocOadd 0
  1 0) e`, recurse tail. Lemmas `iomul_zero`, `iomul_ocOadd`.

**KEY SIMPLIFICATION (lap 40):** `ineq6_step_internal` (the `step`) keeps `ievalNat βₖ` SYMBOLIC —
it only needs `isNF`, `iCanon`, `icmp`-descent of the codes, NOT computed `ievalNat` values. So the
messy `ievalNat_iadd`/`ievalNat_iomul` laws are NOT needed for the assembly. Only `isNF` + `iC`(canon)
+ `icmp`-descent of the `βₖ = ω·αₖ + (K-i)` codes are required.

**DONE this lap (7 commits, all axiom-clean, green 1307):**
- ✅ `iadd` (CNF addition), `iomul` (ω·α).
- ✅ `iC_one_add`, `iC_iomul` (`iC(ω·c) ≤ iC c + 1`), `iC_iadd_finite` (`iC(ω·c + m) ≤ max(iC(ω·c)) m`)
  → the full `C(βₖ) ≤ k+1` canonicity bound (Rathjen Thm 3.5).
- ✅ `icmp_self`, `icmp_betaTail_within` (within-block descent `ω·α+p ≺ ω·α+(p+1)`).
- ✅ `icmp_one_add` (`1+·` preserves the comparison) + helpers — the boundary crux.

**NEXT (hardest-first) toward `hbound`:**
1. **`icmp_iomul`** (`icmp (iomul a)(iomul b) = icmp a b`, ω-mult order-preserving) — structural
   induction via `icmp_one_add` (head) + IH (tail). NF hyps needed.
2. **boundary descent** `icmp (ω·αNext + s)(ω·α + t) = 0` from `icmp αNext α = 0` — via icmp_iomul
   (decision happens in the iomul part, before the appended finite tails).
3. **`isNF_iomul`, `isNF_iadd_finite`** — isNF preservation. Needed for step's isNF hyps.
4. **βₖ assembly** from the M-internal descent (seam) — 𝚺₁-def in k, `iCanon (k+1) βₖ` (iC bounds, HAVE),
   icmp-descent (within + boundary), isNF; `b k = ievalNat (k+1) βₖ`; `step` = `ineq6_step_internal`
   (HAVE); base/hpos; assemble `hbound`. Plus the SEAM rewire (route b) for the descent input.
Aristotle: idle. Candidate open lemma = `icmp_iomul` (self-contained given icmp_one_add). Spec before submit.

## ⭐ Lap 39 — internal arithmetic for `hbound`'s `step` COMPLETE (3 axiom-clean commits)

The lone wall is still `hbound` (`DescentSemantic.lean:416`). Pieces 1–2 of the decomposition are DONE
this lap (all `#print axioms`-clean, build green 1307):
- ✅ **`InternalONote.evalNat_succ_base`** `ievalNat (b+1) c = ibump (b+1) (ievalNat b c)` (isNF/iCanon),
  digit-direct strong induction (helpers `ilog_eq_of_bounds`, `ievalNat_tail_lt`, div/mod peel). `53d1b00`.
- ✅ **`InternalPow.ibump_mono`/`ibump_strictMono`** — ported the Aristotle ℕ blueprint (UUID 7c8bb0e8)
  into clean IΣ₁ (combined UB+strict-mono induction, no nlinarith). `c7675f0`.
- ✅ **`InternalONote.ineq6_step_internal`** — the internalized Rathjen ineq (6), = `hbound`'s `step`:
  `ievalNat (k+2) bk1 ≤ ibump (k+2) m - 1` from `bk1 ≺ bk` + `ievalNat (k+1) bk ≤ m`. Chains
  `evalNat_succ_base` + `ibump_mono` + `ievalNat_lt_of_icmp_eq_zero`. `5f9df55`.

**Remaining to assemble `hbound`** (`∃ m₀ b, 𝚺₁-Function₁ b ∧ b 0 ≤ igoodstein m₀ 0 ∧ step ∧ ∀k 0<b k`):
With `βₖ` the slowed descent, `b k = ievalNat (k+1) βₖ`, `m₀ = ievalNat 1 β₀`: `step` = `ineq6_step_internal`
(HAVE); `base` = refl; `hpos` = `ievalNat_pos` (need `βₖ ≠ 0`). The two HARD remaining pieces:
3. **Seam/F re-wire (route b)** — make `Mlt`/`precφ`/`MX` (in `paLX_models_TI_of_PA_provable`) decode to
   `icmp`/codes, so the `no_min` descent becomes a `≺`-descent of ε₀-codes. RISKY (touches the proven
   `peano_not_proves_TI` girder) — re-`#print axioms peano_not_proves_TI` after EVERY edit (must stay clean).
   FIRST investigate: `DescentLift`/`DescentSemantic` defs of `Mlt`/`MX`/`prec`; `Thm56.prec`/`precφ`;
   `SeamDefinability`. Decide whether a standalone "slow-down of an abstract code-descent" lemma can be
   built BEFORE the seam (so piece 4 proceeds in parallel).
4. **βₖ slow-down (Rathjen Thm 3.5)** + assemble — from the code-descent build `βₖ` with `iC βₖ ≤ k+1`
   (so `iCanon (k+1) βₖ`), still `≺`-descending; `𝚺₁`-definable in k; feed `DescentArith.nonterminating_internal`.

Aristotle: idle (next genuinely-open lemma = the slow-down or the seam; spec one before submitting).

## ⭐ Lap 38 — INTERNAL-ONOTE SUBSTRATE COMPLETE (read `HANDOFF-2026-06-23-lap38.md`)

`InternalONote.lean` now has the full ε₀-notation arithmetic inside `IΣ₁`, all axiom-clean: codes,
`iC`, `ievalNat`, `iCanon`, **`icmp`** (CNF comparison), **`isNF`** (well-formedness), and the **crux
`ievalNat_lt_of_icmp_eq_zero`** (order-reflection, Rathjen 2.3(iii), digit-direct). Remaining road to
`hbound` (`DescentSemantic.lean:392`), hardest-first:
1. internal `evalNat_succ_base` (`ievalNat (b+1) c = ibump (b+1) (ievalNat b c)`) — extract the tail
   bound `ievalNat_tail_lt` from order-reflection's `TB` first; needs `ilog` peel facts.
2. internal `ineq6_step` (port `DescentCore.ineq6_step` onto codes, uses 1 + order-reflection).
3. seam/F re-wire to transparent `natCodeT` (route (b); re-`#print axioms` girder after each change).
4. `βₖ` slow-down (Rathjen Thm 3.5) + assemble `hbound`.
Aristotle `ibump_mono` COMPLETE in `scratchpad/ibump_x/` (ℕ form), not yet ported to V.

## ⭐ Reflection — 2026-06-23 (lap 36, deep): NEW DIRECTION — refactor the sentence transparent. Read FIRST.

Full synthesis: `REFLECTION-2026-06-23-lap36.md`. Headline state (real `#print axioms`): girder
(`Thm56.peano_not_proves_TI`) **clean**; headline honest `sorry`; the chain `…_modulo_semantic` carries
exactly **one** `sorryAx` from `no_min_descent_absurd_of_goodstein`, which is `hCD` (wall C+D, `:410`) +
`hB` (wall B, `:419`).

**The finding — wall B is self-inflicted.** Every lap since 24 treated `goodsteinSentence = ∀⁰ codeOfREPred
goodsteinTerminates` (Foundation's opaque `Classical.epsilon` r.e. blob) as a FIXED target and tried to
*bridge to it* inside nonstandard `M` (wall B; the open `ON-LINE-REQUEST`; the "`PA_delta1Definable`-
flavoured gap"). But `goodsteinSentence` is **not** locked, and `Encoding.lean`'s docstring (lines 35–39)
**explicitly sanctions** refactoring it to a transparent form gated on the bridge spec.

**STOP**: bridging the opaque code; reasoning about `Classical.epsilon` Kleene codes on nonstandard inputs;
treating `goodsteinSentence` as immutable. The `ON-LINE-REQUEST.md` wall-B question is **superseded** — do
not wait on it.

**KEEP**: the lap-30 model-internal completeness architecture; the route-neutral ONote kernel
(`DescentCore`); route 1 (ordinal analysis — monument done; route 2 is no shortcut); `#print axioms` audits.

**✅ Transparent-sentence refactor — DONE lap 36 (wall B dissolved):**
1. ✅ `goodsteinSentence := “∀ m, ∃ N, !igoodsteinDef 0 m N”` (`Encoding.lean`, imports `InternalGoodstein`).
   `InternalPow.igoodstein` IS `InternalGoodstein.igoodstein` (one function, namespace `GoodsteinPA.InternalPow`).
2. ✅ `Bridge.goodsteinSentence_faithful` re-proved axiom-clean — identical locked RHS — eval via
   `InternalPow.igoodstein_defined.iff` + `InternalPow.igoodstein_nat` + `eq_comm`. `models_lMap_goodstein`
   compiled unchanged (form-independent, confirmed).
3. ✅ `hB` (`DescentSemantic.lean:419`) closed: `Semiformula.models_lMap.mp hgood` → `simp only
   [ReductModel.reduct_eq_standardModel]` → coerce `.toStruc ⊧` to `Evalbm (s := @standardModel M oM)`
   (defeq, `models_iff` rfl) → same eval `simp only` set → `hev m₀`. `ON-LINE-REQUEST` archived.
   Real `#print axioms`: `goodsteinSentence_faithful` clean; chain's lone `sorryAx` = `hCD` only.
   GOTCHA banked: to eval a `lMap Φ`-lifted ℒₒᵣ sentence in `M`'s reduct, `models_lMap.mp` gives
   `(inst.lMap Φ).toStruc ⊧ σ`; `simp only [reduct_eq_standardModel]` (NOT `rw` — dependent `reductORing`
   motive) rewrites the reduct to `standardModel oM`, then `have h : Evalbm (s := @standardModel M oM) … := this`
   coerces by defeq (`rw [models_iff]` does NOT fire on the `.toStruc ⊧` form).

**`hCD` NARROWED lap 36 — run side baked in; the lone open obligation is `hbound`.** `hCD`
(`DescentSemantic.lean:409`) now closes via `DescentArith.nonterminating_internal` + the run's
`𝚺₁`-definability (both proved), so the **only** remaining `sorry` is:
```
hbound : ∃ (m₀ : M) (b : M → M), (𝚺₁-Function₁ b) ∧
  b 0 ≤ igoodstein m₀ 0 ∧
  (∀ k, b k ≤ igoodstein m₀ k → b (k+1) ≤ igoodstein m₀ (k+1)) ∧   -- internalized ineq6_step
  (∀ k, 0 < b k)
```
This is the Rathjen §3 slow-down, internalized in `M`'s `𝗜𝚺₁`-reduct. Decomposition for the next laps
(the deep infra; DescentCore has all of it at ONote/ℕ level, the gap is making it `𝚺₁`-definable in `M`):
1. **Internal ordinal-notation codes + `C` (slow-down measure) in `M`.** Need CNF-coded ordinals as
   `M`-elements with `C(β) ≤ k` (`DescentCore.C`/`Canon_iff_C_le`) as a `𝚺₁` predicate on `M`.
2. **Internal `T̂_ω` evaluation** `ievalNat : M → M → M` (base, ordinal-code → value), `𝚺₁`-definable,
   matching `DescentCore.evalNat` on standard inputs (the InternalPow `ipow`/`ilog` substrate feeds this).
3. **Internal `βₖ` slow-down** from the descent `descent_seq_exists` (extract a coherent `a : M → M` or
   reuse the coded `W`; build `βₖ` with `C(βₖ) ≤ k+1` per `DescentCore.C_betaTail_le`), then
   `b k = ievalNat (k+2)^[k+2] (βₖ)`. `𝚺₁`-definable.
4. **Internalized `ineq6_step`** (`step`): the `Δ₀` numeral form of `DescentCore.ineq6_step` (Lemma 3.6,
   ineq (6)) — proved in `M` by its `𝗜𝚺₁` arithmetic. `base`/`hpos` fall out of the `βₖ` positivity.
This is multi-lap infrastructure (internalizing ONote arithmetic into a nonstandard `M`); attack hardest-
first = piece 2 (`ievalNat`) + piece 4 (`ineq6_step` internal), since pieces 1/3 are codings on top.

**LAP-37 progress (numeric bricks + Aristotle dispatch).** Landed `InternalLog.ilog_mono` (`2≤b`,
`0<n≤n'` ⟹ `ilog b n ≤ ilog b n'`, green). Identified that pieces 2/4 both bottom out on **`ibump`/
`evalNat` monotonicity** — the digit-direct "next hard chip" (lap-29 NB1), which is genuinely interdependent
(the per-digit bound and monotonicity are mutually recursive — `ibump b r < (b+1)^(ibump b e)` needs
`ibump b (ilog b r) < ibump b e`, i.e. mono, while mono's `e<e'` case needs that bound). Architected the
self-contained statement and **submitted `ibump_mono` to Aristotle** (UUID `7c8bb0e8-23cc-4118-9bab-70b37a2debbc`,
`scratchpad/ibump_mono.lean`): goal `2≤b → n≤n' → ibump b n ≤ ibump b n'` over ℕ with the true `ibump`/`ipow`/
`ilog` laws as axioms (algebra identical to the V-model, so a clean proof PORTS to `InternalBump`).
NEXT-LAP: poll `aristotle list`; on COMPLETE, verify + port to `src/GoodsteinPA/InternalBump.lean` as
`ibump_mono` (then strict-mono `ibump_strictMono` follows). This is the numeric core that internal `evalNat`
order-reflection (piece 2) and internal `ineq6_step` (piece 4) both consume.

**Also landed lap 37 (green): `DescentCore.evalNat_succ_base`** — `Canon b o → o.NF → 2≤b →
evalNat (b+1) o = bump (b+1) (evalNat b o)` (via `canon_round_trip` + `evalNat_toONote`). THE bridge:
raising the evalNat base by one is exactly the numeric `bump`. So `evalNat (k+2) βₖ = bump (k+2) (evalNat
(k+1) βₖ) = ibump (k+2) (b k)` — meaning the *internal* `ibump` substrate realizes `evalNat`'s base-bump
inside `M` directly (no separate internal ONote-evaluation needed for the base-change). This is the precise
restatement that `ineq6_step`'s `bump (k+2) m = evalNat (k+2) (toONote (k+2) m)` step should be rebuilt on
internally: internal `ineq6_step` = `ibump (k+2) (b k) - 1`-domination + internal evalNat ORDER-REFLECTION
(the still-open piece needing internal ONote codes for the `βₖ₊₁ ≺ βₖ` comparison).

**Refined decomposition of `hbound` after lap 37** (what internal ONote codes are STILL needed for):
- ✅ Base-change (evaluation) side: `evalNat (b+1) o = ibump (b+1) (evalNat b o)` — internalizes via the
  existing `ibump` substrate (`evalNat_succ_base` is the ℕ-shadow; internal version is `ibump`-direct).
- ❌ Order-reflection side: `βₖ₊₁ ≺ βₖ ⟹ evalNat (k+2) βₖ₊₁ < evalNat (k+2) βₖ` — STILL needs internal
  ONote codes + internal `evalNat` as a function of the code (`evalNat_lt_iff`/`evalNat_lt_of_lt`
  internalized). This is the irreducible internal-ONote requirement: the descent comparison.
- ❌ `βₖ` construction (the slow-down Thm 3.5 / Cor 3.4) from the M-internal descent (`descent_seq_exists`):
  needs internal ONote codes + internal `C` + the `C(βₖ) ≤ k+1` bound, all `LX`/`𝚺₁`-definable in `M`.
So the genuine remaining internal-ONote build is the CODE representation + `evalNat` (as code-fn) + `C` +
order-reflection. The base-change/run side is now substrate-direct. NEXT cold-start subproject:
`wip/InternalONote.lean` — code CNF terms as nested HFS pairs (`0 ↦ 0`, `oadd e n r ↦ ⟪⟪ec,n⟫,rc⟫`),
`isONoteCode` predicate (Fixpoint/Δ₁), `iC`/`ievalNat` via course-of-values table (à la `ibumpTable`),
internal `evalNat_lt_iff`. Multi-lap.

**⭐ STRATEGIC FINDING lap 37 (read `ANALYSIS-2026-06-23-lap37-order-reflection-opacity.md`).**
Grounded the order-reflection wall in Rathjen 2014 §3 (paper on disk). The descent is `Mlt f y x =
M ⊧ precφ(y,x)` with `precφ = codeOfREPred₂(natCode a < natCode b)` — the **opaque r.e. blob**, the
SAME opacity that was wall B; `natCode = (Denumerable.eqv NONote).symm` is arbitrary. Rathjen's βₖ
construction (Cor 3.4 / Thm 3.5) manipulates the **CNF** of descent elements, so the descent must be
decodable to CNF in `M`. **Route decision = (b): transparent HFS-CNF coding.** Build internal ONote
codes (a code IS its CNF), define `natCodeT : ℕ ≃ NONote` + transparent `precT`, re-wire seam + F
(`epsilon0_le_orderType_ltPull` holds for ANY `e : ℕ ≃ NONote`, so the order-type half transfers;
F-φ computability is easier for transparent CNF compare). Multi-lap girder refactor of the (axiom-
clean) order argument — re-validate `peano_not_proves_TI` with `#print axioms` at every step.

**✅ FOUNDATION STARTED lap 37 (green, sorry-free, `src/GoodsteinPA/InternalONote.lean`).** Internal
ONote CNF codes as nested HFS pairs: `ocOadd ec n rc := ⟪⟪ec,n⟫,rc⟫+1` (0 ↦ 0), decode projections
`ocExp`/`ocCoeff`/`ocTail` with round-trip simp lemmas, and the **subterm-bound lemmas** `ocExp_lt`/
`ocCoeff_lt`/`ocTail_lt` (+ `_of_pos` forms) — the course-of-values strict-decrease facts the next
recursions need.

**✅ `iC` (internal `C` max-coefficient) LANDED lap 37 (green, sorry-free, `InternalONote.lean`).**
Built `iC : V → V` via the same course-of-values table reduction as `ibump` (`iCTable n = ⟨iC 0,…,iC
n⟩`, `iCNext` reads the two sub-results at `ocExp`/`ocTail` out of the table). Proved `𝚺₁`-definable
(`iC_defined`), `iC_zero`, and the **recursion `iC_ocOadd : iC (ocOadd ec n rc) = max (max (iC ec) n)
(iC rc)`** (Rathjen's `C_oadd`). The CofV-table pattern now proven to work on the new codes.

**✅ `ievalNat` + `iCanon` LANDED lap 37 (green, sorry-free, `InternalONote.lean`).**
- `ievalNat : V → V → V` (Rathjen `T̂^b_ω` on codes) via the binary CofV table (parameter = base `b`),
  `𝚺₁`-definable, with `ievalNat_zero` + recursion `ievalNat_ocOadd : ievalNat b (ocOadd ec n rc) =
  n * ipow (b+1) (ievalNat b ec) + ievalNat b rc` (mirrors `Domination.evalNat_oadd`).
- `iCanon b c := iC c ≤ b` (internal `Canon`, FREE from `iC` via `Canon_iff_C_le`), with `iCanon_zero`,
  recursion `iCanon_ocOadd : iCanon b (ocOadd ec n rc) ↔ n ≤ b ∧ iCanon b ec ∧ iCanon b rc`, and the
  `Γ-Relation` definability instance.

**NEXT — the deep piece: internal order-reflection.** Two routes to the order the descent consumes:
1. `icmp : V → V → V` — 3-valued CNF lexicographic comparison via a BINARY CofV table indexed by the
   pair `⟪o,p⟫` (sub-calls `icmp(ocExp o, ocExp p)`/`icmp(ocTail o, ocTail p)` sit at `⟪e1,e2⟫`/
   `⟪r1,r2⟫` `< ⟪o,p⟫` by `pair_lt_pair`). Then `icmp` ≡ ievalNat-order on `iCanon` codes.
2. Direct internal `evalNat_lt_iff`: `iCanon b o → iCanon b p → isNF o → isNF p → (ievalNat b o <
   ievalNat b p ↔ o ≺ p)`. Structural induction using ievalNat arithmetic + the "tail value < leading
   power" NF bound (`ievalNat b rc < ipow (b+1) (ievalNat b ec)`). This is the SAME difficulty family
   as `ibump_mono` (on Aristotle, UUID `7c8bb0e8`) — harvest that proof's digit-direct technique first.
Also needed: internal `isNF` predicate (exponents strictly decreasing — needs `icmp`), and the internal
`evalNat_succ_base` (`ievalNat (b+1) c = ibump (b+1) (ievalNat b c)` for `iCanon b c ∧ isNF c`, by
structural induction + `ibump_pos`, given the NF leading-power bound). Then seam/F re-wire to `natCodeT`
(route b, `ANALYSIS-2026-06-23-lap37-order-reflection-opacity.md`) and the slow-down `βₖ`.

---

## 🎯 LAP-34 (2026-06-23) — wall-C/D model-internal induction TOOLKIT landed. Read FIRST.

**Done this lap (green 1304 jobs, all `[propext, choice, Quot.sound]`, in `DescentSemantic.lean`):** the
`X`-essential induction toolkit `no_min_descent_absurd_of_goodstein`'s `hCD` (wall C+D) needs, all derived
from lap-33's `lx_succ_induction`:
- `lxDef_ballLT` — `fun x ↦ ∀ y<x, P y` is `LX`-definable when `P` is (installs `Structure.LT LX M` off
  `reductORing`; formula `(φ ⇜ ![#0]).ballLT #0`). The closure step order-induction needs.
- `lx_order_induction` — `<`-below progressivity ⟹ totality for `LX`-definable `P` over `M`'s reduct
  arithmetic `<`. Mirrors Foundation's `InductionOnHierarchy.order_induction`.
- `lx_least_number` — every nonempty `LX`-definable `P` has a `<`-least witness. **The choice-free,
  M-internal selector wall C's `Mlt`-descent recursion picks the canonical `Mlt`-smaller ¬MX element
  with** (resolves the ⚠ "must be definable, not metatheoretic `choice`" subtlety).
- `lx_nonterminating` — **wall-D run side, `X`-essential form.** Given an `LX`-definable bound predicate
  `P k := b k ≤ igoodstein m₀ k`, seed domination `b 0 ≤ m₀`, the internalized ineq-(6) `step`, and
  `0 < b k`, the run never reaches `0`. Iteration is `lx_succ_induction` (NOT the lap-29
  `igoodstein_nonterminating_of_dominating`, which wants an `ℒₒᵣ`-`𝚺₁` bound — but the Rathjen §3 bound
  `b k = T̂^{k+2}(βₖ)` is `X`-dependent, so that ℒₒᵣ tool is the wrong one; this is the corrected substrate).

**Wall-C SCAFFOLD landed in `wip/DescentConstruction.lean`** (typechecks, ONE disclosed `sorry`, off the
build so `src/` stays sorry-free): the `Seq`-coded `M`-internal descent.
- `IsDescent f a₀ W` — `W` codes a finite `Mlt`-descending sequence through `¬MX` from `a₀`.
- `descent_base` / `descent_extend` — **PROVEN** (real content): length-1 base + the canonical one-step
  `seqCons` extension via `descent_step` (incl. all the `znth`-preservation/`¬MX`/descent clauses; the
  generic-`M` order arithmetic uses Foundation `PeanoMinus` lemmas, NOT `omega`/`ring`).
- `descent_seq_exists` — `∀ k, ∃ W, IsDescent W ∧ lh W = k+1`, by `lx_succ_induction` (base/step wired).
  **The lone `sorry`** = `hDdef`, the `LX`-definability of `D(k) := ∃ W, IsDescent f a₀ W ∧ lh W = k+1`
  (a `Seq`-existential `LX`-formula with `Mlt`/`¬MX` atoms on `znth`-terms). NEXT-LAP TASK: build that
  formula. **LAP-35 progress — `isDescent_iff_mem` (PROVEN, wip):** reformulated `IsDescent` into
  **membership form** (over the reduct, when `0 < lh W`): `Seq W ∧ ⟪0,a₀⟫∈W ∧ (∀ i x x', ⟪i,x⟫∈W →
  ⟪i+1,x'⟫∈W → Mlt f x' x) ∧ (∀ i x, ⟪i,x⟫∈W → ¬MX x)`. **Key win:** the `X`-atom now sits on a *bound
  variable* `x`, not a `znth`-function-term — `hDdef` no longer needs `znth`-graph-into-`X` plumbing.
  **NEXT (hDdef, decomposed):** `D(k) ↔ ∃ W, A(W,k) ∧ B(W) ∧ C(W)` with
    - `A(W,k) := Seq W ∧ ⟪0,a₀⟫∈W ∧ lh W = k+1` — pure `ℒₒᵣ`-on-reduct (NO prec/X); `Semisentence` from
      Foundation `Defined.df` (`seq_defined`/`lh_defined`/membership+pairing DSL); bridge via a *binary*
      `lxDef2_of_reduct` (generalize `lxDef_of_reduct` to `![W,k]` + `a₀` as a free-var in `e`).
    - `B(W) := ∀ i x x', ⟪i,x⟫∈W → ⟪i+1,x'⟫∈W → Mlt f x' x` — `∈`-guards + `prec` atom (X-free, fvar-free)
      under bounded `∀∀∀`; build directly in `LX`.
    - `C(W) := ∀ i x, ⟪i,x⟫∈W → ¬MX x` — `∈`-guard + `Xsym`-atom under bounded `∀∀`; build directly.
    Combine via binary `lxDef2_and`, then `∃`-close `W` (`lxDef_exists`, Foundation `eval_ex`). Needed
    combinators (verifiable generalizations of the unary ones in `DescentSemantic`): `lxDef2_and`,
    `lxDef2_of_reduct`, `lxDef_exists`. Then `descent_seq_exists` is sorry-free → promote to `src/`.

**NEXT (wall C — after `hDdef`), hardest-first:**
1. **Build the `X`-descent `a : M → M`** from `no_min`/`ha₀`: `a 0 = a₀`, `a (k+1) =` `lx_least_number`
   applied to the `LX`-predicate `Q y := Mlt f y (a k) ∧ ¬MX y` (nonempty by `no_min`). This needs
   **M-internal recursion** so `a` is `LX`-definable as a function of `k` (Foundation `PR.Construction`,
   the way `igoodstein` was built — but the step is `X`-dependent, so it's an `LX`-recursion, not
   `ℒₒᵣ`-`𝚺₁`; check whether `PR.Construction` admits `LX`-formula steps or needs a bespoke
   sequence-coding (HFS `Seq`) argument). The `Mlt`-strict-descent + `¬MX`-along-`a` are then immediate.
2. **Slow-down `βₖ`** (Rathjen 3.3/3.4/Thm 3.5): from the `Mlt`-descent `(a k)` build `(βₖ)` with
   `C(βₖ) ≤ k+1`, as an `LX`-definable function. The ONote/`C` machinery is in `DescentCore`/`Domination`
   (route-neutral) — port the value facts to internal-`M`.
3. **Define `b k = T̂^{k+2}(βₖ)`, `m₀ = T̂²(β₀)`; prove `(hPdef, base, step, hpos)`** and feed
   `lx_nonterminating` ⟹ `hCD`. `step` is the internalized `DescentCore.ineq6_step`.

Wall B (the opaque `codeOfREPred` ↔ `igoodstein` bridge) is unchanged + literature-gated
(`ON-LINE-REQUEST.md`); independent of wall C/D.

## 🎯 LAP-31 (2026-06-23) — reduct→𝗜𝚺₁ bridge DONE + architecture correction (equality). Read FIRST.

**Verified this lap (green 1303 jobs, axiom-clean `[propext, choice, Quot.sound]`):**
`src/GoodsteinPA/ReductModel.lean` (NEW). The lap-30 plan to run Rathjen §3 inside `M` via the lap-26
`igoodstein` substrate needs `M`'s `ℒₒᵣ`-reduct presented as `[ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]`. This
brick does it:
- `reductORing : ORingStructure M` — read off `M`'s `LX`-interpretation of the ring/order symbols.
- `reduct_eq_standardModel : inst.lMap Φ = @standardModel M reductORing` — via `standardModel_unique`
  (template: Foundation `FirstOrder/Arithmetic/TA/Nonstandard.lean`).
- `reduct_models_PA` / `reduct_models_isigma1` — `M ⊧ paLX ⟹ reduct ⊧ 𝗣𝗔 ⟹ ⊧ 𝗜𝚺₁`
  (via `lMap_PA_subset` + `modelsTheory_onTheory₁` + `models_of_subtheory` on `𝗜𝚺₁ ⪯ 𝗣𝗔`).

**⚠ ARCHITECTURE CORRECTION (the lap-30 plan understated this).** Two genuine subtleties for the
completeness route, BOTH must be handled before the substrate can run inside `M`:

1. **Equality (FULLY SCOPED lap 31 — see `ANALYSIS-2026-06-23-lap31-equality-architecture.md`).** The
   Tait `Derivation` calculus has NO equality rules (verified `Calculus.lean:20`), so
   `completeness_of_encodable` (used by `descentE`) gives models where `=` is an arbitrary relation,
   NOT real equality. The substrate needs real `=`. **Honest precondition = `[Structure.Eq LX M]`**
   (proved sufficient in `ReductModel`). To SUPPLY it, restrict to `[Structure.Eq]`-models via
   `EQ.provOf` (`Completeness/Corollaries.lean`) — which needs **`𝗘𝗤 ⪯ paLX`**. The EXACT gap = ONE
   axiom: **X-congruence `Theory.Eq.relExt Xsym` = `∀x y, x=y → X(x) → X(y)`** (the ℒₒᵣ-part of
   `𝗘𝗤(LX)` is `lMap Φ 𝗘𝗤(ℒₒᵣ)`, already in `lMap Φ 𝗣𝗔⁻ ⊆ paLX`; `𝗘𝗤 ⪯ paLX` `infer_instance`
   FAILS only for X-cong — verified). **NEXT-LAP TASK A**, two parts:
   - **A1 (the crux, deep-but-bounded):** augment `paLX` with X-congruence and re-validate
     `peano_not_proves_TI` — `hax_paLX` needs a NEW branch discharging X-congruence into the
     `PXFc`/`XFreeAx` `Z∞` carrier (it is NOT X-free, so `provable_true_x` doesn't apply; it's not an
     induction instance either). ONE simple true low-complexity axiom → a small bounded-ordinal `PXFc`
     derivation in `EmbeddingBound`/`EmbeddingX`. The `α`/cut-rank bound of `peano_not_proves_TI` is
     otherwise unchanged. This is the real new work; START it next lap.
   - **A2 (plumbing):** `EQ.provOf` + `completeness_of_encodable : T ⊨ φ → T ⊢ φ` + `Semiformula.toEmpty`
     of `TI prec` (`emb_toEmpty` un-coerces) + `provable_def`/`provable_iff_derivable2` → `Derivation2`.
     Fiddly/bounded. Blast radius: `paLX` is woven through 6 files — augmenting its def risks a red
     build; consider a separate `paLX'` (but `peano_not_proves_TI'` still re-runs the embedding, A1).

2. **Opaque headline blob ↔ transparent substrate (THE arithmetization wall).** `hgood` gives
   `reduct ⊧ goodsteinSentence`, and `goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is an
   OPAQUE Foundation r.e.-code (`Encoding.lean`), NOT `∃N, igoodstein m N = 0`. They agree on ℕ
   (`InternalBridge`), but in a nonstandard `M` you need them **IΣ₁-provably equivalent** to use the
   descent contradiction. This is the #4 arithmetization wall (landscape doc). **NEXT-LAP TASK B**
   (deep): either (i) prove `IΣ₁ ⊢ codeOfREPred goodsteinTerminates m ↔ ∃N, igoodstein m N = 0`
   (needs the register-machine ↔ igoodstein computation internalized — very deep), or (ii) reconsider
   making `goodsteinSentence` a transparent igoodstein-Σ₁ form whose ℕ-faithfulness is `InternalBridge`
   (touches the audit surface `Encoding.lean`; Bridge.lean RHS is LOCKED so re-prove faithfulness with
   SAME RHS — `InternalBridge.igoodstein_nat` already supplies it). (ii) is architecturally cleaner but
   needs an anti-fraud review; do NOT do it silently.

**Remaining decomposition of `no_min_descent_absurd_of_goodstein` (the lone wall), hardest-first:**
- (A) reduct→𝗜𝚺₁ — ✅ DONE (this lap, modulo wiring `[Structure.Eq]` via Task A).
- (B) opaque↔transparent (Task B above) — deep, unstarted.
- (C) M-internal `Mlt`-descent from `no_min` via `M`'s LX least-number principle — deep, unstarted.
- (D) slow-down `βₖ`-definable + internal `ineq6` iteration (`DescentCore.ineq6_step` is the kernel) —
  deep; substrate (`igoodstein_nonterminating_of_dominating`) ready to consume `(b, step, hpos)`.

## 🎯 LAP-30 (2026-06-23) — STRATEGIC REDIRECT: the E wall = ONE semantic lemma via completeness. Read FIRST.

**The whole headline now reduces to a single model-theoretic statement.** Fresh-mind review found the
lap-27 plan ("Route B = hand-build the `paLX` sequent derivation of `TI_≺(X)`", literature-gated) is not
the cleanest path. Foundation's **first-order completeness** (`Derivation.completeness_of_encodable`,
general FO, on disk) produces `paLX ⟹ [TI prec]` from the semantic premise "every `M ⊧ paLX` models
`TI prec`". So `Thm56.DescentE` is now **PROVED** (`src/GoodsteinPA/DescentSemantic.lean`, NEW, green 1302
jobs) modulo ONE disclosed `sorry`:

```
paLX_models_TI_of_PA_provable (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M} [Nonempty M] [Structure LX M] (hM : M ⊧ₘ* paLX) (f : ℕ → M) : Evalfm M f (TI prec)
```

`#print axioms descentE` = `#print axioms peano_not_proves_goodstein_modulo_semantic` =
`[propext, sorryAx, choice, Quot.sound, ONoteComp…native_decide.ax_1_5]` — **NO `PA_delta1Definable`, NO
custom axiom**. Discharge the one `sorry` ⟹ the headline is axiom-clean. (Built `LX.Encodable`: 4 small
instances, only `Encodable (XRel k)` was missing.) `Statement.lean` headline `sorry` UNTOUCHED (anti-fraud).

**Why it's correct (vs the superseded sequent plan):** (i) **resolves the free-`X` obstruction** — work in
models of `paLX` (where `X` is `M`'s relation), not `V ⊧ 𝗜𝚺₁`; completeness lifts to a derivation for free;
(ii) **no literature gate** — standard model theory, `ON-LINE-REQUEST.md` question is moot; (iii) **reuses
the lap-26 substrate** — `igoodstein`/`ibump` run in `M`'s `ℒₒᵣ`-reduct, `DescentCore.ineq6_step` is the
kernel. Full map in **`DESCENT-PLAN.md §5`**.

**PROGRESS (lap 30, all green + axiom-clean in `DescentSemantic.lean`):**
- **✅ Step 1 — `M ⊧ lMap goodsteinSentence`.** `models_lMap_goodstein` (E-lift + `provable_def` +
  `Semiformula.lMap_emb` + `models_of_provable` soundness) and `reduct_models_goodstein` (via
  `Semiformula.models_lMap`: `M`'s `ℒₒᵣ`-reduct ⊧ `goodsteinSentence`). Axiom-clean.
- **✅ Step 2 — unfold `TI prec` semantics in `M`.** `evalfm_TI_unfold` : `Evalfm M f (TI prec) ↔
  ((∀x, (∀y, Mlt f y x → MX y) → MX x) → ∀x, MX x)` — **abstract transfinite induction** for `(Mlt, MX)`,
  where `MX a := Structure.rel Xsym ![a]` (M's X) and `Mlt f y x := Eval M ![y,x] f Thm56.prec` (M's ≺).
  Pure `map_imply`/`eval_all`/`eval_rel₁` unfolding + `rfl`. The main lemma now `rw`s this and `intro`s
  progressivity; the lone `sorry` sits on the crisp goal `∀ x, MX x`.

**NEXT — the deep core (`DescentSemantic.lean:144`), hardest-first:** goal `∀ x : M, MX x` given
`hProg : ∀ x, (∀ y, Mlt f y x → MX y) → MX x` and Goodstein-in-`M`. Suppose `¬MX a₀`. Sub-obligations:
1. **M-internal `Mlt`-descent.** `Prog`-contrapositive: `∀x, ¬MX x → ∃y, Mlt y x ∧ ¬MX y`. Build the
   descending sequence **as an M-INTERNAL/definable object** (NOT metatheoretic `choice` — see ⚠ below):
   `G : M → M` by M-recursion, `G(k+1) = ≺`-least `y` with `Mlt y (G k) ∧ ¬MX y`, via `M`'s LX
   least-number principle. NEED: LNP for LX-formulas from `M ⊧ InductionScheme LX` (search Foundation for
   a semantic `leastNumber`/order-induction over models of induction, or derive it).
2. **`M`'s `ℒₒᵣ`-reduct as an `ORingStructure`/`𝗜𝚺₁` model.** `hM ⊧ paLX ⊇ lMap 𝗣𝗔` ⟹ reduct ⊧ `𝗣𝗔` ⊇
   `𝗜𝚺₁`. Bridge the reduct `inst.lMap Φ : Structure ℒₒᵣ M` into the substrate's `[ORingStructure M]
   [M ⊧ₘ* 𝗜𝚺₁]` (instance juggling: the substrate's `igoodstein` uses the ambient `ORingStructure`).
3. **Slow-down + inequality (6) in `M`.** Slow `(G k)` ⟹ `(βₖ)` (`C(βₖ) ≤ k+1`, Rathjen §3); run special
   Goodstein from `m₀ = T̂²(β₀)` (lap-26 `igoodstein` in the reduct); iterate `ineq6_step` by `M`'s
   induction ⟹ `M ⊧ ∀k mₖ > 0`; contradict Goodstein-in-`M`.

**⚠ THE key subtlety (M-internal vs external descent):** the descent must be **M-internal/definable**, not
built by Lean-level `choice` over real ℕ. An external `g : ℕ → M` makes inequality (6) hold only for
*standard* `k`, but `M ⊧ goodstein` gives termination at an `M`-natural `N` that may be *nonstandard* — the
external bound never reaches it. Building `G` M-internally (definable + M-recursion) makes the run align
with `M`'s internal termination statement. This is the crux of why the deep core is genuine work.

**Banked/superseded (true + green, keep in `src/`):** `DescentInternal.igoodstein_nonterminating_of_dominating`
and the `DescentArith`/`sigma1_pos_succ_induction` scaffold are the X-free `V ⊧ 𝗜𝚺₁` framing — their
arithmetic content transfers to step 3, but re-targeted to `M ⊧ paLX`. The internal-bump bricks
(`ibump_pos`, `le_ibump`, `ibump_gt`, + a still-needed `ibump_mono`) are reusable in `M`'s reduct.

## 🎯 LAP-29 (2026-06-23) — `InternalBridge` FINISHED: substrate faithfulness machine-checked. Read FIRST.

**Done this lap (green, 1300 jobs, axiom-clean `[propext, choice, Quot.sound]`):** the lap-28 parked
`ibump_nat`/`igoodstein_nat` bridges are now **theorems** in `src/GoodsteinPA/InternalBridge.lean`. The
internal `𝚺₁`-definable Goodstein substrate (`ibump`/`igoodstein` over a model `V`) is proven to compute
the **audited** `Defs.bump`/`Defs.goodsteinSeq` on the standard model `ℕ` — the anti-fraud faithfulness
link Route B relies on (the internal run is the genuine Goodstein process, not a look-alike).

**The Foundation-ℕ operation diamond is SOLVED** (the lap-28 blocker). Foundation declares `noncomputable
scoped` `Div`/`Mod`/`Sub` instances over any `PeanoMinus` model `V` (built from `Classical.choose!`),
which over `V=ℕ` are **distinct instances** from `Nat.instDiv`/`instMod`/`instSub` (NOT defeq for
`/`,`%`,`−`; only `+`,`*` and `OfNat 0/1` coincide — there is NO `instAdd_foundation`/`instMul_foundation`).
Three bridge lemmas convert them:
- `fdiv_nat`/`fmod_nat`/`fsub_nat` — must state the LHS with the **explicit Foundation instance**
  `@HDiv.hDiv ℕ ℕ ℕ (@instHDiv ℕ (@LO.FirstOrder.Arithmetic.instDiv_foundation ℕ _ _)) x d` (a bare `_`
  resolves to `Nat.instDiv`, the global winner — confirmed via pp.all probe). Proofs: `div_eq_of`
  (foundation) + Nat facts; `sub_spec_of_ge`/`sub_spec_of_le` (foundation) + `omega` (omega treats the
  foundation sub as an atom and the `+` as Nat's).
- **Gotcha:** `igoodstein_succ`'s `ibump (k+2) …` uses the generic `instOfNatAtLeastTwo` numeral (V was
  generic), NOT `instOfNatNat`, so `rw [ibump_nat (k+2) …]` won't match a freshly-written `k+2`; first
  `rw [fsub_nat]` to Natify the `−1`, then `show … (k+2) … = …` to re-cast the numeral (defeq), then
  the rewrite matches. (Saved to memory.)

Route-neutral / on the Route-B path (the substrate doubles as `LX`-formula builders). The ONE wall is
unchanged: **E-core(b) Route-B** (the integrated paLX descent), partially literature-gated (see
`ON-LINE-REQUEST.md` — the precise calculus-internal `Goodstein ⟹ paLX ⊢ TI_≺(X)` shape).

**Also landed lap 29 (`src/GoodsteinPA/DescentInternal.lean`, green, axiom-clean):** wired the bridged
internal run into the (6)-scaffold. `igoodstein_sigma1 (m₀) : 𝚺₁-Function₁ (igoodstein m₀)` (partial
application of `igoodstein_definable` via `DefinableFunction₂.comp`), and
`igoodstein_nonterminating_of_dominating` = `nonterminating_internal` specialized to `m := igoodstein
m₀`. **This makes the RUN side of E-core(b) axiom-clean and pins the precise remaining obligation: a
`𝚺₁`-bound `b k = T̂^{k+2}(βₖ)` with `(base, step, hpos)`.** `step` is the internalized `ineq6_step`
(numeral-Δ₀ form of `DescentCore.ineq6_step`); `b`/`βₖ` is the slow-down side, fed in Route B by the
`X`-definable descent from `¬TI prec`.

**Internal-arithmetic bricks STARTED (lap 29, green, axiom-clean) toward the internal `ineq6_step`:**
- `InternalPow.ipow_le_ipow_left` / `ipow_lt_ipow_left` — `ipow` (strict) monotone in the base.
- `InternalLog.ilog_pos` — `1 ≤ ilog b n` for `b ≤ n`.
- `InternalBump.ibump_pos` — the general positive-argument recursion (`ibump_succ` for arbitrary `0<n`).
- `InternalBump.le_ibump` — `n ≤ ibump b n` (Δ₀-numeral analogue of `Domination.le_bump`), via `𝚺₁`
  order-induction (`ISigma1.sigma1_order_induction`) peeling through `ibump_pos`.
- `InternalBump.ibump_gt` — `b ≤ n → n+1 ≤ ibump b n` (analogue of `Domination.bump_gt`), digit-direct.
- **NB1:** the ℕ proof of `bump_mono` goes *via ordinals* (`toOrdinal` StrictMono), NOT internalizable
  (`DESCENT-PLAN §3b`: avoid internal ONote) — internal `ibump_mono` needs a fresh **digit-direct** proof
  (genuinely subtle: comparing hereditary reps of `a ≤ a'`). This is the next hard chip.
- **NB2 (reusable):** `omega` and `ring` do **NOT** work over a generic model `V` (only `ℕ`/`Int`);
  `ring` is also not imported in the `Internal*` files. Use manual ordered-semiring lemmas
  (`add_le_add`, `mul_le_mul`, `add_right_comm`, `lt_iff_succ_le`, `pos_iff_one_le`, `le_iff_lt_succ`).

**NEXT (hardest-first, offline-tractable pieces):**
1. **Internal `ineq6_step`** (the `step` hyp): the genuine non-vacuous Π₁ kernel as a `Δ₀`-numeral fact
   inside `V` — base-`b` digit form (Rathjen 2.2(ii)), NOT internalized ONote (`DESCENT-PLAN §3b`).
   Build on `ibump` (bridged) + `le_ibump` + internal `ibump`-monotonicity (digit-direct) + internal
   `ibump_gt` (`b ≤ n → n+1 ≤ ibump b n`). Deep, multi-lap; the irreducible content.
2. **The `b`/`βₖ` side**: requires the descending input. In Route B this is `X`-definable from `¬TI
   prec` — literature-gated on the exact paLX shape (`ON-LINE-REQUEST.md`).
3. **Route-B paLX glue**: from `¬TI prec` (free-`X`) extract the descent via the LX least-number scheme;
   contradict the lifted `goodsteinSentence` via `igoodstein_nonterminating_of_dominating`. Skeleton-
   decompose into named `wip/` obligations once the paLX shape is pinned.

## 🎯 LAP-28 (2026-06-23) — F-φ DISCHARGED (in build). ONE wall left: E-core(b) Route-B. Read FIRST.

**Done this lap:** F-φ ported + wired (`src/GoodsteinPA/ONoteComp.lean`); `peano_not_proves_TI` is now
fully axiom-clean (mod trust base + 1 🟢 `native_decide`). The project has **exactly one wall: `DescentE`**
(`Thm56.lean:133`) — the integrated paLX Route-B construction (`𝗣𝗔 ⊢ goodstein → paLX ⊢ TI prec`).

**Attempted + parked (off-critical-path):** the route-neutral faithfulness bricks `ibump_nat`/
`igoodstein_nat` in `InternalBridge.lean` (PENDING-26 NEXT). The math is straightforward strong
induction matching `ibump_succ`/`Defs.bump`, BUT it hit a **Foundation-ℕ operation diamond**: Foundation's
`/`,`%` on a model `V` are `noncomputable scoped instance`s built from `Classical.choose!`
(`IOpen/Basic.lean:86,260`), so over `V=ℕ` they are **NOT defeq** to `Nat.div`/`Nat.mod` (instances
`instDiv_foundation`/`instMod_foundation` ≠ `Nat.instDiv`/`Nat.instMod`). `ipow_nat`/`ilog_nat` work
because `ipow`/`ilog` are hand-built (bridged by their own induction); but `ibump_succ` exposes raw V-`/`,`%`.
- **The fix (next lap):** build two bridge lemmas `Vdiv_nat`/`Vmod_nat` (Foundation `/`,`%` over ℕ = Nat's)
  via `LO.FirstOrder.Arithmetic.div_eq_of` (`hb : b*c ≤ a`, `ha : a < b*(c+1)` ⟹ `a/b = c`) + `rem_graph`
  / `div_add_mod` (`IOpen/Basic.lean:106,267,275`), feeding Nat facts (`Nat.mul_div_le`,
  `Nat.lt_div_add_one_mul_self`) through `le_def`. CAUTION: the scoped Foundation `Div`/`Mod` lose to
  Nat's global instance in plain `a / b` notation — must state the bridges with explicit
  `@HDiv.hDiv ℕ ℕ ℕ <foundation-inst>`. Then `ibump_nat` closes (the `*`,`+` ARE defeq; only `/`,`%` need it).
- This is **route-neutral** (faithfulness link to audited `Defs`), NOT the headline crux. Do it only as
  warm-up / when E-core stalls.

## 🎯 LAP-27 (2026-06-23) — DEEP REFLECTION: F-φ SOLVED on Aristotle; back-end DECIDED = Route B. Read FIRST.

Full synthesis in **`REFLECTION-2026-06-23.md`**. Two changes the grind laps inherit:

**(1) F-φ is solved — PORT IN PROGRESS (`wip/aristotle-fphi/`).** Aristotle proved
`rePred_ltPull_natCode` (verified faithful: verbatim our statement + our `natCode`). **Port started lap
27** (`ONoteComp.v431-port-wip.lean`): reuses our `Epsilon0Complete` scaffolding, 4 proofs fixed, the
`native_decide +revert` >10min hang resolved. **~12 proofs still break on v4.28→v4.31 drift** — full
error analysis + fix recipe + compile-time strategy (low-heartbeat diagnostic; full build is >10min) in
**`wip/aristotle-fphi/PORT-STATUS.md`**. The disclosed `axiom` stays in `SeamDefinability.lean` (TRUE +
PROVEN, honest 🟡) until the port is green. **Mechanical multi-lap port — NOT the crux.** When green:
wire into the lib + SeamDefinability, confirm `#print axioms peano_not_proves_TI =
[propext, choice, Quot.sound]` (+ ≤2 🟢 `native_decide`). If it stays painful (see PORT-STATUS),
deprioritize vs E-core (the actual crux).

**(2) Back-end DECIDED: Route B. STOP the internal-V induction-toward-headline.** The lap 25–26
`DescentArith.ineq6_internal` (`sigma1_pos_succ_induction`) lands X-free `𝗣𝗔 ⊢ PRWO(ε₀)` = **Route A's**
antecedent; it **cannot** feed the built `peano_not_proves_TI` (free-`X` obstruction — exactly the
lap-24 correction; `𝗣𝗔 ⊢ PRWO`/primrec can't refute the X-definable counterexample to `TI prec`, and
E-lift can't make the free `X`). Route A also carries `PA_delta1Definable` (🟡), which anti-fraud
forbids on the headline. **So:**
- **KEEP** the lap-26 arithmetic substrate (`InternalPow/Digits/Log/Bump/Goodstein` + `InternalBridge`)
  — it encodes Goodstein arithmetic as definable formulas, needed by Route B too (~70% transfers).
  **Finish `InternalBridge`** (`ibump_nat`, `igoodstein_nat`) — faithfulness link to `Defs`, route-neutral.
- **STOP** extending `DescentArith.ineq6_internal` toward the headline. It's a true lemma (stays in
  `src/`, green), but it's Route-A-flavored and off the clean-headline path.
- **START** E-core(b) the **Route-B way:** inside a paLX derivation, set up the X-definable descent from
  `¬TI prec` (LX least-number scheme), define the Goodstein run from it via the lap-26 substrate (now as
  `LX`-formula builders), and run inequality (6) as an **`InductionScheme LX`** step (NOT
  `sigma1_pos_succ_induction`), contradicting the lifted X-free `goodsteinSentence` at the X-definable
  seed `m₀ = T̂²(β₀)`. This is the integrated paLX construction the lap-24 correction named — the last wall.

**Fallback endpoint (if E-core(b) Route-B proves intractable after sustained effort):** state E-core as
ONE narrow cited axiom (`DescentE`) on top of the built monument + F — a legitimate, valuable artifact,
and strictly better than Route A's `PA_delta1Definable` + unbuilt `PRWO ⟹ Con(PA)`.

## 🎯 LAP-26 (2026-06-23) — E-core(b) "THE WALL" CRACKED: internal `bump`/`goodsteinSeq` BUILT. Read FIRST.

The lap-25 gating prereq ("make `bump`/`goodsteinSeq` `𝚺₁`-definable inside `V`") is **DONE + axiom-clean**.
Five new files (`InternalPow`/`InternalDigits`/`InternalLog`/`InternalBump`/`InternalGoodstein`) build the
internal Goodstein substrate via Foundation's `PR.Construction` (base-2-only `Exponential` forced a hand-built
`ipow`). Highlights: `ilog_defined : 𝚺₁-Function₂`, `ibump` (table reduction of the course-of-values bump) with
the **proven peel recursion `ibump_succ` = `Defs.bump`**, and `igoodstein` = the concrete `m : V → V` for
`DescentArith.ineq6_internal`. Faithfulness bridge started (`InternalBridge`: `ipow_nat`, `ilog_nat`). Full
details + resolved gotchas (aesop-can't-do-ibumpTable → explicit `comp` terms; LE diamond on ℕ → `le_def`) in
**`HANDOFF-2026-06-23-lap26.md`**. Build green 1280 jobs; headline `sorry` intact.

**NEXT (hardest-first):** (1) finish `InternalBridge` (`ibump_nat` by `Nat.strong_induction_on`,
`igoodstein_nat`) — anti-fraud link to audited `Defs`. (2) **THE math content:** internal `ineq6_step`
(Rathjen Lemma 3.6 slow-down) — build `b k = T̂^{k+2}∘βₖ` as `𝚺₁`-fn, prove base + step, plug `m=igoodstein`
into `DescentArith.ineq6_internal`. (3) back-end (Route A/B, deferred). (4) F-φ on Aristotle.

## 🎯 LAP-24 (2026-06-23) — E-core kernel landed + back-end correction. Read FIRST.

**Two walls left: E-core + F-φ** (D' discharged lap 22; E-lift X-free half done lap 23). Build green
1271 jobs; headline `sorry` intact. F-φ on Aristotle (`aris_onotecmp`, running). See refreshed
`STATUS.md` + `DESCENT-PLAN.md §3a` (Σ₁-completeness reframe) + `DESCENT-PLAN.md §1 CORRECTION`.

**✅ Landed this lap (`src/GoodsteinPA/DescentCore.lean`, axiom-clean):** `Dom.ineq6_step` — the
non-vacuous Π₁ kernel of Rathjen Lemma 3.6 (one special Goodstein step from `m ≥ T̂^{k+2}_ω(βₖ)` lands
`≥ T̂^{k+3}_ω(β_{k+1})`), + `lemma36_ineq6`/`lemma36_nonterminating` (the `∀k` iteration — **semantic
shadow only**, vacuous hypotheses since ε₀ is well-founded; the real content is the arithmetization).
Weakened `Domination.canon_repr` `2≤b → 1≤b` (base-2 `T̂²_ω` needs `evalNat 1`).

**⚠️ Back-end correction (lap 24).** The DESCENT-PLAN's "`PRWO ⟹ TI prec` = one X-instance" understated
the Route-B bridge: Rathjen's `PRWO(ε₀)` is the **primrec** well-ordering statement (Thm 2.8), and a
counterexample to the free-X `TI prec` yields an **X-definable** (not primrec) descent, so primrec-`PRWO`
can't refute `TI prec` directly. The honest Route-B bridge = carry out Rathjen §3 **inside paLX** with the
free-X descent (LX least-number scheme + inequality (6), contradicting the lifted X-free Goodstein at the
X-definable seed). **De-risking:** `Goodstein ⟹ PRWO(ε₀)` (Rathjen §3) is **shared by both back-ends**
(Route A `PRWO ⟹ Con(PA)` + Gödel II, costs `PA_delta1Definable`; Route B the integrated paLX construction,
axiom-clean). **Focus E-core on the shared §3; defer the back-end choice.** Lit request filed
(`ON-LINE-REQUEST.md` lap 24) to pin the cheaper back-end.

**✅ Landed lap 25 (`DescentCore.lean`, axiom-clean):** Rathjen's tower `ωₙ` (`omegaStack`: `ω₀=1`,
`ωₙ₊₁=ω^{ωₙ}`) + `omegaStack_NF`, `C_omegaStack : C(ωₙ)=1`, `repr_omegaStack_succ`,
`repr_omegaStack_strictMono` (the Thm 3.5 head-term scaffold). **✅ Also landed lap 25 (`DescentCore.lean`, axiom-clean):** the C-arithmetic for the tail terms —
`one_add_oadd` (`1 + oadd e' n' a'` evaluation), `C_one_add_le : C(1+e) ≤ C(e)+1`, and the headline
`C_omega_mul_le : C(ω·α) ≤ C(α)+1` (= Rathjen's "multiplying by ω bumps coeffs by ≤1"; `omegaO := oadd 1 1 0`,
induction on the `ONote.mul` recursion). **✅ Also landed lap 25 (`DescentCore.lean`, axiom-clean):** the Thm 3.5 tail-term `C`-bound, complete —
`C_ofNat`, `one_add_ne_zero`, `NoFin`/`noFin_omega_mul` (ω·α has no finite part), `C_add_ofNat_le`
(`C(a+finite) ≤ max(C a, finite)` for `NoFin` NF `a`; mirrors `add_nfBelow` with cmp-gt), `NF_omegaO`,
and the headline **`C_betaTail_le : C(ω·αₙ + (K-i)) ≤ K(n+1)+i+1`** (= `C(βᵣ)≤r+1` for the tail block,
given `C(αₙ)≤K(n+1)`, `i<K`). **✅ Tail-block DESCENT done lap 25 (`DescentCore.lean`, axiom-clean):** `repr_omegaO` (repr ω=ω),
`repr_betaTail_within` (larger finite tail → larger value), `repr_betaTail_boundary`
(`ω·αₙ₊₁+K < ω·αₙ` from `αₙ₊₁≺αₙ`; ω absorbs the finite K). **Both halves of Thm 3.5's TAIL block —
`C(βᵣ)≤r+1` and `βᵣ₊₁<βᵣ` — are now machine-checked.** This is the asymptotic (non-vacuous) content.

**ARITHMETIZATION MAP VERIFIED lap 25 (see `DESCENT-PLAN.md §3b`):** the inequality-(6) PA-induction is
feasibility-confirmed — `sigma_one_completeness` (Σ₁ free) and `sigma1_pos_succ_induction` (the internal
`𝗜𝚺₁` induction; `succ` = internal `ineq6_step`) both exist with verified signatures; `P(k):=mₖ≥T̂^{k+2}(βₖ)`
is Δ₀ hence a `𝚺₁-Predicate`, so the induction applies directly. **The one gating prerequisite = make
`bump`/`goodsteinSeq`/`T̂`/`βₖ` `𝚺₁`-definable *inside* `V`** (the `PA_delta1Definable`-flavoured gap, here
only for the concrete primrec `bump` the repo already has `computable_bump` for). 

**✅ Arithmetization SCAFFOLD machine-checked lap 25 (`src/GoodsteinPA/DescentArith.lean`, axiom-clean,
now in the lib build).** `ineq6_internal` : inside `[V ⊧ₘ* 𝗜𝚺₁]`, given `𝚺₁`-functions `m,b`, base
`b 0 ≤ m 0`, and the internal step, `sigma1_pos_succ_induction` yields `∀k, b k ≤ m k` — the `definability`
tactic discharges the `𝚺₁`-predicate automatically. `nonterminating_internal` adds `0<b k ⟹ 0<m k`
(the PA-internal Lemma 3.6). **The inequality-(6) induction now assembles in Lean**; the deep layer is
isolated behind the two `𝚺₁`-function hyps + the step. Also: wired `DescentLift`/`DescentCore`/`DescentArith`
into `src/GoodsteinPA.lean` (build 1271→1274 jobs).

**Next bricks (priority):** (1) **THE WALL — internalized definability:** supply the concrete `𝚺₁`-function
`m` = internalized `goodsteinSeq`/`bump` (build on Foundation `𝗜𝚺₁` `log`/`exp`/`bexp` in
`Arithmetic/Exponential/`; `bump` is base-b digit manipulation) + `b` = `T̂^{k+2}∘β`, and prove the
internal `ineq6_step` (`Δ₀` numeral form of `DescentCore.ineq6_step`), then plug into `ineq6_internal`.
Multi-lap. (2) Optional completeness: the Thm 3.5 HEAD block (`βⱼ=Σω_{s-i}`,
`j<K`) — a finite boundary detail, vacuous on its own; `headBeta s t := oadd (omegaStack (s-1)) 1
(headBeta (s-1) t)`, `C=1` from `C_omegaStack`, descent by `repr_add`. Low value vs (1).

**Next concrete bricks (route-independent §3):** (1) the slow-down constructions Rathjen Lemma 3.3 / Cor
3.4 / Thm 3.5 — the explicit padding function `g : ℕ² → ω^ω` and the bounded-coefficient sequence `βⱼ`,
with their *step* properties (descending-at-a-step, `C(βᵣ)≤r+1`) as non-vacuous finite ℕ/ONote facts
(Lemma 3.2 = mathlib `exists_lt_ack_of_nat_primrec`). (2) Then the arithmetization: inequality (6)'s `∀k`
as a genuine PA-induction (the dominant wall; Σ₁ glue is free via `sigma_one_completeness`).
**Landed lap 24:** `Dom.C : ONote → ℕ` (Rathjen's max-coefficient) + `Canon_iff_C_le` (`Canon b o ↔ C o ≤ b`).

### Arithmetization API — GROUNDED (lap 24 scoping of the dominant wall)

Scoped Foundation's machinery for the inequality-(6) PA-induction (E-core's irreducible core). Findings:
- **Σ₁ glue is free:** `LO.FirstOrder.Arithmetic.sigma_one_completeness {σ : Sentence ℒₒᵣ}
  (hσ : Hierarchy 𝚺 1 σ) : ℕ ⊧ₘ σ → T ⊢ σ` (for `[𝗥₀ ⪯ T]`, so `𝗣𝗔`) — every TRUE Σ₁ sentence is
  PA-provable (`R0/Basic.lean:146`). This is the engine `precφ`/F-φ already rides (`codeOfREPred₂` →
  `sigma_one_completeness_iff`). All Δ₀/Σ₁ *computations* (specific Goodstein/`T̂`/βₖ values) are free.
- **The inductive core is the genuine work.** `∀k (mₖ ≥ T̂^{k+2}(βₖ))` is Π₁ (∀ of Δ₀) — NOT free. It
  needs a PA-induction. Foundation's idiom = the **internalized-model approach**
  (`Arithmetic/Induction.lean`: `sigma1_pos_succ_induction`, `bounded_all_sigma1_order_induction`, …):
  work inside an arbitrary `V ⊧ 𝗜𝚺₁` with `𝚺₁`-definable predicates/functions, do internal induction,
  and the framework yields the `𝗜𝚺₁`/`𝗣𝗔` proof.
- **KEY SIMPLIFICATION — arithmetize over base-b NUMERALS, not internalized ONote.** Rathjen's whole
  framework is numeral-based: `T̂^b_ω(α)`/`S^b_c` are base-conversions on numerals, and the order
  comparison is base-b *digit* comparison (Lemma 2.2(ii)), which is **Δ₀** (PA-provable directly). The
  ordinal/ONote/`repr`/ε₀ detour is only the *semantic* (ZFC-side) proof convenience (e.g. `ineq6_step`
  via `evalNat_lt_iff`/`canon_repr`); the **PA-side proof of inequality (6) uses Δ₀ numeral comparison**
  and avoids internalizing ONote into `V`. This is the big de-risk vs re-implementing ONote in HFS.
- **Prerequisite chain:** (i) the Goodstein function `goodsteinSeq` is already arithmetized
  (`Encoding.lean`/`goodsteinSentence`); (ii) the slow-down sequence `βₖ` + `T̂^{k+2}` as `𝚺₁`/primrec
  numeral functions (define from the Lean fns via `codeOfREPred`, or hand-build in `IΣ₁`); (iii) the
  arithmetized `ineq6_step` (Δ₀ numeral comparison); (iv) internal induction (`sigma1_pos_succ_induction`)
  to land `𝗣𝗔 ⊢ ∀k ψ(k)`; (v) the back-end (Route A/B, deferred). **(ii)–(iv) are the multi-lap wall.**

---

## 🎯 LAP-23 (2026-06-23) — E decomposition GROUNDED + first E-lift bricks LANDED.

Read **`DESCENT-PLAN.md`** (new, this lap): the full E wall mapped from Rathjen 2014 §2–3 to repo defs,
with the exact Foundation E-lift bricks (`Derivation.lMap`, `provable_iff_derivable2`,
`Derivation.toDerivation2`) verified present, and the **X-essential subtlety** spelled out (`TI prec`
mentions the set variable `X`, so it is NOT the `lMap` of any `ℒₒᵣ` sentence — E genuinely needs the
X-induction instance, not just proof-translation).

**✅ X-FREE E-LIFT COMPLETE (axiom-clean, `src/GoodsteinPA/DescentLift.lean`, `#print axioms =
[propext, Classical.choice, Quot.sound]`).** The full proof-translation half of E-lift is machine-
checked: **`paLX_derivable2_lMap_of_PA_provable : 𝗣𝗔 ⊢ σ → Nonempty (Derivation2 paLX {lMap Φ ↑σ})`**.
The chain, all landed:
- `lMap_{zero,one}_const`, `lMap_succT`, **`lMap_succInd`** — `lMap` commutes with the induction-axiom
  builder (the operator-`lMap` leaves, proved symbol-by-symbol since there is **no
  `Semiterm.lMap_operator` lemma**; also **`fin_cases` is NOT available** in this build — use
  `Fin.cases`/`.elim0`).
- `fvSup_lMap`, `lMap_fixitr`, `lMap_univCl'`, **`lMap_univCl`** — `lMap` commutes with universal closure.
- **`lMap_inductionScheme_subset`** : `lMap (InductionScheme ℒₒᵣ univ) ⊆ InductionScheme LX univ`.
- `lMap_PA_subset`, `coe_schema_lMap`, `schema_lMap_PA_subset` — `(𝗣𝗔:Schema).lMap Φ ⊆ (paLX:Schema)`.
- The lift: `provable_def` → `Derivation.lMap` → schema-weaken → `provable_iff_derivable2`.

**E-core brick landed** (`src/GoodsteinPA/DescentCore.lean`, axiom-clean): `evalNat_lt_iff` /
`evalNat_le_iff` / `evalNat_lt_of_lt` — Rathjen Lemma 2.3(iii), `evalNat` (= `T̂^b_ω`) order-reflects
on the `Canon`/`NF` domain (immediate from the already-present `Domination.canon_repr` round-trip +
`toOrdinal` strict monotonicity, also added `toOrdinal_lt_iff`/`le_iff`). **Note:** `Domination.lean`
is far more developed than the lap-22 map implied — it already has `Canon`/`Good`/`canon_repr`/
`canon_round_trip` (the full T̂/T round-trip) plus the entire `goodsteinLength ~ fastGrowingε₀` growth
analysis. Grep it before building any semantic ONote/Goodstein lemma.

**Next (E-core — the real remaining content):** the **X-essential** step `𝗣𝗔 ⊢ goodstein → Derivation2
paLX {TI prec}`. `TI prec` mentions the set variable `X` so it is NOT an `lMap`-image (the lift above
does NOT produce it directly). Path: (a) `𝗣𝗔 ⊢ goodsteinSentence → 𝗣𝗔 ⊢ ⌜PRWO(ε₀)⌝` (Rathjen §3
slowing-down, formalized inside PA — the dominant wall; first bricks: `C : ONote → ℕ` + `evalNat`
order-monotonicity, Aristotle-eligible), then (b) the X-induction instance `PRWO ⟹ TI prec` in `paLX`
(one least-number/induction instance for the `X`-formula — the lift's schema inclusion already gives
`paLX` those axioms). See `DESCENT-PLAN.md §1, §3`.

## 🎯 LAP-22 (2026-06-23) — D' DISCHARGED + E (DescentE) MAPPED FROM RATHJEN. Read FIRST.

**D' is closed.** `Thm56.embed_TI_bounded` is now machine-checked (the embedded ordinal `< ε₀`); the
entire `EmbeddingBound.lean` chain is axiom-clean. `#print axioms peano_not_proves_TI` = `[propext,
choice, Quot.sound, rePred_ltPull_natCode]` — `sorryAx` GONE. **Walls left: F-φ (Aristotle) + E.**

### E = `DescentE` decomposition (grounded in Rathjen-2014 "Goodstein revisited" §2-3, read lap 22)

`DescentE := 𝗣𝗔 ⊢ ↑goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})`. The math (Rathjen):
Goodstein's theorem is **PA-equivalent to PRWO(ε₀)** (no descending prim-rec sequences of ordinals `<ε₀`,
= transfinite induction), and `𝗣𝗔 ⊬ PRWO(ε₀)` by Gentzen+Gödel-II. The two halves:

1. **The SEMANTIC descent is ALREADY in the repo** (`Domination.lean`, axiom-clean):
   - `toOrdinal b n` = Rathjen's `T^b_ω(m)` (base-`b` rep → CNF ordinal); `repr_toONote` ties it to `ONote`.
   - `seqOrd m k := toOrdinal (k+2) (goodsteinSeq m k)`; **`seqOrd_step` = Rathjen eq. (4)** — the ordinal
     strictly DECREASES along a Goodstein sequence (`goodsteinSeq m k ≠ 0 → seqOrd m (k+1) < seqOrd m k`).
   - `goodstein_terminates` (the (ii)⟹(i) direction, semantic) is fully proven.
   This is the **backbone**; E does NOT need to redo it.

2. **The SYNTACTIC gap (E's real content):** realize "Goodstein ⟹ TI(≺)" as a `Derivation2 paLX`
   proof-object, i.e. lift the semantic descent to a Z-proof of `TI prec`. Sub-lemmas (attack order):
   - **E-lift:** a finitary `𝗣𝗔`(ℒₒᵣ)-proof of an arithmetic `TI`/`PRWO(ε₀)` statement maps to a
     `Derivation2 paLX` of `TI prec` (proof-translation along `ℒₒᵣ ↪ LX`; `paLX ⊇ lMap 𝗣𝗔⁻ + induction`;
     match the arithmetic well-ordering formula to Buchholz's `TI prec = Prog prec 🡒 ∀⁰ Xat #0`, the
     set-variable `X` = the induction predicate). Mechanical-ish but needs the ℒₒᵣ `TI(ε₀)` formula DEFINED.
   - **E-core (the deep part):** `𝗣𝗔 ⊢ Goodstein ⟹ 𝗣𝗔 ⊢ TI(ε₀)` (Rathjen Cor 2.7 (i)⟹(ii), the
     reversal). Needs §3 "slowing down" (Lemma 3.2 Grzegorczyk bound, Lemma 3.3/Cor 3.4: convert arbitrary
     descending prim-rec sequences to SLOW ones `|αᵢ| ≤ K·(i+1)`, since PA only expresses prim-rec sequences).
   - **ALT (Route A escape hatch):** `Reduction.goodstein_implies_consistency : 𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`
     (Rathjen Thm 2.8: PRA ⊢ PRWO(ε₀)→Con(PA)) then Gödel II. Reintroduces `PA_delta1Definable` (🟡).
   - **First concrete prerequisite to formalize next lap:** the ℒₒᵣ-arithmetic statement of `PRWO(ε₀)` /
     `TI(ε₀)` + Rathjen Lemma 2.3 (the `T^b_ω`/`T̂^ω_b` order-iso, mostly in `toOrdinal_mono_and_bound`).
   - Scaffold (sorried statements) belongs in `wip/Descent.lean` (keeps `src/` sorry-free for the gate).

### Earlier notes below ⤵


## ✅ LAP-19 (2026-06-22) — F ORDER-TYPE WALL CLOSED (axiom-clean). Read FIRST.

The order-type half of **F** is **DONE + `#print axioms`-clean** in `src/GoodsteinPA/Epsilon0Complete.lean`
(build green, 1268 jobs). This was the campaign's dominant risk (laps 12-19: "the real F girder mathlib
LACKS"). Landed, in dependency order:
1. `exists_NF_repr_eq : ∀ o<ε₀, ∃ x:ONote, x.NF ∧ x.repr=o` — ε₀-completeness of CNF notations (CNF
   recursion via `WellFoundedLT.induction`; key step `log_omega0_lt_self` = no ω^· fixed point below ε₀).
2. `repr_lt_epsilon0` (NF ⟹ repr<ε₀, induction on ONote) + `range_NONote_repr` (= `Iio ε₀`).
3. `rk_ltPull_eq_repr` (= seam-advice `note_rank_eq_repr`) + `epsilon0_le_orderType_ltPull (e : ℕ≃NONote)`
   — `ε₀ ≤ orderType (ltPull e)`. Proved by naming `orderType`/`rk` itself as some `repr (e n₀)` via
   surjectivity ⟹ NO Iio-sup identity, NO universe bump (all `Ordinal.{0}`; the `NONote ≃o Iio ε₀` route
   would land in `Ordinal.{1}` ≠ project's `orderType`).
4. `encodeONote`/`decodeONote` (computable `Encodable ONote`; ONote only derives DecidableEq) + `Infinite`/
   `Denumerable NONote` ⟹ `natCode : ℕ ≃ NONote` + `epsilon0_le_orderType_natCode` (concrete `Seam.ge`).

**F now reduces to ONE Foundation-side wire-up** (Worker B): the X-free `ℒₒᵣ` formula `φ : Semiformula ℒₒᵣ ℕ 2`
(via `codeOfREPred₂` from `codeOfPartrec'`) defining **`natCode`'s order** (`ltPull natCode`), then instantiate
`GoodsteinPA.EpsilonOrder.Seam` with `φ`, `hφ`, and `ge := epsilon0_le_orderType_natCode`. The definability
half (`hprec`/`hprecXPos`) is already discharged (lap 18, `EpsilonOrder.lean`). **Binding constraint:** `φ` must
define the SAME order `natCode` induces (`repr(natCode a) < repr(natCode b)` — express arithmetically via the
computable `ONote.cmp` on codes, since `<` itself routes through noncomputable `repr`).

### Remaining open obligations (priority for lap 20+)
- **C₂ glue `hax_paLX`** X-induction case (`EmbeddingX.lean:705`) — closes **Thm 5.6 (`PA ⊬ TI(ε₀)`)**
  axiom-clean modulo E+F. Recipe inlined at the sorry (steps 1-7); all four helper lemmas proven
  (`metaInduction_cong`, `subst_value_subst`, `succInd_nnf`, `PXFc_allClosure`). Friction = Foundation-DSL
  Rew-pushing through `succInd`/`univCl`/`fixitr` (steps 3-5). ALL-OR-NOTHING (can't partial-commit the sorry);
  extract step-4 `rew_succInd : g ▹ succInd ψ = succInd (g.q ▹ ψ)` as a standalone helper first.
- **F-definability `φ`** (Worker B, Foundation-side) — see above. Independent of C₂ glue and E.
- **E**: Goodstein⟹TI_≺(natCode order) in PA — the other unstarted wall. Per seam-advice Reviewer-2 §3:
  commit to `natCode`'s CNF order for BOTH F and E; E uses `Domination.toONote` as a descent MAP into it
  (E's order need not have type ε₀, only a PA-provable strictly-decreasing descent). Needs papers/ reading.

---

## Reflection — 2026-06-22 (lap 18, deep-reflection) — the F seam, grounded vs an outside attack plan

**Context.** Evaluated an external (GPT-5.5) attack plan for **F** (the arithmetization seam,
`‖≺‖=ε₀` + discharge `hprec`/`hprecXPos`) against the real repo + mathlib. The plan is largely
sound (it read the code: its `EpsilonOrder.hprec` reproduces `Boundedness.lean:699-702` exactly), but
it under-scopes the hard part and omits the E-coupling. Verified facts + corrected attack below.

**Direction call: KEEP the Buchholz Boundedness route; it is working.** As of lap 17 the *entire
machine from D back is machine-checked and `#print axioms`-clean*: Boundedness (Thm 5.4) + corollary B,
C₁ `PXFc.cutElim`→cr0, D `orderType_le_of_TIprovable`, C₂-structural `embedC_LX_gen`, M4 `embedC`,
M5 `cutElim`. The honest realistic endpoint: **headline reduced to two well-scoped girders — E
(Goodstein⟹TI) and F (arithmetization seam) — atop a fully-built, axiom-clean infinitary
proof-theory core.** That is a valuable, net-new-in-Lean endpoint even if F lands as one narrow
cited fact + built remainder. Remaining open obligations, in priority order:
1. **C₂ glue** `hax_paLX` induction case (`EmbeddingX.lean:705`) — pure integration, recipe inlined
   at the sorry (lap-17 HANDOFF #3). ~1 lap. Closes **Thm 5.6 (`PA ⊬ TI(ε₀)`)** axiom-clean modulo E+F.
2. **F-girder: ε₀-completeness of CNF notations** — the real wall (below). Mathlib-only ⟹ Aristotle-eligible.
3. **E**: Goodstein ⟹ TI_≺(X) — and it *constrains which ≺ F may use* (coupling, below).

### F attack — corrected (what the outside plan got right / wrong, verified)
- ✅ **Seam structure** (abstract `hprec`/`hprecXPos` into a record so F proceeds in parallel) — good.
  FIX 1: `orderType lt = ε₀` is stronger than needed; the contradiction only needs **`ε₀ ≤ orderType lt`**
  (D gives `‖≺‖ ≤ 2^β`, `β<ε₀`). The `≤ε₀`/embedding obligation is then free to drop.
  FIX 2: carry the **X-free ℒₒᵣ defining formula** `φ` (set `prec := φ.lMap (ORing.embedding LX)`), so
  `hprecXPos : XPos (∼prec)` is *automatic* (X-free ⟹ XPos, `XPositive.lean:18`), not a separate field.
- ✅ **`hprec` reduces to definability** — `hprec_of_lMap_defined`. `TruthSem.models_lMap`
  (`TruthSem.lean:120`, closed case) + the `levelSet lt γ={n|rk<γ}` interpretation (`TruthSem.lean:51`)
  already exist; after unfolding `hyp prec=∀⁰(prec🡒Xat #0)` every `prec` occurrence is a *closed*
  instance, so the closed `models_lMap` suffices (no need to generalize it to arity-2). **TRACTABLE —
  do this FIRST among F bricks. Foundation-side.**
- ✅ **`codeOfREPred₂` via `codeOfPartrec'`** — verified real: `Foundation/.../R0/Representation.lean:233`
  `codeOfPartrec' {k} : (Vector ℕ k →. ℕ)→Semisentence ℒₒᵣ (k+1)`; `:245 codeOfREPred`+`:250` spec is the
  unary template. Binary version constructible. (Our `lt` is computable — NONote `cmp` is decidable.)
- 🔴 **THE under-scope — `note_rank_eq_repr : rank(·<·) o = repr o` is NOT a mathlib wire-up.** It is
  **equivalent to completeness of the notation system up to ε₀** (every ordinal `<ε₀` is some `repr`),
  and **mathlib does NOT have that.** `Mathlib/SetTheory/Ordinal/Notation.lean` (1298 lines) proves only
  that `repr` is order-preserving + injective on `NF` (an *embedding* `NONote↪ε₀`: `lt_def:111`,
  `repr_inj:319`) — no surjectivity/`ofOrdinal`/order-type lemma. The embedding gives `rank o ≤ repr o`
  and `orderType ≤ ε₀` cheaply; the `=`/`≥` direction is the missing girder. **And the FIX-1 relaxation
  does NOT save you**: `ε₀ ≤ orderType lt` still needs the represented set to fill `[0,ε₀)` (cof ε₀ = ω,
  so a cofinal ω-chain has order type ω, not ε₀). ⟹ **formalize `∀ o<ε₀, ∃ x:ONote, x.NF ∧ x.repr=o`
  (CNF existence up to ε₀). ~1–3 laps. Pure mathlib ordinal arith, ZERO Foundation dep ⟹ the one piece
  of this project genuinely well-suited to ARISTOTLE** (contra the lap-17 blanket "poor fit").
  - The outside plan's "Domination.lean has `towerO/repr_towerO/exists_repr_lt_omegaTower`" is **wrong**
    — those names don't exist. Repo has `toONote`/`repr_toONote`/`toONote_NF` (base-b Goodstein coding,
    sparse) + tower material in `Hardy.lean` (`tower i`, `fastGrowingε₀`, A4 `fastGrowing_lt_fastGrowingε₀`).
- ✅ **Don't reuse `toOrdinal 2 n`/`seqONote`** — correct, and worse than "sparse": `toOrdinal b ·` is
  strictly monotone, so the pullback has `rk lt n = n` and `orderType = ⨆ succ n = ω`, NOT ε₀. F needs a
  **bijective ℕ↔NONote** coding (order type of the *whole* system), not a monotone enumeration.

### F's real blind spot — E pins the order (co-design E and F)
The `≺` whose order type F proves `=ε₀` MUST be the **same** `≺` for which PA proves `TI_≺(X)` from
Goodstein in E. Pick an arbitrary clean NONote-coding for a tidy order-type proof → you then owe E
(*PA ⊢ Goodstein → PA ⊢ TI along that coding*). The repo's natural Goodstein descent (`Domination.seqONote`,
`repr_seqONote`, `seqONote_lt`) is tailored to E but has order type ω (wrong for F). **Crux = one order
simultaneously (a) honestly ε₀ in order type [F], (b) X-free-definable [F2/F3], (c) PA-provably-TI-from-
Goodstein [E].** Co-design, or make `EpsilonOrder` expose the E-hook (standard CNF order on ℕ-codes +
Goodstein-descent-embeds-into-it).

### Corrected F work order
1. ✅ **DONE (lap 18, `src/GoodsteinPA/EpsilonOrder.lean`, all axiom-clean).** The whole **definability
   half** of F is built: `eval_lMap_structLX`, `hprec_of_eval`, `hprec_of_lMap_defined` (discharge the
   exact Boundedness `hprec` for ANY `lMap`-definable `lt`); `xpos_lMap` + `hprecXPos_lMap` (⟹ `hprecXPos`
   automatic); and the **`Seam` structure** (`GoodsteinPA.EpsilonOrder.Seam`) bundling `lt`/`φ`/`hφ`/`ge`
   with methods `Seam.prec`/`hprec`/`hprecXPos`. **Only `Seam.ge : ε₀ ≤ orderType lt` is left undischarged.**
2. **`codeOfREPred₂` + spec (Foundation-side)** — NEXT tractable brick. NOTE `Semisentence ℒₒᵣ 2 =
   Semiformula ℒₒᵣ Empty 2` ⟹ need `Empty→ℕ` embedding (`Rew.emptyMap`/`Semiformula.emb`) to feed
   `Seam.φ : Semiformula ℒₒᵣ ℕ 2` / `hφ`. (Or add a `Semisentence`-flavoured `hprec_of_lMap_defined`.)
3. **ε₀-completeness `∀ o<ε₀, ∃ x:ONote, NF x ∧ repr x = o`** = `Seam.ge` (the real girder; mathlib-only;
   Aristotle-eligible). mathlib `Ordinal.lt_epsilon_zero : o<ε₀ ↔ ∃ n, o<(ω^·)^[n] 0` is the tower hook.
4. Bijective ℕ↔NONote coding + transfer order type (build `Seam.lt` + its `ge`).
5. Instantiate `Seam` (combine 2+3+4). The definability fields are already discharged by step 1.
6. Reconcile with E (same `lt`) before claiming the seam closes the headline.

---

## ⏭️ LAP-16 (2026-06-22) — C₂ structural port LANDED; the `exs` wall = a calculus retrofit. Read FIRST.

**Landed (green, committed):** `src/GoodsteinPA/EmbeddingX.lean` — `embedC_LX_gen` (9/10 `Derivation2`
cases, `axm`-abstracted) + `provable_true_x` (X-free ω-completeness, `XFreeAx`-safe) + `XFreeForm`.

**THE finding (corrects the lap-15 "mechanical" claim):** the `exs` case is NOT mechanical. Collapsing
a closed witness to a numeral needs a **value-congruent EM**; for an X-atom body that requires Buchholz's
**value-congruent X-pair axiom** `{Xs,¬Xt}` (`sᴺ=tᴺ`, `AX(Z∞)`, lecture notes p.27), which our same-atom
`Deriv.axL` does NOT provide. **Read `ANALYSIS-2026-06-22-lap16-exs-axLv.md`** — full obligation map +
retrofit recon (5/8 ZinftyGen sites mechanical; `atomCutAux` = Buchholz Remark p.27 = the one hard spot;
`removeFalseLit_x` X-free-restriction keeps `XFreeAx` safe; Boundedness case 1.2 = p.29).

### LANDED (lap 16): the `axLv` retrofit — green across all 3 files, 1 disclosed `sorry` left
`Deriv.axLv` (value-congruent literal axiom, Buchholz `AX(Z∞)` p.27) threaded through ZinftyGen
(incl. `atomCutAux` Remark p.27 + 3-case `removeFalseLitAux`), Boundedness (case 1.2 p.29), and
XFreeCutElim (7/8 `_x` sites). Remaining `sorry`: `PXFc.atomCutAux`'s value-cong **X-atom-cut** case
(`XFreeCutElim.lean:1048`) — C₁/D carry it temporarily.

### NEXT (lap 17): `nrel_value_subst` clears it; then `exs`; then `embedC_LX`
1. **`PXFc.nrel_value_subst`** — `Δ` cut-free `XFreeAx`, `nrel r v ∈ Δ`, `|v|=|w|` ⟹
   `PXFc d.o 0 (insert (nrel r w) (Δ.erase (nrel r v)))`. Mirror `removeFalseLitAux_x` with frame
   `Γ.erase Lit → insert Lit' (Γ.erase Lit)`; leaves close via `PXFc.axLv`/X-free `axTrue`; matched
   `axLv` leaf: extract via `congrArg (∼·)` not raw dependent `injection`. Then transport `hNC` in
   `atomCut_x` Case `hrel`.
   - **fallback** if the dependent leaf cases swamp: isolate as a disclosed `axiom` (NOT on headline)
     to let `cutElim` go clean-modulo-that, OR keep the current `sorry` and move to `exs`/`embedC_LX`
     (which don't depend on `nrel_value_subst`) to make orthogonal progress.
2. ~~`exs`~~ ✅ DONE lap 16 — `embedC_LX_gen` is sorry-free + axiom-clean (`provable_em_cong_gen_x`
   via `axLv` + `PXFc.exI_closed`).
3. **`embedC_LX`** = `embedC_LX_gen` at `↑paLX` + `hax` (X-free `provable_true_x`, X-ind `metaInduction`).
   Independent of `nrel_value_subst` (only the cutElim end of D needs that).

### C₂-axm discharge (after structural is sorry-free) — `paLX` + `hax`
`paLX := Theory.lMap (ORing.embedding LX) 𝗣𝗔⁻ + InductionScheme LX Set.univ`. X-free axioms via
`provable_true_x`; X-induction via `metaInduction` glue. (`InductionScheme L` IS generic over ORing `L`.)

---

## ⏭️ LAP-15 (2026-06-22) — review validated lap-14 design; EXECUTE C₁ then C₂. Read this FIRST.

**Direction CONFIRMED sound** (fresh-mind review). Lap 14 finished the crux (Boundedness Thm 5.4 +
corollary B, axiom-clean). The remaining work to **Thm 5.6 (`PA ⊬ TI(ε₀)`)** is C₁+C₂ (connective
tissue), then E (Goodstein⟹TI bridge) + F (arithmetization seam). **Key validated fact (lap 15):** the
cr=0 design is feasible — `atomCut` on an X-atom, applied to `XFreeAx` inputs, preserves `XFreeAx`, because
(i) our `Provable.axL` is the *same-atom* EM axiom `{Xs,¬Xs}` so X-atomic cuts close by **set idempotence**
(the `axL` branch of `atomCutAux`, no truth), and (ii) the truth-surgery branch (`removeFalseLitAux`) fires
only on an `axTrue` leaf *equal to the cut atom* = an X-`axTrue` leaf, which `XFreeAx` forbids ⟹ **vacuous**.
So `removeFalseLitAux` is only ever invoked on X-FREE cut atoms (emitting X-free `axTrue`, fine).

### ✅ C₁ — XFreeAx-preserving cutElim → cr=0 — **DONE lap 15, axiom-clean** (`src/GoodsteinPA/XFreeCutElim.lean`).
Full `PXFc` port: builders + inversions-at-cr≤c + cut reductions + truth layer + `cutElim` + the Thm-5.6
tail `orderType_le_of_TIprovable` (`PXFc α c {TI} ⟹ ‖≺‖ ≤ 2^(ω_c^α)`). **C₂ is now the only connective
gap to Thm 5.6.** (Original C₁ plan kept below for reference.)

### C₂ — `embedC` over LX. **CRUX DONE lap 15; structural port is THE NEXT TARGET (lap 16).**
Done lap 15 (`src/GoodsteinPA/XFreeCutElim.lean`, axiom-clean): `provable_em_x` (LX excluded middle →
`PXFc`, `XFreeAx`-automatic) + **`metaInduction`** (the X-induction embedding via a cut-tower on `ψ(i)`,
`XFreeAx`-preserving — the faithfulness-critical case). **Remaining = the STRUCTURAL `embedC` port:**
mirror `src/Embedding.lean:525–660` (induct on `Derivation2 (𝗣𝗔(LX):Schema) Γ`, emit `PXFc`), swapping
`ZinftyF`/`ℒₒᵣ` → `ZinftyGen`/`LX`. `axm`: PA⁻(LX) via `provable_true_x` (port `provable_true`, X-free
`axTrue`); X-induction via `metaInduction` (+ Foundation-DSL to build `step` from `ψ` + strip
`univCl`/`🡒`). `exs`: port `exI_closed`. **First resolve: what is `Z ⊢ TI(X)` in Lean?** (the target
schema is entangled with F — check Foundation's `PeanoMinus`/`InductionScheme` genericity over `ORing`).
See HANDOFF §"NEXT (lap 16)" for the full breakdown.

### C₁ original plan (reference; superseded by the DONE above):
Introduce in `Boundedness.lean` (or a new `src/GoodsteinPA/XFreeCutElim.lean`) the cut-rank-carrying carrier
`PXFc α c Γ := ∃ d : Deriv Γ, d.o ≤ α ∧ d.cr ≤ c ∧ XFreeAx d` (generalises lap-14's `PXF` = `PXFc α 0`).
Port, each tracking `XFreeAx` (the `Deriv` constructors used are exactly axL / X-free-axTrue / verumR / weak
/ andI / orI / allω / exI / cut — none add an X-`axTrue` except the vacuous `removeFalseLit` branch above):
1. **Smart builders** `PXFc.{mono,weakening,axL,axTrue(Xfree),verumR,andI,orI,exI,allω,cut,contr}` —
   mirror `ZinftyGen.Provable.*` (lines 179–265) but carry the third `XFreeAx` component. Most are trivial
   (`XFreeAx` of a built node = conjunction/∀ of the parts' `XFreeAx`, by the `def XFreeAx` clauses).
2. **`removeFalseLitAux` / `removeFalsumAux`** preserve `XFreeAx`: port `ZinftyGen` 1087/1334 threading the
   property. KEY: `removeFalseLitAux` is stated for a FALSE literal `signedLit b₀ r₀ v₀`; on the X-route it
   is only ever called with `r₀` X-FREE (from the vacuous-branch argument), so its emitted `axTrue` leaves
   are X-free ⟹ `XFreeAx`. State it with an added hyp `Sum.isLeft r₀ = true` (X-free cut atom) to make this
   explicit, OR thread `XFreeAx d` and show the X-axTrue case can't arise.
3. **`atomCutAux` / `atomCut`** (ZinftyGen 1191/1320) preserve `XFreeAx`: the `axTrue`/`heq` branch needs the
   leaf = cut atom; for X-free cut atoms it's an X-free leaf (fine); the cut atom is X-free anyway on the
   route. To be safe handle generic atoms: if the cut atom is an X-atom, the `axTrue`/heq branch is vacuous
   by `XFreeAx`, and the `axL` branch + structural cases are truth-free.
4. **`cutReduceConj/Disj/AllAux/All`** (ZinftyGen 796/826/862/1017) preserve `XFreeAx`: they compose the
   `XFreeAx`-preserving inversions (lap-14 `andInv_xfree`/`orInv_xfree`/`allInv_xfree` — already built! but
   at cr=0; **generalise them to cr ≤ c** since inversions don't change cut rank) + builders + `cut`.
5. **`cutElimPrincipal` / `cutElimStepAux` / `cutElimStep` / `cutElim`** (1422/1479/1529/1537): structural
   port; `cutElim : PXFc α c Γ → PXFc (omegaTower c α) 0 Γ`. This is the deliverable feeding corollary B.
**Aristotle target:** a self-contained "`removeFalseLitAux` preserves `XFreeAx` for X-free `r₀`" or a
`PXFc` builder lemma (inline the `Deriv`/`XFreeAx`/`o`/`cr` defs). Bounded + mechanical.

### C₂ — `embedC` over generic LX (parallel/after C₁). Plan in lap-14 HANDOFF §C₂ (CRITICAL: X-induction
axioms via the meta-induction tower of `cut`s on `φ(i)` + `provable_em` base/step — NOT `provable_true`,
which would lone-X-`axTrue`. `𝗣𝗔⁻` X-free axioms can still go via `provable_true`. Port the lap-10 worked
meta-induction). Produces the `XFreeAx` derivation of `{TI}` that C₁ then reduces to cr=0.

## ⏭️ LAP-13 (2026-06-22) — Buchholz route EXECUTING; read this FIRST

**Read `ANALYSIS-2026-06-22-lap13-boundedness-design.md`** (full Buchholz §5 pp.26–31 read + the design).
Lap 13 built ALL the Boundedness prerequisites — green, axiom-clean, in `src/`:
- `LangX.lean` — `structLX (S:ℕ→Prop) : Structure LX ℕ` (the `⊨^S` carrier) + DecidableEq instances +
  `eval_Xatom`. **The `⊨^α` carrier.**
- `ZinftyGen.lean` — **M5 cut-elim generalised over `{L}[ORing L][Structure L ℕ][DecEq…]`**,
  `Provable.cutElim` axiom-clean. Reused wholesale (no cut-elim re-proof on the X-route).
- `TruthSem.lean` — `rk`/`orderType`/`levelSet`/`models (⊨^γ)`/`Sat` + **`models_lMap` (X-free
  invariance)** + `orderType_le_of_forall`.
- `XPositive.lean` — `XPos` + **`models_mono` (⊨^γ monotone in γ on X-positive formulas)** (Buchholz
  cases 2/3/4) + `val_structLX_eq` + `eval_mono`.
- `wip/BoundednessProbe.lean` — `Xatom_axiom`: the Buchholz X-atom axiom `{Xs,¬Xt}` (sᴺ=tᴺ) is
  derivable in generic Z∞ at `(LX,structLX S)` for ANY S. (Validation probe; stays in wip.)

**THE crux still open = Boundedness Thm 5.4 (the 8-case induction) + its formula scaffolding.** Next:
1. **Construct `Prog_≺(X)` / `TI_≺(X)` as `LX`-formulas.** Parametrise by `prec : Semiformula LX ℕ 2`
   (the order, with its ℕ-interpretation = the wellfounded `lt`; for the app `prec` is ℒₒᵣ-definable OT
   order). `Prog := ∀x(∀y(y≺x → Xy) → Xx)`, `¬Prog ≃ ∃x(∀y≺x Xy ∧ ¬Xx)`. Use Foundation DSL/`∀⁰`/`∃⁰`
   + `Xatom`. Pin the inversion shape (`exI`/`allω`/`orI` on `¬Prog`) the induction needs.
2. **Boundedness (Thm 5.4):** induction on the cut-free `Provable β 0` `Deriv` over `LX` (cases =
   our constructors axL/axTrue/verumR/weak/andI/orI/allω/exI/cut ↔ Buchholz's 8). Ingredients ALL
   built: Ax→`Xatom_axiom` (X-pair) / `models_lMap` (TRUE₀); ⋀/⋁/Rep→IH + `models_mono`; ¬Prog `exI`
   inversion = case 2; `cut` on X-atom = case 8. Conclude `Sat lt (α+2^β) Γ`. THE new theorem.
3. **Corollary** `‖≺‖ ≤ 2^β` via `orderType_le_of_forall` (invert TI → ⊢^β_1 ¬Prog,Xn → 5.4 → ⊨^{2^β}Xn
   → rk n < 2^β ∀n).
4. **M4 `embedC` over LX** (mechanical `{L}` generalisation like M5; PA(X) axioms true in structLX S
   for any S since first-order induction holds for any fixed predicate) + assemble **Thm 5.6**
   (`Z⊢TI(X) ⟹ ‖≺‖<ε₀`).
5. **Goodstein⟹TI_≺(X)** bridge (VERIFY-(b)) + arithmetization seam (OT↔ε₀, `‖≺‖=ε₀`) ⟹ headline.

**Banked off-path (do NOT resume):** witness-bounded `wip/` calculi (Towsner/operator-H). The ℒₒᵣ-only
`src/Zinfty.lean`/`src/Embedding.lean` stay for now (existing users); the live chain uses the LX versions.

## ⏭️ LAP-12 PIVOT (2026-06-22) — superseded by lap-13 above (kept for the Buchholz-route rationale)

**Read `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`.** The lap-11 "build the witness-bounded `Zᵏ`" plan
below is **retired**: lap 12 proved its §19.6 cut-elim needs the Buchholz operator `H` (ADDENDUM 7 in
`ANALYSIS-…-cutelim-k-threading.md`) — a multi-lap wall — while Buchholz §5's **witness-FREE** route reuses
the done-and-axiom-clean **M4 `embedC`** + **M5 `cutElim`** and needs only a **Boundedness** theorem. The
lap-11 "embedC is the wrong object" verdict was a conflation of order-type-boundedness (valid, Buchholz
Thm 5.4) with witness-boundedness (walled, Towsner). **`embedC` is the RIGHT object** (Buchholz Thm 5.5).

**New critical path (Buchholz §5 — `Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀`, then Goodstein⟹TI(ε₀)):**
- **0. VERIFY-FIRST (do before deep work):** (a) M5/M4 take the set variable `X` (extend `ℒₒᵣ`→`ℒₒᵣ∪{X}`
  or add `X` as a fixed relation symbol; `embedC.axm`/`provable_true` only need the `X`-free PA axioms);
  (b) the Goodstein⟹TI_≺(X) bridge is provable in PA via the Phase-0 CNF-ε₀ encoding. Neither is a known
  wall; confirm before sinking laps.
- **1.** Truth semantics `⊨^α Γ` (`X := {n : |n|_≺<α}`), `Prog_≺`, ≺-norm `|n|_≺`, order type `‖≺‖`,
  X-positivity — light self-contained defs.
- **2.** **Boundedness (Thm 5.4)** — `Z∞ ⊢^β_1 ¬Prog_≺(X),¬Xs₁,…,¬Xsₖ,Γ & |sᵢ|_≺≤α ⟹ ⊨^{α+2^β} Γ`
  (Γ X-positive), by induction on the cut-free `Provable β 0`-derivation (8 cases, Buchholz p.29).
  Corollary: `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`. THE new theorem; no Hardy, no witness bound.
- **3.** Goodstein ⟹ TI_≺(X) for the ε₀-order (bridge; Kirby–Paris/Cichoń; reuse Phase-0 encoding).
- **4.** Assembly: PA⊢Goodstein ⟹ (M4) ⟹ (M5 cut-free `β<ε₀`) ⟹ (Boundedness) `‖≺‖≤2^β<ε₀`, but the
  ε₀-order has `‖≺‖=ε₀` ⟹ `False` ⟹ discharge headline, `#print axioms` clean.

**Banked off-path (do NOT resume on this route):** the witness-bounded `wip/` calculi. Lap-12 PROVED the
norm-budget half of Towsner §19.6 (`cutReduceAllAux` in `wip/OperatorZinfty.lean`, axiom-clean, via the
norm-carrying `ZekdProv` wrapper — see ADDENDUM 6); the witness-budget half needs operator `H` (ADDENDUM
7). Kept as reference IF the Buchholz route ever stalls. M6 (Hardy) is off-path too.

---

## ⏭️ LAP-11 FINAL STATE (2026-06-22) — SUPERSEDED by the lap-12 pivot above (kept for history)

**M4 — the embedding `embedC` — is COMPLETE, axiom-clean, promoted to `src/GoodsteinPA/Embedding.lean`,
in the default build.** `embedC : Derivation2 (𝗣𝗔:Schema) Γ → ∃ c, ∀ e, ∃ α, Provable α c (Γ.image
(asg e ▹))`. The two hard cases fell to two reusable lemmas: `Provable.exI_closed` (closed-witness
∃-intro, from value-congruent EM `provable_em_cong_gen` + cut) for `exs`; `provable_true`
(ω-completeness) for `axm`. See HANDOFF lap-11.

**⚠️ COURSE CORRECTION (lap 11, grounded in Towsner §13–17) — read
`ANALYSIS-2026-06-22-witness-bound-gap.md`.** The headline needs the **witness-bounded calculus
`Zᵏ`**, NOT a bound on M5's `Provable`. M5 tracks cut-rank `c` but drops Towsner's I∃ witness bound
`k` (`value(t) ≤ h_α(k)`) — and without it the lower bound (Thm 17.1) does not bite (`provable_true`
gives a cut-free `< ε₀` derivation of `{↑gs}`; bounded quantifiers cost `allω`=`ω`, `exI` costs `+1`
regardless of witness value). So `embedC` = the *unbounded* embedding (Towsner Thm 14.2), reusable but
not the headline object; the lap-11 `wip/Bounding.lean` bridge `cutfree_lt_eps0_absurd` is FALSE as
stated. The lap-9 "bound directly on unbounded `Deriv`" reframe is retracted.

**Corrected critical path (= lap-5 plan steps 1–4, now confirmed):**
1. **`Zᵏ`** = M5 `Deriv` + `(α,k)` witness bound on `exI`. Revive banked `wip/` Zekd/OperatorZinfty
   (lap-8 worked §19.2–19.5 + control axis). Carrier: `ZekdProv` wrapper `∃ α'≤α, α'.NF ∧ Zᵏ …`.
2. **Bounded embedding (Towsner Thm 16.1/16.5/16.7)** into `Zᵏ`. `axm`: 16.1 (universal axioms, via
   `provable_true` on the bounded matrix) + 16.5 (induction, bounded meta-induction ordinal
   `ω·4#2^{rk}#2`, via `provable_em` + `Provable.exI_closed`). Structural: port `embedC` cases.
3. **`(α,k)`-cut-elim (Thm 19.9)** — `wip/` Zekd §19 grind (`ANALYSIS-…-cutelim-k-threading.md`).
4. **Subformula bridge to `B`** (M6) + Σ₁-arithmetization seam (M7a: `codeOfREPred` ↔ `atomTrue`,
   anchor `codeOfREPred_spec`) + ONote↔Ordinal<ε₀ seam ⟹ contradiction with
   `lowerBound_hardy_selfcontained`.

**BANKED reusable (src/Embedding.lean, axiom-clean):** `provable_true`, `provable_em`,
`provable_em_cong_gen`, `Provable.exI_closed`, `embedC` structural cases. Do NOT discard.
**Aristotle candidates:** a `Zᵏ` mono/inversion lemma; the ONote↔Ordinal<ε₀ bridge; a `norm_add_le`/
NF ordinal fact from the §19 bookkeeping.

---

## ⏭️ LAP-10 FINAL STATE (2026-06-22) — superseded by lap-11 above; kept for context

**Headline result: the M5 `axTrue` truth-layer surgery is DONE (axiom-clean) and the assignment-
carrying embedding `embedC` is 8/10.** Full status in `HANDOFF.md`. The TWO remaining `embedC` cases
(`axm`, `exs`) both reduce to ONE shared deep lemma — build it next:

**`provable_subst_congr` (closed-term substitution congruence — THE next chip).** For closed terms
`s s'` of equal ℕ-value and any `ψ : SyntacticSemiformula ℒₒᵣ 1`: the sequent `{∼(ψ/[s]), ψ/[s']}` is
Z∞-derivable (`∃ a, Provable a 0 {...}`). Proof = induction on `ψ.complexity` (the `provable_em`
template), tracking the two terms:
- **atomic** `ψ = rel/nrel R v` (v mentions `#0`): `ψ/[s]` and `ψ/[s']` have EQUAL truth (`Evalm`
  depends on a term only via its value — `Semiterm.val_substs` (Semantics.lean:123) + `eval_substs`
  (l.391)). So `∼(ψ/[s])` and `ψ/[s']` can't both be false ⟹ one is a true literal ⟹ `Provable.axTrue`.
  (Needs the value-equality `hval` and that `(ψ/[s]).LitTrue ↔ (ψ/[s']).LitTrue`.)
- **and/or/all/exs**: recurse structurally, exactly mirroring `provable_em`'s compound cases (the ∀/∃
  cases use the `nm`-family + `exI`/`allω`, with the substituted term threaded through `/[·]`).
Then derive:
- **`Provable.exI_closed (s closed, value m)`: `Provable α c (insert (ψ/[s]) Γ) → ∃ β, Provable β c
  (insert (∃⁰ψ) Γ)`** — cut `provable_subst_congr s (nm m)` (weakened into Γ) against the hypothesis to
  swap `ψ/[s] ⤳ ψ/[nm m]`, then `Provable.exI ψ m`. Finishes `embedC.exs` (the `rew_subst_term` setup
  is already in place — see `wip/Embedding.lean`).
- **`embedC.axm`**: `𝗣𝗔⁻` instances → strip `∀` (`allω`), decompose connectives, bottom at `axTrue`;
  `univCl(succInd ψ)` → the worked meta-induction below, with `nm n+1 = nm(n+1)` via the same congruence.

API notes: term value = `Semiterm.valm ℕ ![] id s`; numeral value `valm ℕ … (nm m) = m` (find/derive
`val_numeral`); `nm`/`signedLit`/`LitTrue` live in `src/GoodsteinPA/Zinfty.lean` now.

---

## ⏭️ LAP-10 PROGRESS (earlier in lap)

**Done lap 10 (all committed, green):**
- `rew_subst_nm` PROVED ⟹ `provable_rew`/`ZProvable.rew` fully axiom-clean (`[propext, choice,
  Quot.sound]`). The M4 renaming enabler is DONE.
- `embed` `shift` + `all` PROVED ⟹ **8/10 cases** (only `axm`, `exs` remain). `all` is the ω-rule
  case: `provable_rew` substitutes the freed var by each `nm n` (undoing the `shift` on `Γ` via
  `rewrite_comp_shift_eq_id`), then `Provable.allω`.

**Remaining M4 cases — both deep:**

### `axm` (THE crux — Z∞-derive each PA axiom). `φ ∈ (𝗣𝗔:Schema)` = `↑σ`, `σ ∈ 𝗣𝗔⁻ ∪ InductionScheme`.
`axm` does NOT need the assignment reformulation (φ=↑σ is CLOSED). By `ZProvable.weakening` (`{↑σ} ⊆ Γ`
since `↑σ ∈ Γ`) reduces to `ZProvable {↑σ}` per axiom.
- **(a) `σ ∈ 𝗣𝗔⁻` (PeanoMinus, finite):** each a true closed ∀-sentence (semiring/order axioms). Z∞-
  derivable at finite ordinal. Bounded grind (enumerate Foundation's `PeanoMinus` axiom set).
- **(b) `σ = univCl(succInd ψ)` — induction via ω-rule. FULL PAPER PROOF WORKED OUT (lap 10):**
  `succInd ψ = ψ(0) → (∀x, ψ(x)→ψ(x+1)) → ∀x, ψ(x)`. After stripping `univCl` (iterated `allω` over the
  free-var numeral assignments) and two `orI` (Tait `A→B ≡ ∼A⋎B`), reduce to the sequent
  `S := {∼ψ(0), ∼(∀x,ψ(x)→ψ(x+1)), ∀x,ψ(x)}`. Introduce `∀x,ψ(x)` by `allω`: ∀n need `{∼ψ(0), ∼∀step, ψ(n)}`.
  **Meta-induction on n** (the heart — ω-rule absorbs PA-induction):
  - n=0: `{∼ψ(0), …, ψ(0)}` has `ψ(0)` and `∼ψ(0)` ⟹ `provable_em`. ✓
  - n→n+1: want `{∼ψ0, ∼∀step, ψ(n+1)}`. **`cut` on `ψ(n)`** (cut rank = `complexity ψ + 1`, uniform):
    - left `{∼ψ0, ∼∀step, ψ(n)}` = IH `D_n`. ✓
    - right `{∼ψ0, ∼∀step, ψ(n+1), ∼ψ(n)}`: `∼∀step = ∃y∼step(y)`; `exI` witness `n` reduces to
      `{∼ψ0, ∼step(n), ψ(n+1), ∼ψ(n)}` where `∼step(n) = ψ(n) ⋏ ∼ψ(n+1)`; `andI` splits into
      `{ψ(n),…,∼ψ(n)}` (em ✓) and `{∼ψ(n+1),…,ψ(n+1)}` (em ✓).
  Cut rank uniform `complexity ψ + 1`; ordinal O(n) per instance ⟹ `allω` gives ~ω. **Uses ONLY M5's
  existing constructors** (`provable_em`/`cut`/`exI`/`andI`/`allω`/`orI`) — no new smart constructors.
  Lean friction = Foundation-syntax wrangling: unfold `↑(univCl(succInd ψ))` `“…”`-DSL into the nested
  `⋎/∼/∀/∃` structure + the numeral substitutions `step(n)`, `ψ(x+1)`. Mechanical but intricate; multi-step.

### `exs` (needs the assignment reformulation). Open witness term `t` ⟹ naive statement can't close it.
Reformulate `embed : ∀ e:ℕ→ℕ, ZProvable (Γ.image (ρe ▹))`, `ρe := Rew.rewrite (nm∘e)`. ALSO needs a Z∞
closed-term→numeral collapse (`ρe▹t = nm m` is arithmetic, built from PeanoMinus eqns ⟹ intertwined with
`axm`(a)). Restructure re-proves the 8 done cases (mechanical, ρe distributes) — do AFTER `axm`.

---

## 🧭 LAP-9 DEEP-REFLECTION COURSE-CORRECTION (2026-06-22)
Full synthesis: `REFLECTION-2026-06-22.md`. STATUS refreshed. **The priority order below (A/B/…) is
SUPERSEDED.** New order, hardest-first = **unavoidable-first**:

1. **M4 — embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` = THE next target.** The *universal bottleneck*:
   needed on Route A, two-phase Route B, AND the abandoned Zekd route — there is no headline path that
   skips it. **LAP-9 FEASIBILITY PROBE (done this lap) — the machinery EXISTS; here is the mapped path:**
   - **Foundation's finitary calculus** (`.lake/.../Foundation/FirstOrder/Basic/Calculus.lean`):
     `Derivation 𝓢 : Sequent L → Type` (List sequents), constructors
     `axm (φ∈𝓢) | axL | verum | or | and | all (φ.free :: Γ⁺) | exs t | wk | cut` — maps almost 1-1
     onto M5's `ZinftyF.Deriv`. A **Finset** variant `Derivation2` exists (`Calculus2.lean:13`, same
     constructors) + `provable_iff_derivable2 : 𝓢 ⊢ φ ↔ 𝓢 ⊢!₂! φ` (`Calculus2.lean:94`) — matches M5's
     Finset substrate (use it to skip the List→Finset bridge).
   - **The lap-6 "derivation-substitution" deep case is ALREADY PROVIDED:**
     `Derivation.rewrite : 𝓢 ⟹ Γ → ∀ (f:ℕ→SyntacticTerm L), 𝓢 ⟹ Γ.map (Rew.rewrite f ▹ ·)`
     (`Calculus.lean:255`). So the **finitary `all` (`φ.free :: Γ⁺`) → M5 ω-rule `allω`** conversion is:
     for each numeral `n`, `rewrite` the free var by `n` to get `𝓢 ⟹ φ/[n] :: Γ`, embed each, assemble
     via `Provable.allω` (`src/Zinfty.lean:183`). **No missing machinery.**
   - **The `axm` case** splits cleanly because `𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`
     (`Foundation/FirstOrder/Arithmetic/Schemata.lean:52`): (a) `φ ∈ 𝗣𝗔⁻` (PeanoMinus, **finite**) —
     each a true ∀-sentence, Z∞-derivable at a finite ordinal (bounded grind); (b) `φ = univCl(succInd ψ)`
     (`mem_InductionScheme_of_mem`, Schemata.lean:85) — derive in Z∞ **via the ω-rule** (`ψ(n)` for each
     `n` by `n`-fold step, then `allω`), ordinal ~`ω·k`. **This is the one genuine deep case** (Buchholz
     §5.5 / Towsner §16) — but it's standard textbook content and `Provable.allω` is already built.
   - **LAP-9 DID THIS: `wip/Embedding.lean` COMPILES** (`lake env lean wip/Embedding.lean`).
     `embed : Derivation2 (𝗣𝗔:Schema) Γ → ∃ α c, Provable α c Γ` over the SAME `Finset (SyntacticFormula
     ℒₒᵣ)` substrate (no language translation). **6/10 cases DONE** (verum/and/or/wk/cut/closed).
     **`provable_em` FULLY PROVED + axiom-clean** (`[propext,choice,Quot.sound]`): the Z∞ excluded-middle
     `∀ φ Γ, φ∈Γ → ∼φ∈Γ → ∃ a, Provable a 0 Γ`, incl. the ∀/∃ numeral ω-family. Promotable to `src/`.
   - **4 disclosed `sorry`s remain = the genuine deep content, ALL needing free-var/subst machinery
     for M5's `Deriv` (interdependent). Build the shared enabler FIRST:**
     - **(0, enabler) M5 renaming/subst lemma** = analogue of Foundation `Derivation.rewrite`
       (`Calculus.lean:255`): `Provable α c Γ → Provable α c (Γ.image (Rew…▹·))`, induction on `Deriv`
       (8 cases; `allω` case = the care point). Unlocks `shift`/`all`/`exs` together.
     - **`shift`** — corollary of the enabler. **`all`** — free var `&0` → each numeral via enabler →
       `allω`. **`exs`** — witness term → numeral value → `exI`. **`axm`** (deepest) — PeanoMinus finite +
       `univCl(succInd ψ)` via ω-rule. Buchholz §5.5.
2. **M7a — transparent arithmetization** = parallel/fallback (shovel-ready, faithfulness-gated):
   `gAllReal = ∀x∃y[g_y(x)=0]` + `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`.
3. **Bounding bridge (small, downstream):** prove on M5's **real cut-free `Deriv`** directly
   (`allInv` ∀ away, read `exI` numeral off, witness `≤ hardy(toONote α)N`), combine with M6's
   `hardy_lt_goodsteinLength` (`src/LowerBound.lean:258`). **Reuse M6's ℕ-domination fact, NOT the
   abstract `B` transport** — the `B` lower bound is the template, banked. Ordinal seam = one `toONote`
   (check mathlib `ONote.repr` surjectivity onto `[0,ε₀)`).

**DO NOT RESUME** the witness-bounded cut-elim thread: `cutReduceAllAux`, `Zekd`, any 4th index
calculus. Proven off-critical-path (lap-8 findings: single-index Hardy inequality is FALSE; landscape
memory: the Hardy `k` index was never needed for cut-elim). `wip/{BoundedZinfty,SplitZinfty,
OperatorZinfty}.lean` = reference only. Everything below this block (the lap-7/8 A/B/Zekd plans) is
**historical context**, not the live plan.

---

## 🗺️ OPEN-OBLIGATION INVENTORY (lap-7 end) — full list + 3 attack paths each
### ⚠️ SUPERSEDED by the lap-9 block above — kept for history/attack-path detail only.
The headline `Statement.peano_not_proves_goodstein` is the only `src/` sorry (the designated open
target; anti-fraud — do NOT fill until the chain genuinely closes axiom-clean). It is reached via the
connecting spine. Open spine pieces, with attack paths:

## 🧭 LAP-8 STRATEGIC PIVOT (ON-LINE-FINDINGS 2026-06-22) — TWO-PHASE architecture is the headline path
The findings doc (`archive/findings/…omega-rule-commuting-bound.md`) **proves the §19.6 commuting bound
cannot close in any single-numeric-`k`/`(k,d)`/`(k,d,e)` system** (the Hardy inequality is FALSE; Towsner
hand-waves it). The lap-8 `Zekd cutReduceAllAux` commuting cases hit exactly this wall (norm-boundary
strictness). **Resolution (literature-standard, Buchholz §5 / Schwichtenberg–Wainer Ch.4): NEVER thread
the witness index through cut-elim. Two phases:**
  1. **Cut-elimination on the WITNESS-INDEX-FREE calculus** — pure ordinal + cut-rank. **This is M5,
     `src/Zinfty.lean`, ALREADY DONE + axiom-clean** (`Deriv.Provable.cutElim`). Commuting cases there are
     one-liners (`α#βₙ < α#β`) — no `k`/`d`/`e` to thread.
  2. **Hardy-bound the CUT-FREE result** — on a cut-free derivation there is NO `+α` growth, so the
     `max{k,n}`-vs-`+α` clash cannot arise. **This is M6, `lowerBound_hardy_selfcontained`, ALREADY DONE**
     (applied at `c=0`).
**The remaining work is the BRIDGE connecting them** (was "step 4 subformula bridge", now the critical
path): a cut-free `Z∞ ⊢^{α}_0 {gAll}` (from M4-embed + M5-cutElim) ⟹ a witness-bounded `B`-derivation
(subformula property: cut-free `{gAll}` uses only `GForm` subformulas; + a Hardy **bounding lemma** reading
off `∃`-witnesses ≤ `H_α(N)` on the cut-free structure) ⟹ contradicts `lowerBound_hardy_selfcontained`.
**Next lap: build this bridge.** The `Zekd`/`SplitZinfty` witness-bounded-cut-elim effort is a banked
alternative (NOT on the critical path anymore); its inversions/§19.5/`mono_e`/structural-`cutReduceAllAux`
cases stand for reference. Faithfulness corrections from the findings (carry into write-ups): Lemma 16.10
is `α<β ∧ τα<k ⟹ h_α(k)<h_β(k)` (strict); cut-elim base is `ω^α` (Towsner)/`3^α` (Buchholz), not `2^α`;
`h_{β#ω}(k)=h_β(2k)` is NOT a Towsner lemma (heuristic only); the operator `H[X]` is Buchholz-1992, not
the on-disk notes (which are pure-ordinal for PA).

---

**LAP-8 UPDATE — (A)/(B) substantially advanced.** Hardy-infra layer BANKED (axiom-clean, `src/`):
`hardy_add_comp`/`hardy_add_collapse` (control collapse) + `hardy_comp_lt_goodsteinLength` (lower-bound
nested-index domination). Control-ordinal operator calculus `Zekd α e k d c Γ` built in
`wip/OperatorZinfty.lean`, sorry-free through §19.5, with the NEW `mono_e` control axis. Design validated
(ADDENDUM 5): single control ordinal `e` closes the ADDENDUM-4 witness-index obstruction (no set-valued
`H` needed). **ONE remaining girder for step-1 cut-elim: §19.6 `cutReduceAll` on `Zekd`.**
  - **[LAP-8 NEXT] Port `Zinfty.lean:785 cutReduceAllAux` to `Zekd`.** Invert ∀-side → `fam`; induct on
    ∃-side; principal `exI` cuts `fam(witness)`; commuting cases reapply at `osucc(α+γ)`
    (`add_osucc_descent` banked), `d ↦ d + norm α` (norm-budget), `e` raised at the top cut via `mono_e`.
    **FIRST**: NF-ify the `Zekd` leaf rules (`trueRel`/`trueNrel` need `hαNF`) — leaf cases need
    `norm(α+γ) ≤ norm α + norm γ` (`norm_add_le`, NF-essential). ADDENDUM 5 has the subtlety + 3 fixes
    (option (b)/NF-ify-leaves cleanest). Budget arithmetic: issue leaf at the node's own `γ` then `weak`
    up to `osucc(α+γ)` (avoids the `osucc` `+1`-vs-strict-`<` boundary).

**(A) §19.6 `cutReduceAll` — the critical-path crux** (calculus + Hardy infra now in place — see LAP-8).
  1. **Control-ordinal operator calculus (RECOMMENDED).** Replace `Zkd`'s `(k,d)` with an index
     `(e, k, d)` where `e : ONote` is a *control ordinal* and the ω-premise / witness bound use
     `hardy e (n + k) + …` (a `hardy`-closed index). Cut-elim raises `e` to dominate cut-formula bounds;
     the principal cut's witness `w ≤ hardy γ (max k n + d) ≤ hardy e (n + k + d)` (γ<e, hardy mono in
     both args) stays controlled. Lower bound survives via **general Hardy additivity** `hardy α (hardy e m)
     ~ hardy (e (#)+ α) m` (e+α<ε₀ ⟹ G dominates). Port §19.2–19.5 from `SplitZinfty` (`max k ·` ⤳
     `hardy e ·`). **Lap-7 de-risk:** the cut-elim *control* side needs NO new lemma — the witness
     control `hardy γ (idx) ≤ hardy e (idx)` (γ<e) is the **existing** `hardy_le_of_lt` (`src/Hardy.lean`,
     `+ hardy_monotone` for the argument). Only the *lower-bound* side needs general Hardy additivity (B).
  2. **Buchholz set-valued operator `H`** (Buchholz §9 / 1992) — fully general; heavier. Fallback if the
     single control-ordinal `e` can't express some closure. `ON-LINE-REQUEST` filed for the PA spec.
  3. **Restrict the calculus to the `GForm` fragment** (the headline only needs cut-elim for derivations
     of `{gAll}` and its subformulas). The ∃-side may then have bounded structure making the witness
     index controllable without a full operator. Investigate whether the subformula property pre-bounds it.

**(B) General Hardy additivity** `hardy (e (#)+ α) m = hardy α (hardy e m)` (infra for A.1; generalizes
  the proved finite-tail `hardy_add_ofNat`).
  1. Induct on α through the fundamental-sequence structure (successor + limit), using the banked
     `fundamentalSequence`/`Reaches`/`hardy_le_of_reaches` machinery in `src/Hardy.lean`.
  2. Prove only the *inequality* `hardy α (hardy e m) ≤ hardy (e + α) m` (ordinary `+`) — weaker but may
     suffice for domination; likely easier than the exact `#`-additive identity.
  3. Aristotle target: self-contained ONote/Hardy statement (feed once A.1's exact form is pinned).

**(C) §19.7 `cutElimStep` + §19.9 `cutElim`** (depend on A). Ordinal `ω^α` (`norm_omegaPow` banked);
  iterate. Paths: port `src/Zinfty.lean` structure / the `SplitZinfty` helpers / existential-index.

**(D) Subformula bridge** (cut-free operator-derivation of `{gAll}` ⟹ `B`-derivation ⟹ lower bound).
  Paths: structural subformula-closure induction / `GForm ↪ ℒₒᵣ` identification / reuse M6 as-is.

**(E) M4 embedding `PA ⊢ φ ⟹ (calculus) ⊢ φ`** — INDEPENDENT of A (parallel thread). Recon done lap 6.
  Paths: induct on Foundation `Derivation` (axm = Lemma 16.1 + Cor 16.6 induction instances; `all`→ω-rule
  via derivation-substitution; `exs`→witness bound) / list→finset bridge / scope `axm` first.

**(F) M7a language gap** `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal` — INDEPENDENT (parallel thread). Paths:
  arithmetize `goodsteinSeq` as a real Π₂ `ℒₒᵣ` formula (Foundation Σ₁ tools) / gate by `Bridge.lean` /
  prove one direction first.

**Lap-7 acted on (A): conceptual crux resolved, 4 lemmas proved, `(k,d)` calculus through §19.5 built,
the two §19.6 obstructions precisely characterized (norm-budget CLOSED, witness-index ⟹ needs operator).**

---

## ✅ LAP-7 — cut-elim `k`/`τ` crux RESOLVED (offline read of Towsner §15–§20). See `ANALYSIS-2026-06-22-cutelim-k-threading.md`.
The lap-6 "norm grows under addition ⟹ cut-elim might break `norm<k`" worry was a **misframing**.
Resolved facts (the design for ALL of §19): (a) `k` is **not** fixed — it grows (§19.5 `k↦2k`; §19.6
`k↦h_{β#ω}(k)`; §19.7 `k↦h_{ω^α}(k)`). (b) `lowerBound_hardy_selfcontained` is already `∀k` ⟹ growth
harmless. (c) every `ONote` is `<ε₀` by construction ⟹ ε₀ side-condition **free**. ⟹ **state the whole
cut-elim chain existentially in `k`**: `CutFree α Γ := ∃k, Zk α k 0 Γ`; endgame
`(∃k c, Zk α k c Γ) → α.NF → ∃ α' k', α'.NF ∧ Zk α' k' 0 Γ`, then subformula-bridge + lower bound.
Route decision recorded in `STATUS.md`: **STAY ROUTE B**. `ON-LINE-REQUEST` closed.

### Refined §19.6 plan (`cutReduceAll` for `Zk`) — the next girder, now unblocked
Port `src/Zinfty.lean:785 cutReduceAllAux` (the lap-3 ∀/∃ reduction over the unbounded `(α,c)`
calculus, fully proved) to `Zk`, adding the `(k,NF,norm)` bookkeeping:
- **Structure (unchanged from lap 3):** invert the ∀-side once (`allInv` → numeral family
  `fam : ∀n, Zk α k c (insert (φ/[nm n]) Γ)`), then **induct on the ∃-side `Zk γ k c Δ`** with
  `(∃∼φ)∈Δ`; principal `exI` case = cut `fam n` at the witness numeral; commuting cases re-apply the
  rule over `Δ.erase(∃∼φ) ∪ Γ`. `Zk` is `Prop`-valued, so induct directly (no height fn `o d`); the
  running ordinal is the constructor bound `γ` itself (sub-bounds `<γ` come from the descent premises).
- **Bound:** ordinal `α + γ` (`ONote.+`, `add_lt_add_left_NF`/`le_add_left_NF` banked); slack via
  `osucc` at cuts (`lt_osucc`, `osucc_NF` banked).
- **`k`-growth (the new content vs lap 3):** the conclusion's `k` is **`h_{β#ω}(k)`** (a Hardy value),
  NOT the input `k` — Towsner §19.6 exactly. ⚠️ **LAP-7 FINDING — the `allω`-commuting case is a REAL
  obstruction, not mechanical.** Reconstructing the ω-rule after adding `α` to the bound needs
  `norm(α+βₙ) < max K n`, but `norm(α+βₙ) ~ norm α + n` exceeds `max K n ~ n` for large `n`, for ANY
  fixed `K` (norm is not `<`-monotone, so `βₙ<β` doesn't bound `norm βₙ`; natural sum + `τα<k` don't
  save it). Towsner's "follows from IH" glosses this. **The numeric `(α,k)` form may genuinely need
  either (1) Buchholz operator-controlled derivations, (2) a generalized `Zk.allω` with a controlled
  premise-index `f n` (re-verify M6 lower bound survives — tension: cut-elim wants `f` to GROW to fit
  `+α`, the lower bound wants witnesses `≤ h(f n) < G(n)` BOUNDED), or (3) re-derived Towsner 16.8–16.10
  Hardy inequalities (likely insufficient per the `+α` analysis).** Full derivation +
  attack options in `ANALYSIS-2026-06-22-cutelim-k-threading.md` ADDENDUM. `ON-LINE-REQUEST` re-filed.
  ⚠️ **LAP-7 UPDATE — option (2) (global numeric index swap) is ELIMINATED.** Tried `max k n → k + n`:
  it fixes §19.6-commuting (`(k+n)+norm α = (k+norm α)+n`) but **breaks `allInv`**, whose principal case
  relies on `max`'s idempotence (`max(max k n₀)n₀ = max k n₀`); under `+` the lingering-duplicate subcase
  produces index `k + 2n₀` (slope 2), forcing the lower bound to need `hardy α (2n) < G n` — a
  *multiplicative* rescaling the additivity lemma does NOT give. So **no single numeric `idx(k,n)` serves
  both** `allInv` (wants idempotence) and §19.6-commuting (wants additive shift). Full analysis:
  `ANALYSIS-…-cutelim-k-threading.md` **ADDENDUM 2**. The `k+n` experiment was reverted (wip stays
  sorry-free). **REVISED RECOMMENDATION = option (1): function/operator-valued `allω` index** (Buchholz
  operator-controlled derivations specialized to PA): each `allω` carries a controlled index *function*
  `g : ℕ → ℕ` (`g n ≤ n + const`), rules compose `g`s (idempotently for `allInv`, post-composing `+norm α`
  for cut-elim). Keeps slope 1, so the proved domination lemmas (`hardy_add_ofNat`,
  `hardy_shift_lt_goodsteinLength`) still apply. Larger refactor of `wip/BoundedZinfty.lean` + `B`/lower
  bound, but it's the only design closing BOTH obstructions. Start fresh-headed; don't half-break wip.
  Lap-7 investigation confirmed M6 domination is STRONG (`hardy_lt_goodsteinLength {α NF} : ∃ N, ∀ m ≥ N,
  hardy α m < G m` — beats `hardy α` at *every* large `m`), so the controlled-`g` lower bound is viable.
  **This is now the hardest-first crux of step 1 — the principal `exI` case is clean; the commuting
  `allω` bounding is the live frontier.** Use `hardy` (`src/Hardy.lean`; `Reaches`/`fundamentalSequence`/
  `hardy_le_of_reaches`/`hardy_monotone` already banked).
- **`norm` ingredient (lap 7): BOTH PROVED + banked, axiom-clean** in `wip/BoundedZinfty.lean`:
  `norm_addAux_le` (head-merge bound) and `norm_add_le {α γ NF} : norm(α+γ) ≤ norm α + norm γ` (the
  `τ(α#β)≤τα+τβ` budget fact). NF is essential — the NF-free version is machine-checked FALSE; the
  eq-merge case is discharged by additive-principality **absorption** (`a + γ = γ` when `repr a <
  ω^(repr e) ≤ repr γ`, via `Ordinal.add_of_omega0_opow_le`). `wip/BoundedZinfty.lean` is **sorry-free**.

---

State after lap 6 (2026-06-22). Build green (`lake build GoodsteinPA`, 1257 jobs). Phase 0 + Phase 1
clean; **M5 (cut-elim) and M6 (Hardy lower bound) both DONE**. Headline stays a literal `sorry`
(anti-fraud). See `PHASE2-DECOMPOSITION.md` for the girder ladder; `ANALYSIS-…-bounding-resolution.md`
§"M4 scoping" for the 5-step connecting spine.

## ✅ LAP-6 — M6 DONE (lower bound self-contained); TOP PRIORITY now = step 1, the `Zᵏ` calculus
`src/GoodsteinPA/LowerBound.lean` (`lowerBound_hardy_selfcontained`) is the full Towsner Thm 17.1 with
no hypotheses beyond `α.NF`, axiom-clean modulo the 🟢 `native_decide` Goodstein base-cases. M5 + M6
are now both complete but **disconnected** (M5 = unbounded `(α,c)` over real `ℒₒᵣ`; M6 = bounded
`(α,k)` over the `GForm` fragment). The connecting spine (hardest-first):

### Step 1 — `Zᵏ`: witness-bounded ω-calculus over real `SyntacticFormula ℒₒᵣ` (Towsner §15)
**DEFINED + §19.2–19.5 DONE** (`wip/BoundedZinfty.lean`, lap 6, all axiom-clean). Chosen design:
**ONote-indexed, B-style (bound-as-parameter, no `⨆`-suprema)** over real `ℒₒᵣ` formulas, with both
`(α,k)` side conditions the lower bound needs (lap-4 finding — cannot be dropped): truth-atom rules
`trueRel`/`trueNrel` (`norm α < k`) + `∃`-witness bound (`exI` carries `n ≤ hardy α k`). Plus a
height-preserving `wk`, a β<α `weak` (raises ordinals in principal inversion cases), `∧`/`∨`/`cut`.
Built: `mono_k`, `mono_c`, `wk`/`weakening`; the **full inversion suite** `orInv`/`andInvL`/`andInvR`/
`allInv` (reshuffle helpers `invPush`/`invPull`/`invPush2`/`inv1Push`/… kept standalone so
`DecidableEq Form` doesn't blow the heartbeat limit inside the big inductions); the **§19.5** ∧/∨
cut-reductions `cutReduceConj`/`cutReduceDisj` (`lt_osucc` + caller-supplied NF upper bound `δ`, result
at `osucc δ` — no natural sum needed).

**NEXT — §19.6 ∀/∃ cut-reduction `cutReduceAllAux`** (the hard, non-invertible one; the witness-bound
survival crux). Port `src/Zinfty.lean`'s measure-style version to parameter-style:
- **Bound framing:** the family `fam : ∀ n, Zk α k c (insert (φ/[nm n]) Γ)`; induct on the ∃-side
  `d : Zk γ k c Δ` with running conclusion bound **`α + γ`** (`ONote.add`; `add_nf` instance gives NF,
  `repr_add` + `Ordinal.add_lt_add_left` give strict monotonicity in `γ` for the premise-`<` conditions).
- **Principal `exI` case** (∃-side introduces `∃⁰∼φ` at witness `n`): cut `fam n` (∀-instance) against
  the ∃-premise on `φ/[nm n]` (complexity `< c`). This is the witness cut.
- The non-principal cases mirror the inversions (reuse the union-reshuffle pattern; src frames the
  running sequent as `Δ.erase (∃⁰∼φ) ∪ Γ`).

**Then `cutElimStep` (§19.7, `c+1→c`, bound `ω^α = oadd α 1 0`) + `cutElim` (§19.9).**

⚠️ **KEY FINDING (lap 6) — the `norm<k` budget does NOT survive ordinal addition; it grows.** `norm`
is `max` over CNF coefficients (`Hardy.lean:637`), and addition MERGES coefficients when leading
exponents coincide: machine-checked `norm ω = 1` but `norm (ω+ω) = norm (ω·2) = 2`. So the naive
"`norm(α+γ) ≤ max`" is **false**; the true bound is additive (`norm(α+γ) ≤ norm α + norm γ`, to verify).
Consequences for the cut-elim design:
- **§19.7 `ω^α` blow-up is SAFE:** `norm (oadd α 1 0) = max (norm α) 1` (machine-checked, `norm_omegaPow`),
  coefficient stays `1` — a pure ω-tower never bumps `norm` beyond `max(norm α, 1)`. So iterating the
  rank-reduction keeps the budget (for `k ≥ 2`).
- **§19.6 within-rank addition is where `norm` grows.** The ω-rule combines premises by *supremum*
  (bound-as-parameter, no sum), NOT addition — so it doesn't bump `norm`. Only the §19.6 cut-combination
  (∀-family `α` + ∃-side `γ`) is an addition, and cut-elim performs finitely many such reductions (cut
  rank `c` finite), so `norm` grows by a *bounded* amount ⇒ choosing `k` large enough at embedding (M4)
  absorbs it. **The precise bookkeeping (how Towsner threads `τ`/`k` through §19; the exact growth bound)
  needs the paper — see `ON-LINE-REQUEST.md`.** Do NOT claim cut-elim closed until this is pinned down.
- Helpers banked this lap: `lt_osucc`, `add_lt_add_left_NF`, `le_add_left_NF`, `norm_omegaPow`. Still
  need (build with §19.6): `norm (α+γ) ≤ norm α + norm γ`, `norm (osucc δ) ≤ norm δ + 1`.
(`Ordinal.nadd`/`♯` absent in mathlib v4.31.0; ordinary `+`/`osucc` with slack, as `src/Zinfty.lean` did
— note natural sum would NOT help here, it merges coefficients the same way.)

### Step 2 — M4 embedding `PA ⊢ φ ⟹ Zᵏ ⊢^{α,k}_c φ`  (UNBLOCKED — independent of the §19.6 τ/k question)
α<ε₀, finite c (Towsner §16/§18). **Reconnaissance done (lap 6).** Foundation's proof object is
`Derivation (𝓢 : Schema L) : Sequent L → Type` in `Foundation/FirstOrder/Basic/Calculus.lean:20`
(`Sequent L = List (SyntacticFormula L)`, one-sided/Tait). Constructors + their `Zᵏ` image (the
embedding inducts on this `Derivation`):
- `axm : φ ∈ 𝓢` — **the PA-axiom case, the crux.** `Zᵏ` must derive each PA axiom at a bounded `(α,k)`:
  Lemma 16.1 (true Δ₀/atomic axioms via the `trueRel`/`trueNrel` rules, low bound) + Cor 16.6 (the
  **induction-scheme** instances at bound `ω·4 # 2rk(φ) # 8` — the real work; `∀`-closure via the
  ω-rule). This is the bulk of M4.
- `axL r v`→`Zk.axL`; `verum`→`Zk.verumR`; `or`→`Zk.orI`; `and`→`Zk.andI`; `wk`→`Zk.wk`;
  `cut`→`Zk.cut` (finitely many cut formulas of bounded complexity ⇒ finite cut rank `c`).
- `all` (eigenvariable `φ.free`) → **`Zk.allω`** (finitary ∀ becomes the ω-rule: derive `φ/[nm n]` for
  every `n`). 2nd deep case: needs **derivation-substitution** — specialize the single eigenvariable
  premise (`φ.free :: Γ⁺`, fresh free var) to each numeral `n` (Foundation `Rew`/free-var substitution
  on a whole `Derivation`). The uniform eigenvariable proof instantiates to all `ℕ`-many ω-rule premises.
- `exs t` (witness *term* `t`) → **`Zk.exI`** with numeral `⟦t⟧ℕ`, needing the **witness bound**
  `⟦t⟧ℕ ≤ hardy α k` (Towsner picks `k` large enough — where the bound is established).
Two wrinkles: (a) Foundation sequents are **`List`**, `Zᵏ` uses **`Finset`** — need a list→finset bridge.
(b) Confirm how `𝗣𝗔 ⊢ ↑goodsteinSentence` (the headline's `LO.Entailment`) connects to `Derivation
𝗣𝗔-schema` (the `OneSided` instance at `Calculus.lean:31` is `Derivation`). The structural map is
clean — the depth is all in `axm`. Foundation-heavy; not Aristotle-friendly.

### Step 3 — cut-elim with `k`
Redo `src/Zinfty.lean` §19 tracking the witness bound. The inversions/reductions *strategy* ports; the
new content is threading `h_{ω^α}(k)` through §19.6 (∀/∃ reduction) and confirming `ω^α < ε₀` keeps the
final cut-free bound `< ε₀` (so domination still bites). No deep math doubt (literature-standard,
host-verified) — formalization labor.

### Step 4 — subformula bridge (the clean small connector)
A cut-free `Zᵏ`-derivation of `{gAll}` contains only subformulas of `gAll` closed under numeral
substitution = exactly `{gAll, gEx n, atom m n}` = the `GForm` fragment, so it **is** a `B`-derivation
⇒ `lowerBound_hardy_selfcontained` refutes it. Needs: a subformula-closure lemma for the ω-calculus
(structural induction over `Deriv`, ω-rule = closure under numeral substitution) + the `GForm ↪ ℒₒᵣ`
encoding identification. Reuses M6 as-is.

### M7a — the language gap (the other hard girder; Towsner Remark 10.3)
`goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is an **opaque Σ₁ blob**, NOT the
transparent `∀x∃y g_y(x)=0` that step 4 needs. Build a transparent Π₂ `gAllReal` (arithmetize
`goodsteinSeq` as a real `ℒₒᵣ` formula — Foundation's Σ₁/representability tools) and prove
`𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`'s spec so faithfulness can't regress.
Then the subformula bridge runs on `gAllReal`.

## ✅ LAP-5 — O0 done + the I∀ frontier RESOLVED; TOP PRIORITY is now O0′ (port `Hdom`)
The witness-bounded calculus `B` is now built over `ONote` with the **concrete** Hardy hierarchy
(`src/GoodsteinPA/Hardy.lean`, ported from Track-1). `wip/LowerBoundHardy.lean` proves, axiom-clean:
the ∃-fragment lower bound (`lowerBound_existential_hardy`, zero abstract hyps), `k`-monotonicity,
**∀-inversion** (`B.allInv`), and the **full Thm 17.1 modulo domination** (`lowerBound_hardy`). The
lap-4 "accumulating existentials" wall is resolved by inverting `gAll` away rather than carrying it
(see `ANALYSIS-2026-06-22-bounding-resolution.md`).

### O0′ (TOP) — discharge `Hdom : ∃ x, hardy α (max k x) < G x`
`G = goodsteinLength`; Goodstein defs (`bump`/`base`/`goodsteinSeq`) are **byte-identical** to Track-1.
Port `~/src/lean-formalizations Logic/Goodstein/{Length,Domination,DominationOmega,TowerDomination,
GrowthStatement,DominationCorollary,GoodsteinLike,DominationBaseCases}.lean` →
`goodsteinLength_dominates_fastGrowing {o}(ho:o.NF) : ∃ N, ∀ m≥N, fastGrowing o m ≤ goodsteinLength m+2`.
Chain `hardy α m ≤ fastGrowing α m` (`hardy_le_fastGrowing`) + identify `G = goodsteinLength`. **Bridge
the `+2` to strict `<`** (the one genuinely-open bit; fastGrowing's gap over hardy swallows +2 for
large m — good Aristotle target). Then `lowerBound_hardy` becomes a self-contained Thm 17.1. NB the
port carries documented `native_decide` finite-base-case axioms.

<details><summary>Superseded lap-4 O0 (re-architect on the witness-bounded calculus) — DONE</summary>

## ⚠️ TOP PRIORITY (lap 4) — O0: re-architect on the witness-bounded calculus
**Finding (machine-checked, axiom-clean, `wip/WitnessBound.lean`):** the completed M5 cut-elimination
in `src/Zinfty.lean` is for a calculus with an **unbounded `∃`-witness** and **no numeric index `k`**.
That calculus cannot reach the headline — `unbounded_proves_goodstein` derives the Goodstein sentence
cut-free at ordinal 2, so Towsner's lower bound (17.1) is FALSE for it. The headline needs the
**witness-bounded, Hardy-indexed `(α,k)` calculus** (Towsner §15), where `∃` carries `v ≤ h α k`,
`True` carries `τ α < k`, and `∀`'s premises use `max k n`. See `STATUS.md` lap-4 finding.

Attack paths (hardest-first; the crux is now the lower bound + the `k`-tracking cut-elim):
1. **Finish the lower bound (M6 / Thm 17.1).** `wip/WitnessBound.lean` has the calculus `B` and the
   `∀`-free fragment proved (`lowerBound_existential`). The remaining frontier is the `gAll`/`I∀`
   case with *accumulating* existentials — Towsner's stated invariant looks insufficient there
   (see `ON-LINE-REQUEST.md`). Either crack the refined invariant (likely a single-ordinal
   `H`-controlled measure, Buchholz style) or get it from the literature, then discharge the abstract
   Hardy hypotheses `Hmono`/`Hdom`/`HG` from a real `h_α`/`τ`/`G` (mathlib `ONote.fastGrowing`?).
2. **Retrofit `k` into cut-elimination.** Redo `src/Zinfty.lean`'s inversions/reductions tracking the
   numeric bound `k` (the *strategy* ports; only the bookkeeping changes). Needed so the cut-free
   output of M5 still carries the `(α,k)` bound that 17.1 refutes.
3. **Decide architecture:** Towsner two-index `(α,k)` vs. Buchholz single-ordinal `H`-controlled
   derivations. The latter may formalize more cleanly (one well-founded measure, standard boundedness
   theorem). Resolve via `ON-LINE-REQUEST.md` before sinking the cut-elim redo.

Plus the **PA↔PA⁺ language gap**: our headline is real-`ℒₒᵣ` PA with an opaque Σ₁ `goodsteinSentence`,
not Towsner's extended-language `∀x∃y g_y(x)=0`; the arithmetization bridge Towsner skips (Remark
10.3) is a separate deep girder (M7-adjacent). Route A (via `Con(PA)`, O1) stays entirely in real PA
and sidesteps this — re-evaluate Route A vs Route B in light of the language gap.
</details>

## Open obligations (toward a clean headline)

### O1 — `Reduction.goodstein_implies_consistency` (Route A girder) — `sorry`
`𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. The deep ordinal-analysis content via Con(PA).
Attack paths:
1. **Gentzen `TI(ε₀) ⊢ Con(𝗣𝗔)` + `γ ⟹ TI(ε₀)`** — the classic route; needs `PA_∞`
   cut-elimination (same `Z_∞` machinery as Route B) plus the Con(PA) lower bound. Reuses
   Foundation's Gödel II downstream. (Buchholz `on-gentzens-first-consistency-proof`.)
2. **Drop Route A entirely for Route B** (recommended) — Towsner shows `𝗣𝗔 ⊬ γ` directly without
   Con(PA); then `goodstein_implies_consistency` becomes unnecessary (leave it as a documented,
   never-used alternative). The headline is discharged via O2's chain instead.
3. Partial: keep the lemma but prove the *easier* converse direction / a weaker reflection
   principle first as warmup, to exercise Foundation's provability API (`⊢`, `Con`, D1–D3).

### O2 — the Phase-2 girder (Route B, Towsner) — milestones M3…M7 in `PHASE2-DECOMPOSITION.md`

**✅ M3 (Z_∞ calculus) + M5 (cut-elimination) COMPLETE & axiom-clean** in
`src/GoodsteinPA/Zinfty.lean` (promoted from `wip/`, 0 sorries, `#print axioms` = trust base only,
2026-06-22 lap 3). The whole Towsner §19 is machine-checked: inversions 19.2–19.4, cut reductions
19.5 (`cutReduceConj/Disj`) + 19.6 (`cutReduceAll`), atomic/⊥ cuts (`atomCut`/`removeFalsum`, **no
truth layer needed** — set sequents dissolve them), `cutElimStep` (19.7), `cutElim` (19.9). Key
findings: `Ordinal.nadd` ABSENT in mathlib v4.31.0 → ordinary `+` with `+1` slack (bounded below
`ω^(·+1)` by additive principality); the Hardy `k` index was NOT needed for cut-elim (pure Schütte
`(α,c)` suffices — it's a §17 device); `exI` restricted to numeral witnesses.

**NEXT (hardest-first): M4 — the embedding `PA⁺ ↪ Z_∞`** (Towsner §16 Thm 16.7 / §18 Thm 18.1). A
`PA⁺` proof of `φ` yields `∃ α<ε₀, ∃ k c, Z_∞ ⊢^{α}_c φ`, finite `c` (finitely many induction
instances ⇒ finitely many finite-rank cuts — the hinge of the whole argument). Sub-targets:
M4.1 (Lemma 16.1, true universal sentences derivable at finite bound), M4.2 (Lemma 16.5/Cor 16.6,
induction axioms at bound `ω·4 # 2rk(φ) # 8`), M4.3 (Thm 16.7, induct over a Hilbert-style proof;
reuse Foundation's finitary `Derivation`, map `∀`→ω-rule). M6 (Hardy lower bound, §17) is
**independent and parallelizable** (M6.1–M6.3 overlap Track 1 `Logic/FastGrowing`; M6.4 = Thm 17.1
is new and likely DOES need the Hardy `k` threaded through a cut-free `Provable₀`).

<details><summary>Superseded lap-2 status (M5 was one open leaf `cutElimStep`)</summary>
Done and **machine-checked** (`lake env lean wip/ZinftyF.lean`, only `cutElimStep` sorry):
- The `Z_∞` calculus `inductive Deriv` over `SyntacticFormula ℒₒᵣ`, **Finset sequents** (set-based,
  per Towsner ⇒ contraction is FREE, no `contr` rule), ω-rule `allω`, ordinal bound `o`, `ℕ∞`
  cut rank `cr`. The `ℕ∞/⊤` blocker is **gone**: `complexity : Form → ℕ` is finite.
- Full predicate-level inference API: `axL/verumR/andI/orI/exI/allω/cut/mono/weakening/cast`,
  contraction free.
- **All three inversion lemmas PROVED** (the syntactic content of cut-elimination):
  `orInvAux`/`Provable.orInv` (§19.2 ∨), `andInvAux`/`Provable.andInvL`/`.andInvR` (§19.3 ∧),
  `allInvAux`/`Provable.allInv` (§19.4 ω/∀). Each by structural induction on `Deriv`, all 8 cases,
  preserving ordinal bound and cut rank.
- `cutElim` (Thm 19.9) reduced to the single open leaf `cutElimStep` (Thm 19.7).

**NEXT (hardest-first): the cut-REDUCTION lemma (Towsner §19.5–19.7), the ordinal-arithmetic
heart of `cutElimStep`.** With all inversions in hand, the reduction lemma is: a top-level cut on a
formula of complexity `= c` between two `Provable _ c` derivations can be replaced by a cut-free-at-
rank-`c` derivation with the ordinal bounds *added* (not `max+1`). The principal-formula reduction
uses the inversions to push the cut to the immediate subformulas (∨/∧ → smaller-complexity cut;
ω/∀ → instantiate at the ∃-witness numeral). Then `cutElimStep` does the transfinite induction over
the derivation eliminating all rank-`c` cuts, raising `α ↦ ω^α`. Likely needs a numeric/Hardy `k`
parameter re-added to `Provable` (Towsner threads `h_{ω^α}(k)` through 19.6/19.7) — assess whether
the `(α,c)` indexing suffices first.

Attack paths:
1. **Continue the `wip/Zinfty.lean` prototype** (E2 encoding — *compiles*). Next: (a) connect
   `AForm` to a faithful arithmetic formula with a real free-variable/substitution layer (replace
   the `ℕ → AForm` family with a single body + numeral substitution), so `rk` is genuinely
   finite; (b) state M3.3 bound-monotonicity lemmas; (c) state M4 embedding + M5 cut-elimination
   theorems as disclosed `sorry`s. Bank each as it typechecks; promote to `src/` when green.
2. **Develop M6 (Hardy domination) via Track 1.** `~/src/lean-formalizations` `Logic/FastGrowing`
   is building `h_α`, monotonicity, and Goodstein-length domination on mathlib's
   `ONote.fastGrowing`. Reuse those for M6.1–M6.3; only M6.4 (Thm 17.1, the cut-free lower bound)
   is new here. (Does NOT block M3–M5 — parallelizable.)
3. **Tackle cut-elimination (M5) on the prototype first**, before the embedding — it is the
   self-contained heart (Towsner §19). **STATUS: M5 is now structured down to ONE leaf.**
   `wip/Zinfty.lean` has `Provable.cutElim` (Thm 19.9, full elimination) *proved* by induction on
   cut rank, reducing entirely to the single open lemma **`Provable.cutElimStep`** (Thm 19.7, one
   level). So the next concrete target is exactly `cutElimStep` = §19 inversions 19.2–19.4 +
   reductions 19.5–19.6 + the principal-`Cut`-on-rank-`c` case. Proving it makes the whole
   cut-elimination machine-checked (mod the embedding M4 and lower bound M6.4). NOTE: `cutElimStep`
   likely needs the numeric/Hardy `k` bound that `Provable` currently elides — re-add a `k : ℕ`
   index to `Provable`/`Deriv.o` first (it threads the `h_{ω^α}(k)` bound through 19.6/19.7).
   *(Resolved lap 3: the `k` index turned out NOT to be needed for cut-elimination.)*
</details>

### O2′ — M4 DESIGN DECISION (scouted lap 3, execute lap 4) ⭐
The embedding needs Z_∞ to derive PA's **true defining axioms** (e.g. `n+(m+1)=(n+m)+1`), which the
current calculus CANNOT: `axL` is the clash-based identity (`rel r v ∧ nrel r v ∈ Γ`) and `verumR`
is only `⊤`. Towsner's "True" rule is a **truth-based atomic axiom**. So M4 requires extending the
calculus. Concrete plan:
1. **Atomic truth predicate** — reuse Foundation `Semiformula.Evalm ℕ` (the `standardModel`
   instance for `ℒₒᵣ` over `ℕ`; `=`/`<` decidable). For embedding-substituted formulas (free vars
   replaced by numerals) truth is assignment-independent. **VALIDATED (lap 3)** — this typechecks
   (imports `Foundation.FirstOrder.Arithmetic.Basic.Model`):
   ```
   noncomputable def atomTrue (φ : SyntacticFormula ℒₒᵣ) : Prop :=
     Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ
   ```
   (`Foundation/.../Semantics/Semantics.lean:241`, `Arithmetic/Basic/Model.lean:25`.)
2. **Add `trueAtom` constructor** to `Deriv`: `(φ : Form) → (φ atomic) → Evalm ℕ … φ → φ ∈ Γ →
   Deriv Γ`, with `o = 0`, `cr = 0`. ⚠️ **This touches the completed cut-elimination**: every
   induction (`orInvAux`, `allInvAux`, `andInvAux`, `cutReduceAllAux`, `atomCutAux`,
   `removeFalsumAux`, `cutElimStepAux`) gains one new leaf case — mostly trivial (like `verumR`),
   EXCEPT `atomCutAux`: a `trueAtom` on the cut atom `rel r v` means `rel r v` is true ⇒ `nrel r v`
   is false ⇒ must remove it from the other premise. So `atomCut` needs a **truth-based false-atomic
   removal** (the genuine §19.2 content, now unavoidable, but only for atomics — decidable ℕ
   arithmetic). Do this extension on a `wip/` copy first; re-green; re-promote.
3. **ε₀** is `ε_ 0` in `Mathlib.SetTheory.Ordinal.Veblen` (first fixed point of `ω^·`); `omegaTower
   c α < ε₀` for `α < ε₀` is the closure fact M5.4/M7 need (ε₀ closed under `ω^·`).
4. Then M4.1 (Lemma 16.1) → M4.2 (Cor 16.6) → M4.3 (Thm 16.7), inducting over a `Peano`-proof
   (`𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`), reusing Foundation's finitary `Derivation`.

**Caveat on the clean state:** cut-elimination is currently truth-free and axiom-clean precisely
because of clash-`axL`. Adding `trueAtom` re-introduces a (decidable, atomic-only) truth layer.
This is the standard Schütte setup and is correct; just do it carefully so the §19 proofs stay green.

### O3 — `PA_delta1Definable : 𝗣𝗔.Δ₁` (Foundation axiom) — only on Route A
Needed to *state* Gödel II for `𝗣𝗔`; Foundation axiomatizes it (TODO in
`Incompleteness/Examples.lean`). Route B avoids it. Attack paths:
1. **Avoid** — go Route B (O1 path 2); the axiom never enters the headline profile.
2. Discharge it: construct the Δ₁-definition of PA's axiom set (PA⁻ + induction scheme) in
   Foundation's `Theory.Δ₁` framework and prove `isDelta1`. Deep arithmetization; multi-lap.
3. Upstream: check whether a newer Foundation rev proves it (the TODO may get filled upstream);
   file an `ON-LINE-REQUEST.md` to check the latest Foundation `Incompleteness/Examples.lean`.

**UPDATE (lap 6, cross-session news):** a separate session (`~/src/Foundation-delta1-burndown`,
branch `feat/induction-scheme-delta1`) is **actively discharging** both `PA_delta1Definable` and
`ISigma1_delta1Definable` (proving them in `InductionSchemeDelta1.lean`; reduced `PA.Δ₁` to 3 isolated
obligations, build green, ~1–2 laps to PA-complete per that session). So path 3 is in progress
**upstream** — do NOT duplicate it here. When it lands and our Foundation pin bumps to include it,
Route A's `not_proves_of_implies_consistency` becomes axiom-clean (no `PA_delta1Definable`). This is a
**fallback de-risk only**: our headline stays on **Route B** (Towsner direct, avoids `Con(PA)` and this
axiom). `goodstein_implies_consistency` (the `TI(ε₀)⊢Con(PA)`-inside-PA girder of Route A) remains
deeply blocked regardless, so the Δ₁ news doesn't make Route A the preferred path.

## Done — lap 4 (2026-06-22)
- **Witness-bound architectural finding** (machine-checked, axiom-clean, `wip/WitnessBound.lean`):
  the `src/Zinfty.lean` `(α,c)` cut-elimination is OFF the headline path (its unbounded `∃` makes the
  lower bound false). Built the corrected witness-bounded calculus `B`; proved the existential-fragment
  lower bound (`lowerBound_existential[_real]`) grounded against the real `G`; decomposed the full
  Thm 17.1 to the single `bounding` frontier (`True`/`W`/`I∃` cases machine-verified via `sat_mono_ord`,
  `I∀` case the literature-gated frontier; `lowerBound` contradiction-extraction real). Goodstein-side
  grounded: `G`, `goodstein_zero_succ`/`_mono`, `atomTrue_iff_G_le`. Filed `ON-LINE-REQUEST.md` for the
  rigorous `bounding` invariant + architecture (Towsner `(α,k)` vs Buchholz `H`-controlled).
- Next deep brick (architecture-independent, but gated on the notation/architecture decision):
  the **Hardy / fast-growing hierarchy + τ-controlled monotonicity** to discharge `Hmono`/`Hmono_n`,
  and **Goodstein domination** (Towsner §5–§9) to discharge `Hdom`. mathlib `ONote.fastGrowing`
  exists but has NO growth lemmas (deliberately minimal).
  - **STARTED** (`wip/FastGrowing.lean`, axiom-clean): `fastGrowing_id_le` — `n ≤ fastGrowing o n`
    (the inflationary half, which IS separable from ordinal-monotonicity: successor case via
    iterating a `≥id` map, limit case via the smaller-ordinal IH).
  - **Confirmed entangled:** *numeric* monotonicity (`Hmono_n` analogue) of `fastGrowing` — its
    limit case `fastGrowing (f m) m ≤ fastGrowing (f m') m` needs *ordinal* monotonicity at fixed `n`,
    which is the τ-subtle one (false for small `n` without the coefficient control — Towsner §8). So
    `Hmono`/`Hmono_n` for the real hierarchy genuinely need the τ machinery; not a quick brick.

## Done — lap 1
- M1: `Encoding.goodsteinTerminates_re` proved (`Computability.lean`: `primrec_natLog`,
  `primrec_bump`, `primrec_goodsteinSeq`). Phase 0 axiom-clean.
- M2: `Reduction.lean` — Gödel II hook + meta-reduction (axiom-clean mod `PA_delta1Definable`).
- Phase 2: `PHASE2-DECOMPOSITION.md` (Towsner-grounded ladder) + `wip/Zinfty.lean` (E2 encoding
  prototype — compiles: ω-rule inductive, ordinal/cut-rank measures, bound-domination lemma,
  `Provable.mono`/`.weakening`, and the **proved predicate-level inference API** `Provable.orI`,
  `.exI`, `.allI` — the ω-rule with the supremum ordinal bound, machine-checked against the
  `Deriv` measures via `Classical.choice`).

## ⭐ KEY FINDING (2026-06-22, end of lap) — build `Z_∞` ON Foundation's Tait calculus
Foundation **already has a finitary Tait one-sided FO sequent calculus**:
`FirstOrder/Basic/Calculus.lean` — `inductive Derivation (𝓢 : Schema L) : Sequent L → Type`
with constructors `axL, verum, or, and, all, exs, wk, cut` and a `height` measure, over the *real*
`SyntacticFormula ℒₒᵣ` (which already carries free variables, substitution, negation, rank).
Plus `FirstOrder/Hauptsatz.lean` (finitary cut-elimination). **There is NO infinitary calculus /
ω-rule / `PA_∞`** (confirmed by grep — only finitary Tait + Hauptsatz).

**Consequence — revise M3.1:** do NOT continue the standalone `wip/Zinfty.lean` `AForm`. Instead
define `Z_∞` as a new inductive **over Foundation's `SyntacticFormula ℒₒᵣ`/`Sequent`**, replacing
the finitary `all` (eigenvariable, one premise, `ℕ` height) with the **ω-rule** (`all` taking an
`ℕ`-indexed family `n ↦ φ[x ↦ numeral n]`, `Ordinal` height). This:
- **kills the `AForm` substitution-layer prerequisite** — Foundation's formula substitution +
  `rk` are reused, so `rk φ` is already finite and `cut`/`cutElimStep` become directly stateable;
- **shrinks M4 (embedding):** a PA proof already yields a Foundation *finitary* `Derivation`
  (via Hauptsatz machinery); M4 becomes "finitary `Derivation` ↪ `Z_∞`" (map each rule across,
  ∀→ω-rule) instead of re-deriving from `True`/`Lemma 16.1` by hand;
- **makes M7 natural:** everything is over real `ℒₒᵣ` formulas, so connecting to our
  `goodsteinSentence` is a formula-level statement, not a re-encoding.
The `wip/Zinfty.lean` prototype keeps its value as the *proof that the ordinal/ω-rule measures
work* (the encoding-feasibility result) — port its `o`/`cr`/`allI`/`cutElim` skeleton onto
Foundation's `Derivation`-shaped inductive. **This is the recommended first action next lap**
(read `FirstOrder/Basic/Calculus.lean` + `Hauptsatz.lean` first).

## Design note — `Provable.cut` + the `ℕ∞` cut-rank (next lap, read before refactoring)
`cr : Deriv Γ → ℕ∞` (cut rank can be `⊤` for pathological infinite families). A predicate-level
`Provable.cut` is the one rule still missing: from `Provable α c (φ ::ₘ Γ)` and
`Provable β c (φ.neg ::ₘ Γ)` it should give `Provable (max α β + 1) c' (Γ)` where
`c' ≥ rk φ + 1`. But `rk φ : ℕ∞` may be `⊤`, so you can't pick a finite `c' : ℕ` in general —
`Provable`'s `c : ℕ`. **Fix:** when `AForm` gets the real free-variable + numeral-substitution
layer (the M3.1 refinement), `rk φ` becomes provably finite (`rk φ ≠ ⊤`) for genuine formulas, so
`Provable.cut` and the Hardy-bounded `cutElimStep` both become stateable with finite `c`. So the
substitution-layer refactor is a prerequisite for *both* `cut` and `cutElimStep` — do it first.

## Gotcha noted (for the corpus)
For `Ordinal`, `add_le_add_right h c` elaborates to `c + a ≤ c + b` (adds on the *left*) — use
`add_le_add h le_rfl` to get `a + 1 ≤ b + 1` from `a ≤ b`. `gcongr` on `⨆`-bounds spawns a
`BddAbove (Set.range …)` side-goal (discharge with `Ordinal.bddAbove_range`).

## lap 48 — internal Cor 3.4 bricks landed; MinExpGe assembly remaining (2026-06-23)
DONE (axiom-clean, green): `icmp_iadd_clean`/`_boundary` (within+boundary unified), `iC_iadd_clean`
(C-split = Grz.C_add_clean), `iAbove_iomul` (MinExpGe step: `iAbove e0 a → iAbove (1+e0)(ω·a)`),
`iAbove_zero_iomul` (MinExpGe base: `iAbove 0 (ω·a)`). Plus general `icmp_swap` antisymmetry infra
in InternalONote.

REMAINING for the `iAbove (ocExp g) (ibigMul (l+1) β)` clean-condition (3 attack paths):
1. **Meta-iterate (recommended).** By `induction k:ℕ`: `iAbove (oadd1iter k 0) (ibigMul (k+1) β)`
   from base `iAbove_zero_iomul` + step `iAbove_iomul` (needs `isNF_ibigMul` for the NF arg, exists).
   `oadd1iter k = (iadd (ocOadd 0 1 0))^[k]`. Then identify `oadd1iter k 0 = ocOadd 0 k 0` (finite k)
   via `iadd_one_zero`/`iadd_one_fin`, and weaken the threshold `ofin l → ocExp g` (g < ω^(l+1) ⟹
   ocExp g ⪯ ofin l).
2. **Threshold weakening** is the one piece needing care: `iAbove (ofin l) a → (ocExp g ⪯ ofin l) →
   iAbove (ocExp g) a`. Since g's exps are FINITE codes (ig0/iblk have finite ocExp), the spine-vs-
   threshold comparisons are all finite (cmpV on coeffs) OR infinite-head-vs-finite
   (`icmp_infHead_finHead`) — provable WITHOUT general `icmp` transitivity. State as
   `icmp_spine_finThresh_mono : icmp s (ofin (l+1)) = 2 → j ≤ l → icmp s (ofin j) = 2` by cases on s.
3. Alternatively prove general `icmp_trans` (≺ transitive) once — heavier but unblocks everything.

Then assemble `icorAlpha` (mirror `Grz.corAlpha`): C-bound (`iC_iadd_clean`+`iC_ibigMul_le`+`iC` of g),
within (`icmp_iadd_clean` with `icmp a a`=1 via the same-lead), boundary (`icmp_iadd_clean_boundary`
+ `icmp_ibigMul` lifting β-descent). Feeds `DescentSemantic.nonterminating_of_xDescent`.
