# SERIES-4 JUDGE PASS — VERDICT: **PASS (validity)** · architecture scaffolded · SERIES-5 completion order

**Judge**: host session (Ren), 2026-07-03. Seated per the SERIES-2/3 supersession note.
**Baseline**: `plan` @ `844a27d` → work branch **`wip/series4-discharge`**.
**Machine gates re-run host-side** (box stopped): bare `lake build` green; witness `#print axioms`
re-run by the judge (not grinder-claimed).

---

## 1. Validity verdict — the route-B growth axiom discharge is AUTHORIZED

Independently re-verified (my own `#print axioms` on the wip modules):

| decl | footprint | role |
|---|---|---|
| `E1EmbeddingGrind.wainer_bound_witness` | `[propext, Classical.choice, Quot.sound]` **sorryAx-FREE** | the summit witness, at the axiom's verbatim type |
| `ReadoffValueGate.gated_certificate_uniform` | `[propext, Classical.choice, Quot.sound]` | hyp `Hcert` |
| `HardyMajorization.Scirc_dom_pad` | `[propext, Classical.choice, Quot.sound]` | hyp `HSdom` |
| `HardyMajorization.master_conversion` | `[propext, Classical.choice, Quot.sound]` | hyp `Hconv` |

The math is real. `wainer_bound_witness` genuinely dodges E1's disclosed sorries (kernel-certified
sorryAx-free), and the three hypothesis theorems are its verbatim hypothesis *types*.

## 2. Architecture scaffolded this pass (on `wip/series4-discharge`)

- **Promoted** `wip/{E1EmbeddingGrind,ReadoffValueGate,HardyMajorization}.lean` → `src/GoodsteinPA/`.
  All three compile as src library modules (`lake build` reached 1342/1346 with only the splice open).
- **New** `src/GoodsteinPA/WainerBound.lean` — a terminal module downstream of the embedding chain,
  holding the discharged `wainer_bound_of_pa_proves_goodstein` (theorem, verbatim former-axiom type) +
  the route-B headline `peano_not_proves_goodstein_growth`. Wired into the public root
  (`GoodsteinPA.lean`) and the blueprint root (`GoodsteinPABlueprint.lean`, so the audit sees nodes
  14/15).
- **Stripped** the `axiom` + headline + their blueprint attrs out of `WainerRoute.lean` (they moved to
  `WainerBound`; `WainerRoute` imports `Statement`, so they cannot live there — see §4).

## 3. ⚔️ SERIES-5 ORDER — complete the discharge (binding on grind laps)

**Mission**: from this scaffold, make `peano_not_proves_goodstein` print exactly
`[propext, Classical.choice, Quot.sound]`, `blueprint_audit` all-green, `lean-sorry src/` = 0.

### Lane A — land the splice (THE mandate; est. 1-3 laps)
`WainerBound.wainer_bound_of_pa_proves_goodstein` is currently `sorry`, blocked on ONE integration
snag (fully diagnosed in-file): the intended one-liner
`wainer_bound_witness gated_certificate_uniform Scirc_dom_pad master_conversion h` fails because
`gated_certificate_uniform` yields **`ReadoffValueGate.Gated`** while `wainer_bound_witness`'s `Hcert`
expects **`E1EmbeddingGrind.Gated`** — E1's forced duplicate (the wip modules couldn't import each
other). Now co-located → **de-duplicate**: make `E1EmbeddingGrind` import `ReadoffValueGate` and use
`ReadoffValueGate.Gated` (delete E1's copy; retype `wainer_bound_witness`'s `Hcert`), OR bridge the two
`Gated` defs under the binders. Watch for the SAME duplication on other shared defs across the three
modules. Then: real splice body → `#print axioms wainer_bound_of_pa_proves_goodstein` must be
`[propext, choice, Quot.sound]` → flip nodes 14/15 `debt "0-1" 95` → `clean "0" 100`.

### Lane B — the crown re-point (JUDGE-flavored; break a real cycle)
`Statement.peano_not_proves_goodstein` still routes Route-A (`goodstein_implies_consistency`). The
re-point `:= WainerRoute.peano_not_proves_goodstein_growth` (literally the identical proposition) is
blocked by an import cycle the ledger missed: **`WainerRoute` imports `Statement`**, so `Statement`
cannot import `WainerBound`. Break it — relocate the crown `peano_not_proves_goodstein` into a terminal
module downstream of `WainerBound` (re-export/rename to keep the audit surface), OR drop `WainerRoute`'s
`import GoodsteinPA.Statement` if it's only transitive. Then re-point, flip node 16 `debt`→`clean`,
confirm `#print axioms peano_not_proves_goodstein` = `[propext, choice, Quot.sound]`. **Statement's
headline TYPE is FROZEN — re-point the body only.**

### Lane C — sorry-prune (src 20 → 0; `lean-sorry src/` is the gate)
Accurate census (`lean-sorry src/`, this pass): **20** real sorries in 5 files.
- **5 in `E1EmbeddingGrind` (285, 728, 740, 1110, 4324)** — the disclosed W1/W2/axm/all/exs + retired
  `readoffTC_core`/`readoff_delta0_Zef2TC` leaves. OFF the witness cone (kernel-confirmed) → **prune**
  the dead scaffolding until E1 is sorry-free without breaking `wainer_bound_witness`'s cone.
- **12 in `Crux2Blueprint` + 1 `OperatorZeh:1925` + 1 `WainerLadder:45`** — the pre-existing 15 (minus
  the 2 above files' overlap). See the ⚠️ CORRECTED findings in §4 before touching these.
- **`WainerLadder:45` (`wainer_splice_Zef2`)** re-points to the now-landed bound (Lane A must finish first).
- **`DescentSemantic:582`** + the crux-2 KEEP frontier feed the OTHER girder
  (`goodstein_implies_consistency`) — out of the growth-discharge scope; close only if driving full src-0.

### FORBIDDEN
- **Do NOT trust the OLD ledger's Block-4 deletion proposals** — 2 are verified WRONG (§4). Re-derive
  every retirement against the compiler (`grep` for consumers + a real build), never delete on say-so.
- Do NOT touch the frozen statement TYPES (WainerBound's verbatim axiom type; Statement's headline).

### STOP condition
`lake build` green + `#print axioms peano_not_proves_goodstein` = `[propext, choice, Quot.sound]` +
`blueprint_audit` all-green + `lean-sorry src/` = 0 → stamp the SERIES-5 judge package → STOP.

## 4. ⚠️ Judge findings — the SERIES-4 ledger (`REBUILD-Z-SERIES-4-LEDGER.md`) is UNRELIABLE

Three spot-checks, three inaccuracies. Treat that ledger as claims, not ground truth:
1. **Sorry disclosure undercounts** — "E1 has exactly TWO sorryAx decls"; actually 5 live `sorry` sites
   (285/728/740/1110/4324) + disclosed leaves. Fine for the witness (cone kernel-clean), but a wholesale
   promotion drags them into trusted src — hence Lane C.
2. **"Group-2 red-cluster safe to RETIRE" is FALSE** — `zKValidF_iIndReduct_of_zInd` (`Crux2Blueprint:1688`),
   `ZDerivation_red_zK_crit` (`:1652`), `ZDerivation_red_zK_splice` (`:1635`), and `redSound` (`:1888`, via
   `redSoundGen`) are LIVE consumers. Deleting the 6 as proposed breaks the build. Group-2 ("dead") and
   Group-3 ("keep") are intertwined in the `redSoundGen`/`redSound` chain — retire the whole chain +
   downstream, or keep it; a compiler-checked call, not the ledger's per-decl list.
3. **Splice is not "zero adaptation"** — the Gated-duplication mismatch (Lane A) means the copy-not-compose
   splice needs a de-dup/bridge. Small, but real.

Supersedes the interim note and Block 5's "can execute from this ledger alone."

*Fire shape for SERIES-5: operator's call — running `--model opus --effort low` (Fable-low did well;
evaluating opus-low), review-every-4, max-laps, stop-when-done.* 🪷⚖️
