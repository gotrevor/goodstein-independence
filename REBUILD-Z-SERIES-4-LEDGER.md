# REBUILD-Z — SERIES-4 LEDGER (append-only; block per lane-advance)

Order in force: `E-2026-07-03-JUDGE-series3-validation.md` §4 (the SERIES-4 FINAL-DISCHARGE order).
Baseline for judge diffs: `ab41710` (lap-210 baton; Lane S landed across laps 209–210).

---

## Block 1 — LANE S COMPLETE (S-1…S-5): `wainer_bound_witness` GREEN at the axiom's VERBATIM type

**Laps**: 209–210 · **Files**: `wip/HardyMajorization.lean`, `wip/ReadoffValueGate.lean`,
`wip/E1EmbeddingGrind.lean` (src UNTOUCHED; the swap is judge-gated) · **Build**: 🟢 all three
modules re-compiled clean via `lake env lean` this lap (lap 211, 2026-07-03).

### The summit statement (S-5, `649b1e4`)

`GoodsteinPA.E1EmbeddingGrind.wainer_bound_witness` (wip/E1EmbeddingGrind.lean:4985) concludes,
from hypotheses `Hcert`/`HSdom`/`Hconv` (see pairing below) and `h : 𝗣𝗔 ⊢ ↑goodsteinSentence`:

```lean
∃ o : ONote, o.NF ∧
  GoodsteinPA.WainerRoute.EventuallyLE GoodsteinPA.Dom.goodsteinLength
    (fun n => fastGrowing o n)
```

— the VERBATIM type of the sole route axiom `wainer_bound_of_pa_proves_goodstein`
(`src/GoodsteinPA/WainerRoute.lean:119-121`), copied not composed (namespace-qualified since wip
sits outside the `GoodsteinPA.WainerRoute` namespace; `EventuallyLE`/`goodsteinLength`/
`fastGrowing`/`goodsteinSentence` are the same src decls).

### Hypothesis pairing (the three-module seam)

The three wip modules cannot import each other (standalone `lake env lean` files), so S-5 takes
the sibling results as hypotheses whose statements are the siblings' VERBATIM statements:

| S-5 hypothesis | = verbatim statement of | location | delta |
|---|---|---|---|
| `Hcert` | `ReadoffValueGate.gated_certificate_uniform` | RVG:590 | none (binder-for-binder) |
| `HSdom` | `HardyMajorization.Scirc_dom_pad` | HM:1301 | none (`oadd (ofNat 2) 1 0` spelled identically; `Wpow`-free) |
| `Hconv` | `HardyMajorization.master_conversion` | HM:1344 | none (implicit-binder order identical) |

Judge splice = concatenate/import the three modules in src and apply the three theorems to the
witness's hypotheses — zero statement adaptation required.

### `#print axioms` transcript (lap 211 re-verification, real compiler output)

```
'GoodsteinPA.E1EmbeddingGrind.wainer_bound_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.E1EmbeddingGrind.readoff_value_goodstein'' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.E1EmbeddingGrind.readoff_value_pipeline'' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.E1EmbeddingGrind.embedding_Zef2TC_V3_linearK' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.ReadoffValueGate.gated_certificate_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.ReadoffValueGate.gvb_le_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.ReadoffValueGate.gvb_substs_q_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.Scirc_dom_pad' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.master_conversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.ewIterTower_dom_pad' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.ewIter_dom_pad_levelcap' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.hardy_pad_lt_fastGrowing_osucc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Disclosure**: `wip/E1EmbeddingGrind.lean` contains exactly TWO `sorryAx`-bearing decls —
`readoffTC_core` and `readoff_delta0_Zef2TC` — the SUPERSEDED pre-value read-off (the lap-205
`allω` trap, route (c) replaced it with `readoffVTC_core`/`readoff_value_*`, lap 207). Neither is
in `wainer_bound_witness`'s dependency cone (its transcript above is sorryAx-free, which is the
kernel's own certification of that). Judge may retire both at splice time. RVG and HM transcripts
are sorryAx-free in full.

### Chain of custody (commit per stage)

- S-1 `ewIterTower_dom_pad` — `564b51f`
- S-2 `gvb_le_iter` `15f6617` · `hardy_Wpow_iter_dom_pad`/`dom_pad_max`/`Sstar_dom_pad` `b22dbc3`
- S-3 `ewIter_dom_pad_levelcap`+`two_pow_le_hardy_Wpow2` `b22d33f` · primed pipeline
  (`readoff_value_pipeline'`/`embedding_Zef2TC_V3_linearK`/`readoff_value_goodstein'`) `d5f044a`
  · `dom_pad_comp` `4511346` · `gated_certificate_uniform` `5370cf0` ·
  `master_conversion`+`Scirc_dom_pad`+`two_mul_add_le_hardy_omega_sq` `64902f1`
- S-4 `hardy_pad_lt_fastGrowing_osucc`+`dom_pad_eventuallyLE` — `19065e7`
- S-5 `wainer_bound_witness` — `649b1e4`

**Lane S status: COMPLETE.** Remaining for the SERIES-4 pass: Lane B (blocks below) + judge
executes the src splice and axiom→theorem swap.

---
