#!/usr/bin/env -S uv run --quiet python3
"""Sync blueprint statuses + annotate the dep graph, from the Lean ledger.

Single source of truth = the `@[goodstein_blueprint <order> <category>
"<stage>" "<laps>" <confidence> ...]` attribute sites in src/**/*.lean.
This script transports them into the blueprint:

  * STATUS SYNC (anti-drift): each ledger-matched node's `\\leanok`/`\\notready`
    tag in blueprint/src/content.tex is REWRITTEN from the ledger category
    (clean/trusted -> \\leanok, debt/broken -> \\notready). Hand-edited statuses
    on covered nodes get overwritten -- per the blueprint doctrine, status is
    machine-derived, never hand-kept. (Nodes without an attribute site are left
    alone: they are still hand-claims until they get a ledger entry.)
  * each matched node's label in the embedded DOT gains a second line,
    e.g.  pathBOperatorCutElimination
          ~5-10 laps | 65%
  * each matched node's click-modal gains the same one-line estimate

Matching: a tex node (\\label{...} + \\lean{...} in blueprint/src/content.tex)
is matched to an attribute site when the attribute's stage-declaration ident
equals the last component of any \\lean{} name on the node, modulo a
trailing `_stage`/`_capstone` (the ledger names some sites by capstone
where the tex binds the stage theorem).

A tex node WITHOUT a \\lean{} binding is matched by NAME instead: an attribute
whose stage string equals the node's label suffix (e.g. ledger stage
"pa_not_proves_goodstein" -> tex thm:pa_not_proves_goodstein, the crown
re-point row). A name-claimed attribute is withdrawn from decl matching, so a
\\lean-alias node binding the same decl (thm:routeA_headline binds
peano_not_proves_goodstein) keeps its own hand status + banked styling.

The numbers are transported verbatim (including `0 laps | 100%` on ledger-clean
nodes) -- this script never adjudicates status, it only surfaces the ledger.

Idempotent: re-running skips nodes already annotated. A plain `leanblueprint
web` rebuild WIPES the annotations, so the one-command refresh is:

    blueprint/annotate_depgraph.py --web     # rebuild web/, then annotate
"""

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def norm(decl: str) -> str:
    """last component, modulo the _stage/_capstone naming split"""
    return re.sub(r"_(stage|capstone)$", "", decl.split(".")[-1])
TEX = REPO / "blueprint" / "src" / "content.tex"
HTML = REPO / "blueprint" / "web" / "dep_graph_document.html"

# attribute [goodstein_blueprint <order> <category> "<stage>" "<laps>" <conf> <stageDecl> ...
ATTR_RE = re.compile(
    r'attribute\s*\[goodstein_blueprint\s+(\d+)\s+(\w+)\s+"([^"]*)"\s+"([^"]*)"\s+(\d+)\s+([\w.]+)'
)

NODE_RE = re.compile(
    r'\\begin\{(definition|theorem|lemma)\}\s*\\label\{([^}]+)\}(.*?)\\end\{\1\}',
    re.S,
)


def lean_annotations() -> list:
    """[(stage string, stage-decl last component, {category, laps, confidence})]"""
    rows = []
    for f in sorted((REPO / "src").rglob("*.lean")):
        for m in ATTR_RE.finditer(f.read_text()):
            _order, cat, stage, laps, conf, decl = m.groups()
            rows.append((stage, norm(decl), {
                "category": cat,
                "laps": laps,
                "confidence": int(conf),
            }))
    return rows


def tex_node_decls() -> dict:
    """tex node id -> [last components of its \\lean{} names] ([] = no binding)"""
    nodes = {}
    for m in NODE_RE.finditer(TEX.read_text()):
        _env, label, body = m.groups()
        lm = re.search(r'\\lean\{([^}]*)\}', body)
        nodes[label] = [norm(d.strip()) for d in lm.group(1).split(",")] if lm else []
    return nodes


def estimate_text(info: dict) -> str:
    prefix = "" if info["laps"] == "0" else "~"
    return f"{prefix}{info['laps']} laps | {info['confidence']}%"


STATUS_FOR = {"clean": "\\leanok", "trusted": "\\leanok",
              "debt": "\\notready", "broken": "\\notready"}

# Route-A read-off nodes are BANKED per DIRECTION.md (2026-07-01 route pivot):
# grey/dashed "abandoned trail" styling so the map doesn't show two live routes
# to the summit. (The pathB capstone chain was originally kept live as "the
# someK substrate of the W0-W7 masterplan" — that framing died with the Zᵉ
# fork; see SUPERSEDED below.) This transports an operator decision, not a
# kernel fact.
#
# EDGES touching a banked node recede with it (dotted, dim, thin). Rationale:
# leanblueprint's \uses is conjunctive-only — the dep graph has NO native
# "one-of-several-paths" (OR) notation, and the summit is a disjunction of the
# two route headlines. The prose on thm:summit carries the OR; this overlay
# makes the banked alternative's edges read as deprioritized, not required.
BANKED = {"thm:routeA_headline", "thm:crux2_axiom"}
BANKED_EDGE_STYLE = 'style=dotted, color="#4a5056", penwidth=0.7, arrowsize=0.6]'

# The pathB capstone chain is SUPERSEDED-IN-SUBSTRATE (2026-07-02, Zᵉ fork):
# its capstones 2–8 are stated over the (k,d)/someK calculus that SPIKE-W4B
# kernel-killed, and its only consumer is the banked crux2_axiom. The
# decomposition SHAPE re-keys onto Zeh at the embedding phase (it will then
# feed wainer_axiom); until that restatement exists, the chain's EDGES fade
# like the banked trail. Node colors stay kernel-honest (ledger-audited) —
# only the edges transport this operator decision.
SUPERSEDED = {
    "thm:pathBGoodsteinSentenceShape", "thm:pathBPeanoMinusAxiomLeaves",
    "thm:pathBInductionAxiomShell", "thm:pathBClosedWitnessBudgets",
    "thm:pathBSomeKStructuralEmbedding", "thm:pathBOperatorCutElimination",
    "thm:pathBSubformulaProjection", "thm:pathBGoodsteinFragmentExtraction",
    "thm:pathBTerminalRouteBridge",
}
# NOT-REQUIRED nodes: conceptual gaps (hardy/ti_schema/wainer_class) + aspirational
# monument (infinitary_tower/gentzen_conpa/two_sided) that the summit does NOT need
# — the live orange work realizes or routes around them. These are NON-BLOCKING,
# which is RADICALLY different from ABANDONED (Route A, hit the M2 wall — that stays
# grey). leanblueprint has no state for "not required", and its orange means "not
# ready, needs work" (misreads them as blocking); green would mean "formalized"
# (falsely claims the unbuilt monument is done). So they get their own TEAL border,
# dashed — "not in the way", without claiming done or dead. NODE_NOTE says why each.
NOT_REQUIRED_COLOR = "#17A2B8"  # teal — distinct from green/orange/grey/blue
NOT_REQUIRED = {
    "def:hardy", "def:ti_schema", "def:wainer_class",
    "thm:infinitary_tower", "thm:gentzen_conpa", "thm:two_sided",
}

FADED = BANKED | SUPERSEDED | NOT_REQUIRED

# Node-level PLANNING notes — the estimates the Lean ledger structurally CANNOT
# carry, so they live here instead (hand-authored, sourced from
# MASTERPLAN-2026-07-01-ZERO-AXIOMS.md; NOT audit-backed like the ledger rows).
# Two reasons a node lands here rather than in the ledger:
#   * a sorry-bearing decl (e.g. cutElimPass_Zf, the lap-5 gate) — tagging it
#     would make `blueprint_audit` compute `broken` and turn CI red;
#   * a prose/aspirational node has no Lean decl at all to attach an attribute to.
# Colors stay whatever content.tex declares; this only adds one label line.
NODE_NOTE = {
    # Live Route-B remaining work — real lap costs (rebased 2026-07-02, trap-8
    # judge pass + WAINER-LADDER-2026-07-02.md rung P: lap-7 E–W statement lap +
    # lap-8 judged port + the pass grind on Zef2).
    "thm:zeh_pass":                "~4-7 laps | 70%",    # rung P (E–W rebuild; sorry: pin-3 gate)
    "thm:zeh_readoff_delta0":      "~2-3 laps | 80%",    # rung D (Towsner-5.4 pattern; re-based per the ladder)
    # The rest of the wainer ladder (decl-less until the lap-8 port erects the
    # named pins + ledger rows; estimates = WAINER-LADDER-2026-07-02.md).
    "thm:zeh_rank_zero":           "~1 lap | 90%",       # rung R (plain induction over the pass)
    "thm:zeh_embedding":           "~8-20 laps | 65%",   # rung E (the long pole after P)
    "thm:wainer_splice":           "~2-4 laps | 75%",    # rung W (Hardy brackets banked lap 179)
    # thm:pa_not_proves_goodstein (the summit) now carries LEDGER row 16 — the
    # rung-C re-point (1 lap @ 95% once routeB_headline is clean, + W7 burndown).
    # It is NAME-matched above (decl-less tex node), so no hand note here.
    # OPEN GAPS — the general ordinal-analysis monument. These are NOT on the
    # treadmill's per-lap path: the live plan AXIOMATIZES the needed slice
    # (wainer_axiom) and discharges THAT via the Zᵉ substrate, rather than building
    # these. So no lap number — the markers condense each node's OWN blueprint
    # status (see its modal), which is the authoritative source, not a hand-guess.
    "def:hardy":                   "(gap: fn ported, growth theory absent)",
    "def:ti_schema":               "(gap: net-new in Lean)",
    "def:wainer_class":            "(deep gap: ordinal analysis of PA)",
    "thm:infinitary_tower":        "(crown monument: ~6-7k lines, multi-month)",
    "thm:gentzen_conpa":           "(shared monument engine)",
    "thm:two_sided":               "(crown: full ordinal analysis)",
    # Green node (Foundation Hauptsatz, imported + bound): note clarifies it's the
    # FINITARY template, not the infinitary monument, so green isn't misread.
    "thm:hauptsatz":               "(finitary template)",
}


def sync_tex_statuses(ann: dict) -> bool:
    """Rewrite each ledger-matched node's status tag in content.tex from the
    ledger category. Returns True if the file changed."""
    text = TEX.read_text()
    changes = []

    def fix(m):
        env, label, body = m.groups()
        lm = re.search(r'\\lean\{([^}]*)\}', body)
        if not lm:
            return m.group(0)
        info = next(
            (ann[d] for d in (norm(x.strip()) for x in lm.group(1).split(",")) if d in ann),
            None,
        )
        if info is None:
            return m.group(0)
        want = STATUS_FOR[info["category"]]
        if re.search(r'(?<!textbackslash )\\leanok\b' if want == "\\leanok"
                     else r'(?<!textbackslash )\\notready\b', body) and not re.search(
                     r'(?<!textbackslash )\\notready\b' if want == "\\leanok"
                     else r'(?<!textbackslash )\\leanok\b', body):
            return m.group(0)  # already exactly right
        # strip any existing status tag lines, then insert the wanted one
        # right after the \lean{} line (prose uses \textbackslash forms, safe)
        body2 = re.sub(r'[ \t]*(?<!textbackslash )\\(leanok|notready)\b[ \t]*\n?', '', body)
        body3 = re.sub(r'(\\lean\{[^}]*\}[ \t]*\n)',
                       lambda mm: mm.group(1) + "  " + want + "\n",
                       body2, count=1)
        changes.append(f"{label}: -> {want} (ledger: {info['category']})")
        return f"\\begin{{{env}}}\\label{{{label}}}{body3}\\end{{{env}}}"

    new = NODE_RE.sub(fix, text)
    if new != text:
        TEX.write_text(new)
    for c in changes:
        print("status sync:", c)
    return bool(changes)


def main() -> int:
    rows = lean_annotations()
    if not rows:
        print("no @[goodstein_blueprint] annotations found", file=sys.stderr)
        return 1

    nodes = tex_node_decls()
    # NAME-matching for decl-less tex nodes (see docstring). A name-claimed
    # attribute is withdrawn from decl matching so a \lean-alias node binding
    # the same decl keeps its own hand status/styling.
    stage_matched = {}
    for node in sorted(n for n, ds in nodes.items() if not ds):
        suffix = node.split(":", 1)[-1]
        info = next((i for (s, _d, i) in rows if s == suffix), None)
        if info is not None:
            stage_matched[node] = info
    claimed = {n.split(":", 1)[-1] for n in stage_matched}
    ann = {d: i for (s, d, i) in rows if s not in claimed}

    changed = sync_tex_statuses(ann)
    if "--web" in sys.argv:
        subprocess.run(["leanblueprint", "web"], cwd=REPO, check=True)
    elif changed:
        print("warn: content.tex statuses were re-synced from the ledger; "
              "re-run with --web to rebuild the site", file=sys.stderr)

    matched = {
        node: ann[d]
        for node, decls in nodes.items()
        for d in decls
        if d in ann
    }
    matched.update(stage_matched)

    html = HTML.read_text()
    changed = 0
    for node, info in sorted(matched.items()):
        suffix = node.split(":", 1)[-1]
        est = estimate_text(info)
        # DOT label (inside a JS template literal: file needs \\n so the JS
        # string carries \n, which Graphviz renders as a centered line break)
        old = f"label={suffix},"
        new = f'label="{suffix}\\\\n{est}",'
        if old in html:
            html = html.replace(old, new, 1)
            changed += 1
        elif f'label="{suffix}\\\\n' not in html:
            print(f"warn: no DOT label found for {node}", file=sys.stderr)
        # modal: prepend the estimate line to the node's LaTeX link
        anchor_re = re.compile(r'(<a class="latex_link" href="[^"]*#' + re.escape(node) + '">)')
        if f'data-estimate="{node}"' not in html:
            html = anchor_re.sub(
                f'<p class="node-estimate" data-estimate="{node}">Ledger estimate: {est} confidence</p>\n    \\1',
                html,
                count=1,
            )

    # Node-level planning notes (see NODE_NOTE above): estimates for nodes the
    # ledger can't reach (sorry-bearing or prose). Idempotent — skips a node whose
    # label already carries a second line.
    node_notes = 0
    for node, note in sorted(NODE_NOTE.items()):
        suffix = node.split(":", 1)[-1]
        old = f"label={suffix},"
        new = f'label="{suffix}\\\\n{note}",'
        if old in html:
            html = html.replace(old, new, 1)
            node_notes += 1
        elif f'label="{suffix}\\\\n' not in html:
            print(f"warn: no DOT label found for node-note {node}", file=sys.stderr)
        anchor_re = re.compile(r'(<a class="latex_link" href="[^"]*#' + re.escape(node) + '">)')
        if f'data-note="{node}"' not in html:
            html = anchor_re.sub(
                f'<p class="node-estimate" data-note="{node}">Plan note (not audit-backed): {note}</p>\n    \\1',
                html,
                count=1,
            )
    print(f"node-level planning notes: {node_notes} label(s)")

    # Summit at the TOP: rank flow bottom-to-top, so dependencies climb
    # shores -> foothills -> routes -> crown (matches the mountain metaphor).
    html = html.replace(
        "graph [bgcolor=transparent];",
        "graph [bgcolor=transparent,\trankdir=BT];",
        1,
    )

    # Banked-route styling (see BANKED above).
    for node in sorted(BANKED):
        suffix = node.split(":", 1)[-1]
        pat = re.compile(
            r'("' + re.escape(node) + r'"\s*\[)color=[^,]*,(\s*)label=' + re.escape(suffix) + r','
        )
        def _grey(m, s=suffix):
            return (m.group(1) + 'color="#8a9096",' + m.group(2)
                    + 'label="' + s + '\\\\n(banked)",' + m.group(2) + 'style=dashed,')
        html = pat.sub(_grey, html, count=1)

    # Not-required styling (see NOT_REQUIRED): recolor the orange border to teal +
    # dash it, preserving the NODE_NOTE label. Distinct from the grey ABANDONED
    # (Route A) nodes. Idempotent — an already-teal node has no orange to match.
    nr = 0
    for node in sorted(NOT_REQUIRED):
        pat = re.compile(r'("' + re.escape(node) + r'"\s*\[)color="#FFAA33",')
        html, n = pat.subn(
            lambda m: m.group(1) + f'color="{NOT_REQUIRED_COLOR}",\n\tstyle=dashed,',
            html, count=1)
        nr += n
    print(f"not-required (teal): {nr} node(s)")

    # Banked/superseded EDGE styling (see the BANKED/SUPERSEDED comments):
    # every edge with a faded endpoint recedes. Idempotent — already-faded
    # edges no longer match the stock `style=dashed]` tail.
    edge_pat = re.compile(r'("(?P<tail>[^"]+)" -> "(?P<head>[^"]+)"\s*\[)style=dashed\]')
    def _fade(m):
        if m.group("tail") in FADED or m.group("head") in FADED:
            return m.group(1) + BANKED_EDGE_STYLE
        return m.group(0)
    html, _ = edge_pat.subn(_fade, html)
    faded = len(re.findall(re.escape(BANKED_EDGE_STYLE), html))
    print(f"banked/superseded-edge fade: {faded} edge(s) deprioritized")

    # Legend: leanblueprint's legend only documents its own states, so add the two
    # non-standard colors this script introduces. Anchored after the last stock
    # entry; idempotent.
    legend_anchor = "<dt>Dark green border</dt><dd>this is in Mathlib</dd>"
    legend_extra = (
        "\n      <dt>Teal border</dt><dd>not required for the summit — a conceptual "
        "gap or aspirational monument the live proof routes around (real math, but nothing "
        "blocks on it)</dd>"
        "\n      <dt>Grey border, dashed</dt><dd>abandoned / parked — a path that hit "
        "a wall (e.g. Route A), kept for provenance</dd>"
    )
    if legend_anchor in html and "Teal border" not in html:
        html = html.replace(legend_anchor, legend_anchor + legend_extra, 1)

    HTML.write_text(html)
    print(f"annotated {changed} DOT labels / {len(matched)} matched nodes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
