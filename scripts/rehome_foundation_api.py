#!/usr/bin/env -S uv run --quiet python3
"""Deterministic rewrite: point goodstein's proof internals at the `GoodsteinPA.Compat`
anti-corruption shim instead of Foundation's churny semantics API.

Upstream `FormalizedFormalLogic/Foundation` moved `Structure` from an explicit argument to an
instance argument in `Semiformula.Eval` / `Semiterm.val`, and removed `Semiformula.Evalm`,
`Semiterm.valm`, and the arity-specialised `eval_rel₀/₁/₂` (+ `nrel`) simp lemmas. `Compat.lean`
re-provides all of these under stable names hung off the current upstream API. This script rewrites
every call site to the Compat name and ensures the file imports the shim.

Only the REMOVED / SIGNATURE-CHANGED names are rewritten; the general lemmas upstream kept
(`eval_rel`, `eval_substs`, `eval_all`, …) and the `⊧ₘ*` notation are left as-is — the notation is
restored globally by importing Compat, and the general lemmas fire through the reducible abbrevs.

Idempotent: re-running is a no-op. Dry-run by default; pass --apply to write.

    ./scripts/rehome_foundation_api.py            # show the diff summary
    ./scripts/rehome_foundation_api.py --apply    # perform the rewrite
"""
from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path

SRC = Path(__file__).resolve().parent.parent / "src" / "GoodsteinPA"
SHIM_MODULE = "GoodsteinPA.Compat"
SHIM_IMPORT = f"import {SHIM_MODULE}"
SHIM_FILE = "Compat.lean"

# Ordered (pattern, replacement) rules. Negative lookahead `(?![\w.])` keeps us from clobbering
# longer names that share a prefix (Eval vs Evalm/Evalf, val vs valm/val_func, and any `.field`
# access such as `Semiformula.Eval.of_eq`). Subscript-tagged lemmas carry their subscript through.
RULES: list[tuple[re.Pattern[str], str]] = [
    # removed arity-specialised rel/nrel simp lemmas -> Compat re-proofs (keep the subscript)
    (re.compile(r"Semiformula\.eval_rel([₀₁₂])"), rf"{SHIM_MODULE}.eval_rel\1"),
    (re.compile(r"Semiformula\.eval_nrel([₀₁₂])"), rf"{SHIM_MODULE}.eval_nrel\1"),
    # removed model-variant evaluators (M explicit) -> Compat abbrevs
    (re.compile(r"Semiformula\.Evalm(?![\w.])"), f"{SHIM_MODULE}.gEvalm"),
    (re.compile(r"Semiterm\.valm(?![\w.])"), f"{SHIM_MODULE}.gValm"),
    # structure explicit -> instance: wrap in Compat abbrevs with the old (explicit) signature
    (re.compile(r"Semiformula\.Eval(?![\w.])"), f"{SHIM_MODULE}.gEval"),
    (re.compile(r"Semiterm\.val(?![\w.])"), f"{SHIM_MODULE}.gVal"),
]

# A file needs the shim import iff the FINAL text references anything Compat provides: a Compat
# name (post-rewrite), the ⊧ₘ* notation, or a restored formula alias. Checked on the rewritten
# text, so it must look for what the text ends up containing — not the pre-rewrite trigger names.
NEEDS_IMPORT = re.compile(
    re.escape(SHIM_MODULE) + r"|⊧ₘ|SyntacticSemiformula|SyntacticFormula"
)

# Both spellings of the shim import; a `module` file requires the `public import` form.
_IMPORT_LINES = {"import " + SHIM_MODULE, "public import " + SHIM_MODULE}


def ensure_import(text: str) -> str:
    """Idempotently place the shim import in the right spot. Self-correcting: strips any existing
    (possibly mis-placed) shim-import line first, then reinserts after the last import — using
    `public import` and anchoring under the `module` header for Lean module-system files."""
    lines = [ln for ln in text.splitlines(keepends=True) if ln.rstrip("\n") not in _IMPORT_LINES]
    is_module = any(ln.rstrip("\n") == "module" for ln in lines)
    keyword = "public import " if is_module else "import "
    imp = keyword + SHIM_MODULE + "\n"

    if is_module:
        anchor = max((i for i, ln in enumerate(lines) if ln.startswith("public import ")),
                     default=None)
        if anchor is None:
            anchor = next((i for i, ln in enumerate(lines) if ln.rstrip("\n") == "module"), None)
    else:
        anchor = max((i for i, ln in enumerate(lines) if ln.startswith("import ")), default=None)

    if anchor is None:
        return imp + "".join(lines)
    lines.insert(anchor + 1, imp)
    return "".join(lines)


# Upstream changed the simp normal form of rewritten relation vectors from `fun i => f (v i)` to
# `f ∘ v`. Any simp/simpa bracket that drives a rel/nrel eval-or-rewrite lemma now leaves a `∘`
# that downstream steps (stated with `fun i =>`) can't match, so we append `Function.comp_def`
# (`f ∘ g = fun x => f (g x)`) to renormalize. Idempotent (skips brackets that already have it).
_COMP_TRIGGER = re.compile(r"Semiformula\.(eval_rel|eval_nrel|rew_rel|rew_nrel)")
# `simp`/`simpa`/`simp_all`/`dsimp` (optionally `only`) followed by a lemma bracket.
_SIMP_CALL = re.compile(r"(?<![\w.])(simp(?:a|_all)?|dsimp)((?: only)?\s*)\[([^\[\]]*)\]")
# `rw`/`rewrite`/`erw` (optionally `only`) followed by a lemma bracket.
_RW_CALL = re.compile(r"(?<![\w.])(rw|rewrite|erw)((?: only)?\s*)\[([^\[\]]*)\]")


def _add_comp(m: re.Match[str]) -> str:
    head, gap, inner = m.groups()
    if _COMP_TRIGGER.search(inner) and "Function.comp_def" not in inner:
        inner = inner + ", Function.comp_def"
    return f"{head}{gap}[{inner}]"


def _strip_comp(m: re.Match[str]) -> str:
    # `rw` fails when a lemma's pattern is absent, so never carry comp_def into a rewrite bracket.
    head, gap, inner = m.groups()
    inner = re.sub(r"\s*,\s*Function\.comp_def|Function\.comp_def\s*,\s*", "", inner)
    return f"{head}{gap}[{inner}]"


def rewrite(text: str) -> tuple[str, dict[str, int]]:
    counts: dict[str, int] = {}
    for pat, repl in RULES:
        text, n = pat.subn(repl, text)
        if n:
            counts[pat.pattern] = n
    before = text.count("Function.comp_def")
    text = _SIMP_CALL.sub(_add_comp, text)   # renormalize `∘` inside simp-family calls
    text = _RW_CALL.sub(_strip_comp, text)   # ...but never inside `rw` (fails if pattern absent)
    delta = text.count("Function.comp_def") - before
    if delta:
        counts["±Function.comp_def"] = delta
    return text, counts


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--apply", action="store_true", help="write changes (default: dry run)")
    args = ap.parse_args()

    total_sites = 0
    total_files = 0
    imports_added = 0
    for path in sorted(SRC.glob("*.lean")):
        if path.name == SHIM_FILE:
            continue
        orig = path.read_text()
        # Lean `module` files can't import the non-module shim; they use upstream spelling
        # directly and are maintained by hand (see FvSubst.lean). Skip them entirely.
        if any(ln.rstrip("\n") == "module" for ln in orig.splitlines()):
            continue
        new, counts = rewrite(orig)
        needs = bool(NEEDS_IMPORT.search(new))
        if needs:
            after = ensure_import(new)
            if after != new:
                imports_added += 1
            new = after
        if new == orig:
            continue
        total_files += 1
        n = sum(counts.values())
        total_sites += n
        rule_summary = ", ".join(f"{k.split(chr(92))[0][:22]}…={v}" for k, v in counts.items())
        print(f"{'WROTE' if args.apply else 'would rewrite'} {path.name}: {n} sites  [{rule_summary}]")
        if args.apply:
            path.write_text(new)

    print(f"\n{total_files} files, {total_sites} call sites, {imports_added} imports added"
          f"{' (dry run — pass --apply)' if not args.apply else ''}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
