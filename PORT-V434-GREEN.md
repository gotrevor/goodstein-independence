# PORT-V434 — GREEN

Branch `v4.34`, commit `20a7b8c` (`v4.34 port: lake build + AxiomCheck green`), local only.
Toolchain `leanprover/lean4:v4.34.0`; Foundation `bde9bc28`, mathlib `5ed29652` (v4.34.0),
manifest and lakefiles exactly as `lean-bump` left them (no `lake update`, no `lake exe cache get`).

Every statement pinned in `scripts/AxiomCheck.lean` is unchanged, as is every expected axiom list.
No `axiom` was added anywhere, and the whole repo is `sorry`-free (`lake build` reports no
`declaration uses 'sorry'`).

## `lake build` (whole repo)

```
$ lake build
...
Build completed successfully (1548 jobs).
```

## `lake env lean scripts/AxiomCheck.lean`

```
$ lake env lean scripts/AxiomCheck.lean
$ echo $?
0
```

Silent — all `#print axioms` / `#guard_msgs` pins matched.

The per-pattern migration log (24 distinct kinds of breakage: symptom → fix → example site) is at
the end of `PORT-V434.md`.  The two entries worth reading before the next bump are #15 (PA⁻'s
`addEqOfLt` became *bounded*, so its `Zef2TC` derivation genuinely changed shape) and #17/#19
(Lean 4.34's stricter `rw` transparency check and mathlib's `@[no_expose]` on
`Nat.Subtype.denumerable`, both of which needed real proof work rather than a rename).
