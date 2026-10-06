# Goodstein independence over PA

[![CI](https://github.com/FormalizedFormalLogic/goodstein-independence/actions/workflows/ci.yml/badge.svg)](https://github.com/FormalizedFormalLogic/goodstein-independence/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/github/license/FormalizedFormalLogic/goodstein-independence)](LICENSE)

**Experimental.** The proofs here are written by AI agents and are not reviewed line by line by
FFL; the statements are the part to read.  For arithmetic metamathematics developed with human
review of every pull request, see the sister project
[AlphaCentauri](https://github.com/FormalizedFormalLogic/AlphaCentauri).

Lean 4 formalizations of independence results over Peano Arithmetic, built on
[Foundation](https://github.com/FormalizedFormalLogic/Foundation).

## Headlines

| Result | Declaration |
| --- | --- |
| Goodstein's theorem is independent of PA (Kirby–Paris) | [`goodstein_independent`](GoodsteinPA/Statement.lean) |
| Wainer's bound: a $\Pi_2$ sentence PA proves has witnesses eventually below some $f_\alpha$, $\alpha < \varepsilon_0$ | [`pa_provable_pi2_eventually_witnessed_below_fastGrowing`](GoodsteinPA/WainerGeneral.lean) |
| PA does not prove that the hydra battle terminates (Kirby–Paris) | [`pa_not_proves_hydra`](GoodsteinPA/HydraEscape.lean) |
| PA does not prove the Paris–Harrington principle | [`pa_not_proves_ph`](GoodsteinPA/PH/Main.lean) |
| PA does not prove transfinite induction along Kreisel's $\Delta_1$ well-ordering of type $\omega$ | [`pa_not_proves_TI_kreisel`](GoodsteinPA/Kreisel/Statement.lean) |

## Import Graph

![Import Graph](https://formalizedformallogic.github.io/goodstein-independence/import_graph.png)

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
