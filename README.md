# srrg-lean

**Lean 4** library for the **Self-Referential Renormalization Group (SRRG)** and its
connection to the **Information Profit Threshold (IPT)** programme (P15 / GXT / P27).

This repo mirrors the layout of [`ugp-physics-lean`](https://github.com/novaspivack/ugp-physics-lean):
`SrrgLean/` sources, `paper/` notes, `scripts/`, top-level `lakefile.lean`, `REPRODUCE.md`.

## Internal specification IDs (companion archive `ugp-physics`)

Epic orchestration: **EPIC_046** → `MASTER_STATUS.md` (folder `EPIC_046_SRRG — Self-Referential Renormalization Group and IPT`).

| ID | Topic |
|----|--------|
| **SPEC_046_R3K** | GXT ↔ SRRG morphism (frozen v1.0) |
| **SPEC_046_Y8L** | IPT from SRRG FP — theorem [H1]–[H4] |
| **SPEC_046_Q2N** | β_SRRG sign / IR vs UV in η |
| **SPEC_046_Z9M** | CFT ε₃ₛ numerics (Python sandbox) |
| **SPEC_046_H4P** | Lean formalization targets (this repo, Phase 0) |

Full library architecture: **EPIC_047** → `SPEC_047_SRL_SRRG_LEAN.md`.

## Modules

| Module | Sorries | Summary |
|--------|---------|---------|
| `FixedPoints.EtaFlow` | 0 | β_η two-fixed-point structure; IR/UV sign analysis |
| `FixedPoints.H4Discharge` | 0 | h_psc_sc discharge attempt; proxy no-flat-directions |
| `FixedPoints.NoThirdFixedPoint` | 0 | β_η = 0 ↔ η = IPT ∨ η = 2 (no third zero) |
| `FixedPoints.BetaEtaQuadratic` | 0 | Vieta uniqueness: β_η = κ(η−IPT)(η−2) derived |
| `FixedPoints.PhysicalSubspace` | 0 | Landauer sustainability + IR-stability axioms |
| **`FixedPoints.VEVNoGo`** | **0** | **SRRG no-go: β_η with simple zeros prevents EW-scale DT** |
| `Constants.StrongCP` | 0 | θ_QCD = 0 from SRRG C_closure = 0 |
| `Constants.GaugeGroupSelection` | 0 | U(1) minimality + QCD rank from anomaly cancellation |
| `Constants.GenerationCount` | 0 | N_gen = 3 from Jarlskog + PSC closure |
| `Constants.BetaFunction` | 0 | Gauge-coupling proxy Hessian; η_proxy = 2 |
| `Constants.HiggsQuartic` | 0 | λ_H = m_H²/(2v²) structural recovery |
| `Constants.CosmologicalConstant` | 0 | Structural exclusion of Planck-scale Λ_vac |
| `Bridges.*` (5 modules) | 0 | NEMS/PSC → SRRG connection layer |
| `Connection.*` (4 modules) | 1† | IPT/H9/GoldenPhi/U1 bridges |

† One `sorry` in `IPTBridge` (hypotheses [H1][H2][H4]; h_psc_sc grade [A−]).

**Total: 33 imports, zero sorry in all owned modules except one disclosed axiom in IPTBridge.**

## Status

- **FixedPoints layer**: complete. β_η structure, no-third-zero, Vieta uniqueness, physical subspace axioms, and the new **VEVNoGo** dimensional-transmutation obstruction are all zero-sorry.
- **Constants layer**: complete. Six derived-constant modules, all zero-sorry.
- **Connection layer**: `H9Bridge`, `GoldenPhiBridge`, `UOneBridge` are zero-sorry. `IPTBridge` has one explicit `sorry` (h_psc_sc [H4]; grade [A−]).
- **Core modules** (`SrrgLean.Core.*`): not yet started; would replace the `sorry` bundle in `IPTBridge`.

## Layout expectation (sibling checkouts)

```
.../ugp-lean
.../ugp-physics-lean
.../srrg-lean   ← this repository
```

`lakefile.lean` uses `require «ugp-physics-lean» from "../ugp-physics-lean"` (same pattern as
`ugp-physics-lean` → `ugp-lean`).

## Build (**use Mathlib cache — do not compile Mathlib from source in CI**)

```bash
lake exe cache get
lake build
```

Lean toolchain is pinned to **`v4.29.1`** to stay aligned with `ugp-lean` / Mathlib `v4.29.1`.

## License

See `LICENSE`. Research prose under `paper/` may use a separate CC notice when added.

## Author

Nova Spivack.
