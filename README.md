# srrg-lean

**Lean 4** library for the **Self-Referential Renormalization Group (SRRG)** and its
connection to the **Information Profit Threshold (IPT)** programme (P15 / GXT / P27).

This repo mirrors the layout of [`ugp-physics-lean`](https://github.com/novaspivack/ugp-physics-lean):
`SrrgLean/` sources, `paper/` notes, `scripts/`, top-level `lakefile.lean`, `REPRODUCE.md`.

## Research program

This library is part of the UGP Physics research program by [Nova Spivack](https://www.novaspivack.com/).

| Link | Description |
|---|---|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [UGP Physics programme](https://www.novaspivack.com/research/physics-program) | The UGP Physics research programme |
| [Complete GTE Framework](https://doi.org/10.5281/zenodo.20560550) | Paper 48 — the synthesis monograph (SRRG result: EW VEV = 246.16 GeV) |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.20644340) | Citable DOI hub for the UGP Physics program |

---

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
| `Bridges.*` (6 modules) | 0 | NEMS/PSC → SRRG connection layer |
| `Connection.*` (4 modules) | 0 | IPT/H9/GoldenPhi/U1 bridges |
| `VEVProof.GoldstoneEntropyCorrection` | 0 | φ^(1/N_gen) SRRG correction to S³ Goldstone volume |
| `VEVProof.PSCEntropyDuality` | 0 | PSC Entropy-Contraction Duality — core of EW VEV derivation |
| `VEVProof.EWGoldstoneManifold` | 0 | EW Goldstone manifold S³: 3 bosons, Vol = 2π², O1 discharge |
| `VEVProof.EWVacuumBridge` | 0 | Bridge: PhysicalSubspace U(1) minimality → S³ Goldstone manifold ([A−]) |

`IPTBridge` is zero-sorry: the [H1][H2][H4] content enters as the explicit PSC self-consistency hypothesis `h_psc_sc` in its theorem signatures (chain grade [A−]).

**Total: 40 imports, zero sorry in all owned modules. Four disclosed physical axioms ([B]) remain in the FixedPoints layer (`PhysicalSubspace`, `BetaEtaQuadratic`).**

## Status

- **FixedPoints layer**: complete. β_η structure, no-third-zero, Vieta uniqueness, physical subspace axioms, and the new **VEVNoGo** dimensional-transmutation obstruction are all zero-sorry.
- **Constants layer**: complete. Six derived-constant modules, all zero-sorry.
- **Connection layer**: complete and zero-sorry (`H9Bridge`, `GoldenPhiBridge`, `UOneBridge`, `IPTBridge`). `IPTBridge` takes the PSC self-consistency condition `h_psc_sc` ([H4]) as an explicit hypothesis in its theorem signatures (chain grade [A−]).
- **VEVProof layer**: complete. Four modules zero-sorry: `GoldstoneEntropyCorrection` (algebraic chain |ψ|=1/φ → φ^(1/3) volume correction), `PSCEntropyDuality` (proves `psc_entropy_contraction_duality` and `srrg_s3_entropy_increase` as theorems), `EWGoldstoneManifold` (O1 discharge: 3 Goldstone bosons, Vol(S³)=2π²), `EWVacuumBridge` (connects PhysicalSubspace U(1) minimality to S³ Goldstone manifold). Zero open axioms in this layer: `psc_ew_entropy_maximization` is a proved theorem (zero sorry, zero new axioms), grade [A_Lean]. The PhysicalSubspace-conditional bridge in `EWVacuumBridge` is graded [A−] (conditional on the disclosed [B] physical axioms and stated EW-admissibility hypotheses). v_PSC = 246.16 GeV (−0.024% from v_PDG = 246.22 GeV).
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
