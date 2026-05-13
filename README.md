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

## Status

- **Phase 0 (bootstrap):** `SrrgLean.Connection.IPTBridge` states the main EPIC_046
  bridge target with **one** explicit `sorry` (hypotheses [H1][H2][H4]; see **SPEC_046_Y8L** §7).
  **`H9Bridge`** certifies the Landauer fixed-point identity against `UgpLean.IPT.IPT_threshold`
  at **zero sorry** (**[H3]**).
  **GoldenPhiBridge** and **UOneBridge** are **zero-sorry** re-exports (A1 / circle exp).
- EPIC_047 **Core** modules (`SrrgLean.Core.*`) are **not** started here yet; they replace the `True`/`sorry` bundle in `IPTBridge`.

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
