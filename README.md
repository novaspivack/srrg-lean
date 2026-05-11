# srrg-lean

**Lean 4** library for the **Self-Referential Renormalization Group (SRRG)** and its
connection to the **Information Profit Threshold (IPT)** programme (P15 / GXT / P27).

This repo mirrors the layout of [`ugp-physics-lean`](https://github.com/novaspivack/ugp-physics-lean):
`SrrgLean/` sources, `paper/` notes, `scripts/`, top-level `lakefile.lean`, `REPRODUCE.md`.

## Status

- **Phase 0 (bootstrap):** `SrrgLean.Connection.IPTBridge` states the main EPIC_046
  bridge target with **one** explicit `sorry` (hypotheses [H1][H2][H4]).
  **`H9Bridge`** certifies the Landauer fixed-point identity against `UgpLean.IPT.IPT_threshold`
  at **zero sorry** ([H3]).
  **GoldenPhiBridge** and **UOneBridge** are **zero-sorry** re-exports (A1 / circle exp).
- Full architecture is specified in **`SPEC_047_SRL`** (EPIC_047) on the companion
  research archive; staged physics obligations are in **SPEC_046_R3K … SPEC_046_H4P**.

Internal cross-links (not for public README export): `ugp-physics` →
`specs/IN-PROCESS/EPIC_046_SRRG — …/MASTER_STATUS.md`.

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

Lean toolchain is pinned to **`v4.29.0-rc6`** to stay aligned with `ugp-lean` / Mathlib `v4.29.0-rc6`.

## License

See `LICENSE`. Research prose under `paper/` may use a separate CC notice when added.

## Author

Nova Spivack.
