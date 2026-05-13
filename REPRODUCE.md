# srrg-lean — reproducibility

## Toolchain

File `lean-toolchain` pins Lean `v4.29.1` (matches `ugp-lean` / `ugp-physics-lean`).

## Checkout layout

Clone **siblings** on the same parent directory:

- `ugp-lean`
- `ugp-physics-lean`
- `srrg-lean` (this repo)

## Build

```bash
cd /path/to/srrg-lean
lake exe cache get
lake build
```

**Do not** remove the `lake exe cache get` step unless you intend to compile Mathlib locally (slow).

## CI

GitHub Actions (`.github/workflows/ci.yml`) runs the same two commands on `ubuntu-latest`.

## Paper / specs

- Public paper draft target: **P27** (`papers/27_SRRG` on `ugp-physics`).
- Internal formal specifications: EPIC_046 `MASTER_STATUS.md`; **SPEC_046_R3K, Y8L, Q2N, Z9M, H4P**; EPIC_047 `SPEC_047_SRL_SRRG_LEAN.md`.
