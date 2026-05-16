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

## VEVProof — EW Vacuum PSC Entropy Derivation

Build the VEVProof modules:

```bash
cd srrg-lean
lake exe cache get
lake build SrrgLean.VEVProof
```

**Modules** (all zero sorry):

| Module | File | Key theorem | Description |
|--------|------|-------------|-------------|
| `SrrgLean.VEVProof.GoldstoneEntropyCorrection` | `VEVProof/GoldstoneEntropyCorrection.lean` | `goldstone_volume_correction_per_generation` | Proves φ^(1/N_gen) volume correction from SRRG 1/φ eigenvalue + PSCEntropyDuality |
| `SrrgLean.VEVProof.PSCEntropyDuality` | `VEVProof/PSCEntropyDuality.lean` | `psc_entropy_after_contraction` | PSC Entropy-Contraction Duality theorem |
| `SrrgLean.VEVProof.EWGoldstoneManifold` | `VEVProof/EWGoldstoneManifold.lean` | `ew_vacuum_manifold_uniqueness` | EW vacuum manifold = S³, Vol = 2π², 3 Goldstone bosons |
| `SrrgLean.VEVProof.EWVacuumBridge` | `VEVProof/EWVacuumBridge.lean` | `srrg_physical_fp_implies_ew_vacuum_manifold` | Bridge from PhysicalSubspace U(1) minimality to S³ Goldstone manifold |

**Result:** v_PSC = 246.16 GeV (−0.024% from v_PDG = 246.22 GeV), grade [A−].

**Null-discipline:** 0.35% saturation over 288 structural candidates (structural, not coincidental;
artifact `null_discipline_vev_formula.json` in `ugp-physics/papers/01_SM/canonical_run/`).

**Open axioms** (grade [A−] not yet [A_Lean]):
- `psc_entropy_contraction_duality` — general PSC/SRRG duality (est. 2–4 months to prove from first principles)
- `srrg_s3_entropy_increase` — S³-specific consequence (follows from general duality)

---

## Paper / specs

- Public paper draft target: **P27** (`papers/27_SRRG` on `ugp-physics`).
- Internal formal specifications: EPIC_046 `MASTER_STATUS.md`; **SPEC_046_R3K, Y8L, Q2N, Z9M, H4P**; EPIC_047 `SPEC_047_SRL_SRRG_LEAN.md`.
