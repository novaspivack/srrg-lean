import Lake
open Lake DSL

/-! # srrg-lean — Self-Referential Renormalization Group (Lean 4)

Companion to P27 and EPIC_046 / EPIC_047. Phase 0 uses the same **path** pattern as
`ugp-physics-lean → ugp-lean`: resolve sibling checkouts:

  ugp-lean/          (transitive via ugp-physics-lean)
  ugp-physics-lean/
  srrg-lean/   (this repo)

CI and local dev: **always** run `lake exe cache get` before `lake build` so Mathlib
uses precompiled artifacts (no full Mathlib compile).
-/

package «srrg-lean» where

require «ugp-physics-lean» from "../ugp-physics-lean"
require «nems-lean» from "../nems-lean"

-- ── Blocked dependency: viable-continuation-lean ─────────────────────────────
-- Toolchain/Mathlib: viable-continuation-lean is already at leanprover/lean4:v4.29.0-rc6
-- and requires mathlib @ "v4.29.0-rc6", matching srrg-lean.  The remaining blocker is
-- that Lake sees a duplicate mathlib origin when resolving the transitive dependency
-- chain (ugp-physics-lean → mathlib git + viable-continuation-lean → mathlib git).
-- Until that Lake manifest conflict is resolved, this require stays commented out.
-- Correspondence remark: SrrgLean/Core/ViabilityFunctional.lean (SPEC_052_PRI §B1).
-- require «viable-continuation-lean» from "../viable-continuation-lean"

-- ── Blocked dependency: reflexive-closure-lean ───────────────────────────────
-- Path/origin conflict: reflexive-closure-lean requires nems-lean from a pinned git
-- commit ("https://github.com/novaspivack/nems-lean.git" @ "d1379b2d..."), while
-- srrg-lean requires nems-lean from the local path "../nems-lean".  Lake cannot
-- reconcile two different origins for the same package in a single workspace.
-- Toolchain of reflexive-closure-lean is already v4.29.0-rc6.
-- Fix: change reflexive-closure-lean/lakefile.lean to use
--   require «nems-lean» from "../nems-lean"
-- then re-run lake update there.  DO NOT change the toolchain of that repo.
-- Alpha theorem import is documented in SrrgLean/FixedPoints/Existence.lean (SPEC_052_PRI §B4).
-- require «reflexive-closure-lean» from "../reflexive-closure-lean"

@[default_target]
lean_lib «SrrgLean» where
  roots := #[`SrrgLean]
