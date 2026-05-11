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

@[default_target]
lean_lib «SrrgLean» where
  roots := #[`SrrgLean]
