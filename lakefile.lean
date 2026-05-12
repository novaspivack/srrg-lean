import Lake
open Lake DSL

/-! # srrg-lean — Self-Referential Renormalization Group (Lean 4)

Companion to P27 and EPIC_046 / EPIC_047.

## Dependency strategy

- `ugp-physics-lean` and `ugp-lean` (transitive): **local path** — these repos have
  locally-developed modules not yet pushed to GitHub that srrg-lean imports.
- `nems-lean`: **git-pinned** — switching from local-path to git URL is the minimal
  change that resolves the origin conflict with `reflexive-closure-lean`, which also
  requires nems-lean from the same git URL.
- `reflexive-closure-lean`, `viable-continuation-lean`: **git-pinned** — previously
  blocked; now unblocked because all nems-lean consumers share the same git origin.
- `mathlib`: **explicit git pin** so the root's v4.29.0-rc6 constraint overrides
  the v4.29.0-rc3 that viable-continuation-lean's committed manifest would otherwise
  pull in.

CI and local dev: **always** run `lake exe cache get` before `lake build` so Mathlib
uses precompiled artifacts (no full Mathlib compile).
-/

package «srrg-lean» where

-- nems-lean: git dep (same URL as reflexive-closure-lean's requirement) eliminates
-- the path-vs-git origin conflict that previously blocked reflexive-closure-lean.
require «nems-lean» from git
  "https://github.com/novaspivack/nems-lean.git" @ "5b991736e703c5debe6c88b54269890fb573f93f"

-- ugp-physics-lean (and ugp-lean transitively): local path — locally-developed
-- modules not yet pushed to GitHub.
require «ugp-physics-lean» from "../ugp-physics-lean"

require «reflexive-closure-lean» from git
  "https://github.com/novaspivack/reflexive-closure-lean.git" @ "d88025571d71bf8faaac61581ef8a944de38fa44"

require «viable-continuation-lean» from git
  "https://github.com/novaspivack/viable-continuation-lean.git" @ "b83fe969cd4148e20cf49d9b38ba6e57f4a80085"

-- Explicit mathlib pin so the root's v4.29.0-rc6 constraint wins over the
-- v4.29.0-rc3 that viable-continuation-lean's committed manifest otherwise pulls in.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

@[default_target]
lean_lib «SrrgLean» where
  roots := #[`SrrgLean]
