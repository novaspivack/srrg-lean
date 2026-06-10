import Lake
open Lake DSL

/-! # srrg-lean — Self-Referential Renormalization Group (Lean 4)

Companion to P27.

## Dependency strategy

- `ugp-physics-lean` and `ugp-lean` (transitive): **git-pinned** (switched from local
  path). `ugp-physics-lean` is currently private on GitHub.
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
  "https://github.com/novaspivack/nems-lean.git" @ "main"

-- ugp-physics-lean: git-pinned (switched from local path).
-- Note: repo is currently private; local builds work, CI requires public access.
require «ugp-physics-lean» from git
  "https://github.com/novaspivack/ugp-physics-lean" @ "a2c4eea6265606258c5b595766d16b29eb4bfce6"

require «reflexive-closure-lean» from git
  "https://github.com/novaspivack/reflexive-closure-lean.git" @ "main"

require «viable-continuation-lean» from git
  "https://github.com/novaspivack/viable-continuation-lean.git" @ "main"

-- Explicit mathlib pin so the root's v4.29.0-rc6 constraint wins over the
-- v4.29.0-rc3 that viable-continuation-lean's committed manifest otherwise pulls in.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib «SrrgLean» where
  roots := #[`SrrgLean]
