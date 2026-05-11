import Mathlib
import Sieve.Core.TheorySpace

/-!
# Core — Theory space (book §6.1)

`SrrgTheorySpace` extends the NEMS `Sieve.TheorySpace` carrier with a pseudometric
and a real-valued complexity functional. Flow / gradient-layer definitions live in
`FlowEquation.lean`.
-/

namespace SrrgLean
namespace Core

universe u

/-- SRRG theory space: extends `Sieve.TheorySpace` with metric and complexity data. -/
structure SrrgTheorySpace (α : Type u) extends Sieve.TheorySpace α where
  dist : α → α → ℝ
  dist_nonneg : ∀ s t, 0 ≤ dist s t
  dist_symm : ∀ s t, dist s t = dist t s
  complexity : α → ℝ
  complexity_nonneg : ∀ s, 0 ≤ complexity s

/-!
## Extended SRRG theory space (SPEC_052_PRI §A3)

`SrrgTheorySpaceFull` adds the `NemS.Optimality.TheorySpace` fields: descriptional
complexity `K` (as a natural number) and record equivalence `RecordEquivalent`.
These are needed to state PSC-optimality conditions within the SRRG framework.
-/

/--
Extended SRRG theory space that also carries `NemS.Optimality.TheorySpace` fields.

- `K s` — descriptional complexity of theory `s` (Kolmogorov-style, valued in ℕ).
- `RecordEquivalent s t` — record equivalence relation (two theories are record-equivalent
  if they produce the same observational record).
- `K_nonneg` — K ≥ 0 as integers (trivially true for ℕ-valued K, made explicit for API
  compatibility with optimality definitions that work over ℤ).
-/
structure SrrgTheorySpaceFull (α : Type u) extends SrrgTheorySpace α where
  K : α → ℕ
  RecordEquivalent : α → α → Prop
  K_nonneg : ∀ s, 0 ≤ (K s : ℤ)

/-- `K_nonneg` is automatic from the ℕ embedding; proved here for API completeness. -/
theorem SrrgTheorySpaceFull.K_nonneg_auto {α : Type u} (T : SrrgTheorySpaceFull α) (s : α) :
    0 ≤ (T.K s : ℤ) := Int.natCast_nonneg _

end Core
end SrrgLean
