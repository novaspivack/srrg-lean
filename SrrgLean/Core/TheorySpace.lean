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

end Core
end SrrgLean
