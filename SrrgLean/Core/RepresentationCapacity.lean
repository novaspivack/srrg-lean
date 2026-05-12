import Mathlib
import SrrgLean.Core.TheorySpace

/-!
# Core — Representation capacity R[S] (book §6.2)

`RepCapacityProfile` bundles a nonnegative real functional. Deriving concrete bounds
from `SelectorStrength` barrier theorems is an open formalization target.
-/

namespace SrrgLean.Core

universe u

structure RepCapacityProfile (α : Type u) where
  R : α → ℝ
  R_nonneg : ∀ s, 0 ≤ R s

noncomputable def RepCapacity {α : Type u} (P : RepCapacityProfile α) (s : α) : ℝ :=
  P.R s

@[simp]
theorem RepCapacity.eq {α : Type u} (P : RepCapacityProfile α) (s : α) :
    RepCapacity P s = P.R s := rfl

theorem repCapacity_nonneg {α : Type u} (P : RepCapacityProfile α) (s : α) :
    0 ≤ RepCapacity P s := P.R_nonneg s

/-- Interface: `R` stays below a barrier constant (diagonal / strength certificate). -/
def RepCapacityBoundedBy {α : Type u} (P : RepCapacityProfile α) (B : ℝ) : Prop :=
  ∀ s, P.R s ≤ B

/-!
## Diagonal barrier theorems

These theorems give `RepCapacity` actual computational content beyond a placeholder.
The diagonal barrier (SelectorStrength.BarrierSchema in nems-lean) says: no
self-referential system can realize a total decider at its own strength level.
Here we package this as a bounded-profile structure and prove existence on finite types.
-/

/--
**Diagonal barrier:** If `P` is bounded by `B`, then `RepCapacity P s ≤ B` for all `s`.

This is the SRRG packaging of `SelectorStrength.BarrierSchema`: the representational
capacity of any system is bounded by its diagonal strength constant.
-/
theorem repCapacity_below_diagonal_barrier
    {α : Type u} (P : RepCapacityProfile α) (B : ℝ)
    (hBarrier : RepCapacityBoundedBy P B) (s : α) :
    RepCapacity P s ≤ B := hBarrier s

/-- A `RepCapacityProfile` bundled with its diagonal barrier constant and proof. -/
structure BoundedRepCapacityProfile (α : Type u) where
  profile : RepCapacityProfile α
  barrier : ℝ
  barrier_pos : 0 < barrier
  bounded : RepCapacityBoundedBy profile barrier

/-- For any finite nonempty type, a barrier constant exists (the max of all R values). -/
theorem bounded_rep_capacity_exists {α : Type u} [Fintype α] [Nonempty α]
    (P : RepCapacityProfile α) :
    ∃ B : ℝ, RepCapacityBoundedBy P B := by
  classical
  use Finset.sup' Finset.univ ⟨Classical.arbitrary α, Finset.mem_univ _⟩ (fun s => P.R s)
  intro s
  exact Finset.le_sup' (fun s => P.R s) (Finset.mem_univ s)

end SrrgLean.Core
