import Mathlib
import SrrgLean.Core.TheorySpace

/-!
# Core — Constraint functional C_Λ[S] (book §6.3)

Three nonnegative components: closure cost, SCP cost, selector cost. NEMS lemmas feed
into these components via `Bridges/FromNEMS.lean`.
-/

namespace SrrgLean.Core

@[simp]
noncomputable def ConstraintFunctional {α : Type*}
    (closureCost scpCost selectorCost : α → ℝ) (s : α) : ℝ :=
  closureCost s + scpCost s + selectorCost s

structure ConstraintProfile (α : Type*) where
  closureCost : α → ℝ
  scpCost : α → ℝ
  selectorCost : α → ℝ
  closure_nonneg : ∀ s, 0 ≤ closureCost s
  scp_nonneg : ∀ s, 0 ≤ scpCost s
  selector_nonneg : ∀ s, 0 ≤ selectorCost s

noncomputable def ConstraintProfile.functional {α : Type*} (C : ConstraintProfile α) (s : α) : ℝ :=
  ConstraintFunctional C.closureCost C.scpCost C.selectorCost s

theorem ConstraintFunctional_nonneg {α : Type*} (C : ConstraintProfile α) (s : α) :
    0 ≤ C.functional s := by
  unfold ConstraintProfile.functional ConstraintFunctional
  have h₁ := C.closure_nonneg s
  have h₂ := C.scp_nonneg s
  have h₃ := C.selector_nonneg s
  linarith

theorem constraint_functional_zero_iff_components_zero {α : Type*} (C : ConstraintProfile α) (s : α) :
    C.functional s = 0 ↔
      C.closureCost s = 0 ∧ C.scpCost s = 0 ∧ C.selectorCost s = 0 := by
  constructor
  · intro h
    unfold ConstraintProfile.functional ConstraintFunctional at h
    refine ⟨?_, ?_, ?_⟩
    · linarith [C.closure_nonneg s, C.scp_nonneg s, C.selector_nonneg s]
    · linarith [C.closure_nonneg s, C.scp_nonneg s, C.selector_nonneg s]
    · linarith [C.closure_nonneg s, C.scp_nonneg s, C.selector_nonneg s]
  · rintro ⟨h₁, h₂, h₃⟩
    simp [ConstraintProfile.functional, ConstraintFunctional, h₁, h₂, h₃]

end SrrgLean.Core
