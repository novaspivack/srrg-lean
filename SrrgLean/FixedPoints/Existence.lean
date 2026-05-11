import Mathlib
import SelfReference.Core.FixedPoint
import SrrgLean.FixedPoints.Definition

/-!
# Fixed points — existence (book §7.2)

- **Flow-level** existence is a direct corollary of MFP-1 (`CSRI.master_fixed_point`).
- **Viability maximizers** on **finite** theory spaces always exist (purely combinatorial).
-/

namespace SrrgLean.FixedPoints

open SelfReference
open SrrgLean.Core

/-- MFP-1 packaging for an SRRG update map `F : α → α`. -/
theorem srrg_flow_fixed_point_exists
    {α : Type u} [S : CSRI α] (F : α → α)
    (hF : ∀ {x y : α}, S.Equiv x y → S.Equiv (F x) (F y))
    (hquote_id : ∀ x : α, S.Equiv (S.quote x) x)
    (hrun_cong : ∀ {e₁ e₂ c₁ c₂ : α},
        S.Equiv e₁ e₂ → S.Equiv c₁ c₂ →
        S.Equiv (S.run e₁ c₁) (S.run e₂ c₂)) :
    ∃ s : α, S.Equiv s (F s) :=
  CSRI.master_fixed_point F hF hquote_id hrun_cong

theorem viability_maximizer_exists_of_fintype [Fintype α] [Nonempty α]
    (P : RepCapacityProfile α) (C : ConstraintProfile α) :
    ∃ s : α, IsSrrgFixedPoint P C s := by
  classical
  obtain ⟨s, hs⟩ := Finite.exists_max (fun x : α => Viability P C x)
  exact ⟨s, fun t => hs t⟩

end SrrgLean.FixedPoints
