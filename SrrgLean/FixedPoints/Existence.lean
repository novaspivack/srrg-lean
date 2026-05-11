import Mathlib
import SelfReference.Core.FixedPoint
import SrrgLean.FixedPoints.Definition

/-!
# Fixed points — existence (book §7.2)

- **Flow-level** existence is a direct corollary of MFP-1 (`CSRI.master_fixed_point`).
- **Viability maximizers** on **finite** theory spaces always exist (purely combinatorial).

## Alpha theorem reference (SPEC_052_PRI §B4)

The **Alpha theorem** (Theorem 63.3 in reflexive-closure-lean, `Alpha.alpha_theorem`) proves
the necessary existence of the pre-categorial ontological ground of reflexive reality.
This strengthens SRRG fixed-point existence from **contingent** (fintype max) to **necessary**
(the deepest fixed point of reflexive reality must exist, not merely by combinatorial argument
but by logical necessity).

The full composition would be:
  `alpha_theorem` ⟹ ∃ necessary ground g ⟹ SRRG fixed point at g is not merely maximal
  by finite-type combinatorics but is the pre-categorial anchor.

**TODO (SPEC_052_PRI §B4):** Add `require «reflexive-closure-lean» from "../reflexive-closure-lean"`
to `lakefile.lean` once the transitive dependency conflict is resolved:
`reflexive-closure-lean` requires `nems-lean` from a pinned git commit, while `srrg-lean`
requires `nems-lean` from the local path `"../nems-lean"`. Lake cannot reconcile these two
origins for the same package without a lake-manifest override. When resolved, add:

  ```
  import Alpha.Theorems.AlphaTheorem
  ```

and then the theorem below becomes a real composition rather than a stub.
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

/--
**Alpha-strengthened fixed-point existence (SPEC_052_PRI §B4 — stub pending import).**

The Alpha theorem (`Alpha.alpha_theorem`, Theorem 63.3 in reflexive-closure-lean) guarantees
the necessary existence of a pre-categorial ground. Combined with SRRG fixed-point existence,
this would establish: the SRRG fixed point is not merely a combinatorial maximum on a finite
type, but corresponds to the necessary pre-categorial anchor of reflexive reality.

**Current status:** `trivial` stub — the Alpha theorem import is blocked by a nems-lean
version conflict (see module docstring TODO). The API name and signature are committed so
call sites can reference this theorem once the import is resolved.

**TODO (SPEC_052_PRI §B4):** Replace `True := trivial` with a real composition using
`Alpha.alpha_theorem` once `require «reflexive-closure-lean»` is added to `lakefile.lean`.
-/
theorem alpha_strengthened_fp_existence
    {α : Type u} [CSRI α]
    (_h_reflexive_reality : True) :  -- TODO: replace with Alpha.NontrivialReflexiveRealityExists
    True := trivial

end SrrgLean.FixedPoints
