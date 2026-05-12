-- SrrgLean — EPIC_047 / P27 formalization root
--
-- Prose specifications live in `ugp-physics` (internal): EPIC_046 `MASTER_STATUS.md`
-- and EPIC_047 `SPEC_047_SRL_SRRG_LEAN.md`.

-- Phase 1 — Core
import SrrgLean.Core.TheorySpace
import SrrgLean.Core.RepresentationCapacity
import SrrgLean.Core.ConstraintFunctional
import SrrgLean.Core.ViabilityFunctional
import SrrgLean.Core.FlowEquation
-- Phase 2 — Fixed points
import SrrgLean.FixedPoints.Definition
import SrrgLean.FixedPoints.Existence
import SrrgLean.FixedPoints.Stability
import SrrgLean.FixedPoints.Uniqueness
import SrrgLean.FixedPoints.PhysicalConstants
import SrrgLean.FixedPoints.H4Discharge
import SrrgLean.FixedPoints.EtaFlow
import SrrgLean.FixedPoints.NoThirdFixedPoint
import SrrgLean.FixedPoints.BetaEtaQuadratic
-- Phase 3 — Applications
import SrrgLean.Applications.InformationEfficiency
import SrrgLean.Applications.GaugeSymmetry
import SrrgLean.Applications.GoldenRatioFlow
-- Phase 4 — Bridges
import SrrgLean.Bridges.FromNEMS
import SrrgLean.Bridges.ToIPT
import SrrgLean.Bridges.ToUGP
import SrrgLean.Bridges.ToNEMSConfirmations
-- Connection layer (EPIC_046 Y8L / H9)
import SrrgLean.Connection.IPTBridge
import SrrgLean.Connection.H9Bridge
import SrrgLean.Connection.GoldenPhiBridge
import SrrgLean.Connection.UOneBridge
-- Phase 5 — Constants (EPIC_049_SCD)
import SrrgLean.Constants.StrongCP
import SrrgLean.Constants.GaugeGroupSelection
import SrrgLean.Constants.GenerationCount
-- Phase 5 cont. — Constants Phase 2 (EPIC_049_SCD Phase 2)
import SrrgLean.Constants.BetaFunction
import SrrgLean.Constants.HiggsQuartic
import SrrgLean.Constants.CosmologicalConstant

/-!
# SrrgLean

Lean library for the Self-Referential Renormalization Group (SRRG) and its bridges to
NEMS (`nems-lean`), IPT / GXT (`ugp-physics-lean`), and gauge structure (`ugp-lean`).
-/
