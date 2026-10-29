-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyWhole
import BeaconcryptCore.Computational.CborRawAnomalyCca

/-! The actual complete raw World anomaly has an explicit native pre-challenge CCA reduction. The operational full-ledger transport and actual native oracle predictor are both derived, and all three loss terms retain coefficient one. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineAnomaly
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentIdealParams (Target)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- The actual raw anomaly is bounded by the concrete native CCA advantage, correctness error and256-bit comparison term. -/
theorem anomaly_beta (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    {count : Nat} (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[CborRawHeadlineSlots.anomaly setup wire parse target <$>
      CborRawHeadlineSlots.realView setup wire parse checks target ensureInit runtime bounds mode adversary] {true} ≤
      CborRawAnomalyCca.beta setup wire parse checks target ensureInit runtime bounds mode adversary :=
  (CborRawAnomalyWhole.anomaly_pool setup wire parse checks lengths parser phase1 phase2 nativePhase1 target ensureInit
    runtime bounds mode adversary).trans
      (CborRawAnomalyCca.hit_beta setup functional wire parse checks target ensureInit runtime bounds mode adversary)

end BeaconcryptCore.Computational.CborRawHeadlineAnomaly

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineAnomaly.anomaly_beta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineAnomaly.anomaly_beta
