-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram

/-! The actual full/known and thin materialized callbacks have the finite Common source on the same reached private receipt/World state. The proof derives this by literal query translation and complete state-bijection diagrams; no equality of games is an assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedPairedSource
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedState (Core View view restore)
open RegistrationNativeG3MaterializedLocalCommon (project)
open RegistrationNativePairedServerService (Common)
open RegistrationNativeG3MaterializedCommonDiagram (liftCommon translate)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

private theorem paired_translation (full : Bool) (seeds : Seeds n) :
    (fun query : (Common n).Domain => RegistrationNativeG3MaterializedBeaconComplete.paired full setup.source wire.frameWrite sign seeds
      (RegistrationNativeG3MaterializedLocal.service (ProviderState := ProviderState) table setup seed scalar candidate) (.inr query)) =
      RegistrationNativeG3MaterializedFrontend.common (RegistrationNativeG3Common.handler setup.source wire.frameWrite sign) ∘ₛ
        translate full seeds := by
  funext query
  rcases query with publication | effect
  · cases full <;> simp only [RegistrationNativeG3MaterializedBeaconComplete.paired,
      RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
      QueryImpl.compose, translate, Bool.false_eq_true, ite_true, ite_false, simulateQ_spec_query]
    rfl
  · rcases effect with coin | capability
    · cases full <;> simp only [RegistrationNativeG3MaterializedBeaconComplete.paired,
        QueryImpl.compose, translate, simulateQ_spec_query] <;> rfl
    · cases capability <;> try (cases full <;> simp only [RegistrationNativeG3MaterializedBeaconComplete.paired,
        QueryImpl.compose, translate, simulateQ_spec_query] <;> rfl)
      case installServer keyId binding tag => cases tag <;> cases full <;>
        simp only [RegistrationNativeG3MaterializedBeaconComplete.paired,
          RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
          QueryImpl.compose, translate, ite_true, ite_false, Bool.false_eq_true, simulateQ_spec_query] <;> rfl
      case installBeacon owner shell tag => cases tag <;> cases full <;>
        simp only [RegistrationNativeG3MaterializedBeaconComplete.paired,
          RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
          QueryImpl.compose, translate, ite_true, ite_false, Bool.false_eq_true, simulateQ_spec_query] <;> rfl

private theorem actual_program (work : OracleComp (Common n) Value)
    (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState) :
    Prod.map id view <$>
      (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route wire sign seed scalar candidate provider)
        (simulateQ (liftCommon (KemSK := KemSK)) work)).run before =
      (simulateQ (RegistrationNativeG3MaterializedCommonDiagram.actual table setup codec route wire sign seed scalar candidate provider)
        work).run (view before) := by
  rw [← QueryImpl.simulateQ_compose]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [RegistrationNativeG3MaterializedCommonDiagram.actual, QueryImpl.apply_compose, StateT.run,
    RegistrationNativeG3MaterializedState.restore_view]

private theorem actual_translation (full : Bool) (seeds : Seeds n) (query : (Common n).Domain) (before : View n KemSK ProviderState) :
    (RegistrationNativeG3MaterializedLocalSource.actual table setup codec route wire sign seed scalar candidate provider full seeds
      (.inr (.inl (.inr query)))).run before =
      (simulateQ (RegistrationNativeG3MaterializedCommonDiagram.actual table setup codec route wire sign seed scalar candidate provider)
        (translate full seeds query)).run before := by
  have source := actual_program table setup codec route wire sign seed scalar candidate provider (translate full seeds query) (restore before)
  rw [RegistrationNativeG3MaterializedState.view_restore] at source
  rw [← source]
  have translated := congrFun (RegistrationNativeG3MaterializedCommonDiagram.translation_lift (KemSK := KemSK) full seeds) query
  simp only [QueryImpl.apply_compose, liftCommon] at translated
  simp only [RegistrationNativeG3MaterializedLocalSource.actual, RegistrationNativeG3MaterializedLocal.handler,
    RegistrationNativePublicFrontend.liftLocal, StateT.run]
  rw [QueryImpl.simulateQ_compose, translated]

/-- The concrete callback interpretations have the exact finite materialized Common source after the named bilateral accounting projection, retaining every current private receipt and semantic World field. -/
theorem common_source (full : Bool) (seeds : Seeds n) (query : (Common n).Domain) (before : View n KemSK ProviderState) :
    Prod.map id project <$>
      (RegistrationNativeG3MaterializedBeaconComplete.paired full setup.source wire.frameWrite sign seeds
        (RegistrationNativeG3MaterializedLocal.service table setup seed scalar candidate) (.inr query)).run before =
      (RegistrationNativeG3MaterializedLocalSource.actual table setup codec route wire sign seed scalar candidate provider full seeds
        (.inr (.inl (.inr query)))).run (project before) := by
  have first := congrFun (paired_translation (ProviderState := ProviderState) table setup wire sign seed scalar candidate full seeds) query
  rw [first, QueryImpl.apply_compose, actual_translation]
  exact RegistrationNativeG3MaterializedCommonDiagram.program_source table setup codec route wire sign seed scalar candidate provider
    (translate full seeds query) before
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedPairedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedPairedSource.common_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedPairedSource.common_source
