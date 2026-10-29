-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys

/-! The concrete independent-key selective handler has the same bilateral accounting view as its actual guarded source. Every reached state from a normalized input is itself normalized. This derives the prefix condition needed by materialized typed macro assembly without adding a caller-supplied World invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3LocalKeys (State project handler localKeys)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

private theorem project_idempotent (before : State n KemSK ProviderState) : project (project before) = project before := by
  simp only [project, RegistrationNativeG3MetricWorld.mask_idempotent]

/-- Every concrete local-key callback normalizes identically on both input and output, retaining all protocol state and private service fields. -/
theorem query_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK ProviderState) :
    Prod.map id project <$> (handler setup codec route wire sign seed scalar candidate provider query).run before =
      (handler setup codec route wire sign seed scalar candidate provider query).run (project before) := by
  rcases query with (message | (message | common) | kem) | record
  · simp only [handler, localKeys, StateT.run, project, Functor.map_map, Prod.map_def, id_eq]
  · simp only [handler, localKeys, StateT.run, project, Functor.map_map, Prod.map_def, id_eq]
  · exact RegistrationNativeG3LocalKeys.execute_project setup codec route _ before
  · exact RegistrationNativeG3LocalKeys.execute_project setup codec route _ before
  · exact RegistrationNativeG3LocalKeys.execute_project setup codec route _ before

/-- The actual mixed adaptive selective computation retains the same explicit accounting projection throughout its complete execution. -/
theorem program_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    Prod.map id project <$> (simulateQ (handler setup codec route wire sign seed scalar candidate provider) work).run before =
      (simulateQ (handler setup codec route wire sign seed scalar candidate provider) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_project setup codec route wire sign seed scalar candidate provider) work before

/-- Every supported actual prefix outcome from a normalized input has the required normalized World, derived from the literal mixed handler. -/
theorem program_masked (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK ProviderState)
    (result : Value × State n KemSK ProviderState)
    (supported : result ∈ support ((simulateQ (handler setup codec route wire sign seed scalar candidate provider) work).run (project before))) :
    project result.2 = result.2 := by
  rw [← program_project setup codec route wire sign seed scalar candidate provider work before, support_map] at supported
  obtain ⟨earlier, _possible, equal⟩ := supported
  cases equal
  exact project_idempotent earlier.2

end BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame.program_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame.program_masked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeyFrame.program_masked
