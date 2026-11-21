-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentQuery
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocation

/-! The actual thin raw frontend and the initialized entropy environment have the same complete adaptive execution. Actual allocation preservation discharges every source query invariant; no client correspondence, source equality or caller-supplied preservation premise is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentAdaptive
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironment (State environment)
open RegistrationNativeHiddenEnvironmentNative (handler)
open RegistrationNativeHiddenEnvironmentWorld (lower)
variable {n : Nat} {ι KemSK ProviderState Secret Reader Response Value : Type} {base : OracleSpec ι}

private theorem pair_id {First Second : Type} :
    Prod.map (id : First → First) (id : Second → Second) = (id : First × Second → First × Second) := by
  funext value
  cases value
  rfl

/-- Every adaptive actual raw continuation agrees with the original entropy environment while retaining both local states, cursor, Protocol control and complete private service state. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize) × State n KemSK ProviderState source)))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before : RegistrationNativeHiddenEnvironmentJoint.State n KemSK ProviderState Secret source)
    (valid : RegistrationNativeHiddenEnvironmentJoint.Holds before) :
    (lower service codec route (simulateQ (handler setup checks wire source credential seed scalar provider
      selectedOwner selectedAccept) work)).run before =
      (lower service codec route (simulateQ (RegistrationNativeEntropyWorld.native (environment setup checks wire source credential seed scalar provider
        selectedOwner selectedAccept startup)) work)).run before := by
  rw [RegistrationNativeHiddenEnvironmentWorld.program_lower, RegistrationNativeHiddenEnvironmentWorld.program_lower]
  have represented := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (fun query => lower service codec route (handler setup checks wire source credential seed scalar provider selectedOwner selectedAccept query))
    (fun query => lower service codec route (RegistrationNativeEntropyWorld.native (environment setup checks wire source credential seed scalar provider
      selectedOwner selectedAccept startup) query))
    RegistrationNativeHiddenEnvironmentJoint.Holds id
    (fun query current good answer reached => RegistrationNativeHiddenAllocation.handler_holds setup checks wire credential seed scalar provider
      service codec route selectedOwner selectedAccept query current answer good reached)
    (fun query current good => by
      simpa only [pair_id, id_map, id_eq] using
        RegistrationNativeHiddenEnvironmentQuery.query_source setup checks wire source credential seed scalar provider selectedOwner selectedAccept startup
          service codec route query current good)
    work before valid
  simpa only [pair_id, id_map, id_eq] using represented

end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentAdaptive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentAdaptive.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentAdaptive.program_source
