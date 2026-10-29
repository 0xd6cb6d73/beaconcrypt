-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyQuery
import BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation

/-! The actual thin raw frontend and the initialized entropy environment have the same complete adaptive execution. Actual allocation preservation discharges every source query invariant; no client correspondence, source equality or caller-supplied preservation premise is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyAdaptive
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State environment)
open RegistrationNativeSelectiveEntropyNative (handler)
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
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState source)))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before : RegistrationNativeSelectiveAllocationJoint.State n KemSK ProviderState Secret source)
    (valid : RegistrationNativeSelectiveAllocationJoint.Holds before) :
    (lower service codec route (simulateQ (handler setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept) work)).run before =
      (lower service codec route (simulateQ (RegistrationNativeEntropyWorld.native (environment setup checks wire source credential seed scalar candidate provider
        selectedOwner selectedAccept startup)) work)).run before := by
  rw [RegistrationNativeHiddenEnvironmentWorld.program_lower, RegistrationNativeHiddenEnvironmentWorld.program_lower]
  have represented := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (fun query => lower service codec route (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept query))
    (fun query => lower service codec route (RegistrationNativeEntropyWorld.native (environment setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept startup) query))
    RegistrationNativeSelectiveAllocationJoint.Holds id
    (fun query current good answer reached => RegistrationNativeSelectiveAllocation.handler_holds setup checks wire credential seed scalar candidate provider
      service codec route selectedOwner selectedAccept query current answer good reached)
    (fun query current good => by
      simpa only [pair_id, id_map, id_eq] using
        RegistrationNativeSelectiveEntropyQuery.query_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept startup
          service codec route query current good)
    work before valid
  simpa only [pair_id, id_map, id_eq] using represented

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyAdaptive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyAdaptive.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyAdaptive.program_source
