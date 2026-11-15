-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationFrontend
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLocal
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationTypedCaps
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution

/-! The complete actual typed/raw native frontend preserves its physical owner allocation and cursor correspondence. Creation uses the allocator's reached old length; all other real controllers are allocation-free and retain physical owner addresses. These source proofs quantify over every private record service and total KEM provider. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation
attribute [local irreducible] RegistrationNativePublicOwners.create
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
open RegistrationNativeSelectiveAllocationJoint (State Holds)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build

noncomputable def typed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) : QueryImpl TypedSpec (StateT (State n KemSK ProviderState Secret source) ProbComp) := fun query =>
  lower service codec route (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider
    (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar) query))

/-- Every actual typed native command preserves joint allocation under every reached callback and failure branch. -/
theorem typed_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (query : TypedSpec.Domain)
    (before : State n KemSK ProviderState Secret source)
    (result : TypedSpec.Range query × State n KemSK ProviderState Secret source) (valid : Holds before)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept query).run before)) :
    Holds result.2 := by
  have ordinary (quiet : RegistrationNativeHiddenAllocationTypedCaps.NonCreate query)
      (simple : RegistrationNativeHiddenAllocationLocal.Ordinary query) : Holds result.2 := by
    apply RegistrationNativeSelectiveAllocationFrontend.quiet setup wire sign seed scalar candidate provider service codec route _ before result valid
      (RegistrationNativeHiddenAllocationTypedCaps.typed setup checks wire sign selectedOwner selectedAccept _ query before.1.1.1.1 quiet) _ supported
    intro output reached
    have same := RegistrationNativeHiddenAllocationLocal.ordinary setup checks wire sign selectedOwner selectedAccept _ query _ output simple reached
    exact ⟨congrArg List.length same, by
      simpa only [RegistrationNativeHiddenAllocationOwners.Indexed, same,
        RegistrationNativeSelectiveAllocationJoint.drop, RegistrationNativeSelectiveAllocationJoint.dropLocal] using valid.indexed⟩
  cases query with
  | inl coin => exact ordinary trivial trivial
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact RegistrationNativeSelectiveAllocationFrontend.create setup checks wire sign seed scalar candidate provider service codec route
          selectedOwner selectedAccept (setup.dh.publicKey scalar) edPin mlPin keyId before result valid supported
    | bundle index =>
        apply RegistrationNativeSelectiveAllocationFrontend.quiet setup wire sign seed scalar candidate provider service codec route _ before result valid
          (RegistrationNativeHiddenAllocationTypedCaps.typed setup checks wire sign selectedOwner selectedAccept _ (.inr (.bundle index)) _ trivial) _ supported
        intro output reached
        exact RegistrationNativeHiddenAllocationLocal.beacon _ _ output valid.indexed
          (fun owners env answer indexed accepted => RegistrationNativeHiddenAllocationLifecycle.bundle setup wire selectedOwner _ index owners env answer indexed accepted) reached
    | finish index packet =>
        apply RegistrationNativeSelectiveAllocationFrontend.quiet setup wire sign seed scalar candidate provider service codec route _ before result valid
          (RegistrationNativeHiddenAllocationTypedCaps.typed setup checks wire sign selectedOwner selectedAccept _ (.inr (.finish index packet)) _ trivial) _ supported
        intro output reached
        exact RegistrationNativeHiddenAllocationLocal.beacon _ _ output valid.indexed
          (fun owners env answer indexed accepted => RegistrationNativeHiddenAllocationLifecycle.finish setup index packet owners env answer indexed accepted) reached
    | accept packet | build handle application | hmac key bytes | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw => exact ordinary trivial trivial

/-- The actual adaptive typed program preserves joint allocation throughout its full source state. -/
theorem typed_program_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (work : OracleComp TypedSpec Value)
    (before : State n KemSK ProviderState Secret source) (result : Value × State n KemSK ProviderState Secret source)
    (valid : Holds before) (supported : result ∈ support
      ((simulateQ (typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept) work).run before)) : Holds result.2 :=
  simulateQ_run_preserves_inv_of_query _ Holds
    (fun query current good answer reached => typed_holds setup checks wire sign seed scalar candidate provider service codec route
      selectedOwner selectedAccept query current answer good reached) work before valid result supported

/-- The complete actual frontend closure and physical World lowering commute with its adaptive typed query program. -/
theorem typed_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (work : OracleComp TypedSpec Value) :
    lower service codec route (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider
      (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)) work)) =
      simulateQ (typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept) work := by
  rw [RegistrationNativeSelectiveEntropyExecution.close_program, RegistrationNativeHiddenEnvironmentWorld.program_lower]
  rfl

/-- Every literal raw native command preserves joint allocation, including invalid parses and terminal malformed response failures. -/
theorem handler_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (query : RegistrationNativeInterface.Spec.Domain)
    (before : State n KemSK ProviderState Secret source)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK ProviderState Secret source) (valid : Holds before)
    (supported : result ∈ support ((lower service codec route
      (RegistrationNativeSelectiveEntropyNative.handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept query)).run before)) :
    Holds result.2 := by
  change result ∈ support ((lower service codec route
    (RegistrationNativeSelectiveEntropyEffects.close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
      (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar)) (RegistrationNativeRawAdapter.adapter wire query)))).run before) at supported
  rw [typed_program] at supported
  exact typed_program_holds setup checks wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider service codec route
    selectedOwner selectedAccept _ before result valid supported

/-- Every adaptive raw native continuation preserves the same derived joint invariant under arbitrary private record services. -/
theorem program_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before : State n KemSK ProviderState Secret source) (result : Value × State n KemSK ProviderState Secret source)
    (valid : Holds before) (supported : result ∈ support ((lower service codec route
      (simulateQ (RegistrationNativeSelectiveEntropyNative.handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept) work)).run before)) :
    Holds result.2 := by
  rw [RegistrationNativeHiddenEnvironmentWorld.program_lower] at supported
  exact simulateQ_run_preserves_inv_of_query _ Holds
    (fun query current good answer reached => handler_holds setup checks wire credential seed scalar candidate provider service codec route
      selectedOwner selectedAccept query current answer good reached) work before valid result supported

end BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.typed_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.typed_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.typed_program_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.typed_program_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.typed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.typed_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.handler_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.handler_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.program_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation.program_holds
