-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationOwnerFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCaps
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
open RegistrationNativePlatformHiddenAllocationCore (Holds close)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
open RegistrationNativePlatformHiddenAllocationCreate (State)
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "sign" => RegistrationNativeMldsa.owned source credential
local notation "backend" => RegistrationNativePlatformSelectiveEntropyBackend.handler setup canonical sign seed scalar candidate provider
local notation "frontend" => RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks canonical source sign selectedOwner selectedAccept
  (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformSelectiveEntropyExecution.handler (n := n) setup checks wire source credential seed scalar candidate provider
  selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

theorem callback_run (query : TypedSpec.Domain)
    (before : RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source) :
    (actual query).run before = (close backend (frontend query)).run before := rfl

noncomputable def typed : QueryImpl TypedSpec (StateT (State n KemSK ProviderState Platform Secret source) ProbComp) :=
  fun query => lower service codec route (actual query)

/-- Every actual corrected typed callback preserves physical/local owner allocation and cursor absence under arbitrary private record services. -/
theorem typed_holds (query : TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source)
    (result : TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (valid : Holds before) (supported : result ∈ support ((typed setup checks wire credential seed scalar candidate provider
      selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before)) :
    Holds result.2 := by
  have same : actual query = close backend (frontend query) := rfl
  change result ∈ support ((lower service codec route (actual query)).run before) at supported
  rw [same] at supported
  have ordinary (quiet : RegistrationNativeRawAdapter.kind query ≠ 1) : Holds result.2 := by
    apply RegistrationNativePlatformHiddenAllocationCore.quiet backend service codec route (frontend query) before result valid _ _ supported
    · rw [← same]
      exact RegistrationNativePlatformHiddenAllocationCaps.typed setup checks wire source selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer credential seed scalar candidate provider query before.1.1.1 quiet
    · intro output reached
      exact RegistrationNativePlatformHiddenAllocationOwnerFrames.handler_fields setup checks canonical source sign selectedOwner selectedAccept
        (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query quiet
        before.1.1.1.1 output valid.indexed reached
  cases query with
  | inl coin => exact ordinary (by simp only [RegistrationNativeRawAdapter.kind]; decide)
  | inr command =>
    cases command
    case create edPin mlPin keyId =>
      exact RegistrationNativePlatformHiddenAllocationCreate.create setup canonical sign seed scalar candidate provider service codec route
        selectedOwner (setup.dh.publicKey scalar) edPin mlPin keyId before result valid supported
    all_goals exact ordinary (by simp only [RegistrationNativeRawAdapter.kind]; decide)

/-- The full actual adaptive typed execution retains one same-run allocation invariant and every reached platform/private state. -/
theorem program_holds (work : OracleComp TypedSpec A) (before : State n KemSK ProviderState Platform Secret source)
    (result : A × State n KemSK ProviderState Platform Secret source) (valid : Holds before)
    (supported : result ∈ support ((lower service codec route (simulateQ actual work)).run before)) : Holds result.2 := by
  rw [RegistrationNativeHiddenEnvironmentWorld.program_lower] at supported
  exact simulateQ_run_preserves_inv_of_query _ Holds
    (fun query current good answer reached => typed_holds setup checks wire credential seed scalar candidate provider
      selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route
      query current answer good reached) work before valid result supported

/-- Actual malformed raw commands and every later native ledger callback retain the same physical-owner correspondence. -/
theorem raw_holds (query : RegistrationNativeInterface.Spec.Domain)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK ProviderState Platform Secret source)
    (valid : Holds before)
    (supported : result ∈ support ((lower service codec route (simulateQ actual
      (RegistrationNativeRawAdapter.adapter canonical query))).run before)) : Holds result.2 :=
  program_holds setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer service codec route _ before result valid supported

/-- All observation modes keep the original full ledger beside the actual new source and allocation invariant. -/
theorem full_holds (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State n KemSK ProviderState Platform Secret source)
    (result : (A × RegistrationNativeLedger.State) × State n KemSK ProviderState Platform Secret source)
    (valid : Holds before)
    (supported : result ∈ support ((lower service codec route (simulateQ actual
      (RegistrationNativeFullCompiler.compile setup.source.crypto canonical serverKeyId bounds mode work))).run before)) : Holds result.2 :=
  program_holds setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer service codec route _ before result valid supported
end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.callback_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.callback_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.typed_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.typed_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.program_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.program_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.raw_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.raw_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.full_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation.full_holds
