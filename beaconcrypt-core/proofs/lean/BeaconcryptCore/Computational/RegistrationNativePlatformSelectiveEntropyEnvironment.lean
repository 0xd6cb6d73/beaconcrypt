-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend

/-! The corrected raw registration controllers retain actual source writers and a common allocator state in an opaque-material environment. Its state stores slots, material44 and nonselected known108 outputs; selected record seeds and kernels stay in the shared World. Private input-classifier parameters select the hybrid. External uniform requests are explicitly charged through EnvEffects here; literal uncounted source state remains a separate operational comparison. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEnvironment
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open BeaconcryptCore.Refinement
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK ProviderState Platform E : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK ProviderState Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformPublicFrontend.State source Platform × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState

noncomputable def step (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl RegistrationNativeEntropyInterface.EnvSpec
      (StateT (State n KemSK ProviderState Platform source) (OracleComp (EnvEffects n))) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.restricted setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider)
      ((RegistrationNativePlatformPublicFrontendCaps.raw setup checks wire source (RegistrationNativeMldsa.owned source credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr query.val)).run before.1)).run before.2

noncomputable def environment (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize) × State n KemSK ProviderState Platform source))) :
    RegistrationNativeEntropyInterface.Environment n (State n KemSK ProviderState Platform source) :=
  ⟨startup, step setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer⟩

/-- The actual raw native registration callback, including every failure poststate, has exactly the restricted environment AST after embedding in the shared World. -/
theorem step_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : State n KemSK ProviderState Platform source) :
    simulateQ effectLift ((step setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider)
          ((RegistrationNativePlatformPublicFrontendCaps.raw setup checks wire source (RegistrationNativeMldsa.owned source credential)
            selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr query.val)).run before.1)).run before.2 := by
  simp only [step, StateT.run, simulateQ_map]
  have sourceLaw := RegistrationNativePlatformSelectiveEntropyBackend.program_local setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider _ (RegistrationNativePlatformPublicFrontendCaps.raw_zero setup checks wire source
      (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1) before.2
  simpa only [StateT.run] using congrArg (fun distribution =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) sourceLaw

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEnvironment


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEnvironment.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEnvironment.step_source
