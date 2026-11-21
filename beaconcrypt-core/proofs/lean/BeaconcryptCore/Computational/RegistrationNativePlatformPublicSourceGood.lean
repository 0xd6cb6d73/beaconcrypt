-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant
import BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupGood
/-! The actual initialized corrected frontend derives its internal earlier-root, selected-scalar and pending-control conditions. These are maintained by the complete new callback tree and are not added to public event eligibility. Prior record-request histories may be arbitrary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceState (Live MemoCorrect)
variable {n : Nat} {E Platform I KemSK Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
structure Good (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (selected : Nat) (before : State n KemSK Platform source) : Prop where
  live : Live before.1.1 before.2
  memo : MemoCorrect setup seed scalar before.2.roots
  owners : RegistrationNativePlatformPublicOwnerState.Valid selected (setup.dh.publicKey scalar) before.1.1.beacons

/-- Unchanged literal generated startup supplies all internal root and owner conditions for the corrected source frontend. -/
theorem start (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selected : Nat) (started : RegistrationNativePublicStartup.Started source)
    (after : RegistrationNativePublicInterpreter.State n KemSK) (previous : Platform)
    (supported : (some started, after) ∈ support ((RegistrationNativePublicSourceEffects.close setup seed scalar
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
        (RegistrationNativePublicInterpreter.initial : RegistrationNativePublicInterpreter.State n KemSK))) :
    Good setup seed scalar selected ((started.frontend, previous), after) := by
  have initial := RegistrationNativePublicSourceStartupGood.start_good setup source seed scalar ensureInit identityIndex serverKeyId selected started after supported
  exact ⟨initial.live, initial.memo, initial.mask,
    (RegistrationNativePublicInvariantOwners.restored_holds scalar started.frontend.beacons).mpr initial.coherent⟩

/-- Every actual adaptive corrected source program preserves all initialized internal conditions, including arbitrary prior record-request histories. -/
theorem program [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK Platform source)
    (result : Value × State n KemSK Platform source) (good : Good setup seed scalar selectedOwner before)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (simulateQ (RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept
        (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work)).run before)) :
    Good setup seed scalar selectedOwner result.2 := by
  have free := RegistrationNativePlatformPublicSourceExecution.observed_support setup wire route sign seed scalar _ before result supported
  have owners := RegistrationNativePlatformPublicOwnerInvariant.program setup checks wire sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work before.1 (result.1, result.2.1) good.owners free
  rw [← RegistrationNativePlatformPublicSourceInvariant.program_source setup checks wire route sign seed scalar selectedOwner selectedAccept
    (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work] at supported
  have roots := RegistrationNativePlatformPublicSourceInvariant.program setup checks wire route sign seed scalar selectedOwner selectedAccept
    (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work before result good.live good.memo supported
  exact ⟨roots.1, roots.2, owners⟩
/-- Actual initialized generated startup derives every internal source condition for the entire subsequent adaptive corrected program. -/
theorem initialized_program [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (started : RegistrationNativePublicStartup.Started source) (before : RegistrationNativePublicInterpreter.State n KemSK)
    (previous : Platform)
    (startup : (some started, before) ∈ support ((RegistrationNativePublicSourceEffects.close setup seed scalar
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
        (RegistrationNativePublicInterpreter.initial : RegistrationNativePublicInterpreter.State n KemSK)))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (result : Value × State n KemSK Platform source)
    (supported : result ∈ support ((RegistrationNativePlatformPublicSourceExecution.execute setup wire route
      (RegistrationNativeMldsa.owned source started.credential) seed scalar
      (simulateQ (RegistrationNativePlatformPublicFrontend.handler setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer) work)).run ((started.frontend, previous), before))) :
    Good setup seed scalar selectedOwner result.2 := by
  have initial := start setup source seed scalar ensureInit identityIndex serverKeyId selectedOwner started before previous startup
  exact program setup checks wire route (RegistrationNativeMldsa.owned source started.credential) seed scalar selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work ((started.frontend, previous), before) result initial supported

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood.initialized_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood.initialized_program
