-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant
import BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupFresh
/-! The final runtime profile keeps the unchanged native startup as a lifted prefix. Its existing exact seeded source equation is lifted beside the persistent platform state, and actual startup support establishes the internal root conditions for the new callback tree. No old callback or whole-profile equation is reused. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicSourceExecution (State)
open RegistrationNativePublicSourceState (Live MemoCorrect)
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The unchanged actual generated prefix has the same seeded native initializer and literal external poststate, including constructor and ML-generation refusal. -/
theorem start_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (previous : Platform) :
    (fun result => (RegistrationNativePublicSourceStartupWorld.observe setup source seed scalar identityIndex serverKeyId result, previous)) <$>
      (RegistrationNativePublicSourceEffects.close setup seed scalar
        (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
          (RegistrationNativePublicInterpreter.initial : RegistrationNativePublicInterpreter.State n KemSK) =
    (fun initial => (initial, previous)) <$>
      RegistrationNativeSeedStart.start (n := n) setup source ensureInit identityIndex serverKeyId seed := by
  have same := congrArg (Functor.map (fun initial => (initial, previous)))
    (RegistrationNativePublicSourceStartup.start_source (n := n) setup source ensureInit identityIndex serverKeyId seed scalar)
  simpa only [Functor.map_map] using same

/-- Actual successful startup establishes the internal invariant for the corrected public frontend with any persistent platform state. -/
theorem start_invariants (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (started : RegistrationNativePublicStartup.Started source) (after : RegistrationNativePublicInterpreter.State n KemSK)
    (previous : Platform)
    (supported : (some started, after) ∈ support ((RegistrationNativePublicSourceEffects.close setup seed scalar
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
        (RegistrationNativePublicInterpreter.initial : RegistrationNativePublicInterpreter.State n KemSK))) :
    let initial : State n KemSK Platform source := ((started.frontend, previous), after)
    Live initial.1.1 initial.2 ∧ MemoCorrect setup seed scalar initial.2.roots :=
  RegistrationNativePublicSourceStartupFresh.start_invariants setup source seed scalar ensureInit identityIndex serverKeyId started after supported


/-- The actual initialized prefix supplies both internal conditions for every subsequent corrected adaptive source execution. -/
theorem initialized_program [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
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
        (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer) work)).run ((started.frontend, previous), before))) :
    Live result.2.1.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  have initial := start_invariants setup source seed scalar ensureInit identityIndex serverKeyId started before previous startup
  rw [← RegistrationNativePlatformPublicSourceInvariant.program_source setup checks wire route
    (RegistrationNativeMldsa.owned source started.credential) seed scalar selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work] at supported
  exact RegistrationNativePlatformPublicSourceInvariant.program setup checks wire route
    (RegistrationNativeMldsa.owned source started.credential) seed scalar selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work
        ((started.frontend, previous), before) result initial.1 initial.2 supported

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup.start_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup.start_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup.start_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup.start_invariants

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup.initialized_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup.initialized_program
