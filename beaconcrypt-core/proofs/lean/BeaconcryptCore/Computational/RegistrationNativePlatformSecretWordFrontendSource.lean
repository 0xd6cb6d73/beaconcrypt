-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishSource
/-! The complete corrected callback dispatcher and canonical raw-mode program have the candidate-independent Word execution. The full reply, original ledger, opaque roster, one-use session state, environment and persistent platform poststate are retained by the exact operational equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativePlatformSecretWordOrdinary (State evaluate)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)


/-- Every literal corrected callback has the same complete checked Word execution; all source branches and failed allocation histories are retained. -/
theorem handler (query : TypedSpec.Domain) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativePlatformSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before) := by
  by_cases ordinary : RegistrationNativePlatformSecretWordOrdinary.Ordinary query
  · rw [RegistrationNativePlatformSecretWordFrontend.ordinary setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query ordinary]
    exact RegistrationNativePlatformSecretWordOrdinary.handler_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer inside candidate (input setup.joint setup.dh seed scalar) query ordinary before
  · cases query with
    | inl coin => exact (ordinary trivial).elim
    | inr query => cases query with
      | accept packet => exact RegistrationNativePlatformSecretWordAcceptCallback.accept setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer inside candidate seed scalar packet before
      | build handle application => exact RegistrationNativePlatformSecretWordBuildSource.build setup source sign view failure allocation erased helper writer reservePeer inside candidate seed scalar handle application before
      | finish index packet => exact RegistrationNativePlatformSecretWordFinishSource.finish setup wire source inside candidate seed scalar index packet before
      | _ => exact (ordinary trivial).elim

/-- Adaptive execution preserves the entire same-run result and frontend/platform poststate after symbolic reference evaluation. -/
theorem program (work : OracleComp TypedSpec A) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((simulateQ (RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((simulateQ (RegistrationNativePlatformSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind, map_bind]
    rw [handler setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer inside candidate seed scalar query before, bind_map_left]
    apply bind_congr
    rintro ⟨value, after⟩
    exact ih value after

/-- The exact current canonical raw-mode runner retains its original decision bit and ledger on every mode and history. -/
theorem run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          (RegistrationNativePlatformSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before) := by
  exact program setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer inside candidate seed scalar
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work) before

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource.run
