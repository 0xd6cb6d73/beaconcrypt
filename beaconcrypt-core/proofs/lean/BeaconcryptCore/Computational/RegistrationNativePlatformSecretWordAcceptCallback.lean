-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptSource
/-! The literal corrected public accept callback increments the original public attempt count and executes the same routed symbolic root-reference controller, reserve and persistent platform state. The complete full-ABI equality is derived from the source kernel, with no callback equation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCallback
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativePlatformSecretWordOrdinary (State evaluate)
open RegistrationNativePlatformSecretWordFrontendView (nativeBase wordBase)
attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept
  RegistrationNativePlatformSecretWordOpen.accept
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (update : S → S) (before : S) :
    (modify update : StateT S m Unit) before = pure ((), update before) := rfl

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

theorem accept [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
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
    (packet : registration.InitPacket) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet))).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativePlatformSecretWordFrontend.accept setup checks source selectedAccept reserveRegistration packet).run before) := by
  have low := congrArg (fun action => action.run before.2)
    (RegistrationNativePlatformSecretWordAcceptSource.kernel (n := n) setup checks inside candidate seed scalar
      (decide (before.1.parsedAccepts = selectedAccept)) reserveRegistration source.verify packet before.1.server before.1.environment)
  have lifted := congrArg (fun action => (fun result => (result.1.1.1,
    (({ server := result.1.1.2, beacons := before.1.beacons, environment := result.1.2,
        parsedAccepts := before.1.parsedAccepts + 1 } : RegistrationNativePublicFrontend.State source), result.2))) <$> action) low
  dsimp only [RegistrationNativePlatformPublicFrontend.handler]
  simp only [RegistrationNativePlatformPublicFrontend.executeLocal,
    RegistrationNativePlatformPublicFrontend.serverOpen, RegistrationNativePlatformSecretWordFrontend.accept,
    RegistrationNativePlatformSecretWordFrontend.serverOpen, pure_bind, evaluate, Prod.map_def, id_eq, RegistrationNativeSecretWordMessage.State.eval,
    nativeBase, wordBase, RegistrationNativePlatformInterpret.state, StateT.run, bind_apply, get_apply, modify_apply, map_apply,
    simulateQ_map, QueryImpl.simulateQ_compose, Functor.map_map] at lifted ⊢
  convert lifted using 1 <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCallback.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCallback.accept
