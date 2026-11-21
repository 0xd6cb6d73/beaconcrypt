-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix
/-! Concrete source leaf instantiation for the actual post-agreement Beacon suffix. Material addresses are evaluated before the same selective demand; hidden, known and refused choices and every stateful World continuation remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendAccept
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolicProvider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused symbolicProvider
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider
local notation "wordLocal" => symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
local notation "nativeLocal" => wordLocal ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate
local notation "actualLocal" => actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false

local notation "reified" => RegistrationNativePlatformLorCtxRealization.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge

variable {Platform E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : PqxdhServerAuthExperiment.Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "evaluate" => RegistrationNativePlatformSecretWordOrdinary.evaluate candidate
local notation "nativeController" => RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "wordController" => RegistrationNativePlatformSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

omit primitive in
private theorem map_apply {S B C : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : B → C) (work : StateT S m B) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

omit primitive in
private theorem bind_apply {S B C : Type} {m : Type → Type} [Monad m]
    (work : StateT S m B) (next : B → StateT S m C) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
omit primitive in
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before,before) := rfl
omit primitive in
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (f : S → S) (before : S) :
    (modify f : StateT S m Unit) before = pure ((),f before) := rfl

theorem accept_source (packet : registration.InitPacket)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore : Symbolic n KemSK) :
    Prod.map (Prod.map id evaluate) (frame candidate) <$>
      (simulateQ symbolic ((wordController (.inr (.accept packet))).run before)).run privateBefore =
      (simulateQ actual (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((nativeController (.inr (.accept packet))).run (evaluate before)))).run (frame candidate privateBefore) := by
  have core := RegistrationNativePlatformLorIdealAcceptLift.accept_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    checks reserveRegistration (decide (before.1.parsedAccepts = selectedAccept)) source.verify packet before.1.server before.1.environment before.2 privateBefore
  have observed := congrArg (Functor.map (fun result => ((result.1.1.1.1,
    ({(evaluate before).1 with server := result.1.1.1.2,environment := result.1.1.2,parsedAccepts := before.1.parsedAccepts+1},result.1.2)),result.2))) core
  simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.accept,
    RegistrationNativePlatformPublicFrontend.handler,RegistrationNativePlatformPublicFrontend.executeLocal,
    bind_apply,get_apply,modify_apply,pure_bind,
    RegistrationNativePlatformSecretWordFrontend.serverOpen,RegistrationNativePlatformPublicFrontend.serverOpen,
    StateT.run,simulateQ_map,map_apply,Functor.map_map,
    RegistrationNativePlatformSecretWordOrdinary.evaluate,RegistrationNativeSecretWordMessage.State.eval,
    RegistrationNativePlatformLorIdealAcceptLift.nativeBase,QueryImpl.simulateQ_compose,Prod.map_def,id_eq] at observed ⊢
  convert observed using 1
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendAccept.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendAccept.accept_source
