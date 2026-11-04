-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetained
/-! The literal selected source accept retains its own collector through the common platform state and arbitrary persistent private interpretation. Individual source KEM and actual reservation footprints supply the local retained-control contracts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady Message)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformLorSourceRetainedControl (close)
open RegistrationNativePlatformLorIdealStateLift (interpret)
open RegistrationNativePlatformLorSourcePlatform (extend)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform Private : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (reserve : StateT Platform ProbComp Bool)
local notation "localImpl" => extend (Platform := Platform) implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal true
local notation "reservation" => interpret implementation (RegistrationNativePlatformSecretWordOrdinary.platform reserve)
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

/-- The same common-P accept reassembles exactly into its local retained-control state. -/
theorem local_factor (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (server : ServerState) (env : Environment) (previous : Platform) (before : Private) :
    (close (RegistrationNativePlatformSecretWordOpen.accept localImpl reservation setup checks verify packet)).run (server,(env,(previous,before))) =
      (fun result => (result.1.1.1.1,(result.1.1.1.2,(result.1.1.2,(result.1.2,result.2))))) <$>
        (simulateQ implementation
          ((((RegistrationNativePlatformSecretWordOpen.accept (RegistrationNativePlatformSecretWordFrontendView.wordLocal true)
            (RegistrationNativePlatformSecretWordOrdinary.platform reserve) setup checks verify packet).run server).run env).run previous)).run before := by
  have natural := RegistrationNativePlatformSecretWordOpenMap.accept
    (RegistrationNativePlatformLorIdealStateLift.hom (P := Platform) implementation)
    (RegistrationNativePlatformSecretWordFrontendView.wordLocal true)
    (RegistrationNativePlatformSecretWordOrdinary.platform reserve) setup checks verify packet server env
  rw [RegistrationNativePlatformLorSourcePlatform.local_source] at natural
  have ran := congrArg (fun action => action.run (previous,before)) natural
  have mapped := congrArg (Functor.map (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2))))) ran.symm
  simpa only [RegistrationNativePlatformLorSourceRetainedControl.close,RegistrationNativePlatformLorIdealStateLift.interpret,StateT.run,Functor.map_map] using mapped

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before=Prod.map f id <$> work before := StateT.run_map _ _ _

/-- Successful literal frontend support supplies the same local result, server, environment and reached public/private state. -/
theorem accept_support (source : RegistrationNativeMldsa.Source) (selectedAccept : Nat)
    (packet : registration.InitPacket) (before after : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (privateBefore privateAfter : Private) (handle : Nat) (selected : before.1.parsedAccepts=selectedAccept)
    (supported : ((.ok (some handle),after),privateAfter) ∈ support
      ((simulateQ implementation ((RegistrationNativePlatformSecretWordFrontend.accept setup checks source selectedAccept reserve packet).run before)).run privateBefore)) :
    (.ok (some handle),(after.1.server,(after.1.environment,(after.2,privateAfter)))) ∈ support
      ((close (RegistrationNativePlatformSecretWordOpen.accept localImpl reservation setup checks source.verify packet)).run
        (before.1.server,(before.1.environment,(before.2,privateBefore)))) := by
  simp only [RegistrationNativePlatformSecretWordFrontend.accept,StateT.run_bind,StateT.run_get,StateT.run_modify,pure_bind,selected,decide_true] at supported
  simp only [RegistrationNativePlatformSecretWordFrontend.serverOpen,StateT.run,simulateQ_map,map_apply,support_map] at supported
  obtain ⟨raw,called,equal⟩ := supported
  have projected := Set.mem_image_of_mem (fun result =>
    (result.1.1.1.1,(result.1.1.1.2,(result.1.1.2,(result.1.2,result.2))))) called
  have factor := local_factor setup checks implementation reserve source.verify packet before.1.server before.1.environment before.2 privateBefore
  simp only [StateT.run] at factor
  rw [←support_map,←factor] at projected
  have replyEq := congrArg (fun result => result.1.1) equal
  have serverEq := congrArg (fun result => result.1.2.1.server) equal
  have envEq := congrArg (fun result => result.1.2.1.environment) equal
  have platformEq := congrArg (fun result => result.1.2.2) equal
  have privateEq := congrArg (fun result => result.2) equal
  dsimp only [Prod.map,id] at replyEq serverEq envEq platformEq privateEq
  simpa only [StateT.run,replyEq,serverEq,envEq,platformEq,privateEq] using projected

def Retained (crypto : Pqxdh.Crypto) (packet : registration.InitPacket) (challenge : MlKem768Ciphertext)
    (server : ServerState) (handle : Nat) : Prop :=
  ∃ (ready : ServerReady) (authenticated : registration.AuthenticatedInit)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding),
    server.sessions[handle]?=some (some ready) ∧ ready.reference=RegistrationNativeSecretWordServerRoot.message collected ∧
    ready.agreement=⟨PqxdhServerClearedRoot.pending authenticated.binding.server_pin.binding collected.plain,authenticated.binding⟩ ∧
    collected.plain.verified=RegistrationRootInput.verified packet authenticated ∧
    collected.plain.ciphertext=PqxdhAcceptedRegistration.ciphertextArray challenge ∧
    collected.kem=RegistrationNativeSecretWord.Word.atom ∧ ready.reference.kem=RegistrationNativeSecretWord.Word.atom ∧
    PqxdhDeploymentTranscript.acceptedKeys crypto (RegistrationRootInput.candidate packet)=some (collected.plain.verified.identity,collected.plain.verified.keys)

variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option RegistrationNativeSecretWord.Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
include contract

/-- Every successful selected source accept stores its own marked ciphertext, atom, verified packet and agreement. -/
theorem accept_retained (source : RegistrationNativeMldsa.Source) (selectedAccept : Nat)
    (packet : registration.InitPacket) (before after : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (privateBefore privateAfter : Private) (handle : Nat) (selectedCall : before.1.parsedAccepts=selectedAccept)
    (initial : (kem privateBefore).2=none)
    (matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet)).map (fun keys => keys.2.pqKey)=some publicKey)
    (supported : ((.ok (some handle),after),privateAfter) ∈ support
      ((simulateQ implementation ((RegistrationNativePlatformSecretWordFrontend.accept setup checks source selectedAccept reserve packet).run before)).run privateBefore)) :
    Retained setup.source.crypto packet challenge after.1.server handle := by
  have localSupport := accept_support setup checks implementation reserve source selectedAccept packet before after privateBefore privateAfter handle selectedCall supported
  exact RegistrationNativePlatformLorSourceRetained.accept_retained setup checks selected pairs publicKey challenge
    (extend implementation) (fun current : Platform × Private => kem current.2) input
    (RegistrationNativePlatformLorSourcePlatform.lifted_contract implementation kem input _ contract)
    source.verify reservation (fun first result called => congrArg Prod.snd
      (RegistrationNativePlatformLorSourcePlatform.reservation_kem implementation kem input _ contract reserve first result called))
    packet (before.1.server,(before.1.environment,(before.2,privateBefore)))
    (after.1.server,(after.1.environment,(after.2,privateAfter))) handle initial matching localSupport

variable {E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reservePeer : StateT Platform ProbComp Bool) (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserve reservePeer reserveFrame erased helper writer
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private

/-- The literal complete typed dispatcher supplies that same successful selected accept receipt. -/
theorem typed_retained (packet : registration.InitPacket) (before after : State source Platform Private)
    (handle : Nat) (selectedCall : before.1.1.parsedAccepts=selectedAccept) (initial : (kem before.2).2=none)
    (matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet)).map (fun keys => keys.2.pqKey)=some publicKey)
    (supported : (.ok (some handle),after) ∈ support
      ((RegistrationNativePlatformLorStatefulSupport.typed implementation controller (.inr (.accept packet))).run before)) :
    Retained setup.source.crypto packet challenge after.1.1.server handle := by
  rw [RegistrationNativePlatformLorStatefulSupport.typed_run,support_map] at supported
  obtain ⟨⟨⟨reply,current⟩,reachedPrivate⟩,called,equal⟩ := supported
  cases equal
  exact accept_retained setup checks implementation reserve selected pairs publicKey challenge kem input contract source selectedAccept
    packet before.1 current before.2 reachedPrivate handle selectedCall initial matching called

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend.local_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend.local_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend.accept_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend.accept_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend.accept_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend.accept_retained

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend.typed_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend.typed_retained
