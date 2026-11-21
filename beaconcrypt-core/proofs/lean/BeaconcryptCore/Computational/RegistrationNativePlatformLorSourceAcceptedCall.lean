-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetAcceptedCall
/-! The original full ledger supplies its exact successful parsed accept on the same actual source path under an arbitrary persistent Word interpreter. The genuine early-provider leaf contract derives the absent selected getter marker at that prefix; no profile correspondence or desired source result is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptedCall
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
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


variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller



/-- Every full run has the literal chronological path recorded by its original ledger. -/
theorem full_path (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform Private)
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    RegistrationNativeSecretWordTargetPath.Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
      (RegistrationNativeLedger.empty,before) result.2.1.transcript result.2 := by
  obtain ⟨entries,actual⟩ := RegistrationNativeSecretWordTargetPath.program
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
    (RegistrationNativeInterface.asModeO mode work) (RegistrationNativeLedger.empty,before) result supported
  have recorded := RegistrationNativeSecretWordTargetPath.records _ (fun current => current.1.transcript)
    (fun query current next reached => RegistrationNativeLedgerJournal.handler_records _ setup.source.crypto
      (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query current next reached) actual
  simp only [RegistrationNativeLedger.empty,List.nil_append] at recorded
  rw [←recorded] at actual
  exact actual

variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
include contract
/-- Canonical successful acceptance is cut at its actual parsed ordinal, before its first selected getter, retaining the same full source suffix. -/
theorem accepted_call (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform Private)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : (kem before.2).2=none)
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (session : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.2.1.transcript session selectedAccept) :
    ∃ call : RegistrationNativeSecretWordTargetCall.Call (State source Platform Private) typed
      (fun current => current.1.1.parsedAccepts) wire selectedAccept result.2.1.transcript session,
      (kem call.first.2).2=none ∧
      ∃ first last : RegistrationNativeLedger.State × State source Platform Private,
        call.first=first.2 ∧ call.last=last.2 ∧
        RegistrationNativeSecretWordTargetPath.Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
          (RegistrationNativeLedger.empty,before) call.pre first ∧
        (some session,last) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
          (.inl (.inr (.accept call.raw)))).run first) ∧
        RegistrationNativeSecretWordTargetPath.Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
          last call.post result.2 := by
  have actual := full_path setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds mode work before result supported
  obtain ⟨call,first,last,firstEq,lastEq,prior,called,suffix⟩ :=
    RegistrationNativeRegistrationTargetAcceptedCall.accepted_call setup.source.crypto wire typed (fun current => current.1.1.parsedAccepts)
      (RegistrationNativePlatformLorSourceAlignment.typed_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation)
      serverKeyId bounds before initialCounter result.2 actual session selectedAccept accepted
  have phase := RegistrationNativePlatformLorSourcePhase.path_keeps setup selected pairs publicKey challenge implementation kem input contract
    checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds prior (fun _ => initialMarker)
  have ordinal : first.2.1.1.parsedAccepts=selectedAccept := by
    rw [←firstEq]
    exact call.selected
  have absent : (kem call.first.2).2=none := by
    rw [firstEq]
    exact phase (Nat.le_of_eq ordinal)
  exact ⟨call,absent,first,last,firstEq,lastEq,prior,called,suffix⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptedCall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptedCall.full_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptedCall.full_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptedCall.accepted_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptedCall.accepted_call
