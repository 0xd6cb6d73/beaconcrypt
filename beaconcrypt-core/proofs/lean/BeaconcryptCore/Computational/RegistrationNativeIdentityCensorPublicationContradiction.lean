-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleFirst
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativeStageTraceCut
import BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
/-! An actual earlier successful publication of the selected unsigned tuple contradicts the original same-run first-publication failure, with owner-index equality derived from genuine handles. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationContradiction
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeIdentityBundlePhase (Keeps Closed)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


variable {V : Type}
/-- A source publication of the selected one-time unsigned tuple strictly before the original accepted attempt contradicts that same attempt's original first-publication failure. -/
theorem earlier (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (call : Call TypedSpec (Whole n KemSK Platform source)) (split : attempt.leading=leading++call::trailing)
    (index : Nat) (bytes : Pqxdh.Bytes)
    (marked : RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply=some (.bundle index (some bytes)))
    (owner : RegistrationNativeIdentityFrontend.Owner source) (found : (owners call.before)[index]?=some owner)
    (handle : owner.identity.handle=attempt.finalOwner.identity.handle)
    (oneTime : PqxdhEd25519EufCma.X25519PublicKey)
    (selected : PqxdhEd25519EufCma.oneTimeMessage oneTime=PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime)
    (tuple : (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) bytes).bind
      PqxdhDeploymentPublishedTuple.candidateTuple=some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,oneTime,owner.kemPublic⟩) : False := by
  have path := RegistrationNativeFullRegistrationJournal.path setup.source.crypto wire serverKeyId bounds actual mode work before result reached
  have atAccept := path
  rw [attempt.split] at atAccept
  obtain ⟨beforeAccept,_called,_afterAccept⟩ := RegistrationNativeStageTraceCut.split actual attempt.leading attempt.trailing attempt.call atAccept
  have published := RegistrationNativeIdentityBundleFirst.published setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer attempt.leading leading trailing call beforeAccept split index bytes marked
  have member : call ∈ result.2.2.2 := by
    have same := attempt.split
    rw [split] at same
    simp only [same,List.mem_append,List.mem_cons,true_or,or_true]
  have fixed := RegistrationNativePlatformIdentityCtxKeyJournal.full_same_handle setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty result reached call member index owner found
      attempt.finalOwner (List.mem_of_getElem? attempt.finalFound) handle.symm
  obtain ⟨stored,storedAt,storedFields⟩ := RegistrationNativePlatformIdentityCtxKeyJournal.full_captured setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before result reached call member index owner found
  have unique := RegistrationNativePlatformIdentityCtxKeyJournal.full_distinct setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty result reached
  let handles := RegistrationNativeIdentityHistorySync.handles (owners result.2.2.1)
  have atIndex : handles[index]?=some owner.identity.handle := by
    simp only [handles,RegistrationNativeIdentityHistorySync.handles,List.getElem?_map,storedAt,Option.map_some]
    exact congrArg some (congrArg (fun current=>current.1.handle) storedFields)
  have atOwner : handles[attempt.ownerIndex]?=some owner.identity.handle := by
    simp only [handles,RegistrationNativeIdentityHistorySync.handles,List.getElem?_map,attempt.finalFound,Option.map_some]
    exact congrArg some handle.symm
  have indices : index=attempt.ownerIndex :=
    (show handles.Nodup from unique).eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp atIndex).1 (atIndex.trans atOwner.symm)
  have tupleEq : (⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,oneTime,owner.kemPublic⟩ : PqxdhEd25519EufCma.Phase1KeyTuple)=attempt.decoded :=
    PqxdhEd25519EufCma.Phase1KeyTuple.ext'
      ((congrArg (fun current=>PqxdhPhase2InputBytes.word current.2.1) fixed).symm.trans issued.fixedPrekey.symm)
      (PqxdhEd25519EufCma.oneTimeMessage_injective selected)
      ((congrArg (fun current=>current.2.2) fixed).symm.trans issued.fixedPq.symm)
  have actualPublication := published.trans (tuple.trans (congrArg some tupleEq))
  rw [indices] at actualPublication
  exact attempt.unpublished actualPublication

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationContradiction

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationContradiction.earlier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationContradiction.earlier
