import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceResponseFields
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall
/-! A successful current Server build appends exactly the stored Ready descriptor to its own installation trace under any persistent Word interpretation. The free source receipt retains the original reply, platform state, failed prefixes and full raw ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce
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
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets

variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
open RegistrationNativeSecretWordInstallOrdinals (messages)
local notation "traceState" => RegistrationNativePlatformLorStatefulSupport.TracedState
  (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "traceTyped" => RegistrationNativePlatformLorStatefulSupport.traced implementation controller


variable (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped
local notation "FullState" => RegistrationNativeLedger.State × traceState

/-- The actual successful response has consumed its same session slot, retaining every private and platform effect. -/
theorem consumed (session : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : FullState)
    (supported : (some response,after) ∈ support ((full (.inl (.inr (.build session payload)))).run before)) :
    after.2.1.1.server.sessions[session]?=some none ∧
      after.2.1.1.server.sessions.length=before.2.1.1.server.sessions.length := by
  obtain ⟨ready,stored,_ciphertext,_identity⟩ := RegistrationNativePlatformLorSourceResponseFields.full setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets (RegistrationNativePlatformLorStatefulSupport.trace implementation)
    serverKeyId bounds session payload response before after supported
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,equal⟩ := supported
  have replyEq : reply=some response := congrArg Prod.fst equal
  have stateEq : current=after.2 := congrArg (fun result => result.2.2) equal
  subst reply
  rw [stateEq] at reached
  have typedCall := RegistrationNativeTargetRawSuccess.build (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped
    session payload response before.2 after.2 reached
  have free := RegistrationNativePlatformLorStatefulSupport.typed_support
    (RegistrationNativePlatformLorStatefulSupport.trace implementation) controller (.inr (.build session (RegistrationNativeRawAdapter.application payload)))
    before.2 (.ok (some (response.keyId,response.serialized)),after.2) typedCall
  have same := RegistrationNativePlatformSecretWordLiveBuild.sessions setup sign view failure allocation erased helper writer reservePeer
    source session (RegistrationNativeRawAdapter.application payload) before.2.1 (.ok (some (response.keyId,response.serialized)),after.2.1) free
  rw [same]
  unfold RegistrationNativeSecretWordServerMaterial.take
  rw [stored]
  exact ⟨List.getElem?_set_self (List.getElem?_eq_some_iff.mp stored).1,List.length_set⟩

/-- No later actual callback path can publish another successful response from that consumed session. -/
theorem no_later {before first last after : FullState} {pre : List RegistrationNativeInterface.Entry}
    (session : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (firstCall : (some response,first) ∈ support ((full (.inl (.inr (.build session payload)))).run before))
    (between : RegistrationNativeSecretWordTargetPath.Path full first pre last)
    (laterPayload : Option Pqxdh.Bytes) (laterResponse : PqxdhServerRegistrationPublication.Response)
    (laterCall : (some laterResponse,after) ∈ support ((full (.inl (.inr (.build session laterPayload)))).run last)) : False := by
  have gone := consumed setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation serverKeyId bounds session payload response before first firstCall
  obtain ⟨ready,stored,_ciphertext,_identity⟩ := RegistrationNativePlatformLorSourceResponseFields.full setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets (RegistrationNativePlatformLorStatefulSupport.trace implementation)
    serverKeyId bounds session laterPayload laterResponse last after laterCall
  have preserved := RegistrationNativePlatformLorSourceSessions.path setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativePlatformLorStatefulSupport.trace implementation) serverKeyId bounds between
  have below := (List.getElem?_eq_some_iff.mp gone.1).1
  have earlier := preserved.2 session below ready stored
  rw [gone.1] at earlier
  cases earlier
private def pick (session : Nat) : RegistrationNativeInterface.Entry → Option PqxdhServerRegistrationPublication.Response
  | ⟨.inl (.inr (.build index _)),some response⟩ => if index=session then some response else none
  | _ => none

omit primitive in
private theorem pick_entry (session : Nat) (entry : RegistrationNativeInterface.Entry)
    (response : PqxdhServerRegistrationPublication.Response) (found : pick session entry=some response) :
    ∃ payload,entry=⟨.inl (.inr (.build session payload)),some response⟩ := by
  rcases entry with ⟨((coin|command)|secrecy),reply⟩
  · cases found
  · cases command with
    | build index payload => cases reply with
      | none => cases found
      | some encoded =>
        simp only [pick] at found
        split at found
        · rename_i same
          simp only [Option.some.injEq] at found
          subst index encoded
          exact ⟨payload,rfl⟩
        · cases found
    | _ => cases found
  · cases found

omit primitive in
private theorem build_source (entries : List RegistrationNativeInterface.Entry) (session : Nat) :
    PqxdhDeploymentTranscript.buildOf (entries.map RegistrationNativeInterface.Entry.erase) session=entries.findSome? (pick session) := by
  simp only [PqxdhDeploymentTranscript.buildOf,List.findSome?_map]
  apply congrArg (fun observe => entries.findSome? observe)
  funext entry
  rcases entry with ⟨((coin|command)|secrecy),reply⟩
  · rfl
  · cases command <;> try rfl
    cases reply <;> rfl
  · rfl

/-- The corrected session lookup returns this very successful response; no earlier success can consume the same one-use slot. -/
theorem lookup {before first last : FullState} {pre : List RegistrationNativeInterface.Entry}
    (earlier : RegistrationNativeSecretWordTargetPath.Path full before pre first)
    (session : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (called : (some response,last) ∈ support ((full (.inl (.inr (.build session payload)))).run first))
    (post : List RegistrationNativeInterface.Entry) :
    PqxdhDeploymentTranscript.buildOf
      ((pre++⟨.inl (.inr (.build session payload)),some response⟩::post).map RegistrationNativeInterface.Entry.erase) session=some response := by
  have absent : pre.findSome? (pick session)=none := by
    apply List.findSome?_eq_none_iff.mpr
    intro entry member
    cases found : pick session entry with
    | none => rfl
    | some encoded =>
      obtain ⟨priorPayload,equal⟩ := pick_entry session entry encoded found
      subst entry
      obtain ⟨leading,trailing,split⟩ := List.mem_iff_append.mp member
      obtain ⟨priorFirst,priorLast,_prior,priorCall,between⟩ := RegistrationNativeSecretWordTargetPath.split full earlier leading _ trailing split
      exact (no_later setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation serverKeyId bounds session priorPayload encoded
        priorCall between payload response called).elim
  rw [build_source,List.findSome?_append,absent]
  simp only [List.findSome?_cons,pick,ite_true,Option.or]

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce.consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce.consumed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce.no_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce.no_later

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuildOnce.lookup
