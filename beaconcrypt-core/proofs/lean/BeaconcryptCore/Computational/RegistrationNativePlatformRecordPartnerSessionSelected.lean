import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! Every Ready in the corrected source roster either survives an earlier slot or originates at the actual successful accept returning that same session handle. Parsed attempt counters remain a separate source coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected
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


variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
variable (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State source Platform Private
include contract

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

/-- A retained atom's original successful raw acceptance is the selected parsed call, with its actual decoding retained. -/
theorem accept_counter (raw : Pqxdh.Bytes) (before after : FullState) (handle : Nat)
    (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (supported : (some handle,after) ∈ support ((full (.inl (.inr (.accept raw)))).run before))
    (stored : after.2.1.1.server.sessions[handle]?=some (some ready))
    (atom : ready.reference.kem=RegistrationNativeSecretWord.Word.atom) :
    ∃ packet, RegistrationNativeWire.readInit wire raw=some packet ∧ before.2.1.1.parsedAccepts=selectedAccept := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,called,equal⟩ := supported
  have replyEq : reply=some handle := congrArg Prod.fst equal
  subst reply
  cases equal
  cases decoded : RegistrationNativeWire.readInit wire raw with
  | none =>
    simp only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,decoded,
      simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at called
    cases called
  | some packet =>
    simp only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,decoded,
      simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at called
    obtain ⟨⟨outcome,reached⟩,possible,returned⟩ := called
    cases actual : outcome with
    | fail error | div => simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at returned;cases returned.1
    | ok accepted =>
      simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at returned
      obtain ⟨rfl,rfl⟩ := returned
      refine ⟨packet,rfl,?_⟩
      exact RegistrationNativePlatformRecordPartnerAccept.typed_counter setup checks implementation reserveRegistration
        selected pairs publicKey challenge kem input contract wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reservePeer reserveFrame erased helper writer packet before.2 reached handle ready stored atom (by simpa only [actual] using possible)

omit primitive contract in
private theorem parsed_entry (transcript before after : List RegistrationNativeInterface.Entry)
    (raw : Pqxdh.Bytes) (session parsed : Nat) (packet : registration.InitPacket)
    (recorded : transcript=before++⟨.inl (.inr (.accept raw)),some session⟩::after)
    (decoded : RegistrationNativeWire.readInit wire raw=some packet)
    (counted : RegistrationNativeEvents.parsedAcceptCount wire before=parsed) :
    (transcript.filter (RegistrationNativeEvents.parsedAccept wire))[parsed]?=
      some ⟨.inl (.inr (.accept raw)),some session⟩ := by
  have kept : RegistrationNativeEvents.parsedAccept wire ⟨.inl (.inr (.accept raw)),some session⟩=true := by
    simp only [RegistrationNativeEvents.parsedAccept,decoded,Option.isSome_some]
  simp only [recorded,List.filter_append,List.filter_cons,kept,ite_true]
  have size : (before.filter (RegistrationNativeEvents.parsedAccept wire)).length=parsed := counted
  rw [←size,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero]

omit primitive contract in
/-- Equal parsed scanner positions identify the successful session replies without identifying session and attempt indices. -/
theorem same_session (transcript pre post : List RegistrationNativeInterface.Entry) (raw : Pqxdh.Bytes)
    (handle session parsed : Nat) (packet : registration.InitPacket)
    (recorded : transcript=pre++⟨.inl (.inr (.accept raw)),some handle⟩::post)
    (decoded : RegistrationNativeWire.readInit wire raw=some packet)
    (counted : RegistrationNativeEvents.parsedAcceptCount wire pre=parsed)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire transcript session parsed) : handle=session := by
  obtain ⟨before,otherRaw,otherPacket,after,split,otherCount,otherDecoded,_first⟩ := accepted
  have first := parsed_entry wire transcript pre post raw handle parsed packet recorded decoded counted
  have second := parsed_entry wire transcript before after otherRaw session parsed otherPacket split otherDecoded otherCount
  have equal := Option.some.inj (first.symm.trans second)
  cases equal
  rfl
/-- The actual atom-bearing capability has a same-run selected parsed accept, with its successful session reply retained separately. -/
theorem atom_origin {before after : FullState} {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path full before entries after)
    (emptySessions : before.2.1.1.server.sessions=[]) (emptyTranscript : before.1.transcript=[])
    (initialCounter : before.2.1.1.parsedAccepts=0)
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : after.2.1.1.server.sessions[handle]?=some (some ready))
    (atom : ready.reference.kem=RegistrationNativeSecretWord.Word.atom) :
    ∃ (pre post : List RegistrationNativeInterface.Entry) (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (first last : FullState),
      entries=pre++⟨.inl (.inr (.accept raw)),some handle⟩::post ∧
      RegistrationNativeSecretWordTargetPath.Path full before pre first ∧
      (some handle,last) ∈ support ((full (.inl (.inr (.accept raw)))).run first) ∧
      last.2.1.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeSecretWordTargetPath.Path full last post after ∧
      RegistrationNativeWire.readInit wire raw=some packet ∧
      RegistrationNativeEvents.parsedAcceptCount wire pre=selectedAccept := by
  obtain ⟨pre,post,raw,first,last,recorded,earlier,called,retained,later⟩ :=
    RegistrationNativePlatformRecordPartnerSessions.initialized_origin setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds path emptySessions handle ready stored
  obtain ⟨packet,decoded,chosen⟩ := accept_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation selected pairs publicKey challenge kem input contract
    serverKeyId bounds raw first last handle ready called retained atom
  have consistent : before.2.1.1.parsedAccepts=0+RegistrationNativeEvents.parsedAcceptCount wire before.1.transcript := by
    rw [initialCounter,emptyTranscript]
    rfl
  have counted := RegistrationNativePlatformLorSourceCounter.path_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds 0 earlier consistent
  have records := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (RegistrationNativeLedgerJournal.handler_records (RegistrationNativeRawAdapter.handler wire typed) setup.source.crypto
      (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds) earlier
  rw [emptyTranscript,List.nil_append] at records
  rw [records,Nat.zero_add] at counted
  exact ⟨pre,post,raw,packet,first,last,recorded,earlier,called,retained,later,decoded,counted.symm.trans chosen⟩

/-- A later original designation of the selected parsed call uses precisely this capability's returned session, even after failed attempts. -/
theorem atom_session {before middle after : FullState} {leading trailing : List RegistrationNativeInterface.Entry}
    (earlier : RegistrationNativeSecretWordTargetPath.Path full before leading middle)
    (later : RegistrationNativeSecretWordTargetPath.Path full middle trailing after)
    (emptySessions : before.2.1.1.server.sessions=[]) (emptyTranscript : before.1.transcript=[])
    (initialCounter : before.2.1.1.parsedAccepts=0)
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : middle.2.1.1.server.sessions[handle]?=some (some ready))
    (atom : ready.reference.kem=RegistrationNativeSecretWord.Word.atom)
    (session : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire after.1.transcript session selectedAccept) : handle=session := by
  obtain ⟨pre,post,raw,packet,first,last,recorded,_prior,_called,_retained,_suffix,decoded,counted⟩ :=
    atom_origin setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer implementation selected pairs publicKey challenge kem input contract serverKeyId bounds
      earlier emptySessions emptyTranscript initialCounter handle ready stored atom
  have firstRecords := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (RegistrationNativeLedgerJournal.handler_records (RegistrationNativeRawAdapter.handler wire typed) setup.source.crypto
      (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds) earlier
  have lastRecords := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (RegistrationNativeLedgerJournal.handler_records (RegistrationNativeRawAdapter.handler wire typed) setup.source.crypto
      (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds) later
  have combined : after.1.transcript=pre++⟨.inl (.inr (.accept raw)),some handle⟩::(post++trailing) := by
    rw [lastRecords,firstRecords,emptyTranscript,List.nil_append,recorded,List.append_assoc]
    rfl
  exact same_session wire after.1.transcript pre (post++trailing) raw handle session selectedAccept packet combined decoded counted accepted

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected.accept_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected.accept_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected.same_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected.same_session

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected.atom_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected.atom_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected.atom_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessionSelected.atom_session
