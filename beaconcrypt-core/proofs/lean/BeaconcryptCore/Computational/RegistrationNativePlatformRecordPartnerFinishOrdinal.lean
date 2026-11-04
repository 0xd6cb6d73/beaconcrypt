import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishOrdinal
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


omit primitive in
private theorem filterMap_cut {X Y : Type} (f : X → Option Y) (items : List X) (index : Nat) (value : Y)
    (found : (items.filterMap f)[index]?=some value) :
    ∃ before item after, items=before++item::after ∧ f item=some value ∧ (before.filterMap f).length=index := by
  induction items generalizing index with
  | nil => cases found
  | cons head tail ih =>
    cases actual : f head with
    | none =>
      simp only [List.filterMap_cons,actual] at found
      obtain ⟨before,item,after,recorded,selected,counted⟩ := ih index found
      exact ⟨head::before,item,after,by rw [recorded];rfl,selected,by simp only [List.filterMap_cons,actual];exact counted⟩
    | some output =>
      cases index with
      | zero =>
        simp only [List.filterMap_cons,actual,List.getElem?_cons_zero,Option.some.injEq] at found
        subst output
        exact ⟨[],head,tail,rfl,actual,rfl⟩
      | succ index =>
        simp only [List.filterMap_cons,actual,List.getElem?_cons_succ] at found
        obtain ⟨before,item,after,recorded,selected,counted⟩ := ih index found
        exact ⟨head::before,item,after,by rw [recorded];rfl,selected,by simp only [List.filterMap_cons,actual,List.length_cons,counted]⟩

private def ownerHandle (entry : RegistrationNativeInterface.Entry) : Option PqxdhDeploymentInterface.Handle :=
  match (PqxdhRecordLiftInterface.Role.beacon), entry with
  | .server, ⟨.inl (.inr (.build _ _)),some response⟩ => some (.peer response.keyId)
  | .beacon, ⟨.inl (.inr (.finish owner _)),some _⟩ => some (.owner owner)
  | _, _ => none

omit primitive in
private theorem finish_cut (entries : List RegistrationNativeInterface.Entry) (ordinal owner : Nat)
    (found : (RegistrationNativeInstallOrdinals.handles .beacon entries)[ordinal]?=some (.owner owner)) :
    ∃ (pre post : List RegistrationNativeInterface.Entry) (raw bytes : Pqxdh.Bytes),
      entries=pre++⟨.inl (.inr (.finish owner raw)),some bytes⟩::post ∧
      (RegistrationNativeInstallOrdinals.handles .beacon pre).length=ordinal := by
  obtain ⟨pre,entry,post,recorded,mapped,counted⟩ := filterMap_cut ownerHandle entries ordinal (.owner owner) found
  cases entry with
  | mk query reply => cases query with
    | inr secrecy => cases mapped
    | inl request => cases request with
      | inl coin => cases mapped
      | inr command => cases command with
        | finish index raw => cases reply with
          | none => cases mapped
          | some bytes =>
            have equal : index=owner := by
              injection mapped with ownerEq
              exact PqxdhDeploymentInterface.Handle.owner.inj ownerEq
            subst index
            exact ⟨pre,post,raw,bytes,recorded,counted⟩
        | _ => cases mapped

variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
variable (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped
local notation "FullState" => RegistrationNativeLedger.State × traceState

private theorem typed_finish (owner : Nat) (raw bytes : Pqxdh.Bytes) (before after : FullState)
    (supported : (some bytes,after) ∈ support ((full (.inl (.inr (.finish owner raw)))).run before)) :
    (.ok (some bytes),after.2) ∈ support ((traceTyped (.inr (.finish owner
      (RegistrationNativeWire.readResponse (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) raw)))).run before.2) := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,called,equal⟩ := supported
  have replyEq : reply=some bytes := congrArg Prod.fst equal
  have stateEq : current=after.2 := congrArg (fun result => result.2.2) equal
  subst reply
  rw [stateEq] at called
  simp only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,
    simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at called
  obtain ⟨⟨outcome,reached⟩,possible,returned⟩ := called
  cases actual : outcome with
  | fail error | div => simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at returned;cases returned.1
  | ok optional =>
    simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at returned
    obtain ⟨rfl,rfl⟩ := returned
    simpa only [actual] using possible

include contract in
/-- Every actual successful beacon ordinal carrying the atom belongs to the selected original owner, including both scalar paths. -/
theorem owner_of_ordinal (candidate : MlKemSharedSecret) (before : traceState) (initialTrace : before.2.1.events=[])
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2.2).1.keys=[])
    {after : FullState} {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path full (RegistrationNativeLedger.empty,before) entries after)
    (ordinal : Nat) (message : Message) (owner : Nat)
    (installed : RegistrationNativeSecretWordInstallOrdinals.At .beacon after.2.2.1.events after.1.transcript ordinal message (.owner owner))
    (atom : message.kem=RegistrationNativeSecretWord.Word.atom) : owner=selected := by
  have records := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (RegistrationNativeLedgerJournal.handler_records (RegistrationNativeRawAdapter.handler (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped)
      setup.source.crypto (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds) path
  simp only [RegistrationNativeLedger.empty,List.nil_append] at records
  have handleAt := installed.2
  rw [records] at handleAt
  obtain ⟨pre,post,raw,bytes,recorded,count⟩ := finish_cut entries ordinal owner handleAt
  obtain ⟨first,last,earlier,called,later⟩ := RegistrationNativeSecretWordTargetPath.split full path pre _ post recorded
  have typedCall := typed_finish setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation serverKeyId bounds owner raw bytes first last called
  obtain ⟨added,addedEq,addedCount⟩ := RegistrationNativePlatformLorSourceInstall.typed_count setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation (.inr (.finish owner
      (RegistrationNativeWire.readResponse (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) raw))) first.2 (.ok (some bytes),last.2) typedCall .beacon
  have singleton : added.length=1 := by
    simpa only [RegistrationNativeInstallTypedEntry.entry,RegistrationNativeRawAdapter.resultOption,
      RegistrationNativeInstallOrdinals.handles,List.filterMap_cons,List.filterMap_nil,List.length_cons,List.length_nil] using addedCount
  obtain ⟨tail,suffix⟩ := RegistrationNativePlatformLorSourceInstall.path_suffix setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds .beacon later
  have prefixRecords := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (RegistrationNativeLedgerJournal.handler_records (RegistrationNativeRawAdapter.handler (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped)
      setup.source.crypto (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds) earlier
  simp only [RegistrationNativeLedger.empty,List.nil_append] at prefixRecords
  have counted := RegistrationNativePlatformLorSourceInstall.path_counts setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation candidate serverKeyId bounds before initialTrace earlier .beacon
  simp only [RegistrationNativeInstallOrdinals.Counts,RegistrationNativePlatformLorSourceInstall.events,
    RegistrationNativeSecretWordInstallOrdinals.messages_eval,List.length_map,prefixRecords] at counted
  have position : (messages .beacon first.2.2.1.events).length=ordinal := counted.trans count
  have joined : messages .beacon after.2.2.1.events=messages .beacon first.2.2.1.events++(added++tail) := by
    rw [suffix,addedEq,List.append_assoc]
  have selectedAt := installed.1
  rw [joined,←position,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at selectedAt
  have member : message∈added := by
    cases added with
    | nil => cases singleton
    | cons head rest =>
      have restEmpty : rest=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at singleton;omega)
      subst rest
      simp only [List.singleton_append,List.getElem?_cons_zero,Option.some.injEq] at selectedAt
      exact selectedAt ▸ List.mem_singleton_self head
  have tracedContract := RegistrationNativePlatformLorSourceKemTrace.contract implementation kem input _ contract
  have initialAligned : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.1.beacons (kem before.2.2).1.keys := by
    rw [ownersEmpty,keysEmpty]
    exact RegistrationNativeSecretWordTargetAlignment.empty
  have aligned := RegistrationNativePlatformLorSourceAlignment.path_keeps setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge
    (RegistrationNativePlatformLorStatefulSupport.trace implementation) (fun current => kem current.2) input tracedContract serverKeyId bounds earlier initialAligned
  rw [RegistrationNativePlatformLorStatefulSupport.traced,QueryImpl.flattenStateT_mapStateTBase_apply_run] at typedCall
  exact RegistrationNativePlatformRecordPartnerFinish.frontend setup implementation selected pairs publicKey challenge kem input contract
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) owner (RegistrationNativeWire.readResponse (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) raw)
    first.2 (.ok (some bytes),last.2) typedCall aligned added addedEq message member atom
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishOrdinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishOrdinal.owner_of_ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishOrdinal.owner_of_ordinal
