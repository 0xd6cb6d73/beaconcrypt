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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuild
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

private def serverHandle (entry : RegistrationNativeInterface.Entry) : Option PqxdhDeploymentInterface.Handle :=
  match (PqxdhRecordLiftInterface.Role.server), entry with
  | .server, ⟨.inl (.inr (.build _ _)),some response⟩ => some (.peer response.keyId)
  | .beacon, ⟨.inl (.inr (.finish owner _)),some _⟩ => some (.owner owner)
  | _, _ => none

omit primitive in
private theorem build_cut (entries : List RegistrationNativeInterface.Entry) (ordinal : Nat) (keyId : U64)
    (found : (RegistrationNativeInstallOrdinals.handles .server entries)[ordinal]?=some (.peer keyId)) :
    ∃ (pre post : List RegistrationNativeInterface.Entry) (session : Nat) (payload : Option Pqxdh.Bytes)
      (response : PqxdhServerRegistrationPublication.Response),
      entries=pre++⟨.inl (.inr (.build session payload)),some response⟩::post ∧ response.keyId=keyId ∧
      (RegistrationNativeInstallOrdinals.handles .server pre).length=ordinal := by
  obtain ⟨pre,entry,post,recorded,mapped,counted⟩ := filterMap_cut serverHandle entries ordinal (.peer keyId) found
  cases entry with
  | mk query reply => cases query with
    | inr secrecy => cases mapped
    | inl request => cases request with
      | inl coin => cases mapped
      | inr command => cases command with
        | build session payload => cases reply with
          | none => cases mapped
          | some response =>
            have equal : response.keyId=keyId := by
              injection mapped with peerEq
              exact PqxdhDeploymentInterface.Handle.peer.inj peerEq
            exact ⟨pre,post,session,payload,response,recorded,equal,counted⟩
        | _ => cases mapped

variable (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped
local notation "FullState" => RegistrationNativeLedger.State × traceState

/-- The exact successful Server installation ordinal comes from its own moved-token build and original session handle. -/
theorem from_ordinal (candidate : MlKemSharedSecret) (before : traceState) (initialTrace : before.2.1.events=[])
    {after : FullState} {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path full (RegistrationNativeLedger.empty,before) entries after)
    (ordinal : Nat) (message : Message) (keyId : U64)
    (installed : RegistrationNativeSecretWordInstallOrdinals.At .server after.2.2.1.events after.1.transcript ordinal message (.peer keyId)) :
    ∃ (pre post : List RegistrationNativeInterface.Entry) (session : Nat) (payload : Option Pqxdh.Bytes)
      (response : PqxdhServerRegistrationPublication.Response) (first last : FullState)
      (ready : RegistrationNativeSecretWordMessage.ServerReady),
      entries=pre++⟨.inl (.inr (.build session payload)),some response⟩::post ∧ response.keyId=keyId ∧
      RegistrationNativeSecretWordTargetPath.Path full (RegistrationNativeLedger.empty,before) pre first ∧
      (some response,last) ∈ support ((full (.inl (.inr (.build session payload)))).run first) ∧
      RegistrationNativeSecretWordTargetPath.Path full last post after ∧
      first.2.1.1.server.sessions[session]?=some (some ready) ∧ ready.reference=message := by
  have records := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (RegistrationNativeLedgerJournal.handler_records (RegistrationNativeRawAdapter.handler (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped)
      setup.source.crypto (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds) path
  simp only [RegistrationNativeLedger.empty,List.nil_append] at records
  have handleAt := installed.2
  rw [records] at handleAt
  obtain ⟨pre,post,session,payload,response,recorded,key,count⟩ := build_cut entries ordinal keyId handleAt
  obtain ⟨first,last,earlier,called,later⟩ := RegistrationNativeSecretWordTargetPath.split full path pre _ post recorded
  obtain ⟨ready,stored,_ciphertext,_identity⟩ := RegistrationNativePlatformLorSourceResponseFields.full setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets (RegistrationNativePlatformLorStatefulSupport.trace implementation)
    serverKeyId bounds session payload response first last called
  have added := RegistrationNativePlatformLorSourceInstallPeer.full setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds session payload response first last ready stored called
  obtain ⟨tail,suffix⟩ := RegistrationNativePlatformLorSourceInstall.path_suffix setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds .server later
  have prefixRecords := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (RegistrationNativeLedgerJournal.handler_records (RegistrationNativeRawAdapter.handler (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped)
      setup.source.crypto (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds) earlier
  simp only [RegistrationNativeLedger.empty,List.nil_append] at prefixRecords
  have counted := RegistrationNativePlatformLorSourceInstall.path_counts setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation candidate serverKeyId bounds before initialTrace earlier .server
  simp only [RegistrationNativeInstallOrdinals.Counts,RegistrationNativePlatformLorSourceInstall.events,
    RegistrationNativeSecretWordInstallOrdinals.messages_eval,List.length_map,prefixRecords] at counted
  have position : (messages .server first.2.2.1.events).length=ordinal := counted.trans count
  have joined : messages .server after.2.2.1.events=messages .server first.2.2.1.events++ready.reference::tail := by
    rw [suffix,added,List.append_assoc]
    rfl
  have selected := installed.1
  rw [joined,←position,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero] at selected
  have same : ready.reference=message := Option.some.inj selected
  exact ⟨pre,post,session,payload,response,first,last,ready,recorded,key,earlier,called,later,stored,same⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuild.from_ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBuild.from_ordinal
