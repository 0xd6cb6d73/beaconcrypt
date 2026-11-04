-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBornKey
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! Successful source-backed bundle publications remain attached to the same final owner and genuine reserved KEM row under any persistent source interpretation satisfying the individual KEM leaf contract. The complete original ledger, all failures and shared P are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets


variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller

open RegistrationNativeSecretWordTargetRoster (Prefix)
open RegistrationNativeSecretWordTargetPublicationRun (publication Holds)
variable (serverKeyId : U64)
local notation "native" => RegistrationNativeRawAdapter.handler wire typed

omit primitive in
private theorem transport (transcript : List RegistrationNativeInterface.Entry)
    (before after : RegistrationNativePublicOwners.State source)
    (prior : Holds wire transcript before) (preserved : Prefix before after) : Holds wire transcript after := by
  intro entry member index raw published
  obtain ⟨old, packet, found, parsed, key⟩ := prior entry member index raw published
  obtain ⟨current, currentAt, same⟩ := RegistrationNativeSecretWordTargetRoster.lookup before after preserved index old found
  have publicKey : current.view.kemPublic = old.view.kemPublic := congrArg Prod.snd same
  exact ⟨current, packet, currentAt, parsed, by simpa only [publicKey] using key⟩

/-- A successful raw bundle has the actual pre-call owner and its concrete source-decoded PQ payload. -/
theorem raw_bundle (index : Nat) (raw : Pqxdh.Bytes) (before after : State source Platform Private)
    (supported : (some raw, after) ∈ support ((native (.inr (.bundle index))).run before)) :
    ∃ owner packet, before.1.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet owner.view.kemPublic := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, reached⟩, called, equal⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.resultOption] at equal
  | ok optional =>
    simp only [actual, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
    obtain ⟨rfl, rfl⟩ := equal
    rw [actual] at called
    have original := RegistrationNativePlatformLorStatefulSupport.typed_support implementation controller
      (.inr (.bundle index)) before (.ok (some raw), reached) called
    exact RegistrationNativePlatformSecretWordTargetPublication.word_bundle setup selectedOwner index publicPrekey
      reserveFrame reservePackets before.1 reached.1 raw original

include contract in
/-- Every current full step retains earlier source publication receipts and appends its own actual successful bundle receipt. -/
theorem step_keeps (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State source Platform Private)
    (prior : Holds wire before.1.transcript before.2.1.1.beacons)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    Holds wire result.2.1.transcript result.2.2.1.1.beacons := by
  have preserved := RegistrationNativePlatformLorSourceRoster.full_step_prefix setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract
    serverKeyId bounds query before result supported
  have retained := transport source before.1.transcript before.2.1.1.beacons result.2.2.1.1.beacons prior preserved
  have trace := RegistrationNativeLedgerJournal.handler_records native setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId bounds query before result supported
  intro entry member index raw published
  rw [trace, List.mem_append, List.mem_singleton] at member
  rcases member with earlier | rfl
  · exact retained entry earlier index raw published
  · cases query with
    | inr secrecy => cases published
    | inl query =>
      rw [RegistrationNativeTargetLedgerCore.run, support_map] at supported
      obtain ⟨⟨reply, after⟩, called, equal⟩ := supported
      cases equal
      cases query with
      | inl coin => cases published
      | inr command => cases command with
        | bundle requested =>
          cases reply with
          | none => cases published
          | some encoded =>
            simp only [publication, Option.some.injEq, Prod.mk.injEq] at published
            obtain ⟨rfl, rfl⟩ := published
            obtain ⟨old, packet, found, decoded, key⟩ := raw_bundle setup checks source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets implementation
              requested encoded before.2 after called
            obtain ⟨current, currentAt, same⟩ := RegistrationNativeSecretWordTargetRoster.lookup before.2.1.1.beacons after.1.1.beacons preserved requested old found
            have publicKey : current.view.kemPublic = old.view.kemPublic := congrArg Prod.snd same
            exact ⟨current, packet, currentAt, decoded, by simpa only [publicKey] using key⟩
        | _ => cases published

include contract in
/-- The full actual corrected raw execution derives all publication-to-final-owner receipts with no initial owner premise. -/
theorem run_holds (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform Private)
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds wire result.2.1.transcript result.2.2.1.1.beacons := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
    (fun current => Holds wire current.1.transcript current.2.1.1.beacons)
    (fun query current valid next called => step_keeps setup checks source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets selected pairs publicKey challenge implementation kem input contract serverKeyId
      bounds query current valid next called)
    _ (RegistrationNativeLedger.empty, before) _ result supported
  intro entry member
  cases member

omit primitive in
private theorem bundle_mem (transcript : List PqxdhDeploymentInterface.Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf transcript owner = some raw) :
    (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases value
  · cases command with
    | bundle index =>
        cases reply with
        | none => cases value
        | some encoded =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact member
            · cases value
    | _ => cases value
  · cases value

omit primitive in
private theorem erased_bundle (entry : RegistrationNativeInterface.Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (same : entry.erase = (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry)) :
    RegistrationNativeSecretWordTargetPublicationRun.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same


include contract in
/-- Every bundle retained by original public designation has the concrete signed PQ payload of the same final owner. -/
theorem original_bundle (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform Private)
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (index : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript index = some raw) :
    ∃ owner packet, result.2.2.1.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet owner.view.kemPublic := by
  have observed := run_holds setup checks source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets selected pairs publicKey challenge implementation kem input contract serverKeyId
    bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before result supported
  have member := bundle_mem result.2.1.ledger.transcript index raw found
  rw [projected] at member
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  exact observed entry nativeMember index raw (erased_bundle entry index raw erased)

include contract in
/-- Original broad verified-key designation identifies the actual final owner's generated PQ field through the same accepted packet and source publication. -/
theorem designated_public (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform Private)
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (budget : PqxdhDeploymentInterface.Budget) (handle : PqxdhDeploymentInterface.Handle)
    (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget result.2.1.ledger.transcript handle = some target) :
    ∃ owner raw packet keys, result.2.2.1.1.beacons[target.2.val]? = some owner ∧
      PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript target.1.val = some raw ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys ∧
      keys.2.pqKey = owner.view.kemPublic := by
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto _ serverKeyId budget _ handle target designated
  obtain ⟨raw, accepted, keys, published, acceptFound, candidateFound, keysFound, publishedFound, keyFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys setup.source.crypto _ serverKeyId _ handle target.1.val target.2.val plain
  obtain ⟨publishedRaw, bundleFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨owner, publishedPacket, ownerAt, publishedParsed, publishedKey⟩ :=
    original_bundle setup checks source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets selected pairs publicKey challenge implementation kem input contract serverKeyId
      bounds mode work before result supported target.2.val publishedRaw bundleFound
  rw [RegistrationNativeKemPublicTarget.candidate_read wire publishedRaw publishedPacket publishedParsed] at publishedRead
  have pubEq := Option.some.inj publishedRead
  rw [← pubEq] at keyFound
  have actualKey := RegistrationNativeKemPublicTarget.published_key publishedPacket owner.view.kemPublic publishedKey
  have sameKey := Option.some.inj (keyFound.symm.trans actualKey)
  obtain ⟨packet, parsed⟩ := RegistrationNativeParsedTarget.candidate_parsed wire raw accepted candidateFound
  rw [RegistrationNativeKemPublicTarget.candidate_read wire raw packet parsed] at candidateFound
  have acceptedEq := Option.some.inj candidateFound
  rw [← acceptedEq] at keysFound
  exact ⟨owner, raw, packet, keys, ownerAt, acceptFound, parsed, keysFound, sameKey⟩

include contract in
/-- Original designation names the same genuine reserved pair, allowing identical public keys at distinct rows. -/
theorem designated_pair (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (before : State source Platform Private) (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2).1.keys=[])
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (handle : PqxdhDeploymentInterface.Handle) (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget result.2.1.ledger.transcript handle = some target) :
    ∃ owner raw packet keys pair, result.2.2.1.1.beacons[target.2.val]? = some owner ∧
      PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript target.1.val = some raw ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys ∧
      pairs[target.2.val]? = some pair ∧ owner.view.kemHandle = target.2.val ∧ owner.view.kemPublic = pair.1 ∧ keys.2.pqKey = pair.1 := by
  obtain ⟨owner,raw,packet,keys,ownerAt,accepted,decoded,verified,sameKey⟩ :=
    designated_public setup checks source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
      selected pairs publicKey challenge implementation kem input contract serverKeyId bounds mode work before result supported budget handle target designated
  obtain ⟨pair,pairAt,ownerHandle,ownerKey⟩ := RegistrationNativePlatformLorSourceBornKey.full_born_key
    setup checks RegistrationNativePlatformConcreteSource.wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract
    serverKeyId bounds mode work budget bounded reserved before ownersEmpty keysEmpty result supported target.2.val owner ownerAt
  exact ⟨owner,raw,packet,keys,pair,ownerAt,accepted,decoded,verified,pairAt,ownerHandle,ownerKey,sameKey.trans ownerKey⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.raw_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.raw_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.step_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.run_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.original_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.original_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.designated_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.designated_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.designated_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePublication.designated_pair
