import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublication
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun
import BeaconcryptCore.Computational.RegistrationNativePrekeyEvents
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical
/-! The current concrete dynamic publication is attached to the original full native ledger and the retained final owner roster. Constructor extensions, stateful writer failures and later callbacks retain all earlier successful publication receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller



open RegistrationNativeSecretWordPrekeyPublicationRun (publication Holds)
open RegistrationNativeInterface (Entry)
variable (serverKeyId : U64)
local notation "native" => RegistrationNativeRawAdapter.handler wire typed

/-- A successful raw bundle has the actual pre-call owner and its concrete source-decoded PQ payload. -/
theorem raw_bundle (index : Nat) (raw : Pqxdh.Bytes) (before after : State n KemSK source Platform)
    (supported : (some raw, after) ∈ support ((native (.inr (.bundle index))).run before)) :
    ∃ owner packet, before.1.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.view.prekeyPublic) := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, reached⟩, called, equal⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.resultOption] at equal
  | ok optional =>
    simp only [actual, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
    obtain ⟨rfl, rfl⟩ := equal
    rw [actual] at called
    have original := RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller
      (.inr (.bundle index)) before (.ok (some raw), reached) called
    exact RegistrationNativePlatformSecretWordPrekeyPublication.word_bundle setup selectedOwner index publicPrekey
      reserveFrame reservePackets before.1 reached.1 raw original

/-- Each actual full ledger step records the selected owner's unchanged public signed prekey. -/
theorem step_keeps (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source Platform)
    (prior : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.2.1.1.beacons ∧
      Holds wire selectedOwner publicPrekey before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey result.2.2.1.1.beacons ∧
      Holds wire selectedOwner publicPrekey result.2.1.transcript := by
  refine ⟨RegistrationNativePlatformSecretWordPrekeyMask.full_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider outer serverKeyId bounds query before result prior.1 supported, ?_⟩
  have trace := RegistrationNativeLedgerJournal.handler_records native setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query before result supported
  intro entry member raw published
  rw [trace, List.mem_append, List.mem_singleton] at member
  rcases member with earlier | rfl
  · exact prior.2 entry earlier raw published
  · cases query with
    | inr secrecy => cases published
    | inl query =>
        rw [RegistrationNativeTargetLedgerCore.run, support_map] at supported
        obtain ⟨⟨reply, after⟩, reached, equal⟩ := supported
        cases equal
        cases query with
        | inl coin => cases published
        | inr command => cases command with
          | bundle index =>
              cases reply with
              | none => cases published
              | some encoded =>
                  simp only [publication, Option.some.injEq, Prod.mk.injEq] at published
                  obtain ⟨sameOwner, rfl⟩ := published
                  subst index
                  obtain ⟨owner, packet, found, parsed, key⟩ := raw_bundle setup checks source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets selectedOwner encoded before.2 after reached
                  have canonical := prior.1 selectedOwner owner found
                  simp only [RegistrationNativePublicOwnerMask.At, ite_true] at canonical
                  refine ⟨packet, parsed, ?_⟩
                  simpa only [canonical.2, PqxdhPhase2InputBytes.word_rootArray] using key
          | _ => cases published

/-- The selected public prekey is recovered from every actual published bundle of the complete initialized Word source. -/
theorem run_holds (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : State n KemSK source Platform) (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (empty : before.1.1.beacons = [])
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds wire selectedOwner publicPrekey result.2.1.transcript := by
  have invariant := OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
    (fun current => RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey current.2.1.1.beacons ∧
      Holds wire selectedOwner publicPrekey current.1.transcript)
    (fun query current valid next reached => step_keeps setup checks source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds query current valid next reached)
    _ (RegistrationNativeLedger.empty, before)
    (And.intro (empty ▸ RegistrationNativePublicOwnerMask.empty selectedOwner publicPrekey)
      (by intro entry member; cases member)) result supported
  exact invariant.2

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
private theorem erased_bundle (entry : Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (same : entry.erase = (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry)) :
    RegistrationNativeSecretWordPrekeyPublicationRun.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- The public extractor of the selected published bundle returns the selected public prekey under the actual Word source. -/
theorem published_at (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State n KemSK source Platform)
    (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (empty : before.1.1.beacons = [])
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (raw : Pqxdh.Bytes) (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript selectedOwner = some raw) :
    RegistrationNativePrekeyEvents.publishedAt (RegistrationNativeWire.ledgerCodec wire) result.2.1.ledger.transcript selectedOwner = some publicPrekey := by
  have observed := run_holds setup checks source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work before result empty supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before result supported
  have member := bundle_mem result.2.1.ledger.transcript selectedOwner raw found
  rw [projected] at member
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  obtain ⟨packet, parsed, prekey⟩ := observed entry nativeMember raw (erased_bundle entry selectedOwner raw erased)
  simp only [RegistrationNativePrekeyEvents.publishedAt, found, Option.bind_some,
    RegistrationNativeKemPublicTarget.candidate_read wire raw packet parsed,
    RegistrationNativePrekeyEvents.publishedPrekey, RegistrationRootInput.candidate, prekey,
    PqxdhEd25519EufCma.parsePrekeyMessage_prekeyMessage]

/-- A transported literal public pin conjunct identifies the actual accepted prekey in the current Word game. No signing-origin theorem is applied after a game hop. -/
theorem peer_prekey (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State n KemSK source Platform)
    (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform)) (empty : before.1.1.beacons = [])
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (keyId : U64) (session : Nat) (raw : Pqxdh.Bytes) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (pinned : RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId result.2.1.ledger.transcript (.peer keyId))
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId result.2.1.ledger.transcript (.peer keyId) = some (session, selectedOwner))
    (accepted : PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript session = some raw)
    (candidateFound : PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) raw = some candidate)
    (keysFound : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto candidate = some keys) :
    keys.2.prekey = publicPrekey := by
  obtain ⟨_response, _raw, _candidate, _keys, _linked, _accepted, _candidateFound, _keysFound, _valid, published⟩ :=
    PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId keyId result.2.1.ledger.transcript session selectedOwner designated
  obtain ⟨_published, publishedFound, _identity, _pq⟩ := published
  obtain ⟨publishedRaw, bundled, _parsed⟩ := Option.bind_eq_some_iff.mp publishedFound
  have canonical := published_at setup checks source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work before result empty supported publishedRaw bundled
  have equal := pinned session selectedOwner designated
  simpa only [RegistrationNativePrekeyEvents.acceptedAt, accepted, Option.bind_some, candidateFound, keysFound,
    Option.map_some, canonical, Option.some.injEq] using equal

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.raw_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.raw_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.step_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.run_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.published_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.published_at

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.peer_prekey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun.peer_prekey
