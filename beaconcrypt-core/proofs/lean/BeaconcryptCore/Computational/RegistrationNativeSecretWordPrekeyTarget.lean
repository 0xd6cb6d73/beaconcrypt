-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun
import BeaconcryptCore.Computational.RegistrationNativePrekeyEvents
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! The original broad Word designation and its transported public pin conjunct identify the selected accepted prekey from actual signed bundle bytes. No real-source Ed-origin assumption is invoked after a game hop. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyTarget
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode Handle)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}

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

private theorem erased_bundle (entry : Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (same : entry.erase = (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry)) :
    RegistrationNativeSecretWordPrekeyPublicationRun.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

/-- The public extractor of the selected published bundle returns the selected public prekey under the actual Word source. -/
theorem published_at (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (empty : before.1.beacons = [])
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (raw : Pqxdh.Bytes) (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript selectedOwner = some raw) :
    RegistrationNativePrekeyEvents.publishedAt (RegistrationNativeWire.ledgerCodec wire) result.2.1.ledger.transcript selectedOwner = some publicPrekey := by
  have observed := RegistrationNativeSecretWordPrekeyPublicationRun.run_holds setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey serverKeyId readback bounds mode work before result empty supported
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
theorem peer_prekey (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source)) (empty : before.1.beacons = [])
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
  have canonical := published_at setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId
    readback bounds mode work before result empty supported publishedRaw bundled
  have equal := pinned session selectedOwner designated
  simpa only [RegistrationNativePrekeyEvents.acceptedAt, accepted, Option.bind_some, candidateFound, keysFound,
    Option.map_some, canonical, Option.some.injEq] using equal

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyTarget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyTarget.published_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyTarget.published_at

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyTarget.peer_prekey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyTarget.peer_prekey
