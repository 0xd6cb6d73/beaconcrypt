-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical

/-! The original broad native designation identifies its retained symbolic owner's actual signed PQ publication and the canonical accepted packet's verified PQ tuple. This uses the concrete combined Word execution with arbitrary outer material replies. Changed valid packets and owners born after their designated accept remain covered; no equality between public owner and private birth indices is assumed here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode Handle)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

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
    RegistrationNativeSecretWordTargetPublicationRun.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- A successful bundle found by the original designation has the exact current source owner and native PQ bytes. -/
theorem original_bundle (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (index : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript index = some raw) :
    ∃ owner packet, result.2.2.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet owner.view.kemPublic := by
  have observed := RegistrationNativeSecretWordTargetPublicationRun.run_holds setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId readback bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds
    (typed) mode work before result supported
  have member := bundle_mem result.2.1.ledger.transcript index raw found
  rw [projected] at member
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  exact observed entry nativeMember index raw (erased_bundle entry index raw erased)

/-- Broad verified-key designation identifies the actual retained owner's PQ key through the canonical successful accept and original native publication. -/
theorem designated_public (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (budget : Budget) (handle : Handle) (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget result.2.1.ledger.transcript handle = some target) :
    ∃ owner raw packet keys, result.2.2.1.beacons[target.2.val]? = some owner ∧
      PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript target.1.val = some raw ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys ∧
      keys.2.pqKey = owner.view.kemPublic := by
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto _ serverKeyId budget _ handle target designated
  obtain ⟨raw, accepted, keys, published, acceptFound, candidateFound, keysFound, publishedFound, keyFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys setup.source.crypto _ serverKeyId _ handle target.1.val target.2.val plain
  obtain ⟨publishedRaw, bundleFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨owner, publishedPacket, ownerAt, publishedParsed, publishedKey⟩ :=
    original_bundle setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId readback bounds mode work before result supported target.2.val publishedRaw bundleFound
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

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic.original_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic.original_bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic.designated_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic.designated_public
