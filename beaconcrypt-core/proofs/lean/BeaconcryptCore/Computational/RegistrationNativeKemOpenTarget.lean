-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! Original broad native designation under the candidate provider identifies its genuinely created reserved key. The proof uses actual native publication and original verified-key matching; changed accepted bytes, later-born owners and public-key aliases remain eligible. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeInterface (Entry)
open PqxdhDeploymentInterface (Budget FreshBounds Mode Handle)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

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
    RegistrationNativeKemPublicationTrace.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- An original designated bundle has the actual current retained owner and exact genuinely created reserved PQ field in candidate execution. -/
theorem original_bundle (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before after : State n mlSource KemSK)
    (prior : RegistrationNativeKemOpenRoster.Holds pairs before) (value : Value) (ledger : RegistrationNativeLedger.State)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ provider (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender
        bounds mode work parsed)).run).run before))
    (index : Nat) (raw : Pqxdh.Bytes) (found : PqxdhDeploymentTranscript.bundleOf ledger.ledger.transcript index = some raw) :
    ∃ owner packet pair, after.1.1.beacons[index]? = some owner ∧ owner.kemHandle = index ∧ pairs[index]? = some pair ∧
      owner.kemPublic = pair.1 ∧ RegistrationNativeWire.readInit wire raw = some packet ∧ RegistrationNativeKemTarget.PacketKey packet pair.1 := by
  obtain ⟨roster, publications⟩ := RegistrationNativeKemOpenPublicationRun.program_holds setup checks wire route representation
    created credential selected pairs publicKey real parsed readback bounds mode work before after prior value ledger supported
  have projected := RegistrationNativeKemOpenPublicationRun.program_consistent setup checks wire route representation created credential
    selected pairs publicKey real parsed bounds mode work before after value ledger supported
  have member := bundle_mem ledger.ledger.transcript index raw found
  rw [projected] at member
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  obtain ⟨pair, packet, pairAt, active, decoded, key⟩ := publications entry nativeMember index raw (erased_bundle entry index raw erased)
  have activeOwners : index < after.1.1.beacons.length := by simpa only [roster.1] using active
  let owner := after.1.1.beacons[index]'activeOwners
  have ownerAt : after.1.1.beacons[index]? = some owner := List.getElem?_eq_some_iff.mpr ⟨activeOwners, rfl⟩
  obtain ⟨currentPair, currentAt, handle, currentKey⟩ := roster.2 index owner ownerAt
  have samePair : currentPair = pair := Option.some.inj (currentAt.symm.trans pairAt)
  subst currentPair
  exact ⟨owner, packet, pair, ownerAt, handle, pairAt, currentKey, decoded, key⟩

/-- Broad original verified-key designation gives the canonical accepted packet's actual reserved PQ key under the candidate provider. -/
theorem designated_public (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before after : State n mlSource KemSK)
    (prior : RegistrationNativeKemOpenRoster.Holds pairs before) (value : Value) (ledger : RegistrationNativeLedger.State)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ provider (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender
        bounds mode work parsed)).run).run before))
    (budget : Budget) (handle : Handle) (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      created.server.server.metadata.sender budget ledger.ledger.transcript handle = some target) :
    ∃ owner raw packet keys pair, after.1.1.beacons[target.2.val]? = some owner ∧ owner.kemHandle = target.2.val ∧
      pairs[target.2.val]? = some pair ∧ owner.kemPublic = pair.1 ∧
      PqxdhDeploymentTranscript.acceptOf ledger.ledger.transcript target.1.val = some raw ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys ∧ keys.2.pqKey = pair.1 := by
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto _ created.server.server.metadata.sender budget _ handle target designated
  obtain ⟨raw, accepted, keys, published, acceptFound, candidateFound, keysFound, publishedFound, keyFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys setup.source.crypto _ created.server.server.metadata.sender _ handle target.1.val target.2.val plain
  obtain ⟨publishedRaw, bundleFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨owner, publishedPacket, pair, ownerAt, ownerHandle, pairAt, currentKey, publishedParsed, publishedKey⟩ :=
    original_bundle setup checks wire route representation created credential selected pairs publicKey real parsed readback bounds mode work
      before after prior value ledger supported target.2.val publishedRaw bundleFound
  rw [RegistrationNativeKemPublicTarget.candidate_read wire publishedRaw publishedPacket publishedParsed] at publishedRead
  have pubEq := Option.some.inj publishedRead
  rw [← pubEq] at keyFound
  have actualKey := RegistrationNativeKemPublicTarget.published_key publishedPacket pair.1 publishedKey
  have sameKey := Option.some.inj (keyFound.symm.trans actualKey)
  obtain ⟨packet, decoded⟩ := RegistrationNativeParsedTarget.candidate_parsed wire raw accepted candidateFound
  rw [RegistrationNativeKemPublicTarget.candidate_read wire raw packet decoded] at candidateFound
  have acceptedEq := Option.some.inj candidateFound
  rw [← acceptedEq] at keysFound
  exact ⟨owner, raw, packet, keys, pair, ownerAt, ownerHandle, pairAt, currentKey,
    acceptFound, decoded, keysFound, sameKey⟩

/-- Selecting the same single owner/creation coordinate identifies the genuine selected key without a second capacity guess or public-key injectivity. -/
theorem designated_selected (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget) (selected : Fin budget.capacity)
    (chosen : MlKem768PublicKey × KemSK) (others : Fin budget.create → MlKem768PublicKey × KemSK)
    (before after : State n mlSource KemSK)
    (prior : RegistrationNativeKemOpenRoster.Holds (List.ofFn (selected.insertNth chosen others)) before)
    (value : Value) (ledger : RegistrationNativeLedger.State)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ (RegistrationNativeKemOpenProvider.implementation setup checks wire route representation created credential
        selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real)
        (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run).run before))
    (handle : Handle) (session : Fin budget.accept)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      created.server.server.metadata.sender budget ledger.ledger.transcript handle = some (session, selected)) :
    ∃ owner raw packet keys, after.1.1.beacons[selected.val]? = some owner ∧ owner.kemHandle = selected.val ∧ owner.kemPublic = chosen.1 ∧
      PqxdhDeploymentTranscript.acceptOf ledger.ledger.transcript session.val = some raw ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys ∧ keys.2.pqKey = chosen.1 := by
  obtain ⟨owner, raw, packet, keys, pair, ownerAt, ownerHandle, pairAt, currentKey, accepted, decoded, verified, matched⟩ :=
    designated_public setup checks wire route representation created credential selected.val (List.ofFn (selected.insertNth chosen others))
      chosen.1 real parsed readback bounds mode work before after prior value ledger supported budget handle (session, selected) designated
  have chosenAt : (List.ofFn (selected.insertNth chosen others))[selected.val]? = some chosen := by
    simpa only [List.nil_append, List.length_nil, Nat.zero_add] using PqxdhLiveKemSelection.selected_index [] selected chosen others
  have same : pair = chosen := Option.some.inj (pairAt.symm.trans chosenAt)
  subst pair
  exact ⟨owner, raw, packet, keys, ownerAt, ownerHandle, currentKey, accepted, decoded, verified, matched⟩

end BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget.original_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget.original_bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget.designated_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget.designated_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget.designated_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget.designated_selected
