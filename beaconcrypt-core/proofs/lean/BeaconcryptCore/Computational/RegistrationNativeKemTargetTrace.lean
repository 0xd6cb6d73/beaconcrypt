-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeKemBirthRun
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! The original broad native designation has an actual final retained owner, exact native signed PQ payload and genuinely generated indexed private pair. Matching refers to the source-verified accepted PQ key, including changed valid packets. The public owner and retained private KEM handle stay distinct, and a later-born owner is not excluded. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Initial)
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
    RegistrationNativeKemPublicationTrace.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- A successful bundle found by the original designation has the exact current source owner and native PQ bytes. -/
theorem original_bundle (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (index : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript index = some raw) :
    ∃ owner packet, result.2.2.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet owner.kemPublic := by
  have observed := RegistrationNativeKemPublicationTrace.run_holds setup checks wire route representation created credential readback bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) mode work before result supported
  have member := bundle_mem result.2.1.ledger.transcript index raw found
  rw [projected] at member
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  exact observed entry nativeMember index raw (erased_bundle entry index raw erased)

/-- Broad verified-key designation identifies the actual retained owner's PQ key through the canonical successful accept and original native publication. -/
theorem designated_public (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (budget : Budget) (handle : Handle) (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      created.server.server.metadata.sender budget result.2.1.ledger.transcript handle = some target) :
    ∃ owner raw packet keys, result.2.2.beacons[target.2.val]? = some owner ∧
      PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript target.1.val = some raw ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys ∧
      keys.2.pqKey = owner.kemPublic := by
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto _ created.server.server.metadata.sender budget _ handle target designated
  obtain ⟨raw, accepted, keys, published, acceptFound, candidateFound, keysFound, publishedFound, keyFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys setup.source.crypto _ created.server.server.metadata.sender _ handle target.1.val target.2.val plain
  obtain ⟨publishedRaw, bundleFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨owner, publishedPacket, ownerAt, publishedParsed, publishedKey⟩ :=
    original_bundle setup checks wire route representation created credential readback bounds mode work before result supported target.2.val publishedRaw bundleFound
  rw [RegistrationNativeKemPublicTarget.candidate_read wire publishedRaw publishedPacket publishedParsed] at publishedRead
  have pubEq := Option.some.inj publishedRead
  rw [← pubEq] at keyFound
  have actualKey := RegistrationNativeKemPublicTarget.published_key publishedPacket owner.kemPublic publishedKey
  have sameKey := Option.some.inj (keyFound.symm.trans actualKey)
  obtain ⟨packet, parsed⟩ := RegistrationNativeParsedTarget.candidate_parsed wire raw accepted candidateFound
  rw [RegistrationNativeKemPublicTarget.candidate_read wire raw packet parsed] at candidateFound
  have acceptedEq := Option.some.inj candidateFound
  rw [← acceptedEq] at keysFound
  exact ⟨owner, raw, packet, keys, ownerAt, acceptFound, parsed, keysFound, sameKey⟩

/-- At actual generated startup, the original broad designated owner supplies its genuine private pair at its retained handle; no earlier-birth or owner/index equality is assumed. -/
theorem designated_born (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state))
    (budget : Budget) (handle : Handle) (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      initial.created.server.server.metadata.sender budget result.2.1.ledger.transcript handle = some target) :
    ∃ owner raw packet keys pair, result.2.2.beacons[target.2.val]? = some owner ∧
      result.2.2.pool.keys[owner.kemHandle]? = some pair ∧
      pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) ∧
      pair.1 = owner.kemPublic ∧
      PqxdhDeploymentTranscript.acceptOf result.2.1.ledger.transcript target.1.val = some raw ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys ∧
      keys.2.pqKey = pair.1 := by
  obtain ⟨owner, raw, packet, keys, found, accepted, parsed, verified, matched⟩ :=
    designated_public setup checks wire route representation initial.created initial.credential readback bounds mode work initial.state result supported budget handle target designated
  have born := RegistrationNativeKemBirthRun.initialized_run setup checks wire route representation source ensureInit identityIndex
    serverKeyId initial started bounds mode work result supported
  obtain ⟨pair, selected, publicKey⟩ := born.2 owner (List.mem_of_getElem? found)
  exact ⟨owner, raw, packet, keys, pair, found, selected, born.1 pair (List.mem_of_getElem? selected),
    publicKey, accepted, parsed, verified, matched.trans publicKey.symm⟩

end BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace.original_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace.original_bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace.designated_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace.designated_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace.designated_born' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace.designated_born
