-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativePrekeyEvents
import BeaconcryptCore.Computational.RegistrationNativeKemBirthRun
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! Original native bundle lookup recovers the exact signed prekey of the actual final owner. This public extractor is used to split the real-source APP event before changing any cryptographic game. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePrekeyTargetTrace
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
    RegistrationNativePrekeyPublicationTrace.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- A successful bundle found by the original designation has the exact current source owner and native PQ bytes. -/
theorem original_bundle (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (index : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript index = some raw) :
    ∃ owner packet, result.2.2.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.prekeyPublic) := by
  have observed := RegistrationNativePrekeyPublicationTrace.run_holds setup checks wire route representation created credential readback bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) mode work before result supported
  have member := bundle_mem result.2.1.ledger.transcript index raw found
  rw [projected] at member
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  exact observed entry nativeMember index raw (erased_bundle entry index raw erased)


/-- The original public bundle extractor returns the same final owner's immutable prekey. -/
theorem published_at (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (index : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript index = some raw) :
    ∃ owner, result.2.2.beacons[index]? = some owner ∧
      RegistrationNativePrekeyEvents.publishedAt (RegistrationNativeWire.ledgerCodec wire) result.2.1.ledger.transcript index =
        some (PqxdhPhase2InputBytes.word owner.prekeyPublic) := by
  obtain ⟨owner, packet, ownerAt, parsed, prekey⟩ := original_bundle setup checks wire route representation created credential
    readback bounds mode work before result supported index raw found
  refine ⟨owner, ownerAt, ?_⟩
  simp only [RegistrationNativePrekeyEvents.publishedAt, found, Option.bind_some,
    RegistrationNativeKemPublicTarget.candidate_read wire raw packet parsed,
    RegistrationNativePrekeyEvents.publishedPrekey, RegistrationRootInput.candidate, prekey,
    PqxdhEd25519EufCma.parsePrekeyMessage_prekeyMessage]

end BeaconcryptCore.Computational.RegistrationNativePrekeyTargetTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyTargetTrace.original_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyTargetTrace.original_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyTargetTrace.published_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyTargetTrace.published_at
