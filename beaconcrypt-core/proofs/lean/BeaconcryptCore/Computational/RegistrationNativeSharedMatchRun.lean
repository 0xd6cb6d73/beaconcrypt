-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSharedMatchPublication
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeSessionUnique
/-! Actual Native original-ledger executions discharge the public matching scanner's generated-key provenance from their reached bundle trace. All rejected queries, late owner creations and complete final source state remain in the same run; no ownership or AD premise is supplied by the public client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeSharedMatchRun
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentServerAuthEvent (Reg regOfEntry regsOf)
open RegistrationNativeInterface (Entry)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem bundle_entry (entry : PqxdhDeploymentInterface.Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (selected : regOfEntry entry = some (Reg.bundle owner (some raw))) :
    entry = (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases selected
  · cases command with
    | create pin keyId =>
      cases reply with
      | none => cases selected
      | some index =>
        cases parsed : PqxdhDeploymentInterface.parsePin pin <;> simp [regOfEntry, parsed] at selected
    | bundle index => cases selected; rfl
    | _ => cases selected
  · cases selected

private theorem erased_bundle (entry : Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (same : entry.erase = (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry)) :
    RegistrationNativeIdentityPublicationTrace.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- The original registration entries of an actual Native run carry the precise generated-key packet receipts required by the unchanged public SharedMatch event. -/
theorem run_receipts (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (readback : RegistrationNativeWire.InitReadBack wire)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation
      created source credential bounds mode work before)) :
    RegistrationNativeSharedMatchPublication.Receipts setup.joint wire (regsOf result.2.1.ledger.transcript)
      (result.2.2.beacons.map (fun owner => owner.identitySeed)) := by
  have observed := RegistrationNativeIdentityPublicationTrace.run_holds setup checks wire route representation
    created credential readback bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire
    created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)
    mode work before result supported
  intro index raw bundled
  obtain ⟨old, oldMember, selected⟩ := List.mem_filterMap.mp bundled
  have oldEntry := bundle_entry old index raw selected
  rw [projected] at oldMember
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp oldMember
  obtain ⟨owner, packet, found, read, key⟩ := observed entry nativeMember index raw
    (erased_bundle entry index raw (erased.trans oldEntry))
  refine ⟨owner.identitySeed, packet, ?_, read, key⟩
  simp only [List.getElem?_map, found, Option.map_some]

/-- The exact original public SharedMatch event of one actual Native run yields a collision of its final owners' generated keys. Both source invariants are derived from that same run. -/
theorem run_collision (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (readback : RegistrationNativeWire.InitReadBack wire)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation
      created source credential bounds mode work before)) (first second : Nat)
    (shared : RegistrationNativeSharedMatchCollision.SharedMatch setup.source.crypto
      (RegistrationNativeWire.ledgerCodec wire) first second (regsOf result.2.1.ledger.transcript)) :
    PqxdhDeploymentServerAuthInjective.Collision setup.joint (result.2.2.beacons.map (fun owner => owner.identitySeed)) := by
  have receipts := run_receipts setup checks wire route representation created credential readback bounds mode
    work before result supported
  exact RegistrationNativeSharedMatchCollision.shared_collision setup.joint setup.source.crypto
    (RegistrationNativeWire.ledgerCodec wire) (regsOf result.2.1.ledger.transcript)
    (result.2.2.beacons.map (fun owner => owner.identitySeed))
    (RegistrationNativeSessionUnique.run setup checks wire route representation created credential bounds mode work before result supported)
    (fun earlierRegs earlier owner keys selected => RegistrationNativeSharedMatchPublication.generated_key setup.joint wire
      (regsOf result.2.1.ledger.transcript) _ receipts earlierRegs earlier owner keys selected)
    first second shared

end BeaconcryptCore.Computational.RegistrationNativeSharedMatchRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSharedMatchRun.run_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSharedMatchRun.run_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSharedMatchRun.run_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSharedMatchRun.run_collision
