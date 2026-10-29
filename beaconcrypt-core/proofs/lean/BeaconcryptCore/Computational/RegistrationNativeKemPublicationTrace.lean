-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemRoster
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeParsedCounterLedger

/-! Every successful bundle in the complete original native public ledger carries the exact PQ key of its retained owner. The source-derived owner lookup retains the separate opaque KEM handle through every later lifecycle and constructor step. Actual native encoding read-back is the only wire premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemBirthInvariant (metadata)
open RegistrationNativeParsedCounterLedger (native)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler

def publication : Entry → Option (Nat × Pqxdh.Bytes)
  | ⟨.inl (.inr (.bundle owner)), some raw⟩ => some (owner, raw)
  | _ => none

def Holds (wire : Wire) (transcript : List Entry) (owners : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∀ entry ∈ transcript, ∀ owner raw, publication entry = some (owner, raw) →
    ∃ selected packet, owners[owner]? = some selected ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet selected.kemPublic

private theorem transport (wire : Wire) (transcript : List Entry)
    (before after : RegistrationNativeBeaconFrontend.State source)
    (prior : Holds wire transcript before) (preserved : RegistrationNativeKemRoster.Prefix before after) :
    Holds wire transcript after := by
  intro entry member owner raw published
  obtain ⟨old, packet, found, parsed, key⟩ := prior entry member owner raw published
  obtain ⟨current, currentAt, same⟩ := RegistrationNativeKemRoster.lookup before after preserved owner old found
  have publicKey : current.kemPublic = old.kemPublic := congrArg Prod.snd same
  exact ⟨current, packet, currentAt, parsed, by simpa only [publicKey] using key⟩

/-- A successful original raw bundle call has the actual earlier owner and decoded native signed PQ payload. -/
theorem raw_bundle (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (index : Nat) (raw : Pqxdh.Bytes)
    (before after : State n KemSK source)
    (supported : (some raw, after) ∈ support
      ((native setup checks wire route representation created credential (.inr (.bundle index))).run before)) :
    ∃ owner packet, before.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet owner.kemPublic := by
  simp only [native, RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map,
    support_map] at supported
  obtain ⟨⟨reply, reachedState⟩, reached, equal⟩ := supported
  cases result : reply with
  | fail error | div => simp [result, RegistrationNativeRawAdapter.resultOption] at equal
  | ok reply =>
      simp only [result, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      have actual : (.ok (some raw), reachedState) ∈ support
          ((RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeBeaconFrontend.bundle setup source wire index)).run before) := by
        simpa only [result, RegistrationNativeExperiment.handler] using reached
      exact RegistrationNativeBeaconPublication.source_bundle_key setup checks representation created source wire readback index before reachedState raw actual

/-- Complete original ledger steps preserve all earlier actual publication receipts and add the reached native bundle receipt. -/
theorem step_keeps (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (prior : Holds wire before.1.transcript before.2.beacons)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) query).run before)) :
    Holds wire result.2.1.transcript result.2.2.beacons := by
  have preserved := RegistrationNativeKemRoster.full_step_prefix setup checks wire route representation created credential bounds query before result supported
  have retained := transport wire before.1.transcript before.2.beacons result.2.2.beacons prior preserved
  have trace := RegistrationNativeParsedCounterLedger.step_trace setup checks wire route representation created credential bounds query before result supported
  intro entry member owner raw published
  rw [trace, List.mem_append, List.mem_singleton] at member
  rcases member with earlier | rfl
  · exact retained entry earlier owner raw published
  · cases query with
    | inr secrecy => cases published
    | inl query =>
        rw [RegistrationNativeParsedCounterLedger.core_run, support_map] at supported
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
                  obtain ⟨rfl, rfl⟩ := published
                  obtain ⟨old, packet, found, parsed, key⟩ := raw_bundle setup checks wire route representation created credential readback index encoded before.2 after reached
                  obtain ⟨current, currentAt, same⟩ := RegistrationNativeKemRoster.lookup before.2.beacons after.beacons preserved index old found
                  have publicKey : current.kemPublic = old.kemPublic := congrArg Prod.snd same
                  exact ⟨current, packet, currentAt, parsed, by simpa only [publicKey] using key⟩
          | _ => cases published

/-- Every supported complete original native run retains all bundle-to-current-owner PQ receipts, including failed raw and private secrecy paths. -/
theorem run_holds (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK source) (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    Holds wire result.2.1.transcript result.2.2.beacons := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential))
    (fun current => Holds wire current.1.transcript current.2.beacons)
    (fun query current valid next reached => step_keeps setup checks wire route representation created credential readback bounds query current valid next reached)
    _ (RegistrationNativeLedger.empty, before) _ result supported
  intro entry member
  cases member

end BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace.raw_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace.raw_bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace.step_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace.run_holds
