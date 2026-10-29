-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerPinTrace
import BeaconcryptCore.Computational.RegistrationNativeResponseSdk

/-! Original successful build entries carry the immutable initial Server pin's identity through the exact native record, ML signing and response writer. The complete native ledger retains this receipt across later operations, and response read-back transfers it to the original public designation codec. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeWire (Wire)
open RegistrationNativeInterface (Entry)
open RegistrationNativeResponseIdentity (EncodedFrom)
open RegistrationNativeParsedCounterLedger (native)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.build RegistrationNativeExperiment.handler

def publication : Entry → Option (Nat × PqxdhServerRegistrationPublication.Response)
  | ⟨.inl (.inr (.build handle _)), some response⟩ => some (handle, response)
  | _ => none

def Holds (wire : Wire) (identity : Std.Array U8 32#usize) (transcript : List Entry) : Prop :=
  ∀ entry ∈ transcript, ∀ handle response, publication entry = some (handle, response) →
    EncodedFrom wire.encodeResponse identity response.serialized

/-- The actual outer dispatcher returns exactly the bytes encoded by the native SDK under its current immutable pin. -/
theorem source_build (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (credential : RegistrationNativeMldsa.Credential source) (handle : Nat) (application : Option (Slice U8))
    (keyId : U64) (bytes : Pqxdh.Bytes) (before after : State n KemSK source)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support ((RegistrationNativeExperiment.server
      (RegistrationServerSdkSource.build setup (RegistrationNativeWire.ledgerCodec wire) checks
        (RegistrationNativeMldsa.owned source credential) wire.encodeResponse handle application)).run before)) :
    EncodedFrom wire.encodeResponse before.server.pin.binding.identity_public_key bytes := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at supported
  obtain ⟨⟨reply, current⟩, reached, equal⟩ := supported
  have same : reply = .ok (some (keyId, bytes)) := congrArg Prod.fst equal
  subst reply
  exact RegistrationNativeResponseSdk.build_identity setup (RegistrationNativeWire.ledgerCodec wire) checks
    (RegistrationNativeMldsa.owned source credential) wire.encodeResponse handle application before.server current keyId bytes reached

/-- The raw build adapter preserves this source identity through optional-payload conversion and ordinary reply projection. -/
theorem raw_build (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (handle : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : State n KemSK source)
    (supported : (some response, after) ∈ support ((native setup checks wire route representation created credential
      (.inr (.build handle payload))).run before)) :
    EncodedFrom wire.encodeResponse before.server.pin.binding.identity_public_key response.serialized := by
  simp only [native, RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, current⟩, reached, equal⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption] at equal
  | ok reply => cases reply with
    | none => simp [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption] at equal
    | some reply =>
        rcases reply with ⟨keyId, bytes⟩
        simp only [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption,
          Option.map_some, Prod.mk.injEq] at equal
        obtain ⟨same, stateEq⟩ := equal
        have responseEq : (⟨bytes, keyId⟩ : PqxdhServerRegistrationPublication.Response) = response := Option.some.inj same
        cases responseEq
        cases stateEq
        exact source_build setup checks wire credential handle (RegistrationNativeRawAdapter.application payload) keyId bytes before after
          (by simpa only [actual, RegistrationNativeExperiment.handler] using reached)

/-- A complete original ledger step adds only a response encoded under the current Server pin and retains every older receipt. -/
theorem step_keeps (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (identity : Std.Array U8 32#usize) (before : RegistrationNativeLedger.State × State n KemSK source)
    (pin : before.2.server.pin.binding.identity_public_key = identity) (prior : Holds wire identity before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) query).run before)) :
    Holds wire identity result.2.1.transcript := by
  have trace := RegistrationNativeParsedCounterLedger.step_trace setup checks wire route representation created credential bounds query before result supported
  intro entry member handle response published
  rw [trace, List.mem_append, List.mem_singleton] at member
  rcases member with earlier | rfl
  · exact prior entry earlier handle response published
  · cases query with
    | inr secrecy => cases published
    | inl query =>
        rw [RegistrationNativeParsedCounterLedger.core_run, support_map] at supported
        obtain ⟨⟨reply, after⟩, reached, equal⟩ := supported
        cases equal
        cases query with
        | inl coin => cases published
        | inr command => cases command with
          | build session application =>
              cases reply with
              | none => cases published
              | some encoded =>
                  simp only [publication, Option.some.injEq, Prod.mk.injEq] at published
                  obtain ⟨rfl, rfl⟩ := published
                  have receipt := raw_build setup checks wire route representation created credential session application encoded before.2 after reached
                  simpa only [pin] using receipt
          | _ => cases published

/-- Every original native run retains encoded build provenance at the actual initial configured Server identity. -/
theorem run_holds (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    Holds wire before.server.pin.binding.identity_public_key result.2.1.transcript := by
  have invariant : result.2.2.server.pin = before.server.pin ∧ Holds wire before.server.pin.binding.identity_public_key result.2.1.transcript := by
    apply OracleComp.simulateQ_run_preserves_inv_of_query
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential))
      (fun current => current.2.server.pin = before.server.pin ∧ Holds wire before.server.pin.binding.identity_public_key current.1.transcript)
      (fun query current prior next reached => ⟨
        (RegistrationNativeServerPinTrace.full_step_pin setup checks wire route representation created credential bounds query current next reached).trans prior.1,
        step_keeps setup checks wire route representation created credential bounds query before.server.pin.binding.identity_public_key current
          (congrArg (fun pin => pin.binding.identity_public_key) prior.1) prior.2 next reached⟩)
      _ (RegistrationNativeLedger.empty, before) _ result supported
    exact ⟨rfl, fun entry member => by cases member⟩
  exact invariant.2

end BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace.source_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace.source_build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace.raw_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace.raw_build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace.step_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace.run_holds
