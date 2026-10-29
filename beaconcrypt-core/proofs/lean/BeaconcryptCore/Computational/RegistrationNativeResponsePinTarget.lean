-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponsePinTrace

/-! Original buildOf and Linked designation read the exact native encoded response. Its Server identity is the immutable initial configured pin; this conclusion needs no accepted-owner identity/prekey match or ML membership assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponsePinTarget
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}

private theorem build_mem (transcript : List PqxdhDeploymentInterface.Entry) (handle : Nat)
    (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.buildOf transcript handle = some response) :
    ∃ payload, (⟨.inl (.inr (.build handle payload)), some response⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases value
  · cases command with
    | build index payload =>
        cases reply with
        | none => cases value
        | some encoded =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact ⟨payload, member⟩
            · cases value
    | _ => cases value
  · cases value

private theorem erased_build (entry : Entry) (handle : Nat) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (same : entry.erase = (⟨.inl (.inr (.build handle payload)), some response⟩ : PqxdhDeploymentInterface.Entry)) :
    RegistrationNativeResponsePinTrace.publication entry = some (handle, response) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- The first successful response selected by the original ledger was encoded with the actual initial Server pin. -/
theorem original_encoded (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (handle : Nat) (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.buildOf result.2.1.ledger.transcript handle = some response) :
    RegistrationNativeResponseIdentity.EncodedFrom wire.encodeResponse before.server.pin.binding.identity_public_key response.serialized := by
  have observed := RegistrationNativeResponsePinTrace.run_holds setup checks wire route representation created credential bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) mode work before result supported
  obtain ⟨payload, member⟩ := build_mem result.2.1.ledger.transcript handle response found
  rw [projected] at member
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  exact observed entry nativeMember handle response (erased_build entry handle payload response erased)

/-- Native response read-back identifies the same Server pin in the original public designation codec. -/
theorem original_identity (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.ResponseReadBack wire)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (handle : Nat) (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.buildOf result.2.1.ledger.transcript handle = some response) :
    ((RegistrationNativeWire.ledgerCodec wire).read2 response.serialized).bind
      (RegistrationNativeWire.ledgerCodec wire).serverIdentity = some before.server.pin.binding.identity_public_key :=
  RegistrationNativeResponseIdentity.readback_identity wire readback _ _
    (original_encoded setup checks wire route representation created credential bounds mode work before result supported handle response found)

/-- Any original owner-side Linked witness uses the actual Server pin, even when accepted classical fields differ from the designated owner's credentials. -/
theorem linked_pin (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.ResponseReadBack wire)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (handle : Nat)
    (linked : PqxdhDeploymentTranscript.Linked setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      result.2.1.ledger.transcript ciphertext pin pqKey handle) : pin = before.server.pin.binding.identity_public_key := by
  obtain ⟨response, _accepted, _keys, built, _ciphertext, pinned, _rest⟩ := linked
  have actual := original_identity setup checks wire route representation created credential readback bounds mode work before result supported handle response built
  rw [actual] at pinned
  exact (Option.some.inj pinned).symm

end BeaconcryptCore.Computational.RegistrationNativeResponsePinTarget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePinTarget.original_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePinTarget.original_encoded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePinTarget.original_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePinTarget.original_identity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePinTarget.linked_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePinTarget.linked_pin
