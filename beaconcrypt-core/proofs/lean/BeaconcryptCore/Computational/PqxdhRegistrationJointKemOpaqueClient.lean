-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore

/-! The actual initialized Server accept continuation runs with a private KEM marker. Only the private root interpreter materializes selected bytes; acceptance, source erasure callbacks, consumption and the complete cleared token do not. Both the real fixed-HKDF callback and the existing restricted-ROM callback remain explicitly distinct. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient
open PqxdhRegistrationJointKemOpaqueSuffix
open PqxdhServerAuthNative PqxdhServerRelatedRootConsumer
open PqxdhSecretInputKdf
open PqxdhBeaconPhase2Preparation (Word32)
variable {Reader : Type}

abbrev Input (Reader : Type) := Prepared Reader PqxdhJointGapDh.ScalarBytes Word32
abbrev RootSpec (Reader : Type) := Input Reader →ₒ RootOutput
abbrev Spec (Reader : Type) := RootSpec Reader + AuxSpec

/-- The actual four DH outputs remain in their source order; no selected KEM bytes are present. -/
def coordinates (input : Input Reader) : PqxdhHiddenRoot.KnownPqxdhRootCoordinates :=
  PqxdhPhase2InputBytes.coordinates input.first input.second input.third input.fourth

/-- Mathematical root-input interpretation; this is confined to the private backend. -/
def bytes (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader) : Pqxdh.Bytes :=
  PqxdhHiddenRoot.hiddenRootIKM (coordinates input)
    (PqxdhPhase2DecapsulationRouting.materialize candidate input.shared)

/-- The private interpretation is exactly the actual extracted 192-byte input, on its literal accepted branch. -/
theorem accepted_bytes (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader)
    (control final : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (original : pqxdh.PendingServerRegistration)
    (accepted : PqxdhServerRelatedRootInput.accept control binding (materialize candidate input) =
      ok (.Ok (final, original))) :
    absBytes original.root_key_input.bytes = bytes candidate input := by
  have built := PqxdhRegistrationJointKemRootBytes.accepted_input
    (materialize candidate input) control final binding original accepted
  simpa only [bytes, coordinates, materialize, PqxdhServerRelatedRootInput.secrets,
    PqxdhPhase2InputBytes.word_rootArray] using PqxdhPhase2InputBytes.root_input _ _ built

/-- The complete source continuation does not accept a selected-secret argument. Logical erasure remains in source order and rejected inputs issue no root request. -/
noncomputable def client (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : Input Reader) : OracleComp (Spec Reader) (RustM (Option Returned)) := do
  let accepted := PqxdhRegistrationJointKemOpaqueCore.accept control binding input
  let _ ← (Spec Reader).query (.inr .eraseShared)
  match accepted with
  | .ok (.Err _) => pure (ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Ok (_, token)) => do
      let root ← (Spec Reader).query (.inl input)
      let _ ← (Spec Reader).query (.inr .eraseInput)
      let _ ← (Spec Reader).query (.inr (.consume token.registration_id))
      pure (ok (some ⟨root, token⟩))

/-- Existing analysis root interpretation, with its complete restricted Extract-ROM cache/history and original session touch kept private. This definition is not a fixed-HKDF security claim. -/
noncomputable def romRoot (KemSK : Type) (hmac : HmacSha512) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader) : NativeGame KemSK RootOutput := do
  let originalInput := materialize candidate input
  let root ← romRootBytes hmac (nativeMessage originalInput) (bytes candidate input)
  nativeTouch (.session index (nativeMessage originalInput) (some root))
  pure root

/-- A private root request has the complete same native effect as the actual source callback; no history, cache or instrumentation is discarded. -/
theorem rom_root_native (KemSK : Type) (hmac : HmacSha512) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader)
    (control final : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (original : pqxdh.PendingServerRegistration)
    (accepted : PqxdhServerRelatedRootInput.accept control binding (materialize candidate input) =
      ok (.Ok (final, original))) :
    romRoot KemSK hmac index candidate input =
      loggedRoot hmac index (materialize candidate input) original := by
  simp only [romRoot, loggedRoot, PqxdhServerAuthNative.romRoot,
    accepted_bytes candidate input control final binding original accepted]

/-- Erasure is the native experiment's original no-op; consumption appends the actual registration ID to the same native state. -/
def auxiliary (KemSK : Type) : QueryImpl AuxSpec (NativeGame KemSK)
  | .eraseShared => pure ()
  | .eraseInput => pure ()
  | .consume rid => nativeConsume rid

noncomputable def romImpl (KemSK : Type) (hmac : HmacSha512) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) : QueryImpl (Spec Reader) (NativeGame KemSK)
  | .inl input => romRoot KemSK hmac index candidate input
  | .inr query => auxiliary KemSK query

/-- The executable marker client equals the entire current native acceptance continuation, including every rejection and all private state. Materialization is confined to the interpreter side of the equality. -/
theorem client_native (KemSK : Type) (hmac : HmacSha512) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) :
    simulateQ (romImpl KemSK hmac index candidate) (client control binding input) =
      nativeClient hmac index control binding (materialize candidate input) := by
  simp only [client, PqxdhRegistrationJointKemOpaqueCore.accept_native control binding input candidate,
    PqxdhRegistrationJointKemOpaqueCore.clearedAccept, nativeClient]
  cases accepted : PqxdhServerRelatedRootInput.accept control binding (materialize candidate input) with
  | fail error => simp only [simulateQ_bind, simulateQ_spec_query, romImpl,
      auxiliary, pure_bind, simulateQ_pure]
  | div => simp only [simulateQ_bind, simulateQ_spec_query, romImpl,
      auxiliary, pure_bind, simulateQ_pure]
  | ok result =>
      cases result with
      | Err error => simp only [simulateQ_bind, simulateQ_spec_query, romImpl,
          auxiliary, pure_bind, simulateQ_pure]
      | Ok pair =>
          rcases pair with ⟨final, original⟩
          simp only [simulateQ_bind, simulateQ_spec_query, romImpl,
            auxiliary, pure_bind, simulateQ_pure,
            rom_root_native KemSK hmac index candidate input control final binding original accepted,
            PqxdhServerClearedRoot.cleared]
          rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient.accepted_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient.accepted_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient.rom_root_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient.rom_root_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient.client_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient.client_native
