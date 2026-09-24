import BeaconcryptCore.Computational.PqxdhServerRelatedRootInput

/-!
After the real root helper clears the copied192-byte input, the full native pending token is reconstructible from the actual verified fields and public source coins. The executable continuation carries that complete cleared token; it does not return an unavailable static-DH value or silently discard a still-live pending field.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.ProtocolComposition
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerClearedRoot
open PqxdhServerRootPreparation PqxdhServerStaticDhSource PqxdhServerRelatedRootInput
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointDhExtractRoot
open PqxdhRootTableInitialization (rootArray)
open PqxdhBeaconPhase2Preparation (Word32)

def registrationIdValue {Reader : Type} (verified : Verified Reader) : pqxdh.RegistrationId :=
  ⟨⟨(verified.identity.toList ++ verified.keys.oneTime.toList).map concreteByte, by simp⟩⟩

theorem registrationId_source {Reader : Type} (verified : Verified Reader) :
    pqxdh.registration_id (PqxdhProtocolAcceptance.verified verified.identity verified.keys) =
      ok (registrationIdValue verified) := by
  obtain ⟨rid, actual, bytes⟩ := registration_id_abs (PqxdhProtocolAcceptance.verified verified.identity verified.keys)
  have same : rid = registrationIdValue verified := by
    cases rid
    congr 1
    apply BeaconcryptCore.Refinement.PqxdhSurface.bytes_eq_of_abs_eq
    simpa [registrationIdValue, Pqxdh.ValidInit.rid, PqxdhProtocolAcceptance.verified,
      rootArray, absBytes, List.map_map, Function.comp_def] using bytes
  rw [actual, same]

def emptyInput : pqxdh.RootKeyInput :=
  ⟨⟨List.replicate 192 0#u8, by simp only [List.length_replicate]; rfl⟩⟩

def cleared (pending : pqxdh.PendingServerRegistration) : pqxdh.PendingServerRegistration :=
  { pending with root_key_input := emptyInput }

def pending {Reader E Shared : Type} (binding : pqxdh.ServerBinding)
    (input : Inputs Reader E Shared) : pqxdh.PendingServerRegistration :=
  ⟨binding, registrationIdValue input.verified, rootArray input.verified.identity,
    input.ephemeral.publicKey, input.ciphertext, emptyInput⟩

/-- Every field of the cleared native token, including its exact source registration ID, is reconstructed without the unavailable DH value. -/
theorem accepted_cleared {Reader E : Type} (binding : pqxdh.ServerBinding)
    (input : Inputs Reader E Word32) (control : pqxdh.ServerState) (original : pqxdh.PendingServerRegistration)
    (accepted : accept control binding input = ok (.Ok (control, original))) :
    cleared original = pending binding input := by
  obtain ⟨rootResult, rid, rootEq, ridEq, shape⟩ :=
    BeaconcryptCore.Refinement.PqxdhSurface.server_fresh_acceptance_shape control
      (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys) binding
      ⟨input.ephemeral.publicKey, input.ciphertext⟩ (secrets input)
  change pqxdh.registration_id (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys) = ok rid at ridEq
  have ridSame : rid = registrationIdValue input.verified := by
    have same := registrationId_source input.verified
    rw [ridEq] at same
    exact RustM.ok.inj same
  change pqxdh.server_accept control _ .Fresh binding _ _ = _ at accepted
  rw [shape] at accepted
  cases rootResult <;> simp only [RustM.ok.injEq, core.result.Result.Ok.injEq,
    Prod.mk.injEq, reduceCtorEq, true_and] at accepted
  cases accepted
  simp only [cleared, pending, ridSame, PqxdhProtocolAcceptance.verified]

/-- Erasing the temporary input leaves every byte read by the existing response builder unchanged. -/
theorem cleared_tail {Metadata PeerMetadata Consumed : Type}
    (source : FixedHkdfSha512NoSaltSource) (original : pqxdh.PendingServerRegistration)
    (root : RootOutput) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhServerRegistrationPublication.build source (cleared original) root data metadata state =
      PqxdhServerRegistrationPublication.build source original root data metadata state :=
  PqxdhRegistrationInputs.build_used_congr source (cleared original) original rfl root data metadata state

/-- The complete reconstructed token uses no materialized static-DH output, including its registration-ID field. -/
theorem pending_materialized (joint : Primitives) (seed : IdentitySeed) {Reader E : Type}
    (binding : pqxdh.ServerBinding) (input : Inputs Reader E PeerEncoding) :
    pending binding (concreteInputs joint seed input) = pending binding input := rfl

end BeaconcryptCore.Computational.PqxdhServerClearedRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhServerClearedRoot.registrationId_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerClearedRoot.registrationId_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerClearedRoot.accepted_cleared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerClearedRoot.accepted_cleared
/-- info: 'BeaconcryptCore.Computational.PqxdhServerClearedRoot.cleared_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerClearedRoot.cleared_tail
/-- info: 'BeaconcryptCore.Computational.PqxdhServerClearedRoot.pending_materialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerClearedRoot.pending_materialized
