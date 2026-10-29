-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrepare
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface

/-! The actual arbitrary-pin Beacon root capability carries only its opaque KEM word in the private reference. Cleared control, populated binding and application remain literal. The explicit echo compiler preserves the source service's descriptor name on either accepted or rejected preparation; arbitrary unrelated oracle replies are never assumed to preserve it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot
open RegistrationNativeSecretWordBeaconPrepare (Prepared)
open RegistrationNativeSecretWordMessage (Message PrepareSpec BeaconReady)

noncomputable def message (pending : Prepared registration.AuthenticatedResponse) : Message :=
  ⟨PqxdhPhase2GapDhSource.peer pending.collected.plain.serverConverted,
    .pinned (PqxdhPhase2GapDhSource.peer pending.collected.plain.ephemeral),
    PqxdhPhase2InputBytes.word pending.collected.plain.second,
    PqxdhPhase2InputBytes.word pending.collected.plain.fourth, pending.collected.kem⟩

/-- Evaluating the opaque KEM word restores the exact original pin-aware Beacon descriptor, including arbitrary configured Server identities. -/
theorem message_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (pending : Prepared registration.AuthenticatedResponse) :
    RegistrationNativeSecretWordMessage.eval candidate (message pending) =
      RegistrationNativeRelatedRoot.pinnedBeaconMessage
        (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending).collected := by
  simp only [message, RegistrationNativeSecretWordMessage.eval, RegistrationNativeRelatedRoot.pinnedBeaconMessage,
    RegistrationNativeSecretWordBeaconPrepare.eval, RegistrationNativeSecretWordBeaconCollect.eval,
    RegistrationNativeSecretWordBeaconPrefix.setShared, PqxdhPhase2InputBytes.word_rootArray]

noncomputable def client (authenticated : registration.AuthenticatedResponse) (pending : Prepared registration.AuthenticatedResponse) :
    OracleComp PrepareSpec (RustM (Option BeaconReady)) := do
  let reference ← PrepareSpec.query (message pending)
  pure (.ok (reference.map fun reference =>
    ⟨⟨PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata,
      authenticated.pending.binding, authenticated.packet.application⟩, reference⟩))

/-- The concrete Beacon root capability retains its single pre-demand request and all optional refusal branches. -/
theorem client_bound (authenticated : registration.AuthenticatedResponse) (pending : Prepared registration.AuthenticatedResponse) :
    (client authenticated pending).IsTotalQueryBound 1 := by
  rw [client, isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

def restore (candidate : PqxdhKemIndCca.MlKemSharedSecret) : RustM (Option BeaconReady) →
    RustM (Option RegistrationBeaconReferenceRoot.Ready)
  | .fail error => .fail error
  | .div => .div
  | .ok ready => .ok (ready.map (BeaconReady.eval candidate))

noncomputable def annotation (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl PrepareSpec (OracleComp RegistrationServerReferenceRoot.PrepareSpec) := fun query =>
  (fun reply => reply.map (fun _ => query)) <$>
    RegistrationServerReferenceRoot.PrepareSpec.query (RegistrationNativeSecretWordMessage.eval candidate query)

def nativeEcho : QueryImpl RegistrationServerReferenceRoot.PrepareSpec
    (OracleComp RegistrationServerReferenceRoot.PrepareSpec) := fun query =>
  (fun reply => reply.map (fun _ => query)) <$> RegistrationServerReferenceRoot.PrepareSpec.query query

/-- The evaluated opaque-word capability has the exact original arbitrary-pin native source, with its actual echo behavior made explicit. -/
theorem client_source (candidate : PqxdhKemIndCca.MlKemSharedSecret) (authenticated : registration.AuthenticatedResponse)
    (pending : Prepared registration.AuthenticatedResponse) :
    restore candidate <$> simulateQ (annotation candidate) (client authenticated pending) =
      simulateQ nativeEcho (RegistrationBeaconReferenceRoot.client authenticated
        (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending)) := by
  simp only [client, RegistrationBeaconReferenceRoot.client, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, annotation, nativeEcho, Functor.map_map]
  rw [← message_eval candidate pending]
  congr 1
  funext reply
  cases reply with
  | none => rfl
  | some reference => simp only [restore, Option.map_some, BeaconReady.eval, RegistrationNativeSecretWordBeaconPrepare.eval]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot.message_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot.message_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot.client_source
