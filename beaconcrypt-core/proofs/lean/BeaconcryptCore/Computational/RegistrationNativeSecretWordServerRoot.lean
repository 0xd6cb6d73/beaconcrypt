-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCollect
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface

/-! The Server root capability stores an opaque KEM word only in its root-service reference. Its local nonzero admission and native cleared token use the same actual public agreement data. Preparation is an echo capability: the source service can reject but cannot replace the retained descriptor with a different message. The source law below explicitly restores that echo behavior rather than assuming that arbitrary oracle replies preserve names. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot
open RegistrationNativeSecretWordServerCollect (Input)
open RegistrationNativeSecretWordMessage (Message PrepareSpec ServerReady)
open PqxdhJointIdentity (PeerEncoding)
open PqxdhRootTableInitialization (rootArray)
open PqxdhPhase2InputBytes (word)
variable {Reader E : Type}

def message (input : Input Reader E PeerEncoding) : Message :=
  ⟨PqxdhPhase2GapDhSource.peer (rootArray input.plain.verified.keys.prekey),
    .known (word input.plain.third), word input.plain.second, word input.plain.fourth, input.kem⟩

/-- Evaluation changes only the private KEM coordinate of the actual original Server descriptor. -/
theorem message_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader E PeerEncoding) :
    RegistrationNativeSecretWordMessage.eval candidate (message input) =
      RegistrationNativeRelatedFamily.Message.ofLegacy
        (PqxdhServerRelatedRootInput.message (RegistrationNativeSecretWordServerCollect.eval candidate input)) := by
  simp only [message, RegistrationNativeSecretWordMessage.eval, PqxdhServerRelatedRootInput.message,
    RegistrationNativeSecretWordServerCollect.eval, RegistrationNativeSecretWordServerSuffix.replace,
    RegistrationNativeRelatedFamily.Message.ofLegacy, PqxdhJointDhExtractRoot.serverMessage,
    PqxdhPhase2InputBytes.word_rootArray]

/-- Native local DH validation does not inspect the encapsulated shared word. -/
theorem nonzero_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader E PeerEncoding) :
    PqxdhServerRelatedRootInput.localNonzero (RegistrationNativeSecretWordServerCollect.eval candidate input) ↔
      PqxdhServerRelatedRootInput.localNonzero input.plain := Iff.rfl

/-- The actual retained cleared token has no shared-secret-dependent field. -/
theorem pending_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader E PeerEncoding)
    (binding : pqxdh.ServerBinding) :
    PqxdhServerClearedRoot.pending binding (RegistrationNativeSecretWordServerCollect.eval candidate input) =
      PqxdhServerClearedRoot.pending binding input.plain := rfl

noncomputable def client (binding : session.RegistrationBinding) (input : Input Reader E PeerEncoding) :
    OracleComp PrepareSpec (RustM (Option ServerReady)) := by
  classical
  exact if ¬ PqxdhServerRelatedRootInput.localNonzero input.plain then pure (.ok none) else do
    let reference ← PrepareSpec.query (message input)
    pure (.ok (reference.map fun reference =>
      ⟨⟨PqxdhServerClearedRoot.pending binding.server_pin.binding input.plain, binding⟩, reference⟩))

/-- Preparation remains at its actual single pre-demand position, including all local rejection paths. -/
theorem client_bound (binding : session.RegistrationBinding) (input : Input Reader E PeerEncoding) :
    (client binding input).IsTotalQueryBound 1 := by
  classical
  unfold client
  split
  · trivial
  · rw [isTotalQueryBound_query_bind_iff]
    exact ⟨by decide, fun _ => by trivial⟩

def restore (candidate : PqxdhKemIndCca.MlKemSharedSecret) : RustM (Option ServerReady) →
    RustM (Option RegistrationServerReferenceRoot.Ready)
  | .fail error => .fail error
  | .div => .div
  | .ok ready => .ok (ready.map (ServerReady.eval candidate))

def annotation (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl PrepareSpec (OracleComp RegistrationServerReferenceRoot.PrepareSpec) := fun query =>
  (fun reply => reply.map (fun _ => query)) <$>
    RegistrationServerReferenceRoot.PrepareSpec.query (RegistrationNativeSecretWordMessage.eval candidate query)

def nativeEcho : QueryImpl RegistrationServerReferenceRoot.PrepareSpec
    (OracleComp RegistrationServerReferenceRoot.PrepareSpec) := fun query =>
  (fun reply => reply.map (fun _ => query)) <$> RegistrationServerReferenceRoot.PrepareSpec.query query

/-- The actual echo preparation restores the original complete native capability and all optional rejection paths after evaluating the private word. The echo map is explicit on both sides. -/
theorem client_source (candidate : PqxdhKemIndCca.MlKemSharedSecret) (binding : session.RegistrationBinding)
    (input : Input Reader E PeerEncoding) :
    restore candidate <$> simulateQ (annotation candidate) (client binding input) =
      simulateQ nativeEcho (RegistrationServerReferenceRoot.client binding
        (RegistrationNativeSecretWordServerCollect.eval candidate input)) := by
  classical
  simp only [client, RegistrationServerReferenceRoot.client, nonzero_eval]
  split
  · simp only [simulateQ_pure, map_pure, restore, Option.map_none]
  · simp only [simulateQ_map, simulateQ_spec_query, annotation, nativeEcho, bind_pure_comp, Functor.map_map]
    rw [← message_eval candidate input]
    congr 1
    funext reply
    cases reply with
    | none => rfl
    | some reply =>
        simp only [restore, Option.map_some, ServerReady.eval, pending_eval]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.message_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.message_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.nonzero_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.nonzero_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.pending_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.pending_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot.client_source
