-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSourceRoot
import BeaconcryptCore.Computational.RegistrationServerReferenceRestore

/-! The scalar-free Server preparation client restores the exact cleared source agreement under the actual private native root evaluator. The full binding and cleared pending token remain literal; no root is an executable client argument. This source lemma is independent of the surrounding KEM getter routing. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceSourceClient
open PqxdhSecretInputKdf (RootOutput)
open RegistrationServerReferenceRoot (Ready PrepareSpec atRoot)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding)
open PqxdhJointGapDh (DhInterface ScalarBytes)


def prepare (source : FixedHkdfSha512NoSaltSource) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) : QueryImpl PrepareSpec ProbComp := fun message =>
  pure ((RegistrationNativeSourceRoot.value source joint dh seed scalar message).map fun _ => message)

def roots (source : FixedHkdfSha512NoSaltSource) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) : RegistrationServerReferenceRestore.Roots :=
  fun message => (RegistrationNativeSourceRoot.value source joint dh seed scalar message).getD RegistrationBoundKeySchedule.zero

def restore (privateRoots : RegistrationServerReferenceRestore.Roots) :
    RustM (Option Ready) → RustM agreement.AgreementEffect
  | .fail error => .fail error
  | .div => .div
  | .ok none => .ok (.Rejected .None)
  | .ok (some ready) => .ok (.ServerComplete (atRoot ready (privateRoots ready.reference)))

def consumer (source : FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl PqxdhServerRelatedRootConsumer.Spec ProbComp
  | .inl query => simulateQ (RegistrationNativeSourceRoot.handler source hmac joint dh seed scalar)
      (RegistrationNativeRelatedRoot.legacy query)
  | .inr _ => pure ()

/-- Actual preparation returns only its public descriptor; private native root values reconstruct the literal source cleared agreement on every optional branch. -/
theorem client (source : FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (binding : session.RegistrationBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PeerEncoding) :
    restore (roots source joint dh seed scalar) <$>
        simulateQ (prepare source joint dh seed scalar) (RegistrationServerReferenceRoot.client binding input) =
      simulateQ (consumer source hmac joint dh seed scalar) (RegistrationRelatedRoot.client binding input) := by
  classical
  by_cases admitted : PqxdhServerRelatedRootInput.localNonzero input
  · cases selected : RegistrationNativeSourceRoot.value source joint dh seed scalar
        (RegistrationNativeRelatedFamily.Message.ofLegacy (PqxdhServerRelatedRootInput.message input)) <;>
      simp [RegistrationServerReferenceRoot.client, RegistrationRelatedRoot.client,
        PqxdhServerRelatedRootConsumer.client, admitted, prepare, consumer,
        RegistrationNativeSourceRoot.handler, RegistrationNativeRelatedRoot.legacy,
        selected, roots, restore, RegistrationRelatedRoot.completed, atRoot, RegistrationBoundGate.atRoot]
  · simp [RegistrationServerReferenceRoot.client, RegistrationRelatedRoot.client,
      PqxdhServerRelatedRootConsumer.client, admitted, consumer, restore, RegistrationRelatedRoot.completed]

end BeaconcryptCore.Computational.RegistrationServerReferenceSourceClient

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceClient.client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceClient.client
