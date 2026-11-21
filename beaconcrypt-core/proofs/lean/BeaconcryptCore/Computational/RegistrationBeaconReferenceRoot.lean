-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource
import BeaconcryptCore.Computational.RegistrationServerReferenceRoot

/-! Native selected-Beacon preparation returns only cleared public metadata and its actual pin-aware message reference. The selected scalar and optional root32 remain in the private native related-input interpretation. Preparation occurs before material demand, and all pins admitted by the source controller are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRelatedRoot (RootSpec pinnedBeaconMessage sourceImpl)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationServerReferenceRoot (PrepareSpec annotateNative)

structure Ready where
  descriptor : RegistrationBeaconBoundSource.PublicAgreement
  reference : Message

def atRoot (ready : Ready) (root : RootOutput) : agreement.BeaconAgreement :=
  RegistrationBeaconBoundSource.atRoot ready.descriptor root

def client (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    OracleComp PrepareSpec (RustM (Option Ready)) := do
  let reference ← PrepareSpec.query (pinnedBeaconMessage pending.collected)
  pure (.ok (reference.map fun reference =>
    ⟨⟨PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata,
      authenticated.binding, authenticated.packet.application⟩, reference⟩))

def restored (authenticated : registration.AuthenticatedResponse) (root : Option RootOutput) :
    RustM (Option Ready) → RustM agreement.AgreementEffect
  | .fail error => .fail error
  | .div => .div
  | .ok none => .ok (RegistrationBeaconAgreementRoot.rejected authenticated)
  | .ok (some ready) => .ok (.BeaconComplete (atRoot ready (root.getD RegistrationBoundKeySchedule.zero)))

/-- The actual arbitrary-pin root call is restored privately; the executable client receives only a message reference. -/
theorem client_source (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    (fun result => restored authenticated result.2 result.1) <$>
      (simulateQ annotateNative (client authenticated pending)).run none =
      RegistrationNativeBeaconRootSource.client authenticated pending := by
  simp only [client, bind_pure_comp, simulateQ_map, simulateQ_spec_query]
  rw [StateT.run_map]
  simp only [annotateNative, StateT.run, bind_pure_comp, Functor.map_map,
    RegistrationNativeBeaconRootSource.client, RegistrationNativeBeaconRootSource.root]
  apply congrArg (fun continuation => continuation <$>
    (RootSpec.query (.inr (.derive (pinnedBeaconMessage pending.collected))) : OracleComp RootSpec _))
  funext root
  cases root <;> rfl

theorem ready_fields (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) (ready : Ready)
    (supported : .ok (some ready) ∈ support (client authenticated pending)) :
    ready.descriptor.candidate = PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata ∧
      ready.descriptor.binding = authenticated.binding ∧
      ready.descriptor.application = authenticated.packet.application := by
  simp only [client, bind_pure_comp, support_map] at supported
  obtain ⟨reference, _reached, equal⟩ := supported
  cases reference with
  | none => cases equal
  | some reference => cases equal; exact ⟨rfl, rfl, rfl⟩

theorem client_bound (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    (client authenticated pending).IsTotalQueryBound 1 := by
  rw [client, isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

/-- Full native root-controller reconstruction uses actual reached references and the source root builder; no target-pin or owner-ML-key premise is added. -/
theorem client_native {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) {joint : PqxdhJointIdentity.Primitives}
    (dh : PqxdhJointGapDh.DhInterface joint) (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (original : PqxdhBeaconPhase2Preparation.Prepared registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (references : PqxdhPhase2GapDhSource.References domain pending.collected)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    simulateQ (RegistrationNativeBeaconRootSource.familyImpl (sourceImpl source hmac joint dh seed scalar))
      ((fun result => restored authenticated result.2 result.1) <$>
        (simulateQ annotateNative (client authenticated pending)).run none) =
      simulateQ (RegistrationNativeBeaconRootSource.instrument source hmac primitive pending)
        (RegistrationAgreementExecutor.drive 2 (.RootKdf ⟨.Beacon original.candidate
          authenticated.binding authenticated.packet.application⟩)) := by
  rw [client_source]
  exact RegistrationNativeBeaconRootSource.client_source source hmac dh domain seed scalar primitive authenticated original pending references related

end BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot.client_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot.ready_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot.ready_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot.client_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot.client_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot.client_native
