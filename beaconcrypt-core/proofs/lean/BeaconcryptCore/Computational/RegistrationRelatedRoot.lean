-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRootInput
import BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer

/-! The related-root client starts after actual native authentication. It keeps the complete populated registration binding through root hiding and native completion, including the cleared pending token. Its public request carries the received prekey and actual local outputs, without the selected static-DH value. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationRelatedRoot

open PqxdhServerRootPreparation (Inputs)
open PqxdhServerStaticDhSource (PublicDomain prefixImpl nativeImpl concreteInputs)
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhJointDhExtractRoot
open PqxdhServerRelatedRootConsumer (Returned AuxSpec State impl)
open PqxdhBeaconPhase2Preparation (Word32)

def completed (binding : session.RegistrationBinding) : RustM (Option Returned) → RustM agreement.AgreementEffect
  | .fail error => .fail error
  | .div => .div
  | .ok none => .ok (.Rejected .None)
  | .ok (some result) => .ok (.ServerComplete
      ⟨result.pending, binding, ⟨PqxdhRootTableInitialization.rootArray result.root⟩⟩)

noncomputable def client (binding : session.RegistrationBinding)
    (input : Inputs registration.InitPacket Unit PeerEncoding) :
    OracleComp PqxdhServerRelatedRootConsumer.Spec (RustM agreement.AgreementEffect) :=
  completed binding <$> PqxdhServerRelatedRootConsumer.client binding.server_pin.binding input

noncomputable def source {Auxiliary : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (aux : QueryImpl AuxSpec (StateT Auxiliary ProbComp)) (control : pqxdh.ServerState)
    (binding : session.RegistrationBinding) (input : Inputs registration.InitPacket Unit Word32) :
    StateT (State Auxiliary) ProbComp (RustM agreement.AgreementEffect) :=
  completed binding <$> PqxdhServerRelatedRootConsumer.source kdf hmac aux control binding.server_pin.binding input

theorem client_source {Auxiliary : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring kdf.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (aux : QueryImpl AuxSpec (StateT Auxiliary ProbComp))
    (control : pqxdh.ServerState) (binding : session.RegistrationBinding)
    (input : Inputs registration.InitPacket Unit PeerEncoding)
    (references : PqxdhServerStaticDhSource.References domain input) :
    simulateQ (impl (sourceImpl kdf hmac joint dh seed scalar) aux) (client binding input) =
      source kdf hmac aux control binding (concreteInputs joint seed input) := by
  simp only [client, source, simulateQ_map,
    PqxdhServerRelatedRootConsumer.client_source kdf hmac joint dh domain secretOfSeed wiring
      seed scalar aux control binding.server_pin.binding input references]

noncomputable def stage {Auxiliary : Type} {joint : Primitives} (domain : PublicDomain joint)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit)
      (StateT (State Auxiliary) ProbComp))
    (visit : Word32 → StateT (State Auxiliary) ProbComp Unit)
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (aux : QueryImpl AuxSpec (StateT Auxiliary ProbComp))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State Auxiliary) ProbComp (RustM agreement.AgreementEffect) := do
  let input ← simulateQ (prefixImpl domain preImpl visit)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
  match input with
  | none => pure (.ok (.Rejected .None))
  | some input => simulateQ (impl family aux) (client authenticated.binding input)

noncomputable def nativeStage {Auxiliary : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (seed : IdentitySeed)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit)
      (StateT (State Auxiliary) ProbComp))
    (visit : Word32 → StateT (State Auxiliary) ProbComp Unit)
    (aux : QueryImpl AuxSpec (StateT Auxiliary ProbComp)) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State Auxiliary) ProbComp (RustM agreement.AgreementEffect) := do
  let input ← simulateQ (nativeImpl joint seed preImpl visit)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
  match input with
  | none => pure (.ok (.Rejected .None))
  | some input => source kdf hmac aux control authenticated.binding input

set_option backward.isDefEq.respectTransparency false in
/-- The actual post-authentication prefix derives every address reference; the whole native binding and full family state are retained. -/
theorem stage_source {Auxiliary : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring kdf.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit)
      (StateT (State Auxiliary) ProbComp))
    (visit : Word32 → StateT (State Auxiliary) ProbComp Unit)
    (aux : QueryImpl AuxSpec (StateT Auxiliary ProbComp)) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    stage domain preImpl visit (sourceImpl kdf hmac joint dh seed scalar) aux packet authenticated =
      nativeStage kdf hmac joint seed preImpl visit aux control packet authenticated := by
  funext initial
  change (stage domain preImpl visit (sourceImpl kdf hmac joint dh seed scalar) aux packet authenticated).run initial =
    (nativeStage kdf hmac joint seed preImpl visit aux control packet authenticated).run initial
  simp only [stage, nativeStage,
    PqxdhServerStaticDhSource.collectVerified_realization joint domain seed,
    StateT.run_bind, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨input, final⟩ reached
  cases input with
  | none => rfl
  | some input =>
      have references := PqxdhServerStaticDhSource.collectVerified_references domain preImpl visit
        (RegistrationRootInput.verified packet authenticated) initial final input reached
      exact congrFun (client_source kdf hmac joint dh domain secretOfSeed wiring seed scalar aux
        control authenticated.binding input references) final

/-- Fixed-HKDF functional correctness discharges the real-family interpretation without an assumed registration or root simulation. -/
theorem stage_real {Auxiliary : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect kdf hmac) (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring kdf.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit)
      (StateT (State Auxiliary) ProbComp))
    (visit : Word32 → StateT (State Auxiliary) ProbComp Unit)
    (aux : QueryImpl AuxSpec (StateT Auxiliary ProbComp)) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    stage domain preImpl visit
        (PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar ∘ₛ reduction) aux packet authenticated =
      nativeStage kdf hmac joint seed preImpl visit aux control packet authenticated := by
  rw [reduction_step kdf hmac correct]
  exact stage_source kdf hmac joint dh domain secretOfSeed wiring seed scalar preImpl visit aux control packet authenticated

end BeaconcryptCore.Computational.RegistrationRelatedRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationRelatedRoot.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRelatedRoot.client_source

/-- info: 'BeaconcryptCore.Computational.RegistrationRelatedRoot.stage_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRelatedRoot.stage_source

/-- info: 'BeaconcryptCore.Computational.RegistrationRelatedRoot.stage_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRelatedRoot.stage_real
