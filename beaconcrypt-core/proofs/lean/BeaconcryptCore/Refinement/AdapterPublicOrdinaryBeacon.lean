-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryKernel
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon
open AdapterPublicWrapperRustT (RustT)
open AdapterRecordRequestMonad (liftRust)
open beaconcrypt_public_wrapper
open AdapterPublicOrdinaryEnvelope (manager)
variable {m : Type → Type} [Monad m] [LawfulMonad m]
omit [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl

variable [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [AdapterInitEdPrimitive.Operations]
variable [AdapterPublicOrdinaryRequestMonad.Operations (RustT m)]

theorem send (self : beacon.Beacon) (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state = .Established control binding (manager kernel)) (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.beacon.Beacon.encrypt_message (m := RustT m) self bytes =
    (do
      let prepared ← (liftRust (AdapterPublicOrdinaryEnvelope.prepareSend bytes control.server_binding.identity_key_id
        self.identity_key_kid binding.associated_data kernel) : RustT m _)
      match prepared with
      | none => pure (none,self)
      | some context => do
          let sent ← AdapterPublicOrdinaryRequestMonad.Operations.send kernel context
          pure (sent.2,{self with state := .Established control binding (manager sent.1)})) := by
  unfold beaconcrypt_public_ordinary_request.beacon.Beacon.encrypt_message
  rw [stored]
  change (do
    let server ← (liftRust (.ok control.server_binding.identity_key_id) : RustT m U64)
    let ad ← (liftRust (.ok binding.associated_data) : RustT m (Array U8 281#usize))
    let sent ← beaconcrypt_public_ordinary_request.ratchet.encrypt_message_with_ratchet (m := RustT m)
      bytes server self.identity_key_kid ad (manager kernel)
    pure (sent.1,{self with state := .Established control binding sent.2})) = _
  simp only [lift_ok,pure_bind]
  rw [AdapterPublicOrdinaryEnvelope.send_frame]
  simp only [bind_assoc]
  apply bind_congr
  intro prepared
  cases prepared
  · simp only [pure_bind]
    cases self
    cases stored
    rfl
  · simp only [bind_assoc]
    apply bind_congr
    intro sent
    simp only [pure_bind]


theorem receive (self : beacon.Beacon) (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state = .Established control binding (manager kernel)) (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.beacon.Beacon.decrypt_message (m := RustT m) self bytes =
    (do
      let prepared ← (liftRust (AdapterPublicOrdinaryEnvelope.prepareReceive bytes control.server_binding.identity_key_id) : RustT m _)
      match prepared with
      | none => pure (none,self)
      | some view => do
          let effect ← (liftRust (record_effects.begin_record_receive kernel view.sequence view.ciphertext binding.associated_data view.sender) : RustT m _)
          let received ← AdapterPublicOrdinaryRequestMonad.Operations.receive effect
          pure (received.2,{self with state := .Established control binding (manager received.1)})) := by
  unfold beaconcrypt_public_ordinary_request.beacon.Beacon.decrypt_message
  rw [stored]
  change (do
    let server ← (liftRust (.ok control.server_binding.identity_key_id) : RustT m U64)
    let ad ← (liftRust (.ok binding.associated_data) : RustT m (Array U8 281#usize))
    let received ← beaconcrypt_public_ordinary_request.ratchet.decrypt_message_with_ratchet (m := RustT m)
      bytes server ad (manager kernel)
    pure (received.1,{self with state := .Established control binding received.2})) = _
  simp only [lift_ok,pure_bind]
  rw [AdapterPublicOrdinaryEnvelope.receive_frame]
  simp only [bind_assoc]
  apply bind_congr
  intro prepared
  cases prepared
  · simp only [pure_bind]
    cases self
    cases stored
    rfl
  · simp only [bind_assoc]
    apply bind_congr
    intro effect
    apply bind_congr
    intro received
    simp only [pure_bind]

def Inactive (self : beacon.Beacon) : Prop :=
  match self.state with
  | .Established _ _ _ => False
  | _ => True

omit [LawfulMonad m] in
theorem send_inactive (self : beacon.Beacon) (inactive : Inactive self) (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.beacon.Beacon.encrypt_message (m := RustT m) self bytes =
      pure (none,self) := by
  unfold beaconcrypt_public_ordinary_request.beacon.Beacon.encrypt_message
  cases phase : self.state <;> try rfl
  simp only [Inactive,phase] at inactive

omit [LawfulMonad m] in
theorem receive_inactive (self : beacon.Beacon) (inactive : Inactive self) (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.beacon.Beacon.decrypt_message (m := RustT m) self bytes =
      pure (none,self) := by
  unfold beaconcrypt_public_ordinary_request.beacon.Beacon.decrypt_message
  cases phase : self.state <;> try rfl
  simp only [Inactive,phase] at inactive

end BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon.send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon.send

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon.receive

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon.send_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon.send_inactive

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon.receive_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon.receive_inactive
