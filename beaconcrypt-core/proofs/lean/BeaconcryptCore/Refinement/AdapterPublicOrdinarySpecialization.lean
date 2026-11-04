-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicOrdinaryRequestExtraction
/-! The stateful request lift specializes to the actual extracted SDK ownership shell, including every public role branch, admission check, driver call and returned-object update. Its individual source drivers are the already extracted outer send and receive bodies. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization
open beaconcrypt_public_wrapper
variable [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform]
variable [AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [beaconcrypt_record_send.ratchet.Operations] [beaconcrypt.ratchet.Operations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]

omit [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform] [AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [beaconcrypt_record_send.ratchet.Operations] [beaconcrypt.ratchet.Operations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
theorem take (slot : ratchet.RatchetKernelSlot) :
    beaconcrypt_public_ordinary_request.ratchet.RatchetKernelSlot.take (m := RustM) slot =
      beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.take slot := by rfl

omit [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform] [AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [beaconcrypt_record_send.ratchet.Operations] [beaconcrypt.ratchet.Operations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
theorem put (slot : ratchet.RatchetKernelSlot) (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary_request.ratchet.RatchetKernelSlot.put (m := RustM) slot kernel =
      beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.put slot kernel := by rfl

omit [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem send (bytes : Slice U8) (target sender : U64) (ad : Array U8 281#usize)
    (manager : ratchet.RatchetManager) :
    beaconcrypt_public_ordinary_request.ratchet.encrypt_message_with_ratchet (m := RustM) bytes target sender ad manager =
      beaconcrypt_public_ordinary.ratchet.encrypt_message_with_ratchet bytes target sender ad manager := by rfl

omit [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem receive (bytes : Slice U8) (sender : U64) (ad : Array U8 281#usize)
    (manager : ratchet.RatchetManager) :
    beaconcrypt_public_ordinary_request.ratchet.decrypt_message_with_ratchet (m := RustM) bytes sender ad manager =
      beaconcrypt_public_ordinary.ratchet.decrypt_message_with_ratchet bytes sender ad manager := by rfl

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem beacon_send (self : beacon.Beacon) (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.beacon.Beacon.encrypt_message (m := RustM) self bytes =
      beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message self bytes := by rfl

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem beacon_receive (self : beacon.Beacon) (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.beacon.Beacon.decrypt_message (m := RustM) self bytes =
      beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message self bytes := by rfl

theorem server_send (self : server.Server) (bytes : Slice U8) (target : U64) :
    beaconcrypt_public_ordinary_request.server.Server.encrypt_message (m := RustM) self bytes target =
      beaconcrypt_public_ordinary.server.Server.encrypt_message self bytes target := by rfl

theorem server_receive (self : server.Server) (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.server.Server.decrypt_message (m := RustM) self bytes =
      beaconcrypt_public_ordinary.server.Server.decrypt_message self bytes := by rfl

end BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.take

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.put

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.send

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.receive

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.beacon_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.beacon_send

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.beacon_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.beacon_receive

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.server_send

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.server_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization.server_receive
