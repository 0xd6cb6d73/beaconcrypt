-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterRatchetKdf
import BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary
import BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource
import BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationWriterSource

/-! Actual extracted ratchet KDF callbacks replace the record-send, record-receive and public initial-KDF dictionary fields. Successful HKDF API execution on the reached fixed-width domain discharges KDF normality. The remaining interfaces contain only other reached leaves and the existing fixed state laws. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterRatchetKdfSource
open Refinement AdapterNormal beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [operations : AdapterRatchetKdfPrimitive.Operations]

@[instance_reducible] def sourceSendOperations
    (previous : beaconcrypt_record_send.ratchet.Operations) :
    beaconcrypt_record_send.ratchet.Operations :=
  { previous with kdf := beaconcrypt_ratchet_kdf.ratchet.ratchet_hkdf }

@[instance_reducible] def sourceReceiveOperations
    (previous : beaconcrypt.ratchet.Operations) : beaconcrypt.ratchet.Operations :=
  { previous with kdf := beaconcrypt_ratchet_kdf.ratchet.ratchet_hkdf }

theorem source_send_kdf (previous : beaconcrypt_record_send.ratchet.Operations)
    (request : ratchet.SymmetricRatchetKdfRequest) :
    (sourceSendOperations previous).kdf request =
      beaconcrypt_ratchet_kdf.ratchet.ratchet_hkdf request := rfl

theorem source_receive_kdf (previous : beaconcrypt.ratchet.Operations)
    (request : ratchet.SymmetricRatchetKdfRequest) :
    (sourceReceiveOperations previous).kdf request =
      beaconcrypt_ratchet_kdf.ratchet.ratchet_hkdf request := rfl

section Send
variable [sendOps : beaconcrypt_record_send.ratchet.Operations]

structure SendContracts : Prop where
  sealing : ∀ request, Normal (sendOps.sealing request)
  hash : ∀ transcript, Normal (sendOps.hash transcript)
  writer : ∀ request, Normal (sendOps.writer request)

theorem send_contracts (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : SendContracts) :
    letI := sourceSendOperations sendOps
    AdapterRecordSend.Contracts := by
  rcases leaves with ⟨sealing, hash, writer⟩
  let _ := sourceSendOperations sendOps
  exact { kdf := AdapterRatchetKdf.ratchet_hkdf_total kdf
          sealing := sealing, hash := hash, writer := writer }

theorem execute_record_send_total (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : SendContracts) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (context : record_effects.SealFrameContext) :
    letI := sourceSendOperations sendOps
    Normal (beaconcrypt_record_send.ratchet.execute_record_send kernel context) := by
  have selected := send_contracts kdf leaves
  let _ := sourceSendOperations sendOps
  exact AdapterRecordSend.execute_record_send_total selected kernel context

theorem beacon_encrypt_message_preserves (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : SendContracts) (self : beacon.Beacon) (bytes : Slice U8)
    (valid : AdapterPublicOrdinary.ValidBeacon self) :
    letI := sourceSendOperations sendOps
    Ensures (beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message self bytes)
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2) := by
  have selected := send_contracts kdf leaves
  let _ := sourceSendOperations sendOps
  exact AdapterPublicOrdinary.beacon_encrypt_message_preserves selected self bytes valid

theorem beacon_encrypt_message_total (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : SendContracts) (self : beacon.Beacon) (bytes : Slice U8)
    (valid : AdapterPublicOrdinary.ValidBeacon self) :
    letI := sourceSendOperations sendOps
    Normal (beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message self bytes) :=
  ensures_normal (beacon_encrypt_message_preserves kdf leaves self bytes valid)

end Send

section Receive
variable [recordOps : beaconcrypt.ratchet.Operations]

structure ReceiveContracts : Prop where
  hash : ∀ transcript, Normal (recordOps.hash transcript)
  aead : ∀ request, Normal (recordOps.aead request)
  compare : ∀ left right, Normal (recordOps.compare left right)

theorem receive_contracts (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : ReceiveContracts) :
    letI := sourceReceiveOperations recordOps
    AdapterRecordReceive.Contracts := by
  rcases leaves with ⟨hash, aead, compare⟩
  let _ := sourceReceiveOperations recordOps
  exact { kdf := AdapterRatchetKdf.ratchet_hkdf_total kdf
          hash := hash, aead := aead, compare := compare }

theorem execute_record_receive_total (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : ReceiveContracts) (effect : record_effects.RecordReceiveEffect) :
    letI := sourceReceiveOperations recordOps
    Normal (beaconcrypt.ratchet.execute_record_receive effect) := by
  have selected := receive_contracts kdf leaves
  let _ := sourceReceiveOperations recordOps
  exact AdapterRecordReceive.execute_record_receive_total selected effect

theorem beacon_decrypt_message_preserves (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : ReceiveContracts) (self : beacon.Beacon) (bytes : Slice U8)
    (valid : AdapterPublicOrdinary.ValidBeacon self) :
    letI := sourceReceiveOperations recordOps
    Ensures (beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message self bytes)
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2) := by
  have selected := receive_contracts kdf leaves
  let _ := sourceReceiveOperations recordOps
  exact AdapterPublicOrdinary.beacon_decrypt_message_preserves selected self bytes valid

theorem beacon_decrypt_message_total (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : ReceiveContracts) (self : beacon.Beacon) (bytes : Slice U8)
    (valid : AdapterPublicOrdinary.ValidBeacon self) :
    letI := sourceReceiveOperations recordOps
    Normal (beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message self bytes) :=
  ensures_normal (beacon_decrypt_message_preserves kdf leaves self bytes valid)

end Receive

section Maps
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]

section Send
variable [sendOps : beaconcrypt_record_send.ratchet.Operations]

theorem server_encrypt_message_preserves (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : SendContracts) (lookups : AdapterPublicOrdinary.LookupContracts)
    (self : server.Server) (bytes : Slice U8) (key : U64)
    (valid : AdapterPublicOrdinary.ValidServer self) :
    letI := sourceSendOperations sendOps
    Ensures (beaconcrypt_public_ordinary.server.Server.encrypt_message self bytes key)
      (fun result => AdapterPublicOrdinary.ValidServer result.2) := by
  have selected := send_contracts kdf leaves
  let _ := sourceSendOperations sendOps
  exact AdapterPublicOrdinary.server_encrypt_message_preserves selected lookups self bytes key valid

theorem server_encrypt_message_total (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : SendContracts) (lookups : AdapterPublicOrdinary.LookupContracts)
    (self : server.Server) (bytes : Slice U8) (key : U64)
    (valid : AdapterPublicOrdinary.ValidServer self) :
    letI := sourceSendOperations sendOps
    Normal (beaconcrypt_public_ordinary.server.Server.encrypt_message self bytes key) :=
  ensures_normal (server_encrypt_message_preserves kdf leaves lookups self bytes key valid)

end Send

section Receive
variable [recordOps : beaconcrypt.ratchet.Operations]

theorem server_decrypt_message_preserves (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : ReceiveContracts) (lookups : AdapterPublicOrdinary.LookupContracts)
    (self : server.Server) (bytes : Slice U8) (valid : AdapterPublicOrdinary.ValidServer self) :
    letI := sourceReceiveOperations recordOps
    Ensures (beaconcrypt_public_ordinary.server.Server.decrypt_message self bytes)
      (fun result => AdapterPublicOrdinary.ValidServer result.2) := by
  have selected := receive_contracts kdf leaves
  let _ := sourceReceiveOperations recordOps
  exact AdapterPublicOrdinary.server_decrypt_message_preserves selected lookups self bytes valid

theorem server_decrypt_message_total (kdf : AdapterRatchetKdf.Contracts 76#usize)
    (leaves : ReceiveContracts) (lookups : AdapterPublicOrdinary.LookupContracts)
    (self : server.Server) (bytes : Slice U8) (valid : AdapterPublicOrdinary.ValidServer self) :
    letI := sourceReceiveOperations recordOps
    Normal (beaconcrypt_public_ordinary.server.Server.decrypt_message self bytes) :=
  ensures_normal (server_decrypt_message_preserves kdf leaves lookups self bytes valid)

end Receive
end Maps

section Local
variable [platform : PublicWrapperPlatform.Platform]

@[instance_reducible] def sourceLocalOperations (previous : PublicWrapperPlatform.LocalOperations) :
    PublicWrapperPlatform.LocalOperations :=
  { previous with ratchet_initial_ratchet_hkdf := beaconcrypt_ratchet_kdf.ratchet.initial_ratchet_hkdf }

theorem source_initial_kdf (previous : PublicWrapperPlatform.LocalOperations)
    (request : ratchet.InitialRatchetKdfRequest) :
    (sourceLocalOperations previous).ratchet_initial_ratchet_hkdf request =
      beaconcrypt_ratchet_kdf.ratchet.initial_ratchet_hkdf request := rfl

variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [recordOps : beaconcrypt.ratchet.Operations] [authentication : beaconcrypt.auth.Operations]

structure FinishContracts : Prop where
  agreement : AdapterBeaconAgreementSafety.Contracts
  record : ReceiveContracts
  response : AdapterResponseAuthentication.Contracts

theorem finish_contracts (initial : AdapterRatchetKdf.Contracts 64#usize)
    (ongoing : AdapterRatchetKdf.Contracts 76#usize) (leaves : FinishContracts) :
    letI := sourceReceiveOperations recordOps
    letI := sourceLocalOperations localOps
    AdapterRegistrationDecoderSource.FinishContracts := by
  rcases leaves with ⟨agreement, record, response⟩
  have selected := receive_contracts ongoing record
  let _ := sourceReceiveOperations recordOps
  let _ := sourceLocalOperations localOps
  exact { agreement := agreement, record := selected, response := response
          initialKdf := AdapterRatchetKdf.initial_ratchet_hkdf_total initial }

variable [RegistrationValidatorPrimitive.Operations]

theorem finish_registration_preserves (initial : AdapterRatchetKdf.Contracts 64#usize)
    (ongoing : AdapterRatchetKdf.Contracts 76#usize) (leaves : FinishContracts)
    (self : beacon.Beacon) (bytes : Slice U8) (valid : AdapterPublicOrdinary.ValidBeacon self) :
    letI := sourceReceiveOperations recordOps
    letI := sourceLocalOperations localOps
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    Ensures (beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes)
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2) := by
  have selected := finish_contracts initial ongoing leaves
  let _ := sourceReceiveOperations recordOps
  let _ := sourceLocalOperations localOps
  exact AdapterRegistrationDecoderSource.finish_registration_preserves selected self bytes valid

theorem finish_registration_total (initial : AdapterRatchetKdf.Contracts 64#usize)
    (ongoing : AdapterRatchetKdf.Contracts 76#usize) (leaves : FinishContracts)
    (self : beacon.Beacon) (bytes : Slice U8) :
    letI := sourceReceiveOperations recordOps
    letI := sourceLocalOperations localOps
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    Normal (beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes) := by
  have selected := finish_contracts initial ongoing leaves
  let _ := sourceReceiveOperations recordOps
  let _ := sourceLocalOperations localOps
  exact AdapterRegistrationDecoderSource.finish_registration_total selected self bytes

end Local

section Response
open BeaconcryptCore.Computational.RegistrationNativeSourceEncoders (sourceOperations)
open RegistrationSerializerReachableSource (OtherBranches)
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.Allocator]
variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [containers : PublicWrapperPlatform.ContainerOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
variable [allocator : AdapterWirePrimitive.Operations] [primitives : AdapterSealPrimitive.Operations]
variable [FrameDispatchFallback.Operations]

structure ResponseContracts : Prop where
  publicLeaves : AdapterPublicTrivial.Contracts
  hash : ∀ request, Normal (authentication.hash request)
  allocation : AdapterWire.Contracts
  sealingPrimitive : AdapterSeal.PrimitiveContracts
  parse : ∀ input, Normal (primitive.parse input)
  commitment : ∀ transcript, Normal (recordOps.hash transcript)
  sign : ∀ identity request, Normal (localOps.auth_MldsaIdentity_sign_requested identity request)
  contains : ∀ map key, Normal (AdapterPublicServerBuild.mapContains map key)
  reserve : ∀ map, Normal (AdapterPublicServerBuild.mapReserve map)
  entry : ∀ map key, Normal (AdapterPublicServerBuild.mapEntry map key)
  insert : ∀ entry remote, Normal (AdapterPublicServerBuild.vacantInsert entry remote)

omit [FrameDispatchFallback.Operations] in
theorem response_contracts (initial : AdapterRatchetKdf.Contracts 64#usize)
    (ongoing : AdapterRatchetKdf.Contracts 76#usize) (leaves : ResponseContracts) :
    letI := sourceReceiveOperations recordOps
    letI := sourceLocalOperations localOps
    AdapterPublicRegistrationWriterSource.ResponseContracts := by
  rcases leaves with ⟨publicLeaves, hash, allocation, sealingPrimitive, parse, commitment,
    sign, contains, reserve, entry, insert⟩
  rcases publicLeaves with ⟨mldsaPublic, edPublicBytes⟩
  let _ := sourceReceiveOperations recordOps
  let _ := sourceLocalOperations localOps
  exact {
    publicLeaves := { mldsaPublic := mldsaPublic, edPublicBytes := edPublicBytes }
    hash := hash
    allocation := allocation
    sealingPrimitive := sealingPrimitive
    parse := parse
    initial := AdapterRatchetKdf.initial_ratchet_hkdf_total initial
    kdf := AdapterRatchetKdf.ratchet_hkdf_total ongoing
    commitment := commitment
    sign := sign
    contains := contains
    reserve := reserve
    entry := entry
    insert := insert }

theorem build_registration_response_total (initial : AdapterRatchetKdf.Contracts 64#usize)
    (ongoing : AdapterRatchetKdf.Contracts 76#usize) (leaves : ResponseContracts)
    (other : OtherBranches) (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (self : server.Server)
    (registration : server.RegistrationOutput) (data : core.option.Option (Slice U8)) :
    letI := sourceReceiveOperations recordOps
    letI := sourceLocalOperations localOps
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations
      (inferInstance : PublicWrapperPlatform.LocalOperations) sealFallback writerFallback
    Normal (server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self registration data) := by
  have selected := response_contracts initial ongoing leaves
  let _ := sourceReceiveOperations recordOps
  let _ := sourceLocalOperations localOps
  exact AdapterPublicRegistrationWriterSource.build_registration_response_total
    selected other sealFallback writerFallback self registration data

variable [AdapterPublicOrdinaryPlatform.LookupOperations]

omit authentication recordOps allocator primitives [FrameDispatchFallback.Operations] in
theorem local_container_contracts (laws : AdapterPublicServerBuildState.ContainerContracts) :
    letI := sourceLocalOperations localOps
    AdapterPublicServerBuildState.ContainerContracts := by
  rcases laws with ⟨reserve, entry, insert⟩
  let _ := sourceLocalOperations localOps
  exact { reserve := reserve, entry := entry, insert := insert }

theorem build_registration_response_preserves (initial : AdapterRatchetKdf.Contracts 64#usize)
    (ongoing : AdapterRatchetKdf.Contracts 76#usize) (leaves : ResponseContracts)
    (laws : AdapterPublicServerBuildState.ContainerContracts)
    (other : OtherBranches) (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (self : server.Server)
    (registration : server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (valid : AdapterPublicOrdinary.ValidServer self) :
    letI := sourceReceiveOperations recordOps
    letI := sourceLocalOperations localOps
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations
      (inferInstance : PublicWrapperPlatform.LocalOperations) sealFallback writerFallback
    Ensures (server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self registration data)
      (fun result => AdapterPublicOrdinary.ValidServer result.2) := by
  have selected := response_contracts initial ongoing leaves
  have selectedLaws := local_container_contracts laws
  let _ := sourceReceiveOperations recordOps
  let _ := sourceLocalOperations localOps
  exact AdapterPublicRegistrationWriterSource.build_registration_response_preserves
    selected other selectedLaws sealFallback writerFallback self registration data valid

end Response

end BeaconcryptCore.PanicFreedom.AdapterRatchetKdfSource
