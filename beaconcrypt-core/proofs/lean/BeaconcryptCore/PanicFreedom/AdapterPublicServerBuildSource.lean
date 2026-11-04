-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildState
import BeaconcryptCore.PanicFreedom.AdapterSeal
import BeaconcryptCore.PanicFreedom.AdapterRecordRouting

/-! Direct RustM source composition for the public response builder. The selected local dictionary replaces both opaque adapter children with their original extracted seal and routing implementations. Their execution safety follows from primitive normality and content-preserving reservation; no normality of the prior child callbacks or of the complete builder is assumed. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource
open Refinement AdapterNormal beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [primitives : AdapterSealPrimitive.Operations] [wire : AdapterWirePrimitive.Operations]
variable [FrameDispatchFallback.Operations]

@[instance_reducible] def sourceLocalOperations
    (previous : PublicWrapperPlatform.LocalOperations)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) : PublicWrapperPlatform.LocalOperations :=
  { previous with
    ratchet_execute_seal_request := @beaconcrypt_seal.ratchet.execute_seal_request primitives
      (AdapterSealSourceJoin.sourceCallbacks sealFallback)
    ratchet_execute_write_request := @beaconcrypt_record_routing.ratchet.execute_write_request
      (AdapterRecordHelperRouting.sourceCallbacks writerFallback) }

omit primitive [PublicWrapperPlatform.Allocator] in
theorem source_sealing (previous : PublicWrapperPlatform.LocalOperations)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (request : record_effects.AeadSealRequest) :
    (sourceLocalOperations previous sealFallback writerFallback).ratchet_execute_seal_request request =
      @beaconcrypt_seal.ratchet.execute_seal_request primitives
        (AdapterSealSourceJoin.sourceCallbacks sealFallback) request := rfl

omit primitive [PublicWrapperPlatform.Allocator] in
theorem source_writing (previous : PublicWrapperPlatform.LocalOperations)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (request : record_effects.RecordWriteRequest) :
    (sourceLocalOperations previous sealFallback writerFallback).ratchet_execute_write_request request =
      @beaconcrypt_record_routing.ratchet.execute_write_request
        (AdapterRecordHelperRouting.sourceCallbacks writerFallback) request := rfl

/- Both prior child callbacks can fail or diverge: the selected source dictionary never uses them. -/
omit primitive [PublicWrapperPlatform.Allocator] in
theorem prior_children_irrelevant (previous : PublicWrapperPlatform.LocalOperations)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) :
    sourceLocalOperations
      { previous with ratchet_execute_seal_request := fun _ => fail .panic
                      ratchet_execute_write_request := fun _ => div }
      sealFallback writerFallback = sourceLocalOperations previous sealFallback writerFallback := rfl

variable [localOps : PublicWrapperPlatform.LocalOperations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [containers : PublicWrapperPlatform.ContainerOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
variable [writer : RegistrationWriterPrimitive.Operations]

/-- Remaining individual leaves of the public builder, with seal/write discharged by the source implementation. -/
structure Contracts : Prop where
  publicLeaves : AdapterPublicTrivial.Contracts
  allocation : AdapterWire.Contracts
  serialization : AdapterRegistrationWriterCallers.ResponseCallerContracts
  sealingPrimitive : AdapterSeal.PrimitiveContracts
  parse : ∀ input, Normal (primitive.parse input)
  initial : ∀ request, Normal (localOps.ratchet_initial_ratchet_hkdf request)
  kdf : ∀ request, Normal (recordOps.kdf request)
  commitment : ∀ transcript, Normal (recordOps.hash transcript)
  sign : ∀ identity request, Normal (localOps.auth_MldsaIdentity_sign_requested identity request)
  contains : ∀ map key, Normal (AdapterPublicServerBuild.mapContains map key)
  reserve : ∀ map, Normal (AdapterPublicServerBuild.mapReserve map)
  entry : ∀ map key, Normal (AdapterPublicServerBuild.mapEntry map key)
  insert : ∀ entry remote, Normal (AdapterPublicServerBuild.vacantInsert entry remote)

theorem component_contracts (contracts : Contracts)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) :
    letI := sourceLocalOperations localOps sealFallback writerFallback
    AdapterPublicServerBuild.Contracts := by
  rcases contracts with ⟨publicLeaves, allocation, serialization, sealingPrimitive, parse,
    initial, kdf, commitment, sign, contains, reserve, entry, insert⟩
  rcases publicLeaves with ⟨mldsaPublic, edPublicBytes, hash⟩
  let _ := sourceLocalOperations localOps sealFallback writerFallback
  exact {
    publicLeaves := {
      mldsaPublic := mldsaPublic
      edPublicBytes := edPublicBytes
      hash := hash }
    allocation := allocation
    serialization := serialization
    parse := parse
    initial := initial
    kdf := kdf
    commitment := commitment
    sealing := AdapterSeal.execute_seal_request_source_total
      sealingPrimitive allocation sealFallback
    writing := AdapterRecordRouting.source_callbacks_total allocation writerFallback
    sign := sign
    contains := contains
    reserve := reserve
    entry := entry
    insert := insert }

theorem build_registration_response_total (contracts : Contracts)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (self : server.Server)
    (reg_out : server.RegistrationOutput) (data : core.option.Option (Slice U8)) :
    letI := sourceLocalOperations localOps sealFallback writerFallback
    ∃ result, server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
      self reg_out data = ok result := by
  have selected := component_contracts contracts sealFallback writerFallback
  let _ := sourceLocalOperations localOps sealFallback writerFallback
  exact AdapterPublicServerBuild.build_registration_response_total selected self reg_out data

variable [lookup : AdapterPublicOrdinaryPlatform.LookupOperations]

omit crypto authentication recordOps writer in
theorem container_contracts (laws : AdapterPublicServerBuildState.ContainerContracts)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) :
    letI := sourceLocalOperations localOps sealFallback writerFallback
    AdapterPublicServerBuildState.ContainerContracts := by
  rcases laws with ⟨reserve, entry, insert⟩
  let _ := sourceLocalOperations localOps sealFallback writerFallback
  exact { reserve := reserve, entry := entry, insert := insert }

theorem build_registration_response_preserves (contracts : Contracts)
    (laws : AdapterPublicServerBuildState.ContainerContracts)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (self : server.Server)
    (reg_out : server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (valid : AdapterPublicOrdinary.ValidServer self) :
    letI := sourceLocalOperations localOps sealFallback writerFallback
    Ensures (server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self reg_out data)
      (fun result => AdapterPublicOrdinary.ValidServer result.2) := by
  have selected := component_contracts contracts sealFallback writerFallback
  have selectedLaws := container_contracts laws sealFallback writerFallback
  let _ := sourceLocalOperations localOps sealFallback writerFallback
  exact AdapterPublicServerBuildState.build_registration_response_preserves
    selected selectedLaws self reg_out data valid

end BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource.build_registration_response_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource.build_registration_response_total

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource.build_registration_response_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource.build_registration_response_preserves

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource.prior_children_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource.prior_children_irrelevant
