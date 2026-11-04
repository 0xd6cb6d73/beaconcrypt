-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterSource
import BeaconcryptCore.PanicFreedom.AdapterPublicBeacon
import BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource

/-! Public registration safety with one source-selected schema writer dictionary for the complete call. The remaining contracts omit serializer normality: signed-view packet shape and the actual allocated capacity discharge the native writer calls. Source sealing and fixed-three routing remain selected in the server response path. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationWriterSource
open Refinement AdapterNormal beaconcrypt_public_wrapper
open BeaconcryptCore.Computational.RegistrationNativeSourceEncoders (sourceOperations)
open RegistrationSerializerReachableSource (OtherBranches)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations] [authentication : beaconcrypt.auth.Operations]
variable [allocator : AdapterWirePrimitive.Operations]

structure BundleContracts : Prop where
  init : AdapterPublicRegistrationLoops.InitContracts
  kxPublicBytes : ∀ key, Normal (crypto.kxPublicBytes key)
  publicLeaves : AdapterPublicTrivial.Contracts
  allocation : AdapterWire.Contracts
  kemPublicBytes : ∀ key, Normal (crypto.kemPublicBytes key)

theorem bundle_contracts (contracts : BundleContracts) (other : OtherBranches) :
    letI := sourceOperations other
    AdapterPublicBeacon.BundleContracts := by
  rcases contracts with ⟨init, kxPublicBytes, publicLeaves, allocation, kemPublicBytes⟩
  let _ := sourceOperations other
  exact {
    init := init
    kxPublicBytes := kxPublicBytes
    publicLeaves := publicLeaves
    writer := AdapterRegistrationWriterSource.init_caller_contracts allocation other
    allocation := allocation
    kemPublicBytes := kemPublicBytes }

theorem get_registration_bundle_total (contracts : BundleContracts) (other : OtherBranches)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.GenerationContracts generator)
    (self : beacon.Beacon) (rng : R) :
    letI := sourceOperations other
    Normal (beacon.Beacon.get_registration_bundle_with_rng generator self rng) := by
  have selected := bundle_contracts contracts other
  let _ := sourceOperations other
  exact AdapterPublicBeacon.get_registration_bundle_total selected generator random self rng

theorem get_registration_bundle_preserves (contracts : BundleContracts) (other : OtherBranches)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.GenerationContracts generator)
    (self : beacon.Beacon) (rng : R) (valid : AdapterPublicOrdinary.ValidBeacon self) :
    letI := sourceOperations other
    Ensures (beacon.Beacon.get_registration_bundle_with_rng generator self rng)
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2.1) := by
  have selected := bundle_contracts contracts other
  let _ := sourceOperations other
  exact AdapterPublicBeacon.get_registration_bundle_preserves selected generator random self rng valid

variable [PublicWrapperPlatform.Allocator] [containers : PublicWrapperPlatform.ContainerOperations]
variable [recordOps : beaconcrypt.ratchet.Operations] [primitives : AdapterSealPrimitive.Operations]
variable [FrameDispatchFallback.Operations]

structure ResponseContracts : Prop where
  publicLeaves : AdapterPublicTrivial.Contracts
  allocation : AdapterWire.Contracts
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

omit [FrameDispatchFallback.Operations] in
theorem response_contracts (contracts : ResponseContracts) (other : OtherBranches) :
    letI := sourceOperations other
    AdapterPublicServerBuildSource.Contracts := by
  rcases contracts with ⟨publicLeaves, allocation, sealingPrimitive, parse, initial, kdf,
    commitment, sign, contains, reserve, entry, insert⟩
  let _ := sourceOperations other
  exact {
    publicLeaves := publicLeaves
    allocation := allocation
    serialization := AdapterRegistrationWriterSource.response_caller_contracts allocation other
    sealingPrimitive := sealingPrimitive
    parse := parse
    initial := initial
    kdf := kdf
    commitment := commitment
    sign := sign
    contains := contains
    reserve := reserve
    entry := entry
    insert := insert }

theorem build_registration_response_total (contracts : ResponseContracts) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (self : server.Server) (registration : server.RegistrationOutput) (data : core.option.Option (Slice U8)) :
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
    Normal (server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self registration data) := by
  have selected := response_contracts contracts other
  let _ := sourceOperations other
  exact AdapterPublicServerBuildSource.build_registration_response_total selected sealFallback writerFallback
    self registration data

variable [AdapterPublicOrdinaryPlatform.LookupOperations]

theorem build_registration_response_preserves (contracts : ResponseContracts) (other : OtherBranches)
    (laws : AdapterPublicServerBuildState.ContainerContracts)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (self : server.Server) (registration : server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (valid : AdapterPublicOrdinary.ValidServer self) :
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
    Ensures (server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self registration data)
      (fun result => AdapterPublicOrdinary.ValidServer result.2) := by
  have selected := response_contracts contracts other
  let _ := sourceOperations other
  exact AdapterPublicServerBuildSource.build_registration_response_preserves selected laws sealFallback writerFallback
    self registration data valid

end BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationWriterSource
