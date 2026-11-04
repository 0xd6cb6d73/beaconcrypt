-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterFiniteCalls
import BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource
import BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationWriterSource
import BeaconcryptCore.PanicFreedom.AdapterSourceComposition

/-! Finite public-call safety with source decoders, source schema serializers, and source send sealing/routing selected once for the complete run. Ordinary send and receive share the selected record KDF/hash callbacks. Only the remaining individual execution contracts and fixed container laws are required. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace BeaconcryptCore.PanicFreedom.AdapterFiniteCallsSource
open Refinement AdapterNormal AdapterPublicOrdinary beaconcrypt_public_wrapper
open RegistrationSerializerReachableSource (OtherBranches)
open BeaconcryptCore.Computational.RegistrationNativeSourceEncoders (sourceOperations)

variable [recordOps : beaconcrypt.ratchet.Operations] [primitives : AdapterSealPrimitive.Operations]
variable [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]

@[instance_reducible] def sourceSender (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) : beaconcrypt_record_send.ratchet.Operations :=
  AdapterSourceComposition.sendOperations recordOps.kdf recordOps.hash sealFallback writerFallback

theorem sender_contracts (record : AdapterRecordReceive.Contracts)
    (sealing : AdapterSeal.PrimitiveContracts) (allocation : AdapterWire.Contracts)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations) :
    letI := sourceSender sealFallback writerFallback
    AdapterRecordSend.Contracts := by
  let _ := sourceSender sealFallback writerFallback
  exact {
    kdf := record.kdf
    sealing := AdapterSeal.execute_seal_request_source_total sealing allocation sealFallback
    hash := record.hash
    writer := AdapterRecordRouting.source_callbacks_total allocation writerFallback }

section Beacon
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations] [authentication : beaconcrypt.auth.Operations]
variable [validator : RegistrationValidatorPrimitive.Operations]

structure BeaconContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  bundle : AdapterPublicRegistrationWriterSource.BundleContracts
  generation : AdapterPublicRegistrationLoops.GenerationContracts generator
  finish : AdapterRegistrationDecoderSource.FinishContracts
  sealing : AdapterSeal.PrimitiveContracts

theorem beacon_contracts {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : BeaconContracts generator) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations) :
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := sourceSender sealFallback writerFallback
    AdapterFiniteCalls.BeaconContracts generator := by
  have bundle := AdapterPublicRegistrationWriterSource.bundle_contracts contracts.bundle other
  have finish := AdapterRegistrationDecoderSource.finish_contracts contracts.finish
  have send := sender_contracts contracts.finish.record contracts.sealing contracts.bundle.allocation sealFallback writerFallback
  let _ := AdapterRegistrationDecoderSource.sourceCodecs
  let _ := sourceOperations other
  let _ := sourceSender sealFallback writerFallback
  exact { bundle := bundle, generation := contracts.generation, finish := finish, send := send }

theorem beacon_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : BeaconContracts generator) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (calls : List AdapterFiniteCalls.BeaconCall) (self : beacon.Beacon) (rng : R) (valid : ValidBeacon self) :
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.beaconCalls generator calls self rng) (fun result => ValidBeacon result.2.1) := by
  have selected := beacon_contracts generator contracts other sealFallback writerFallback
  let _ := AdapterRegistrationDecoderSource.sourceCodecs
  let _ := sourceOperations other
  let _ := sourceSender sealFallback writerFallback
  exact AdapterFiniteCalls.beacon_calls_preserve generator selected calls self rng valid

variable [AdapterBeaconConstructorPrimitive.Operations]

theorem constructor_and_beacon_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.BeaconContracts generator) (contracts : BeaconContracts generator)
    (other : OtherBranches) (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (identifier : U64)
    (identityKey mldsaKey : Slice U8) (calls : List AdapterFiniteCalls.BeaconCall) (rng : R) :
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.constructBeaconCalls generator identifier identityKey mldsaKey calls rng)
      (fun result => match result.1 with | .Err _ => True | .Ok completed => ValidBeacon completed.2) := by
  have selected := beacon_contracts generator contracts other sealFallback writerFallback
  let _ := AdapterRegistrationDecoderSource.sourceCodecs
  let _ := sourceOperations other
  let _ := sourceSender sealFallback writerFallback
  exact AdapterFiniteCalls.constructor_and_beacon_calls_preserve generator construction selected identifier identityKey mldsaKey calls rng

variable [standard : AdapterBeaconConstructorPrimitive.Standard]

theorem hosted_constructor_and_beacon_calls_preserve
    (construction : AdapterConstructors.BeaconContracts standard.os) (contracts : BeaconContracts standard.os)
    (other : OtherBranches) (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (identifier : U64)
    (identityKey mldsaKey : Slice U8) (calls : List AdapterFiniteCalls.BeaconCall) :
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.constructBeaconHostedCalls identifier identityKey mldsaKey calls)
      (fun result => match result with | .Err _ => True | .Ok completed => ValidBeacon completed.2) := by
  have selected := beacon_contracts standard.os contracts other sealFallback writerFallback
  let _ := AdapterRegistrationDecoderSource.sourceCodecs
  let _ := sourceOperations other
  let _ := sourceSender sealFallback writerFallback
  exact AdapterFiniteCalls.hosted_constructor_and_beacon_calls_preserve construction selected identifier identityKey mldsaKey calls

end Beacon

section Server
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations] [authentication : beaconcrypt.auth.Operations]
variable [validator : RegistrationValidatorPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [containers : PublicWrapperPlatform.ContainerOperations]
variable [lookup : AdapterPublicOrdinaryPlatform.LookupOperations]

structure ServerContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  authentication : AdapterRegistrationDecoderSource.AuthenticationContracts
  agreement : AdapterPublicRegistrationLoops.AgreementContracts
  random : AdapterPublicRegistrationLoops.AgreementRngContracts generator
  replay : AdapterPublicServerAccept.ReplayContracts
  response : AdapterPublicRegistrationWriterSource.ResponseContracts
  containers : AdapterPublicServerBuildState.ContainerContracts
  lookups : LookupContracts
  receive : AdapterRecordReceive.Contracts

theorem server_contracts {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : ServerContracts generator) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations) :
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
    letI := sourceSender sealFallback writerFallback
    AdapterFiniteCalls.ServerContracts generator := by
  let _ := AdapterRegistrationDecoderSource.sourceCodecs
  have response := AdapterPublicRegistrationWriterSource.response_contracts contracts.response other
  let _ := sourceOperations other
  have build := AdapterPublicServerBuildSource.component_contracts response sealFallback writerFallback
  have containerLaws := AdapterPublicServerBuildSource.container_contracts contracts.containers sealFallback writerFallback
  have send := sender_contracts contracts.receive contracts.response.sealingPrimitive contracts.response.allocation sealFallback writerFallback
  rcases contracts.authentication.publicLeaves with ⟨mldsaPublic, edPublicBytes, hash⟩
  rcases contracts.replay with ⟨contains, reserve, insert⟩
  rcases contracts.lookups with ⟨get, getMut⟩
  have init := contracts.authentication.init
  have agreement := contracts.agreement
  have random := contracts.random
  have receive := contracts.receive
  let _ := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
  let _ := sourceSender sealFallback writerFallback
  have authenticationSource : AdapterRegistrationDecoderSource.AuthenticationContracts := {
    publicLeaves := { mldsaPublic := mldsaPublic, edPublicBytes := edPublicBytes, hash := hash }
    init := init }
  exact {
    authentication := AdapterRegistrationDecoderSource.authentication_contracts authenticationSource
    agreement := agreement
    random := random
    replay := { contains := contains, reserve := reserve, insert := insert }
    build := build
    containers := containerLaws
    lookups := { get := get, getMut := getMut }
    send := send
    receive := receive }

theorem server_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : ServerContracts generator) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (calls : List AdapterFiniteCalls.ServerCall) (self : server.Server) (rng : R) (valid : ValidServer self) :
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
    letI := sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.serverCalls generator calls self rng) (fun result => ValidServer result.2.1) := by
  have selected := server_contracts generator contracts other sealFallback writerFallback
  let _ := AdapterRegistrationDecoderSource.sourceCodecs
  let _ := sourceOperations other
  let _ := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
  let _ := sourceSender sealFallback writerFallback
  exact AdapterFiniteCalls.server_calls_preserve generator selected calls self rng valid

variable [AdapterServerConstructorPrimitive.Standard]

omit recordOps crypto authentication validator in
theorem initialization_contracts (initialization : AdapterConstructorValidity.InitializationContracts)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations) :
    letI := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
    AdapterConstructorValidity.InitializationContracts := by
  rcases initialization with ⟨mapValid⟩
  let _ := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
  exact ⟨mapValid⟩

variable [AdapterBeaconConstructorPrimitive.Operations]

theorem constructor_and_server_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.ServerContracts generator)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts generator)
    (other : OtherBranches) (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (identifier : U64)
    (identitySeed mldsaSeed : core.option.Option (Slice U8)) (calls : List AdapterFiniteCalls.ServerCall) (rng : R) :
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
    letI := sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.constructServerCalls generator identifier identitySeed mldsaSeed calls rng)
      (fun result => match result.1 with | .Err _ => True | .Ok completed => ValidServer completed.2) := by
  have selected := server_contracts generator contracts other sealFallback writerFallback
  have initialized := initialization_contracts initialization sealFallback writerFallback
  let _ := AdapterRegistrationDecoderSource.sourceCodecs
  let _ := sourceOperations other
  let _ := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
  let _ := sourceSender sealFallback writerFallback
  exact AdapterFiniteCalls.constructor_and_server_calls_preserve generator construction initialized selected identifier identitySeed mldsaSeed calls rng

variable [standard : AdapterBeaconConstructorPrimitive.Standard]

theorem hosted_constructor_and_server_calls_preserve
    (construction : AdapterConstructors.ServerContracts standard.os)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts standard.os)
    (other : OtherBranches) (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) (identifier : U64)
    (identitySeed mldsaSeed : core.option.Option (Slice U8)) (calls : List AdapterFiniteCalls.ServerCall) :
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
    letI := sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.constructServerHostedCalls identifier identitySeed mldsaSeed calls)
      (fun result => match result with | .Err _ => True | .Ok completed => ValidServer completed.2) := by
  have selected := server_contracts standard.os contracts other sealFallback writerFallback
  have initialized := initialization_contracts initialization sealFallback writerFallback
  let _ := AdapterRegistrationDecoderSource.sourceCodecs
  let _ := sourceOperations other
  let _ := AdapterPublicServerBuildSource.sourceLocalOperations localOps sealFallback writerFallback
  let _ := sourceSender sealFallback writerFallback
  exact AdapterFiniteCalls.hosted_constructor_and_server_calls_preserve construction initialized selected identifier identitySeed mldsaSeed calls

end Server

end BeaconcryptCore.PanicFreedom.AdapterFiniteCallsSource
