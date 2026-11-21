-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterFiniteCallsSource
import BeaconcryptCore.PanicFreedom.AdapterRatchetKdfSource

/-! Joint source composition for finite public calls: native fixed-width ratchet KDFs, source registration decoders and signed-view writers, and source record sealing/routing are selected once around the complete run. The remaining HKDF premises describe successful API execution only on the reached 64/76-byte domains; primitive security is separate. Rejections remain normal replies and preserve the populated-object invariant for subsequent calls. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace BeaconcryptCore.PanicFreedom.AdapterFiniteCallsKdfSource
open Refinement AdapterNormal AdapterPublicOrdinary beaconcrypt_public_wrapper
open RegistrationSerializerReachableSource (OtherBranches)
open BeaconcryptCore.Computational.RegistrationNativeSourceEncoders (sourceOperations)

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [operations : AdapterRatchetKdfPrimitive.Operations]
variable [recordOps : beaconcrypt.ratchet.Operations] [localOps : PublicWrapperPlatform.LocalOperations]
variable [authentication : beaconcrypt.auth.Operations] [validator : RegistrationValidatorPrimitive.Operations]
variable [primitives : AdapterSealPrimitive.Operations] [allocator : AdapterWirePrimitive.Operations]
variable [FrameDispatchFallback.Operations]

section Beacon

structure BeaconContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  bundle : AdapterPublicRegistrationWriterSource.BundleContracts
  generation : AdapterPublicRegistrationLoops.GenerationContracts generator
  finish : AdapterRatchetKdfSource.FinishContracts
  sealing : AdapterSeal.PrimitiveContracts

omit validator [FrameDispatchFallback.Operations] in
theorem beacon_contracts {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (initial : AdapterRatchetKdf.Contracts 64#usize) (ongoing : AdapterRatchetKdf.Contracts 76#usize)
    (contracts : BeaconContracts generator) :
    letI := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    AdapterFiniteCallsSource.BeaconContracts generator := by
  have finish := AdapterRatchetKdfSource.finish_contracts initial ongoing contracts.finish
  rcases contracts.bundle with ⟨init, kxPublicBytes, allocation, kemPublicBytes⟩
  rcases init with ⟨initHash, initPublicBytes, edSign⟩
  have generation := contracts.generation
  have sealing := contracts.sealing
  let _ := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact {
    bundle := {
      init := { hash := initHash, edPublicBytes := initPublicBytes, edSign := edSign }
      kxPublicBytes := kxPublicBytes
      allocation := allocation
      kemPublicBytes := kemPublicBytes }
    generation := generation
    finish := finish
    sealing := sealing }

theorem beacon_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (initial : AdapterRatchetKdf.Contracts 64#usize) (ongoing : AdapterRatchetKdf.Contracts 76#usize)
    (contracts : BeaconContracts generator) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (calls : List AdapterFiniteCalls.BeaconCall) (self : beacon.Beacon) (rng : R) (valid : ValidBeacon self) :
    letI := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterFiniteCallsSource.sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.beaconCalls generator calls self rng) (fun result => ValidBeacon result.2.1) := by
  have selected := beacon_contracts generator initial ongoing contracts
  let _ := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact AdapterFiniteCallsSource.beacon_calls_preserve generator selected other sealFallback writerFallback calls self rng valid

variable [AdapterBeaconConstructorPrimitive.Operations]

theorem constructor_and_beacon_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.BeaconContracts generator)
    (initial : AdapterRatchetKdf.Contracts 64#usize) (ongoing : AdapterRatchetKdf.Contracts 76#usize)
    (contracts : BeaconContracts generator) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List AdapterFiniteCalls.BeaconCall) (rng : R) :
    letI := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterFiniteCallsSource.sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.constructBeaconCalls generator identifier identityKey mldsaKey calls rng)
      (fun result => match result.1 with | .Err _ => True | .Ok completed => ValidBeacon completed.2) := by
  have selected := beacon_contracts generator initial ongoing contracts
  let _ := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact AdapterFiniteCallsSource.constructor_and_beacon_calls_preserve generator construction selected other
    sealFallback writerFallback identifier identityKey mldsaKey calls rng

variable [standard : AdapterBeaconConstructorPrimitive.Standard]

theorem hosted_constructor_and_beacon_calls_preserve
    (construction : AdapterConstructors.BeaconContracts standard.os)
    (initial : AdapterRatchetKdf.Contracts 64#usize) (ongoing : AdapterRatchetKdf.Contracts 76#usize)
    (contracts : BeaconContracts standard.os) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List AdapterFiniteCalls.BeaconCall) :
    letI := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterFiniteCallsSource.sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.constructBeaconHostedCalls identifier identityKey mldsaKey calls)
      (fun result => match result with | .Err _ => True | .Ok completed => ValidBeacon completed.2) := by
  have selected := beacon_contracts standard.os initial ongoing contracts
  let _ := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact AdapterFiniteCallsSource.hosted_constructor_and_beacon_calls_preserve construction selected other
    sealFallback writerFallback identifier identityKey mldsaKey calls

end Beacon

section Server
variable [PublicWrapperPlatform.Allocator] [containers : PublicWrapperPlatform.ContainerOperations]
variable [lookup : AdapterPublicOrdinaryPlatform.LookupOperations]

structure ServerContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  authentication : AdapterRegistrationDecoderSource.AuthenticationContracts
  agreement : AdapterPublicRegistrationLoops.AgreementContracts
  random : AdapterPublicRegistrationLoops.AgreementRngContracts generator
  replay : AdapterPublicServerAccept.ReplayContracts
  response : AdapterRatchetKdfSource.ResponseContracts
  containers : AdapterPublicServerBuildState.ContainerContracts
  lookups : LookupContracts
  receive : AdapterRatchetKdfSource.ReceiveContracts

omit validator [FrameDispatchFallback.Operations] in
theorem server_contracts {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (initial : AdapterRatchetKdf.Contracts 64#usize) (ongoing : AdapterRatchetKdf.Contracts 76#usize)
    (contracts : ServerContracts generator) :
    letI := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    AdapterFiniteCallsSource.ServerContracts generator := by
  have response := AdapterRatchetKdfSource.response_contracts initial ongoing contracts.response
  have receive := AdapterRatchetKdfSource.receive_contracts ongoing contracts.receive
  have containerLaws := AdapterRatchetKdfSource.local_container_contracts contracts.containers
  rcases contracts.authentication.publicLeaves with ⟨mldsaPublic, edPublicBytes⟩
  rcases contracts.replay with ⟨contains, reserve, insert⟩
  rcases contracts.lookups with ⟨get, getMut⟩
  have init := contracts.authentication.init
  have agreement := contracts.agreement
  have random := contracts.random
  let _ := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact {
    authentication := {
      publicLeaves := { mldsaPublic := mldsaPublic, edPublicBytes := edPublicBytes }
      init := init }
    agreement := agreement
    random := random
    replay := { contains := contains, reserve := reserve, insert := insert }
    response := response
    containers := containerLaws
    lookups := { get := get, getMut := getMut }
    receive := receive }

theorem server_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (initial : AdapterRatchetKdf.Contracts 64#usize) (ongoing : AdapterRatchetKdf.Contracts 76#usize)
    (contracts : ServerContracts generator) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (calls : List AdapterFiniteCalls.ServerCall) (self : server.Server) (rng : R) (valid : ValidServer self) :
    letI := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations
      (inferInstance : PublicWrapperPlatform.LocalOperations) sealFallback writerFallback
    letI := AdapterFiniteCallsSource.sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.serverCalls generator calls self rng) (fun result => ValidServer result.2.1) := by
  have selected := server_contracts generator initial ongoing contracts
  let _ := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact AdapterFiniteCallsSource.server_calls_preserve generator selected other sealFallback writerFallback calls self rng valid

variable [AdapterServerConstructorPrimitive.Standard]

omit recordOps authentication validator allocator primitives [FrameDispatchFallback.Operations] in
theorem initialization_contracts (initialization : AdapterConstructorValidity.InitializationContracts) :
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    AdapterConstructorValidity.InitializationContracts := by
  rcases initialization with ⟨mapValid⟩
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact ⟨mapValid⟩

variable [AdapterBeaconConstructorPrimitive.Operations]

theorem constructor_and_server_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.ServerContracts generator)
    (initialization : AdapterConstructorValidity.InitializationContracts)
    (initial : AdapterRatchetKdf.Contracts 64#usize) (ongoing : AdapterRatchetKdf.Contracts 76#usize)
    (contracts : ServerContracts generator) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List AdapterFiniteCalls.ServerCall) (rng : R) :
    letI := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations
      (inferInstance : PublicWrapperPlatform.LocalOperations) sealFallback writerFallback
    letI := AdapterFiniteCallsSource.sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.constructServerCalls generator identifier identitySeed mldsaSeed calls rng)
      (fun result => match result.1 with | .Err _ => True | .Ok completed => ValidServer completed.2) := by
  have selected := server_contracts generator initial ongoing contracts
  have initialized := initialization_contracts initialization
  let _ := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact AdapterFiniteCallsSource.constructor_and_server_calls_preserve generator construction initialized selected other
    sealFallback writerFallback identifier identitySeed mldsaSeed calls rng

variable [standard : AdapterBeaconConstructorPrimitive.Standard]

theorem hosted_constructor_and_server_calls_preserve
    (construction : AdapterConstructors.ServerContracts standard.os)
    (initialization : AdapterConstructorValidity.InitializationContracts)
    (initial : AdapterRatchetKdf.Contracts 64#usize) (ongoing : AdapterRatchetKdf.Contracts 76#usize)
    (contracts : ServerContracts standard.os) (other : OtherBranches)
    (sealFallback : AdapterSealJoinCallbacks.Operations) (writerFallback : RecordRoutingCallbacks.Operations)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List AdapterFiniteCalls.ServerCall) :
    letI := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
    letI := AdapterRatchetKdfSource.sourceLocalOperations localOps
    letI := AdapterRegistrationDecoderSource.sourceCodecs
    letI := sourceOperations other
    letI := AdapterPublicServerBuildSource.sourceLocalOperations
      (inferInstance : PublicWrapperPlatform.LocalOperations) sealFallback writerFallback
    letI := AdapterFiniteCallsSource.sourceSender sealFallback writerFallback
    Ensures (AdapterFiniteCalls.constructServerHostedCalls identifier identitySeed mldsaSeed calls)
      (fun result => match result with | .Err _ => True | .Ok completed => ValidServer completed.2) := by
  have selected := server_contracts standard.os initial ongoing contracts
  have initialized := initialization_contracts initialization
  let _ := AdapterRatchetKdfSource.sourceReceiveOperations recordOps
  let _ := AdapterRatchetKdfSource.sourceLocalOperations localOps
  exact AdapterFiniteCallsSource.hosted_constructor_and_server_calls_preserve construction initialized selected other
    sealFallback writerFallback identifier identitySeed mldsaSeed calls

end Server
end BeaconcryptCore.PanicFreedom.AdapterFiniteCallsKdfSource
