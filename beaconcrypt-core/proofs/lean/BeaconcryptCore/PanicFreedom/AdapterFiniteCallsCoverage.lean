-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterFiniteCalls

/-! Fixed typed guards for the native finite-call executors. The equations pin every call, list transition, and constructor route to its original extracted operation. The execution certificates require an actual RustM.ok return and the precise returned-object invariant, including constructor Err branches. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace BeaconcryptCore.PanicFreedom.AdapterFiniteCallsCoverage
open Refinement AdapterFiniteCalls beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations] [authentication : beaconcrypt.auth.Operations]
variable [recordOps : beaconcrypt.ratchet.Operations] [beaconcrypt_record_send.ratchet.Operations]
variable [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations]
variable [PublicWrapperPlatform.Codecs]

section Beacon

theorem beacon_bundle_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) :
    beaconStep generator .bundle (self, rng) = (do
      let (reply, changed, after) ← beacon.Beacon.get_registration_bundle_with_rng generator self rng
      ok (.bundle reply, changed, after)) :=
  beacon_bundle_source generator self rng

theorem beacon_finish_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) (bytes : Slice U8) :
    beaconStep generator (.finish bytes) (self, rng) = (do
      let (reply, changed) ← beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes
      ok (.finish reply, changed, rng)) :=
  beacon_finish_source generator self rng bytes

theorem beacon_send_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) (bytes : Slice U8) :
    beaconStep generator (.send bytes) (self, rng) = (do
      let (reply, changed) ← beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message self bytes
      ok (.send reply, changed, rng)) :=
  beacon_send_source generator self rng bytes

theorem beacon_receive_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) (bytes : Slice U8) :
    beaconStep generator (.receive bytes) (self, rng) = (do
      let (reply, changed) ← beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message self bytes
      ok (.receive reply, changed, rng)) :=
  beacon_receive_source generator self rng bytes

theorem beacon_nil_exact {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) :
    beaconCalls generator [] self rng = ok ([], self, rng) :=
  beacon_calls_nil_source generator self rng

theorem beacon_cons_exact {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (call : BeaconCall) (calls : List BeaconCall) (self : beacon.Beacon) (rng : R) :
    beaconCalls generator (call :: calls) self rng = (do
      let (reply, next, after) ← beaconStep generator call (self, rng)
      let (replies, final, last) ← beaconCalls generator calls next after
      ok (reply :: replies, final, last)) :=
  beacon_calls_cons_source generator call calls self rng

theorem beacon_sequence_normal_valid {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : BeaconContracts generator) (calls : List BeaconCall) (self : beacon.Beacon) (rng : R)
    (valid : AdapterPublicOrdinary.ValidBeacon self) :
    ∃ result, beaconCalls generator calls self rng = ok result ∧
      AdapterPublicOrdinary.ValidBeacon result.2.1 :=
  beacon_calls_preserve generator contracts calls self rng valid

variable [AdapterBeaconConstructorPrimitive.Operations]

theorem beacon_constructor_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List BeaconCall) (rng : R) :
    constructBeaconCalls generator identifier identityKey mldsaKey calls rng = (do
      let (created, after) ← beaconcrypt_constructor.beacon.Beacon.try_new_with_rng generator identifier identityKey mldsaKey rng
      match created with
      | .Err error => ok (.Err error, after)
      | .Ok self => do
        let (replies, final, last) ← beaconCalls generator calls self after
        ok (.Ok (replies, final), last)) :=
  constructor_beacon_source generator identifier identityKey mldsaKey calls rng

theorem beacon_constructor_sequence_normal_valid {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.BeaconContracts generator) (contracts : BeaconContracts generator)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List BeaconCall) (rng : R) :
    ∃ result, constructBeaconCalls generator identifier identityKey mldsaKey calls rng = ok result ∧
      (match result.1 with | .Err _ => True | .Ok completed => AdapterPublicOrdinary.ValidBeacon completed.2) :=
  constructor_and_beacon_calls_preserve generator construction contracts identifier identityKey mldsaKey calls rng

theorem beacon_successful_constructor_sequence_normal_valid {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.BeaconContracts generator) (contracts : BeaconContracts generator)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (initialRng after : R)
    (self : beacon.Beacon) (calls : List BeaconCall)
    (constructed : beaconcrypt_constructor.beacon.Beacon.try_new_with_rng generator identifier identityKey mldsaKey initialRng =
      ok (.Ok self, after)) :
    ∃ result, beaconCalls generator calls self after = ok result ∧
      AdapterPublicOrdinary.ValidBeacon result.2.1 :=
  beacon_calls_from_try_new_with_rng generator construction contracts identifier identityKey mldsaKey
    initialRng after self calls constructed

variable [standard : AdapterBeaconConstructorPrimitive.Standard]

theorem beacon_hosted_constructor_native (identifier : U64) (identityKey mldsaKey : Slice U8)
    (calls : List BeaconCall) :
    constructBeaconHostedCalls identifier identityKey mldsaKey calls = (do
      let created ← beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey
      match created with
      | .Err error => ok (.Err error)
      | .Ok self => do
        let (replies, final, _) ← beaconCalls standard.os calls self ()
        ok (.Ok (replies, final))) :=
  constructor_beacon_hosted_source identifier identityKey mldsaKey calls

theorem beacon_hosted_constructor_sequence_normal_valid
    (construction : AdapterConstructors.BeaconContracts standard.os) (contracts : BeaconContracts standard.os)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List BeaconCall) :
    ∃ result, constructBeaconHostedCalls identifier identityKey mldsaKey calls = ok result ∧
      (match result with | .Err _ => True | .Ok completed => AdapterPublicOrdinary.ValidBeacon completed.2) :=
  hosted_constructor_and_beacon_calls_preserve construction contracts identifier identityKey mldsaKey calls

theorem beacon_hosted_successful_constructor_sequence_normal_valid
    (construction : AdapterConstructors.BeaconContracts standard.os) (contracts : BeaconContracts standard.os)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (self : beacon.Beacon) (calls : List BeaconCall)
    (constructed : beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey = ok (.Ok self)) :
    ∃ result, beaconCalls standard.os calls self () = ok result ∧
      AdapterPublicOrdinary.ValidBeacon result.2.1 :=
  beacon_calls_from_try_new construction contracts identifier identityKey mldsaKey self calls constructed

end Beacon

section Server
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]

theorem server_accept_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) (bytes : Slice U8) :
    serverStep generator (.accept bytes) (self, rng) = (do
      let (reply, changed, after) ← beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng generator self bytes rng
      ok (.accept reply, changed, after)) :=
  server_accept_source generator self rng bytes

theorem server_build_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) (output : server.RegistrationOutput)
    (application : core.option.Option (Slice U8)) :
    serverStep generator (.build output application) (self, rng) = (do
      let (reply, changed) ← server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self output application
      ok (.build reply, changed, rng)) :=
  server_build_source generator self rng output application

theorem server_send_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) (bytes : Slice U8) (key : U64) :
    serverStep generator (.send bytes key) (self, rng) = (do
      let (reply, changed) ← beaconcrypt_public_ordinary.server.Server.encrypt_message self bytes key
      ok (.send reply, changed, rng)) :=
  server_send_source generator self rng bytes key

theorem server_receive_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) (bytes : Slice U8) :
    serverStep generator (.receive bytes) (self, rng) = (do
      let (reply, changed) ← beaconcrypt_public_ordinary.server.Server.decrypt_message self bytes
      ok (.receive reply, changed, rng)) :=
  server_receive_source generator self rng bytes

theorem server_nil_exact {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) :
    serverCalls generator [] self rng = ok ([], self, rng) :=
  server_calls_nil_source generator self rng

theorem server_cons_exact {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (call : ServerCall) (calls : List ServerCall) (self : server.Server) (rng : R) :
    serverCalls generator (call :: calls) self rng = (do
      let (reply, next, after) ← serverStep generator call (self, rng)
      let (replies, final, last) ← serverCalls generator calls next after
      ok (reply :: replies, final, last)) :=
  server_calls_cons_source generator call calls self rng

theorem server_sequence_normal_valid {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : ServerContracts generator) (calls : List ServerCall) (self : server.Server) (rng : R)
    (valid : AdapterPublicOrdinary.ValidServer self) :
    ∃ result, serverCalls generator calls self rng = ok result ∧
      AdapterPublicOrdinary.ValidServer result.2.1 :=
  server_calls_preserve generator contracts calls self rng valid

variable [AdapterBeaconConstructorPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]

theorem server_constructor_native {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List ServerCall) (rng : R) :
    constructServerCalls generator identifier identitySeed mldsaSeed calls rng = (do
      let (created, after) ← beaconcrypt_server_constructor.server.Server.try_new_with_rng generator identifier identitySeed mldsaSeed rng
      match created with
      | .Err error => ok (.Err error, after)
      | .Ok self => do
        let (replies, final, last) ← serverCalls generator calls self after
        ok (.Ok (replies, final), last)) :=
  constructor_server_source generator identifier identitySeed mldsaSeed calls rng

theorem server_constructor_sequence_normal_valid {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.ServerContracts generator)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts generator)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List ServerCall) (rng : R) :
    ∃ result, constructServerCalls generator identifier identitySeed mldsaSeed calls rng = ok result ∧
      (match result.1 with | .Err _ => True | .Ok completed => AdapterPublicOrdinary.ValidServer completed.2) :=
  constructor_and_server_calls_preserve generator construction initialization contracts identifier identitySeed mldsaSeed calls rng

theorem server_successful_constructor_sequence_normal_valid {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.ServerContracts generator)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts generator)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8)) (initialRng after : R)
    (self : server.Server) (calls : List ServerCall)
    (constructed : beaconcrypt_server_constructor.server.Server.try_new_with_rng generator identifier identitySeed mldsaSeed initialRng =
      ok (.Ok self, after)) :
    ∃ result, serverCalls generator calls self after = ok result ∧
      AdapterPublicOrdinary.ValidServer result.2.1 :=
  server_calls_from_try_new_with_rng generator construction initialization contracts identifier identitySeed mldsaSeed
    initialRng after self calls constructed

variable [standard : AdapterBeaconConstructorPrimitive.Standard]

theorem server_hosted_constructor_native (identifier : U64)
    (identitySeed mldsaSeed : core.option.Option (Slice U8)) (calls : List ServerCall) :
    constructServerHostedCalls identifier identitySeed mldsaSeed calls = (do
      let created ← beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed
      match created with
      | .Err error => ok (.Err error)
      | .Ok self => do
        let (replies, final, _) ← serverCalls standard.os calls self ()
        ok (.Ok (replies, final))) :=
  constructor_server_hosted_source identifier identitySeed mldsaSeed calls

theorem server_hosted_constructor_sequence_normal_valid
    (construction : AdapterConstructors.ServerContracts standard.os)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts standard.os)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8)) (calls : List ServerCall) :
    ∃ result, constructServerHostedCalls identifier identitySeed mldsaSeed calls = ok result ∧
      (match result with | .Err _ => True | .Ok completed => AdapterPublicOrdinary.ValidServer completed.2) :=
  hosted_constructor_and_server_calls_preserve construction initialization contracts identifier identitySeed mldsaSeed calls

theorem server_hosted_successful_constructor_sequence_normal_valid
    (construction : AdapterConstructors.ServerContracts standard.os)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts standard.os)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (self : server.Server) (calls : List ServerCall)
    (constructed : beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed = ok (.Ok self)) :
    ∃ result, serverCalls standard.os calls self () = ok result ∧
      AdapterPublicOrdinary.ValidServer result.2.1 :=
  server_calls_from_try_new construction initialization contracts identifier identitySeed mldsaSeed self calls constructed

end Server
end BeaconcryptCore.PanicFreedom.AdapterFiniteCallsCoverage
