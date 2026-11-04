-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal
import BeaconcryptCore.PanicFreedom.AdapterPublicServerAccept
import BeaconcryptCore.PanicFreedom.AdapterPublicBeaconFinish

/-! Direct RustM composition of the public registration wrappers with the original extracted Init and response decoders. Existing arbitrary-slice decoder totality discharges both decoding dependencies, retaining malformed-input rejection and the public returned-state guarantees. No decoder execution contract or interpreter-normality premise is assumed. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource
open Refinement AdapterNormal beaconcrypt_public_wrapper
variable [validator : RegistrationValidatorPrimitive.Operations]

@[instance_reducible] def sourceCodecs : PublicWrapperPlatform.Codecs where
  decodeInit := beaconcrypt_parse.extraction_decode_init
  decodeResponse := beaconcrypt_parse.extraction_decode_response

theorem source_init (input : Slice U8) :
    sourceCodecs.decodeInit input = beaconcrypt_parse.extraction_decode_init input := rfl

theorem source_response (input : Slice U8) :
    sourceCodecs.decodeResponse input = beaconcrypt_parse.extraction_decode_response input := rfl

theorem decode_init_total (input : Slice U8) : Normal (sourceCodecs.decodeInit input) := by
  obtain ⟨reply, returned, _⟩ := RegistrationPublicDecoderTotal.init_total input
  exact ⟨reply, returned⟩

theorem decode_response_total (input : Slice U8) : Normal (sourceCodecs.decodeResponse input) := by
  obtain ⟨reply, returned, _⟩ := RegistrationPublicDecoderTotal.response_total input
  exact ⟨reply, returned⟩

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [localOps : PublicWrapperPlatform.LocalOperations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]

/-- Remaining authentication leaves; decoding is the proved source decoder. -/
structure AuthenticationContracts : Prop where
  publicLeaves : AdapterPublicTrivial.Contracts
  init : AdapterInitAuthentication.Contracts

/-- Remaining Beacon completion leaves; decoding is the proved source decoder. -/
structure FinishContracts : Prop where
  agreement : AdapterBeaconAgreementSafety.Contracts
  record : AdapterRecordReceive.Contracts
  response : AdapterResponseAuthentication.Contracts
  initialKdf : ∀ request, Normal (localOps.ratchet_initial_ratchet_hkdf request)

omit recordOps in
theorem authentication_contracts (contracts : AuthenticationContracts) :
    letI := sourceCodecs
    AdapterPublicServer.AuthenticationContracts := by
  let _ := sourceCodecs
  exact {
    publicLeaves := contracts.publicLeaves
    init := contracts.init
    decode := decode_init_total }

theorem finish_contracts (contracts : FinishContracts) :
    letI := sourceCodecs
    AdapterPublicBeaconFinish.Contracts := by
  let _ := sourceCodecs
  exact {
    agreement := contracts.agreement
    record := contracts.record
    response := contracts.response
    decode := decode_response_total
    initialKdf := contracts.initialKdf }

omit recordOps in
theorem authenticate_registration_lookup_total (contracts : AuthenticationContracts)
    (self : server.Server) (bytes : Slice U8) :
    letI := sourceCodecs
    ∃ result, server.Server.authenticate_registration_lookup self bytes = ok result := by
  have selected := authentication_contracts contracts
  let _ := sourceCodecs
  exact AdapterPublicServer.authenticate_registration_lookup_total selected self bytes

theorem finish_registration_total (contracts : FinishContracts) (self : beacon.Beacon)
    (bytes : Slice U8) :
    letI := sourceCodecs
    ∃ result, beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes = ok result := by
  have selected := finish_contracts contracts
  let _ := sourceCodecs
  exact AdapterPublicBeaconFinish.finish_registration_total selected self bytes

theorem finish_registration_preserves (contracts : FinishContracts) (self : beacon.Beacon)
    (bytes : Slice U8) (valid : AdapterPublicOrdinary.ValidBeacon self) :
    letI := sourceCodecs
    Ensures (beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes)
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2) := by
  have selected := finish_contracts contracts
  let _ := sourceCodecs
  exact AdapterPublicBeaconFinish.finish_registration_preserves selected self bytes valid

variable [PublicWrapperPlatform.Allocator] [containers : PublicWrapperPlatform.ContainerOperations]

omit recordOps in
theorem get_shared_secret_with_rng_total (authenticationContracts : AuthenticationContracts)
    (agreement : AdapterPublicRegistrationLoops.AgreementContracts)
    (replay : AdapterPublicServerAccept.ReplayContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.AgreementRngContracts generator)
    (self : server.Server) (bytes : Slice U8) (rng : R) :
    letI := sourceCodecs
    ∃ result, beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng
      generator self bytes rng = ok result := by
  have selected := authentication_contracts authenticationContracts
  let _ := sourceCodecs
  exact AdapterPublicServerAccept.get_shared_secret_with_rng_total
    selected agreement replay generator random self bytes rng

variable [lookup : AdapterPublicOrdinaryPlatform.LookupOperations]

omit recordOps in
theorem get_shared_secret_with_rng_preserves (authenticationContracts : AuthenticationContracts)
    (agreement : AdapterPublicRegistrationLoops.AgreementContracts)
    (replay : AdapterPublicServerAccept.ReplayContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.AgreementRngContracts generator)
    (self : server.Server) (bytes : Slice U8) (rng : R)
    (valid : AdapterPublicOrdinary.ValidServer self) :
    letI := sourceCodecs
    Ensures (beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng
      generator self bytes rng)
      (fun result => AdapterPublicOrdinary.ValidServer result.2.1) := by
  have selected := authentication_contracts authenticationContracts
  let _ := sourceCodecs
  exact AdapterPublicServerAccept.get_shared_secret_with_rng_preserves
    selected agreement replay generator random self bytes rng valid

end BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.authenticate_registration_lookup_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.authenticate_registration_lookup_total

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.finish_registration_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.finish_registration_total

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.finish_registration_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.finish_registration_preserves

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.get_shared_secret_with_rng_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.get_shared_secret_with_rng_total

/-- info: 'BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.get_shared_secret_with_rng_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource.get_shared_secret_with_rng_preserves
