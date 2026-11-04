-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicBeacon
import BeaconcryptCore.PanicFreedom.AdapterPublicAgreementSafety
import BeaconcryptCore.PanicFreedom.AdapterPublicFinishSafety
import BeaconcryptCore.PanicFreedom.AdapterResponseAuthentication
import BeaconcryptCore.PanicFreedom.RegistrationPublication
import BeaconcryptCore.PanicFreedom.Trivial

/-! Native Beacon finishing composes response authentication, terminating agreement and first-record opening. Malformed responses and every ordinary dependency error remain normal returns. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace BeaconcryptCore.PanicFreedom.AdapterPublicBeaconFinish
open Refinement AdapterNormal beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
variable [codec : PublicWrapperPlatform.Codecs]

structure Contracts : Prop where
  agreement : AdapterPublicRegistrationLoops.AgreementContracts
  random : AdapterPublicRegistrationLoops.AgreementRngContracts pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError
  record : AdapterRecordReceive.Contracts
  response : AdapterResponseAuthentication.Contracts
  decode : ∀ input, Normal (codec.decodeResponse input)
  initialKdf : ∀ request, Normal (localOps.ratchet_initial_ratchet_hkdf request)

omit material platform primitive crypto localOps authentication recordOps codec in
theorem response_option_total (packet : core.option.Option beaconcrypt_parse.transport.kexresponse) :
    Normal (core.option.Option.and_then
      beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket packet ()) := by
  cases packet with
  | none => exact ⟨.None, rfl⟩
  | some packet => exact AdapterPublicBeacon.response_packet_closure_total () packet

omit codec platform crypto localOps authentication in
theorem finish_loop_installs (contracts : AdapterRecordReceive.Contracts)
    (self : beacon.Beacon) (effect : registration.BeaconInitialOpen) (identifier : U64) :
    Ensures (do
      let (buffer, changedIdentifier, state) ← beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop effect identifier
      ok (buffer, { self with identity_key_kid := changedIdentifier, state }))
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2) := by
  obtain ⟨⟨buffer, changedIdentifier, state⟩, returned, stateValid⟩ :=
    AdapterPublicFinishSafety.finish_loop_preserves contracts effect identifier
  exact ⟨(buffer, { self with identity_key_kid := changedIdentifier, state }),
    by simp! only [returned, bind_tc_ok], stateValid⟩

theorem finish_registration_preserves (contracts : Contracts) (self : beacon.Beacon) (bytes : Slice U8)
    (valid : AdapterPublicOrdinary.ValidBeacon self) :
    Ensures (beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes)
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2) := by
  unfold beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
  simp! only [beacon.Beacon.identity_sk, beaconcrypt_parse.decode_response,
    core.mem.replace, core.option.Option.and_then,
    beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket,
    ratchet.initial_ratchet_hkdf, bind_tc_ok]
  repeat'
    first
      | (solve | simp_all [AdapterPublicOrdinary.ValidBeacon])
      | with_reducible exact contracts.decode _
      | with_reducible exact contracts.initialKdf _
      | exact RegistrationTrivial.BeaconPending_aborted_state_total _
      | exact response_option_total _
      | exact AdapterResponseAuthentication.authenticate_response_total contracts.response _ _
      | exact KeyAgreement.begin_beacon_agreement_total _
      | exact AdapterPublicAgreementSafety.execute_beacon_agreement_total contracts.agreement contracts.random _ _
      | exact RegistrationPublication.begin_beacon_completion_total _
      | exact RegistrationTrivial.BeaconInitialKdf_request_total _
      | exact Trivial.pqxdh_concrete_InitialRatchetKdfResponse_from_bytes_total _
      | with_reducible exact resume_initial_ratchet_kdf_ok _ _
      | with_reducible exact SessionBinding.RegistrationBinding_associated_data_total _
      | with_reducible exact RecordEffects.begin_record_receive_total _ _ _ _ _
      | with_reducible exact Trivial.pqxdh_BeaconRegistrationCandidate_server_key_id_total _
      | with_reducible exact RegistrationPublication.normalize_beacon_open_total _ _
      | exact finish_loop_installs contracts.record _ _ _
      | intro value
      | split
      | apply ensures_bind_at
      | apply normal_bind_at

theorem finish_registration_total (contracts : Contracts) (self : beacon.Beacon) (bytes : Slice U8) :
    ∃ result, beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes = ok result := by
  cases state : self.state with
  | InitSent pending prekey onetime kem =>
    exact ensures_normal (finish_registration_preserves contracts self bytes
      (by simp only [AdapterPublicOrdinary.ValidBeacon, state]))
  | Fresh control prekey kem | FreshWithCoins control prekey onetime kem
  | Established control binding manager | Aborted control =>
    exact ⟨(.None, self), by simp only [beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration, state]⟩

end BeaconcryptCore.PanicFreedom.AdapterPublicBeaconFinish
