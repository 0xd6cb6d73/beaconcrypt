-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops
import BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary
import BeaconcryptCore.PanicFreedom.AdapterPublicTrivial
import BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterCallers
import BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.PanicFreedom.Registration

/-! Native Beacon registration wrappers return normally on dependency errors and protocol rejection, and preserve populated ratchets for subsequent public calls. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace BeaconcryptCore.PanicFreedom.AdapterPublicBeacon
open Refinement AdapterNormal beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
omit recordOps
variable [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations]
attribute [local irreducible] beaconcrypt_registration_writer.wire.encode_init

structure BundleContracts : Prop where
  init : AdapterPublicRegistrationLoops.InitContracts
  kxPublicBytes : ∀ key, Normal (crypto.kxPublicBytes key)
  writer : AdapterRegistrationWriterCallers.InitCallerContracts
  allocation : AdapterWire.Contracts
  kemPublicBytes : ∀ key, Normal (crypto.kemPublicBytes key)

omit platform localOps in
theorem get_registration_bundle_preserves (contracts : BundleContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.GenerationContracts generator) (self : beacon.Beacon) (rng : R)
    (valid : AdapterPublicOrdinary.ValidBeacon self) :
    Ensures (beacon.Beacon.get_registration_bundle_with_rng generator self rng)
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2.1) := by
  unfold beacon.Beacon.get_registration_bundle_with_rng
  simp only [beaconcrypt_crypto.crypto_kx.KeyPair.generate_with_rng,
    beaconcrypt_crypto.crypto_kx.PublicKey.as_bytes,
    beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey.as_bytes,
    beaconcrypt_crypto.crypto_sign.PublicKey.as_bytes,
    beacon.Beacon.identity_pk,
    core.result.Result.ok, core.option.Option.as_ref, core.option.Option.take, core.mem.replace,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    lift, bind_tc_ok]
  repeat'
    try simp only [bind_tc_ok]
    first
      | with_reducible exact AdapterRegistrationWriterCallers.init_native_total contracts.writer (by assumption)
      | (solve | simp_all [AdapterPublicOrdinary.ValidBeacon])
      | with_reducible exact random.kxGenerate _
      | with_reducible exact contracts.kxPublicBytes _
      | with_reducible exact contracts.kemPublicBytes _
      | with_reducible exact contracts.init.edPublicBytes _
      | exact RegistrationSigningContinuations.begin_beacon_init_total _ _ _ _
      | exact AdapterPublicRegistrationLoops.init_ready_total contracts.init _ _
      | exact RegistrationTrivial.BeaconInitReady_message_total _
      | exact RegistrationTrivial.BeaconInitReady_publish_total _ _
      | exact RegistrationTrivial.PublishedBeaconInit_into_parts_total _
      | exact RegistrationTrivial.BeaconPending_aborted_state_total _
      | intro value
      | split
      | apply ensures_bind_at

omit material platform primitive crypto localOps authentication recordOps
  [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations] in
theorem response_packet_closure_total
    (capture : beacon.ProviderBeaconBeacon.finish_registration.closure)
    (packet : beaconcrypt_parse.transport.kexresponse) :
    ∃ result, beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket.call_once capture packet = ok result :=
  Registration.ResponsePacket_from_slices_total packet.identity_key packet.ephemeral_key
    packet.kem_cipher_text packet.key_id packet.app_cipher_text packet.signature

omit platform localOps in
theorem get_registration_bundle_total (contracts : BundleContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.GenerationContracts generator) (self : beacon.Beacon) (rng : R) :
    ∃ result, beacon.Beacon.get_registration_bundle_with_rng generator self rng = ok result := by
  cases state : self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey onetime kem =>
    exact ensures_normal (get_registration_bundle_preserves contracts generator random self rng
      (by simp only [AdapterPublicOrdinary.ValidBeacon, state]))
  | InitSent pending prekey onetime kem | Established control binding manager | Aborted control =>
    exact ⟨(.None, self, rng), by simp only [beacon.Beacon.get_registration_bundle_with_rng, state]⟩

end BeaconcryptCore.PanicFreedom.AdapterPublicBeacon
