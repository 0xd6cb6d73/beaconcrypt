-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterBeaconConstructorExtraction.Funs
import BeaconcryptCore.AdapterServerConstructorExtraction.Funs
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.Refinement.RegistrationInputs

/-! Native constructor safety requires normal external leaves, including ordinary key-generation errors. Neither fallible constructor requires successful allocation or successful cryptography. The convenience `new` functions retain their intentional `expect`. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace BeaconcryptCore.PanicFreedom.AdapterConstructors
open Refinement AdapterNormal
open beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [generators : AdapterBeaconConstructorPrimitive.Operations]
variable [standard : AdapterBeaconConstructorPrimitive.Standard]
variable [authentication : beaconcrypt.auth.Operations]

/-! RNG execution laws are for this selected dictionary only. Quantification over every state of that dictionary closes sequential and repeated calls without requiring successful entropy generation. -/
structure BeaconContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  parse : ∀ input, Normal (primitive.parse input)
  edPublicBytes : ∀ key, Normal (crypto.edPublicBytes key)
  mldsaGenerate : ∀ rng,
    Normal (generators.mldsaGenerate generator rng)
  edGenerate : ∀ rng,
    Normal (generators.edGenerate generator rng)
  kxGenerate : ∀ rng,
    Normal (crypto.kxGenerate generator rng)
  kemGenerate : ∀ rng,
    Normal (generators.kemGenerate generator rng)
  hash : ∀ request, Normal (authentication.hash request)

omit material platform primitive crypto generators standard in
theorem fingerprint_pin_total
    (hash : ∀ request, Normal (authentication.hash request))
    (binding : pqxdh.ServerBinding) (publicKey : Array U8 1952#usize) :
    ∃ result, auth.fingerprint_pin binding publicKey = ok result := by
  obtain ⟨pending, started⟩ := RegistrationTrivial.begin_server_pin_total binding publicKey
  obtain ⟨request, requested⟩ := RegistrationTrivial.PinFingerprint_request_total pending
  obtain ⟨digest, hashed⟩ := hash request
  obtain ⟨result, resumed⟩ := RegistrationTrivial.PinFingerprint_resume_total pending digest
  exact ⟨result, by simp only [auth.fingerprint_pin, started, requested,
    beaconcrypt.auth.execute_hash, hashed, resumed, bind_tc_ok]⟩

omit platform standard in
theorem beacon_try_new_with_rng_total
    {R E : Type} (generator : rand_core.TryCryptoRng R E) (contracts : BeaconContracts generator) (identifier : U64)
    (identityKey mldsaKey : Slice U8) (rng : R) :
    ∃ result, beaconcrypt_constructor.beacon.Beacon.try_new_with_rng
      generator identifier identityKey mldsaKey rng = ok result := by
  unfold beaconcrypt_constructor.beacon.Beacon.try_new_with_rng
  simp only [beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_2.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_3.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_4.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from,
    core.option.Option.ok_or,
    pqxdh.BeaconFresh.new,
    bind_tc_ok]
  repeat'
    try simp only [bind_tc_ok]
    first
      | (solve | simp_all)
      | exact contracts.parse _
      | exact contracts.edPublicBytes _
      | exact contracts.mldsaGenerate _
      | exact contracts.edGenerate _
      | exact contracts.kxGenerate _
      | exact contracts.kemGenerate _
      | exact fingerprint_pin_total contracts.hash _ _
      | exact RegistrationInputs.copied_slice_total _ _
      | (intro value)
      | (split)
      | (split at *)
      | apply normal_bind_at

omit platform in
theorem beacon_try_new_total (contracts : BeaconContracts standard.os) (identifier : U64)
    (identityKey mldsaKey : Slice U8) :
    ∃ result, beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey = ok result := by
  obtain ⟨⟨result, rng⟩, returned⟩ := beacon_try_new_with_rng_total standard.os contracts identifier identityKey mldsaKey ()
  exact ⟨result, by simp only [beaconcrypt_constructor.beacon.Beacon.try_new, beaconcrypt_crypto.OsRng.Insts.Rand_coreTryCryptoRngError, returned, bind_tc_ok]; rfl⟩

omit platform in
theorem beacon_new_of_success (identifier : U64) (identityKey mldsaKey : Slice U8)
    (beacon : beacon.Beacon)
    (constructed : beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey = ok (.Ok beacon)) :
    beaconcrypt_constructor.beacon.Beacon.new identifier identityKey mldsaKey = ok beacon := by
  simp only [beaconcrypt_constructor.beacon.Beacon.new, constructed, bind_tc_ok, core.result.Result.expect]

variable [serverStandard : AdapterServerConstructorPrimitive.Standard]

structure ServerContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  edGenerate : ∀ rng,
    Normal (generators.edGenerate generator rng)
  mldsaGenerate : ∀ rng,
    Normal (generators.mldsaGenerate generator rng)
  edFromSeed : ∀ seed, Normal (serverStandard.edFromSeed seed)
  mldsaFromSeed : ∀ seed, Normal (serverStandard.mldsaFromSeed seed)
  edSecretBytes : ∀ key, Normal (serverStandard.edSecretBytes key)
  mapWithKey : ∀ K V seed, Normal (serverStandard.mapWithKey K V seed)
  setWithKey : ∀ K seed, Normal (serverStandard.setWithKey K seed)
  arcNew : ∀ {T : Type} (value : T), Normal (serverStandard.arcNew value)

omit crypto standard authentication in
theorem server_try_new_with_rng_total
    {R E : Type} (generator : rand_core.TryCryptoRng R E) (contracts : ServerContracts generator) (identifier : U64)
    (identitySeed mldsaSeed : core.option.Option (Slice U8)) (rng : R) :
    ∃ result, beaconcrypt_server_constructor.server.Server.try_new_with_rng
      generator identifier identitySeed mldsaSeed rng = ok result := by
  unfold beaconcrypt_server_constructor.server.Server.try_new_with_rng
  simp only [beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError.call_once,
    core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from,
    pqxdh.ServerState.new,
    bind_tc_ok]
  repeat'
    try simp only [bind_tc_ok]
    first
      | (solve | simp_all)
      | exact normal_ok _
      | exact contracts.edGenerate _
      | exact contracts.mldsaGenerate _
      | exact contracts.edFromSeed _
      | exact contracts.mldsaFromSeed _
      | exact contracts.edSecretBytes _
      | exact contracts.mapWithKey _ _ _
      | exact contracts.setWithKey _ _
      | exact contracts.arcNew _
      | exact RegistrationInputs.copied_slice_total _ _
      | (intro value)
      | (split)
      | (split at *)
      | apply normal_bind_at

omit crypto authentication in
theorem server_try_new_total (contracts : ServerContracts standard.os) (identifier : U64)
    (identitySeed mldsaSeed : core.option.Option (Slice U8)) :
    ∃ result, beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed = ok result := by
  obtain ⟨⟨result, rng⟩, returned⟩ := server_try_new_with_rng_total standard.os contracts identifier identitySeed mldsaSeed ()
  exact ⟨result, by simp only [beaconcrypt_server_constructor.server.Server.try_new,
    beaconcrypt_crypto.OsRng.Insts.Rand_coreTryCryptoRngError, returned, bind_tc_ok]; rfl⟩

omit crypto authentication in
theorem server_new_of_success (identifier : U64)
    (identitySeed mldsaSeed : core.option.Option (Slice U8)) (server : server.Server)
    (constructed : beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed = ok (.Ok server)) :
    beaconcrypt_server_constructor.server.Server.new identifier identitySeed mldsaSeed = ok server := by
  simp only [beaconcrypt_server_constructor.server.Server.new, constructed, bind_tc_ok, core.result.Result.expect]

omit material platform crypto generators standard authentication serverStandard in
theorem beacon_closure_0_total {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (capture : beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure R E) (error : beaconcrypt_crypto.CryptoError) :
    ∃ result, beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once generator capture error = ok result := ⟨(), rfl⟩

omit material platform crypto generators standard authentication serverStandard primitive in
theorem beacon_closure_1_total {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (capture : beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_1 R E) (error : core.array.TryFromSliceError) :
    ∃ result, beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError.call_once generator capture error = ok result := ⟨(), rfl⟩

omit material platform crypto generators standard authentication serverStandard in
theorem beacon_closure_2_total {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (capture : beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_2 R E) (error : beaconcrypt_crypto.CryptoError) :
    ∃ result, beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_2.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once generator capture error = ok result := ⟨(), rfl⟩

omit material platform crypto generators standard authentication serverStandard in
theorem beacon_closure_3_total {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (capture : beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_3 R E) (error : beaconcrypt_crypto.CryptoError) :
    ∃ result, beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_3.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once generator capture error = ok result := ⟨(), rfl⟩

omit material platform crypto generators standard authentication serverStandard in
theorem beacon_closure_4_total {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (capture : beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_4 R E) (error : beaconcrypt_crypto.CryptoError) :
    ∃ result, beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_4.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once generator capture error = ok result := ⟨(), rfl⟩

omit material platform crypto generators standard authentication serverStandard in
theorem server_closure_0_total {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (capture : beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure R E) (error : beaconcrypt_crypto.CryptoError) :
    ∃ result, beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once generator capture error = ok result := ⟨(), rfl⟩

omit material platform crypto generators standard authentication serverStandard primitive in
theorem server_closure_1_total {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (capture : beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure_1 R E) (error : core.array.TryFromSliceError) :
    ∃ result, beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError.call_once generator capture error = ok result := ⟨(), rfl⟩

end BeaconcryptCore.PanicFreedom.AdapterConstructors
