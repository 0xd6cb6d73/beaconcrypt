-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace
import BeaconcryptCore.Computational.RegistrationNativeInitTupleCache
import BeaconcryptCore.Computational.RegistrationCredentialBridge
import BeaconcryptCore.Computational.RegistrationNativeHandlerCacheCore
import BeaconcryptCore.Computational.RegistrationNativeServerPinTrace

/-! Actual common-cache receipts and extracted typed validation identify the exact accepted native Init key tuple. The primitive-width representation is retained; no secret-input agreement or partner premise is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeStageTrace (Call Path)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate
  RegistrationAuthenticationShared.begin RegistrationWorldAuthentication.begin
  RegistrationAuthenticationExecutor.begin RegistrationAuthenticationExecutor.execute
  RegistrationAuthenticationShared.implementation

/-- Actual native authentication returns exactly the original packet's extracted typed key tuple. -/
theorem parsed (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : RegistrationServerFrontendCompiler.State n)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event) (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before)) :
    RegistrationCredentialBridge.parsedPacket packet = some (PqxdhHeadlineBridges.typedVerified authenticated.registration) := by
  rw [RegistrationNativeInitAuthentication.authenticate, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have valueEq : inner.1 = .ok (events, .Accepted authenticated) := congrArg Prod.fst same
  have native : (.ok (events, .Accepted authenticated), inner.2) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1) := by
    simpa only [← valueEq, Prod.mk.eta] using called
  have actual := RegistrationWorldAuthentication.begin_native_support setup codec route verify before.pin packet
    before.world.world.1 inner.2 events authenticated native
  apply RegistrationCredentialBridge.interpreted_accepted_parsed
    (RegistrationAuthenticationShared.implementation setup.source.crypto verify codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source))
      before.pin packet events authenticated (RegistrationWorldAuthentication.project before.world.world.1)
        (RegistrationWorldAuthentication.project inner.2)
  simpa only [RegistrationAuthenticationShared.begin] using actual

/-- The actual cache and typed validation force the accepted registration to be the tuple from this reached source bundle. -/
theorem registration (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : RegistrationServerFrontendCompiler.State n)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event) (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before))
    (cache : CtxRomAuth.CtxRO.QueryCache) (extension : after.world.world.1.primitive.2 ≤ cache)
    (state : registration.BeaconInitState) (started : pqxdh.BeaconStart) (expected : pqxdh.VerifiedInitKex)
    (startedSame : state.started = started) (attached : RegistrationNativeInitTupleSource.Attached started state)
    (validated : pqxdh.validate_init_kex started.message = .ok (.Ok expected))
    (digest : CtxRomAuth.CtxDigest)
    (cached : cache ((), (RegistrationNativeInitStageContents.sourcePayload state).transcript) = some digest)
    (initHash : authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest)
    (collisionFree : ¬ CacheHasCollision cache) :
    authenticated.registration = expected := by
  obtain ⟨actualDigest, actualCached, hashEq⟩ := RegistrationNativeTokenCacheSource.authenticated_cache setup codec route verify created
    packet before after events authenticated supported
  have digestEq : actualDigest = digest := by
    apply List.Vector.toList_injective
    have bytes := congrArg absBytes (hashEq.symm.trans initHash)
    simpa only [RegistrationAuthenticationShared.digest_array_bytes] using bytes
  subst actualDigest
  have fields := RegistrationNativeInitTupleCache.accepted_fields cache state before.pin packet digest cached (extension actualCached) collisionFree
  have credential : BeaconcryptCore.Refinement.RegistrationCredentialMetadata.Credential packet expected := by
    refine ⟨started.message, ?_, ?_, ?_, ?_, validated⟩
    · exact (congrArg (fun value : pqxdh.BeaconStart => value.message.identity_key) startedSame).symm.trans fields.1
    · exact (show state.pre_key.val.drop 64 = started.message.prekey.val from attached.1).symm.trans
        (congrArg (fun value : Std.Array U8 98#usize => value.val.drop 64) fields.2.1)
    · exact (show state.one_time_key.val.drop 64 = started.message.one_time_key.val from attached.2.1).symm.trans
        (congrArg (fun value : Std.Array U8 98#usize => value.val.drop 64) fields.2.2.1)
    · exact (show state.pq_key.val.drop 64 = started.message.pq_key.val from attached.2.2).symm.trans
        (congrArg (fun value : Std.Array U8 1249#usize => value.val.drop 64) fields.2.2.2.1)
  apply PqxdhHeadlineBridges.typedVerified_injective
  exact Option.some.inj ((parsed setup codec route verify created packet before after events authenticated supported).symm.trans
    (RegistrationCredentialBridge.credential_parsed packet expected credential))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "implementation" => RegistrationNativeExperiment.handler setup checks wire route representation created source credential

/-- Every actual source path extends its single shared authentication/record cache. -/
theorem path_cache {first final : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls final) : RegistrationNativeWorldCache.cache first ≤ RegistrationNativeWorldCache.cache final := by
  induction actual with
  | nil => exact le_refl _
  | cons call called rest last following ih =>
      exact (RegistrationNativeHandlerCache.handler setup checks wire route representation created credential call.query call.before
        (call.reply, call.after) called).trans ih

/-- The exact native Server authentication pin is constant along the same actual source path. -/
theorem path_pin {first final : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls final) : final.server.pin = first.server.pin := by
  induction actual with
  | nil => rfl
  | cons call called rest last following ih =>
      exact ih.trans (RegistrationNativeServerPinTrace.handler_pin setup checks wire route representation created credential
        call.query call.before (call.reply, call.after) called)

end BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement.parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement.parsed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement.registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement.registration

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement.path_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement.path_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement.path_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement.path_pin
