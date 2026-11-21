-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationInitAuthenticationCache
import BeaconcryptCore.Computational.RegistrationNativeInitTupleSource
import BeaconcryptCore.Computational.RegistrationAdHashAgreement

/-! Actual successful Init authentication retains all four original attached buffers. A reached outgoing Init hash and the matching accepted hash identify those buffers outside the existing common-cache collision event. This is full raw transcript agreement, including attached signatures, rather than only agreement of parsed Diffie-Hellman inputs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeAdInitFields
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationServerNativeSource.authenticate
  RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin

/-- The actual source authentication cut copies exactly the received raw Init fields. -/
theorem authenticated_fields (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (before after : State n)
    (events : List RegistrationAuthenticationFlow.Event) (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before)) :
    authenticated.binding.init_fields = RegistrationAuthentication.ownedFields packet := by
  rw [RegistrationNativeInitAuthentication.authenticate, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have valueEq : inner.1 = .ok (events, .Accepted authenticated) := congrArg Prod.fst same
  have native : (.ok (events, .Accepted authenticated), inner.2) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1) := by
    simpa only [← valueEq, Prod.mk.eta] using called
  exact (RegistrationWorldAuthentication.begin_request_provenance setup codec route verify
    before.pin packet before.world.world.1 inner.2 events authenticated native).2.1

/-- The actual accepted request and reached outgoing request with the same digest retain identical full attached fields. -/
theorem same_request_fields (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (before after : State n)
    (events : List RegistrationAuthenticationFlow.Event) (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before))
    (cache : CtxRomAuth.CtxRO.QueryCache) (extension : after.world.world.1.primitive.2 ≤ cache)
    (state : registration.BeaconInitState) (digest : CtxRomAuth.CtxDigest)
    (cached : cache ((), (RegistrationNativeInitStageContents.sourcePayload state).transcript) = some digest)
    (initHash : authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest)
    (collisionFree : ¬ CacheHasCollision cache) :
    authenticated.binding.init_fields = RegistrationNativeInitTupleSource.ownedFields state := by
  obtain ⟨actualDigest, actualCached, hashEq⟩ := RegistrationNativeInitAuthentication.authenticated_cache
    setup codec route verify created packet before after events authenticated supported
  have digestEq : actualDigest = digest := by
    apply List.Vector.toList_injective
    have bytes := congrArg absBytes (hashEq.symm.trans initHash)
    simpa only [RegistrationAuthenticationShared.digest_array_bytes] using bytes
  subst actualDigest
  have same := RegistrationAdHashAgreement.init_fields_from_cache cache state before.pin packet digest
    cached (extension actualCached) collisionFree
  exact (authenticated_fields setup codec route verify created packet before after events authenticated supported).trans same.symm

end BeaconcryptCore.Computational.RegistrationNativeAdInitFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAdInitFields.authenticated_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAdInitFields.authenticated_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAdInitFields.same_request_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAdInitFields.same_request_fields
