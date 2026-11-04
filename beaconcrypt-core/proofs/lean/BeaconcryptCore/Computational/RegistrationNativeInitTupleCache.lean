-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitTupleSource
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared

/-! The original native outgoing interpreter places the reached unsigned Init preimage and its exact pending digest in the same shared cache. Its complete source receipt also retains the actual public tuple and final signing attempt; no caller-supplied cache provenance or completed partner is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitTupleCache
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeInitTupleSource (Fixed Attached FingerprintCut)
open RegistrationNativeInitStageContents (sourcePayload)
open RegistrationBeaconInitExecutor (Spec)
variable {n : Nat} {ι KemSK Encoded : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem sign_cache (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (before : RegistrationSigningShared.State) (signature : RegistrationSigningShared.SignReply) (after : RegistrationSigningShared.State)
    (supported : (signature, after) ∈ support ((RegistrationSigningShared.implementation sign (.sign request payload digest)).run before)) :
    after.2 = before.2 := by
  simp only [RegistrationSigningShared.implementation, StateT.run, support_map] at supported
  obtain ⟨reply, _possible, same⟩ := supported
  exact (congrArg (fun value : RegistrationSigningShared.SignReply × RegistrationSigningShared.State => value.2.2) same).symm

/-- The actual source hash and final signing callback retain the original Init preimage at precisely the pending binding's digest. -/
theorem fingerprint_cached (setup : Setup base KemSK) (owner : Owner source)
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) (before : RegistrationSigningShared.State)
    (published : registration.PublishedBeaconInit Encoded) (after : RegistrationSigningShared.State)
    (cut : FingerprintCut (RegistrationNativeMldsaShared.implementation setup owner) encode pending before published after) :
    ∃ digest view,
      after.2 ((), (sourcePayload pending.state).transcript) = some digest ∧
      published.pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest ∧
      published.pending.control = pending.state.started.state ∧
      published.pending.binding.server_pin = pending.state.server_pin ∧
      published.pending.binding.beacon_identity_public_key = pending.state.beacon_identity ∧
      encode view = .Some published.encoded ∧ view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields pending.state := by
  obtain ⟨request, digest, beforeHash, afterHash, signRequest, signature, view, hashSupport, signSupport, bytes,
    _signKey, control, pin, identity, initHash, encoded, fields⟩ :=
    RegistrationNativeInitTupleSource.fingerprint_contents (RegistrationNativeMldsaShared.implementation setup owner)
      encode pending before published after cut
  have cached := (RegistrationSigningShared.hash_cached (RegistrationNativeMldsa.owned source owner.mldsa)
    request beforeHash (digest, afterHash) hashSupport).2
  have retained := sign_cache (RegistrationNativeMldsa.owned source owner.mldsa) signRequest (sourcePayload pending.state)
    digest afterHash signature after signSupport
  refine ⟨digest, view, ?_, initHash, control, pin, identity, encoded, fields⟩
  rw [retained, ← bytes]
  exact cached

/-- Actual native outgoing execution retains its raw generated tuple, actual one-time public input, source stages, pending binding and Init preimage in the same final cache. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : registration.PublishedBeaconInit Pqxdh.Bytes)
    (before after : RegistrationNativeMldsaShared.Local n KemSK source)
    (supported : (.ok (.Ok published), after) ∈ support
      ((RegistrationNativeMldsaShared.lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
          (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
            (RegistrationNativeBeaconFrontend.inputs setup owner)
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey))).run before)) :
    ∃ started pending fingerprint atFingerprint digest view,
      pqxdh.beacon_start ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ = .ok started ∧
      pqxdh.validate_init_kex started.message = .ok (.Ok {
        beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
        beacon_prekey_public_key := owner.prekeyPublic,
        beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
        beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic }) ∧
      RegistrationNativeInitTupleSource.EdLead (RegistrationNativeMldsaShared.implementation setup owner)
        pending (RegistrationNativeMldsaShared.project before) fingerprint atFingerprint ∧
      Fixed started owner.pin (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
        owner.mldsa.publicKey fingerprint.state ∧ Attached started fingerprint.state ∧
      FingerprintCut (RegistrationNativeMldsaShared.implementation setup owner) wire.encodeInit fingerprint atFingerprint published
        (RegistrationNativeMldsaShared.project after) ∧
      (RegistrationNativeMldsaShared.project after).2 ((), (sourcePayload fingerprint.state).transcript) = some digest ∧
      published.pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest ∧
      published.pending.control = fingerprint.state.started.state ∧
      published.pending.binding.server_pin = fingerprint.state.server_pin ∧
      published.pending.binding.beacon_identity_public_key = fingerprint.state.beacon_identity ∧
      wire.encodeInit view = .Some published.encoded ∧
      view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields fingerprint.state := by
  have projected : (.ok (.Ok published), RegistrationNativeMldsaShared.project after) ∈ support
      ((simulateQ (RegistrationNativeMldsaShared.implementation setup owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
          (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)).run
        (RegistrationNativeMldsaShared.project before)) := by
    rw [← RegistrationNativeMldsaShared.program setup checks representation created index owner _ before, support_map]
    exact ⟨(.ok (.Ok published), after), supported, rfl⟩
  obtain ⟨started, pending, fingerprint, atFingerprint, startedRun, validated, _begun, leading, fixed, attached, cut⟩ :=
    RegistrationNativeInitTupleSource.begin_receipt (RegistrationNativeMldsaShared.implementation setup owner) wire.encodeInit
      ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey published
      (RegistrationNativeMldsaShared.project before) (RegistrationNativeMldsaShared.project after) projected
  obtain ⟨digest, view, cached, initHash, control, pin, identity, encoded, fields⟩ :=
    fingerprint_cached setup owner wire.encodeInit fingerprint atFingerprint published (RegistrationNativeMldsaShared.project after) cut
  exact ⟨started, pending, fingerprint, atFingerprint, digest, view, startedRun, validated, leading, fixed, attached,
    cut, cached, initHash, control, pin, identity, encoded, fields⟩

/-- Equal same-cache Init digests determine every accepted attached field and selected Server key outside the one literal cache-collision event. -/
theorem accepted_fields (cache : CtxRomAuth.CtxRO.QueryCache) (state : registration.BeaconInitState)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (digest : CtxRomAuth.CtxDigest)
    (sourceCached : cache ((), (sourcePayload state).transcript) = some digest)
    (acceptedCached : cache ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage pin packet) = some digest)
    (collisionFree : ¬ CacheHasCollision cache) :
    state.started.message.identity_key = packet.identity_key ∧ state.pre_key = packet.pre_key ∧
      state.one_time_key = packet.one_time_key ∧ state.pq_key = packet.pq_key ∧
      state.beacon_mldsa = packet.mldsa_public_key ∧
      state.server_pin.binding.identity_key_id = pin.binding.identity_key_id ∧
      state.server_pin.binding.identity_public_key = pin.binding.identity_public_key ∧ state.server_pin.public_key = pin.public_key := by
  have querySame := cache_lookup_eq_of_noCollision collisionFree sourceCached ⟨digest, acceptedCached, HEq.rfl⟩
  have bytes := congrArg Prod.snd querySame
  apply RegistrationNativeInitStageContents.native_fields state pin packet
  exact congrArg (MldsaTranscriptAuth.Payload.mk .beacon) bytes

end BeaconcryptCore.Computational.RegistrationNativeInitTupleCache
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleCache.fingerprint_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleCache.fingerprint_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleCache.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleCache.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleCache.accepted_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleCache.accepted_fields
