-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitTupleSource
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared

/-! The original native outgoing interpreter places the reached unsigned Init preimage and its exact pending digest in the same shared cache. Its complete source receipt also retains the actual public tuple before pure publication; no caller-supplied cache provenance or completed partner is assumed. -/
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
open RegistrationNativeInitTupleSource (Fixed Attached HashCut)
open RegistrationNativeInitStageContents (sourcePayload)
open RegistrationBeaconInitExecutor (Spec)
variable {n : Nat} {ι KemSK Encoded : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The actual final request hash retains its selected preimage and pending digest in the same reached cache. -/
theorem hash_cached (setup : Setup base KemSK) (owner : Owner source)
    (encode : registration.InitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (before : RegistrationSigningShared.State)
    (published : registration.PublishedBeaconInit Encoded) (after : RegistrationSigningShared.State)
    (cut : RegistrationNativeInitTupleSource.HashCut (RegistrationNativeMldsaShared.implementation setup owner)
      encode pending before published after) :
    ∃ digest view,
      after.2 ((), (sourcePayload pending.state).transcript) = some digest ∧
      published.pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest ∧
      published.pending.control = pending.state.started.state ∧
      published.pending.binding.server_pin = pending.state.server_pin ∧
      published.pending.binding.init_fields.identity_key = pending.state.started.message.identity_key ∧
      encode view = .Some published.encoded ∧ view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields pending.state ∧
      published.pending.binding.init_fields = RegistrationNativeInitTupleSource.ownedFields pending.state := by
  obtain ⟨request, digest, view, called, bytes, control, pin, identity, initHash, encoded, fields⟩ :=
    RegistrationNativeInitTupleSource.hash_contents (RegistrationNativeMldsaShared.implementation setup owner)
      encode pending before published after cut
  have cached := (RegistrationSigningShared.hash_cached (fun _ => pure .None)
    request before (digest, after) called).2
  have retained := RegistrationNativeInitTupleSource.hash_fields_contents
    (RegistrationNativeMldsaShared.implementation setup owner) encode pending before published after cut
  refine ⟨digest, view, ?_, initHash, control, pin, identity, encoded, fields, retained⟩
  rw [← bytes]
  exact cached

/-- Actual native outgoing execution retains its raw generated tuple, actual one-time public input, source stages, pending binding and Init preimage in the same final cache. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : registration.PublishedBeaconInit Pqxdh.Bytes)
    (before after : RegistrationNativeMldsaShared.Local n KemSK source)
    (supported : (.ok (.Ok published), after) ∈ support
      ((RegistrationNativeMldsaShared.lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
          (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
            (RegistrationNativeBeaconFrontend.inputs setup owner)
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin))).run before)) :
    ∃ started pending hashing atHash digest view,
      pqxdh.beacon_start ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ = .ok started ∧
      pqxdh.validate_init_kex started.message = .ok (.Ok {
        beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
        beacon_prekey_public_key := owner.prekeyPublic,
        beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
        beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic }) ∧
      RegistrationNativeInitTupleSource.EdLead (RegistrationNativeMldsaShared.implementation setup owner)
        pending (RegistrationNativeMldsaShared.project before) hashing atHash ∧
      Fixed started owner.pin (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
        hashing.state ∧ Attached started hashing.state ∧
      HashCut (RegistrationNativeMldsaShared.implementation setup owner) wire.encodeInit hashing atHash published
        (RegistrationNativeMldsaShared.project after) ∧
      (RegistrationNativeMldsaShared.project after).2 ((), (sourcePayload hashing.state).transcript) = some digest ∧
      published.pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest ∧
      published.pending.control = hashing.state.started.state ∧
      published.pending.binding.server_pin = hashing.state.server_pin ∧
      published.pending.binding.init_fields.identity_key = hashing.state.started.message.identity_key ∧
      wire.encodeInit view = .Some published.encoded ∧
      view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields hashing.state ∧
      published.pending.binding.init_fields = RegistrationNativeInitTupleSource.ownedFields hashing.state := by
  have projected : (.ok (.Ok published), RegistrationNativeMldsaShared.project after) ∈ support
      ((simulateQ (RegistrationNativeMldsaShared.implementation setup owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
          (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)).run
        (RegistrationNativeMldsaShared.project before)) := by
    rw [← RegistrationNativeMldsaShared.program setup checks representation created index owner _ before, support_map]
    exact ⟨(.ok (.Ok published), after), supported, rfl⟩
  obtain ⟨started, pending, hashing, atHash, startedRun, validated, _begun, leading, fixed, attached, cut⟩ :=
    RegistrationNativeInitTupleSource.begin_receipt (RegistrationNativeMldsaShared.implementation setup owner) wire.encodeInit
      ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin published
      (RegistrationNativeMldsaShared.project before) (RegistrationNativeMldsaShared.project after) projected
  obtain ⟨digest, view, cached, initHash, control, pin, identity, encoded, fields, retained⟩ :=
    hash_cached setup owner wire.encodeInit hashing atHash published (RegistrationNativeMldsaShared.project after) cut
  exact ⟨started, pending, hashing, atHash, digest, view, startedRun, validated, leading, fixed, attached,
    cut, cached, initHash, control, pin, identity, encoded, fields, retained⟩

/-- Equal same-cache Init digests determine every accepted attached field and selected Server key outside the one literal cache-collision event. -/
theorem accepted_fields (cache : CtxRomAuth.CtxRO.QueryCache) (state : registration.BeaconInitState)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (digest : CtxRomAuth.CtxDigest)
    (sourceCached : cache ((), (sourcePayload state).transcript) = some digest)
    (acceptedCached : cache ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage pin packet) = some digest)
    (collisionFree : ¬ CacheHasCollision cache) :
    state.started.message.identity_key = packet.identity_key ∧ state.pre_key = packet.pre_key ∧
      state.one_time_key = packet.one_time_key ∧ state.pq_key = packet.pq_key ∧
      state.server_pin.binding.identity_key_id = pin.binding.identity_key_id ∧
      state.server_pin.binding.identity_public_key = pin.binding.identity_public_key ∧ state.server_pin.public_key = pin.public_key := by
  have querySame := cache_lookup_eq_of_noCollision collisionFree sourceCached ⟨digest, acceptedCached, HEq.rfl⟩
  have bytes := congrArg Prod.snd querySame
  apply RegistrationNativeInitStageContents.native_fields state pin packet
  exact congrArg (MldsaTranscriptAuth.Payload.mk .beacon) bytes

end BeaconcryptCore.Computational.RegistrationNativeInitTupleCache
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitTupleCache.hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitTupleCache.hash_cached

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
