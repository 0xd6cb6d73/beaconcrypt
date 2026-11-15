-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence
import BeaconcryptCore.Computational.RegistrationNativeHandlerCache

/-! Matching Init digests in the actual common collision-free cache identify the pending owner's exact source public tuple and stored private prekey operand. Earlier source publication and current owner coherence are derived from the initialized journal. No cross-role DH equality, KEM agreement or completed partner is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitPendingOperands
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativeBeaconFrontend (Owner Phase)
open RegistrationNativeOwnerFields (metadata)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

private theorem digest_injective (left right : CtxRomAuth.CtxDigest)
    (same : RegistrationAuthenticationShared.digestArray left = RegistrationAuthenticationShared.digestArray right) : left = right := by
  apply List.Vector.toList_injective
  simpa only [RegistrationAuthenticationShared.digest_array_bytes] using congrArg PqxdhRefinement.absBytes same

/-- A packet whose actual cached Init preimage matches the stored pending digest has exactly the source tuple retained by that successful bundle. -/
theorem packet_tuple (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before after : Native) (bytes : Pqxdh.Bytes)
    (receipt : RegistrationNativeBundleInitReceipt.Receipt setup wire index before after bytes)
    (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : after.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (cache : CtxRomAuth.CtxRO.QueryCache) (extension : RegistrationNativeWorldCache.cache after ≤ cache)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (digest : CtxRomAuth.CtxDigest)
    (packetCached : cache ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage pin packet) = some digest)
    (hashSame : pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest)
    (collisionFree : ¬ CacheHasCollision cache) :
    ∃ (original : Owner source) (started : pqxdh.BeaconStart),
      before.beacons[index]? = some original ∧ metadata owner = metadata original ∧
      pqxdh.validate_init_kex started.message = .ok (.Ok {
        beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys original.identitySeed).ed25519,
        beacon_prekey_public_key := original.prekeyPublic,
        beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
        beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray original.kemPublic }) ∧
      packet.identity_key = started.message.identity_key ∧ packet.pre_key.val.drop 64 = started.message.prekey.val ∧
      packet.one_time_key.val.drop 64 = started.message.one_time_key.val ∧ packet.pq_key.val.drop 64 = started.message.pq_key.val ∧

      pin.binding.identity_key_id = original.pin.binding.identity_key_id ∧
      pin.binding.identity_public_key = original.pin.binding.identity_public_key ∧ pin.public_key = original.pin.public_key := by
  obtain ⟨original, stored, scalar, capability, started, hashing, actualDigest, view, originalFound, storedFound, storedPhase,
    immutable, _oldPhase, _started, validated, fixed, attached, cached, _control, _pin, _identity, initHash, _encoded, _fields⟩ := receipt
  have ownerSame := Option.some.inj (storedFound.symm.trans found)
  subst stored
  have capabilities := storedPhase.symm.trans phase
  simp only [Phase.initSent.injEq] at capabilities
  obtain ⟨capabilitySame, scalarSame⟩ := capabilities
  subst capability
  subst scalar
  have digestSame : actualDigest = digest := digest_injective _ _ (initHash.symm.trans hashSame)
  subst actualDigest
  obtain ⟨identity, prekey, oneTimeKey, pq, numeric, ed, ml⟩ := RegistrationNativeInitTupleCache.accepted_fields cache
    hashing.state pin packet digest (extension cached) packetCached collisionFree
  have raw : hashing.state.started = started := congrArg Prod.fst fixed
  have pinSame : hashing.state.server_pin = original.pin := congrArg (fun snapshot => snapshot.2.1) fixed
  refine ⟨original, started, originalFound, immutable, validated, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity.symm.trans (congrArg (fun value : pqxdh.BeaconStart => value.message.identity_key) raw)
  · rw [← prekey]
    exact attached.1
  · rw [← oneTimeKey]
    exact attached.2.1
  · rw [← pq]
    exact attached.2.2
  · exact numeric.symm.trans (congrArg (fun value : session.ServerAuthenticationPin => value.binding.identity_key_id) pinSame)
  · exact ed.symm.trans (congrArg (fun value : session.ServerAuthenticationPin => value.binding.identity_public_key) pinSame)
  · exact ml.symm.trans (congrArg (fun value : session.ServerAuthenticationPin => value.public_key) pinSame)


private theorem cache_path (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (initial final : Native) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) initial calls final) :
    RegistrationNativeWorldCache.cache initial ≤ RegistrationNativeWorldCache.cache final := by
  induction actual with
  | nil state => exact le_rfl
  | cons call called rest last following ih =>
    exact (RegistrationNativeHandlerCache.handler setup checks wire route representation created credential call.query call.before
      (call.reply, call.after) called).trans ih

private theorem prekey_path (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (initial final : Native) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) initial calls final)
    (prior : RegistrationNativePrekeyCoherence.Holds setup initial.beacons) :
    RegistrationNativePrekeyCoherence.Holds setup final.beacons := by
  revert prior
  induction actual with
  | nil state => intro prior; exact prior
  | cons call called rest last following ih =>
    intro prior
    exact ih (RegistrationNativePrekeyCoherence.handler setup checks wire route representation created credential call.query call.before
      prior (call.reply, call.after) called)

def OwnerTuple (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (started : pqxdh.BeaconStart) : Prop :=
  owner.prekeyPublic = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey owner.prekeyScalar) ∧
  pqxdh.validate_init_kex started.message = .ok (.Ok {
    beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
    beacon_prekey_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey owner.prekeyScalar),
    beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
    beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic }) ∧
  packet.identity_key = started.message.identity_key ∧ packet.pre_key.val.drop 64 = started.message.prekey.val ∧
  packet.one_time_key.val.drop 64 = started.message.one_time_key.val ∧ packet.pq_key.val.drop 64 = started.message.pq_key.val ∧

  pin.binding.identity_key_id = owner.pin.binding.identity_key_id ∧
  pin.binding.identity_public_key = owner.pin.binding.identity_public_key ∧ pin.public_key = owner.pin.public_key

/-- On an actual initialized path, equal matching Init digests in its own collision-free cache identify the current pending owner's precise identity, stored private-prekey public key, one-time public key and indexed PQ public key, from an earlier same-run bundle. -/
theorem initialized_packet (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (final : Native) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls final)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : final.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (digest : CtxRomAuth.CtxDigest)
    (packetCached : RegistrationNativeWorldCache.cache final
      ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage pin packet) = some digest)
    (hashSame : pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache final)) :
    ∃ call ∈ calls, RegistrationNativeInitPendingJournal.SourceAt setup wire call index pending oneTime ∧
      ∃ (original : Owner source) (started : pqxdh.BeaconStart),
        call.before.beacons[index]? = some original ∧ metadata owner = metadata original ∧
        OwnerTuple setup owner oneTime pin packet started := by
  obtain ⟨call, member, origin, leading, trailing, earlier, _split, _before, _called, after, earlierFound, earlierPhase, retained⟩ :=
    RegistrationNativeInitPendingJournal.initialized_path setup checks wire route representation ensureInit identityIndex serverKeyId
      initial startup final calls actual index owner pending oneTime found phase
  have sourceOrigin := origin
  obtain ⟨bytes, _query, _reply, receipt, _pending⟩ := origin
  obtain ⟨original, started, originalFound, sourceMetadata, validated, identity, prekey, ephemeral, pq, numeric, ed, ml⟩ :=
    packet_tuple setup wire index call.before call.after bytes receipt earlier pending oneTime earlierFound earlierPhase
      (RegistrationNativeWorldCache.cache final)
      (cache_path setup checks wire route representation initial.created initial.credential call.after final trailing after)
      pin packet digest packetCached hashSame collisionFree
  have immutable := retained.trans sourceMetadata
  have coherent : owner.prekeyPublic = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey owner.prekeyScalar) :=
    prekey_path setup checks wire route representation initial.created initial.credential initial.state final calls actual
      (RegistrationNativePrekeyCoherence.start setup ensureInit identityIndex serverKeyId initial startup)
      owner (List.mem_of_getElem? found)
  have seedSame : owner.identitySeed = original.identitySeed := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.identitySeed) immutable
  have prekeySame : owner.prekeyPublic = original.prekeyPublic := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.prekeyPublic) immutable
  have pqSame : owner.kemPublic = original.kemPublic := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.kemPublic) immutable
  have pinSame : owner.pin = original.pin := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.pin) immutable
  refine ⟨call, member, sourceOrigin, original, started, originalFound, immutable, coherent, ?_, identity, prekey, ephemeral, pq, ?_, ?_, ?_⟩
  · simpa only [← seedSame, ← prekeySame, ← pqSame, coherent] using validated
  · simpa only [← pinSame] using numeric
  · simpa only [← pinSame] using ed
  · simpa only [← pinSame] using ml


/-- The same operand correspondence follows directly from actual supported initialized adaptive journal execution and its reached common cache. -/
theorem journal_packet (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (Native × List (Call RegistrationNativeRawAdapter.TypedSpec Native)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)) work).run (initial.state, [])))
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : result.2.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (digest : CtxRomAuth.CtxDigest)
    (packetCached : RegistrationNativeWorldCache.cache result.2.1
      ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage pin packet) = some digest)
    (hashSame : pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1)) :
    ∃ call ∈ result.2.2, RegistrationNativeInitPendingJournal.SourceAt setup wire call index pending oneTime ∧
      ∃ (original : Owner source) (started : pqxdh.BeaconStart),
        call.before.beacons[index]? = some original ∧ metadata owner = metadata original ∧
        OwnerTuple setup owner oneTime pin packet started :=
  initialized_packet setup checks wire route representation ensureInit identityIndex serverKeyId initial startup result.2.1 result.2.2
    (RegistrationNativeStageTrace.path _ work initial.state result supported) index owner pending oneTime found phase
    pin packet digest packetCached hashSame collisionFree

end BeaconcryptCore.Computational.RegistrationNativeInitPendingOperands

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitPendingOperands.packet_tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitPendingOperands.packet_tuple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitPendingOperands.initialized_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitPendingOperands.initialized_packet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitPendingOperands.journal_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitPendingOperands.journal_packet
