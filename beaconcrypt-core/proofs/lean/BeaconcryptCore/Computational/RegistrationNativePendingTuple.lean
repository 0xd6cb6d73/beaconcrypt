-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement
import BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativeInitOwnerIdentity

/-! A current actual InitSent owner retains its original bundle's checked public tuple, one-time public input, complete unsigned Init preimage and exact shared-cache digest. The witness is derived from the same execution journal, not reconstructed from later ratchet state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePendingTuple
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

structure Receipt (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (cache : CtxRomAuth.CtxRO.QueryCache) where
  started : pqxdh.BeaconStart
  hashing : registration.BeaconInitHash
  digest : CtxRomAuth.CtxDigest
  view : registration.InitView
  bytes : Pqxdh.Bytes
  validated : pqxdh.validate_init_kex started.message = .ok (.Ok {
    beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
    beacon_prekey_public_key := owner.prekeyPublic,
    beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
    beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic })
  fixed : RegistrationNativeInitTupleSource.Fixed started owner.pin
    (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
    hashing.state
  attached : RegistrationNativeInitTupleSource.Attached started hashing.state
  cached : cache ((), (RegistrationNativeInitStageContents.sourcePayload hashing.state).transcript) = some digest
  control : pending.control = hashing.state.started.state
  pin : pending.binding.server_pin = hashing.state.server_pin
  identity : pending.binding.init_fields.identity_key = hashing.state.started.message.identity_key
  initHash : pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest
  encoded : wire.encodeInit view = .Some bytes
  fields : view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields hashing.state
  retained : pending.binding.init_fields = RegistrationNativeInitTupleSource.ownedFields hashing.state

attribute [local irreducible] RegistrationNativeExperiment.handler

/-- Every actual initialized source path supplies the complete current owner's original pending tuple/cache receipt. -/
theorem initialized_path (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid))
    (final : RegistrationNativeExperiment.State n KemSK source)
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source)))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls final)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (found : final.beacons[index]? = some owner)
    (phase : owner.phase = .initSent pending oneTime) :
    Nonempty (Receipt setup wire owner pending oneTime (RegistrationNativeWorldCache.cache final)) := by
  obtain ⟨call, _member, origin, _leading, trailing, earlier, _split, _before, _called, afterPath,
    earlierFound, earlierPhase, lateMetadata⟩ := RegistrationNativeInitPendingJournal.initialized_path
      setup checks wire route representation ensureInit identityIndex serverKid initial startup final calls actual index owner pending oneTime found phase
  obtain ⟨bytes, _query, _reply, receipt, _present⟩ := origin
  obtain ⟨bornOwner, current, scalar, earlierPending, started, hashing, digest, view,
    _bornFound, currentFound, currentPhase, metadata, _fresh, _started, validated, fixed, attached, cached,
    control, pin, identity, initHash, encoded, fields, retained⟩ := receipt
  have sameCurrent : current = earlier := Option.some.inj (currentFound.symm.trans earlierFound)
  subst current
  obtain ⟨pendingEq, scalarEq⟩ := RegistrationNativeBeaconFrontend.Phase.initSent.inj (currentPhase.symm.trans earlierPhase)
  subst earlierPending
  subst scalar
  have sameMetadata : RegistrationNativeOwnerFields.metadata owner = RegistrationNativeOwnerFields.metadata bornOwner := lateMetadata.trans metadata
  have sameIdentity : owner.identitySeed = bornOwner.identitySeed := by
    simpa only [RegistrationNativeOwnerFields.metadata] using congrArg (fun value : RegistrationNativeBeaconFrontend.Owner source => value.identitySeed) sameMetadata
  have samePrekey : owner.prekeyPublic = bornOwner.prekeyPublic := by
    simpa only [RegistrationNativeOwnerFields.metadata] using congrArg (fun value : RegistrationNativeBeaconFrontend.Owner source => value.prekeyPublic) sameMetadata
  have sameKem : owner.kemPublic = bornOwner.kemPublic := by
    simpa only [RegistrationNativeOwnerFields.metadata] using congrArg (fun value : RegistrationNativeBeaconFrontend.Owner source => value.kemPublic) sameMetadata
  have samePin : owner.pin = bornOwner.pin := by
    simpa only [RegistrationNativeOwnerFields.metadata] using congrArg (fun value : RegistrationNativeBeaconFrontend.Owner source => value.pin) sameMetadata
  have extension := RegistrationNativeInitTupleAgreement.path_cache setup checks wire route representation initial.created initial.credential afterPath
  refine ⟨⟨started, hashing, digest, view, bytes, ?_, ?_, attached, extension cached, control, pin, identity, initHash, encoded, fields, retained⟩⟩
  · simpa only [← sameIdentity, ← samePrekey, ← sameKem] using validated
  · simpa only [← samePin, ← sameIdentity] using fixed

/-- Completing the binding retained by this original source publication selects the exact generated Ed key from the same owner, through its original validation and full raw Init receipt. -/
theorem completed_identity (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (cache : CtxRomAuth.CtxRO.QueryCache)
    (receipt : Receipt setup wire owner pending oneTime cache)
    (digest : Std.Array U8 64#usize) (completed : session.CompletedRegistrationBinding)
    (resumed : pending.binding.complete digest = .ok completed) :
    completed.beacon_identity_public_key =
      PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  exact RegistrationNativeInitOwnerIdentity.completed_identity receipt.started receipt.hashing.state owner.pin _
    pending.binding _ digest completed receipt.fixed receipt.identity receipt.validated resumed

/-- Two successful completed bindings from these same source owner receipts can share the owned identity only when the owners' actual generated Ed keys agree. This implication precedes the separate collision probability reduction. -/
theorem same_generated_identity (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (first second : RegistrationNativeBeaconFrontend.Owner source)
    (firstPending secondPending : registration.BeaconPending)
    (firstOneTime secondOneTime : PqxdhJointGapDh.ScalarBytes)
    (firstCache secondCache : CtxRomAuth.CtxRO.QueryCache)
    (firstReceipt : Receipt setup wire first firstPending firstOneTime firstCache)
    (secondReceipt : Receipt setup wire second secondPending secondOneTime secondCache)
    (firstDigest secondDigest : Std.Array U8 64#usize)
    (firstCompleted secondCompleted : session.CompletedRegistrationBinding)
    (firstResumed : firstPending.binding.complete firstDigest = .ok firstCompleted)
    (secondResumed : secondPending.binding.complete secondDigest = .ok secondCompleted)
    (same : firstCompleted.beacon_identity_public_key = secondCompleted.beacon_identity_public_key) :
    (setup.joint.publicKeys first.identitySeed).ed25519 =
      (setup.joint.publicKeys second.identitySeed).ed25519 := by
  have firstKey := completed_identity setup wire first firstPending firstOneTime firstCache firstReceipt
    firstDigest firstCompleted firstResumed
  have secondKey := completed_identity setup wire second secondPending secondOneTime secondCache secondReceipt
    secondDigest secondCompleted secondResumed
  exact RegistrationNativeInitOwnerIdentity.public_key_eq _ _ (firstKey.symm.trans (same.trans secondKey))

end BeaconcryptCore.Computational.RegistrationNativePendingTuple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingTuple.initialized_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingTuple.initialized_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingTuple.completed_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingTuple.completed_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingTuple.same_generated_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingTuple.same_generated_identity
