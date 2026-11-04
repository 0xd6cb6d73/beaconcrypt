-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement
import BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal

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
  fingerprint : registration.BeaconFingerprint
  digest : CtxRomAuth.CtxDigest
  view : registration.SignedInitView
  bytes : Pqxdh.Bytes
  validated : pqxdh.validate_init_kex started.message = .ok (.Ok {
    beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
    beacon_prekey_public_key := owner.prekeyPublic,
    beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
    beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic })
  fixed : RegistrationNativeInitTupleSource.Fixed started owner.pin
    (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
    owner.mldsa.publicKey fingerprint.state
  attached : RegistrationNativeInitTupleSource.Attached started fingerprint.state
  cached : cache ((), (RegistrationNativeInitStageContents.sourcePayload fingerprint.state).transcript) = some digest
  control : pending.control = fingerprint.state.started.state
  pin : pending.binding.server_pin = fingerprint.state.server_pin
  identity : pending.binding.beacon_identity_public_key = fingerprint.state.beacon_identity
  initHash : pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest
  encoded : wire.encodeInit view = .Some bytes
  fields : view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields fingerprint.state

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
  obtain ⟨bornOwner, current, scalar, earlierPending, started, fingerprint, digest, view,
    _bornFound, currentFound, currentPhase, metadata, _fresh, _started, validated, fixed, attached, cached,
    control, pin, identity, initHash, encoded, fields⟩ := receipt
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
  have sameMldsa : owner.mldsa = bornOwner.mldsa := by
    simpa only [RegistrationNativeOwnerFields.metadata] using congrArg (fun value : RegistrationNativeBeaconFrontend.Owner source => value.mldsa) sameMetadata
  have extension := RegistrationNativeInitTupleAgreement.path_cache setup checks wire route representation initial.created initial.credential afterPath
  refine ⟨⟨started, fingerprint, digest, view, bytes, ?_, ?_, attached, extension cached, control, pin, identity, initHash, encoded, fields⟩⟩
  · simpa only [← sameIdentity, ← samePrekey, ← sameKem] using validated
  · simpa only [← samePin, ← sameIdentity, ← sameMldsa] using fixed

end BeaconcryptCore.Computational.RegistrationNativePendingTuple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingTuple.initialized_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingTuple.initialized_path
