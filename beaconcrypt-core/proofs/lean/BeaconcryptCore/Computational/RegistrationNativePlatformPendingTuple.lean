-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase
import BeaconcryptCore.Computational.RegistrationNativeInitOwnerIdentity

/-! A successful complete effectful source bundle retains the original generated tuple, attached fields and cached unsigned Init digest at its actual stored pending owner. The receipt keeps the actual source publication cut through BundleOwnerPhase.Stored, without replacing its terminal writer by a static encoder. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeOwnerFields (metadata)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

structure Receipt (setup : Setup base KemSK) (owner : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (cache : CtxRomAuth.CtxRO.QueryCache) where
  started : pqxdh.BeaconStart
  hashing : registration.BeaconInitHash
  digest : CtxRomAuth.CtxDigest
  view : registration.InitView
  validated : pqxdh.validate_init_kex started.message = .ok (.Ok {
    beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
    beacon_prekey_public_key := owner.prekeyPublic,
    beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
    beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic })
  fixed : RegistrationNativeInitTupleSource.Fixed started owner.pin
    (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519) hashing.state
  attached : RegistrationNativeInitTupleSource.Attached started hashing.state
  cached : cache ((), (RegistrationNativeInitStageContents.sourcePayload hashing.state).transcript) = some digest
  control : pending.control = hashing.state.started.state
  pin : pending.binding.server_pin = hashing.state.server_pin
  identity : pending.binding.init_fields.identity_key = hashing.state.started.message.identity_key
  initHash : pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest
  fields : view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields hashing.state
  retained : pending.binding.init_fields = RegistrationNativeInitTupleSource.ownedFields hashing.state

/-- Exact metadata preservation and an actual later cache extension carry the original pending tuple without reading any later ratchet state. -/
theorem transport (setup : Setup base KemSK) (before after : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (earlier later : CtxRomAuth.CtxRO.QueryCache)
    (same : metadata after = metadata before) (extension : earlier ≤ later)
    (receipt : Receipt setup before pending oneTime earlier) : Nonempty (Receipt setup after pending oneTime later) := by
  have sameIdentity : after.identitySeed = before.identitySeed := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.identitySeed) same
  have samePrekey : after.prekeyPublic = before.prekeyPublic := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.prekeyPublic) same
  have sameKem : after.kemPublic = before.kemPublic := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.kemPublic) same
  have samePin : after.pin = before.pin := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.pin) same
  refine ⟨⟨receipt.started, receipt.hashing, receipt.digest, receipt.view, ?_, ?_, receipt.attached,
    extension receipt.cached, receipt.control, receipt.pin, receipt.identity, receipt.initHash, receipt.fields, receipt.retained⟩⟩
  · simpa only [sameIdentity, samePrekey, sameKem] using receipt.validated
  · simpa only [sameIdentity, samePin] using receipt.fixed

/-- The literal stored source cut yields its original pending tuple in the actual whole-bundle final shared cache. -/
theorem stored (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (bytes : Pqxdh.Bytes)
    (cut : RegistrationNativePlatformBundleOwnerPhase.Stored coins setup checks representation created writer index before after previous next bytes) :
    Nonempty (Receipt setup cut.current cut.cut.published.pending cut.cut.oneTime (RegistrationNativeWorldCache.cache after)) := by
  obtain ⟨started, _pending, hashing, _atHash, digest, view, _encodedView, _atWriter,
    _began, validated, _leading, fixed, attached, _source, cached, initHash, control, pin, identity, fields, retained, _written⟩ :=
    RegistrationNativePlatformInitTupleCache.outgoing coins setup checks representation created writer index cut.cut.owner cut.cut.oneTime
      cut.cut.published cut.cut.atPublication cut.cut.afterPublication cut.cut.publicationPlatform cut.cut.afterPublicationPlatform cut.cut.publicationCalled
  have extension := RegistrationNativePlatformBundlePublication.afterPublished_cache coins setup checks representation created index
    cut.cut.owner cut.cut.oneTime cut.cut.published cut.cut.afterPublication cut.localAfter cut.cut.afterPublicationPlatform next cut.encoded cut.cut.continued
  have finalCache : RegistrationNativeWorldCache.cache cut.localAfter.2.2 = RegistrationNativeWorldCache.cache after := by
    exact (show RegistrationNativeWorldCache.cache (RegistrationNativeMldsaShared.close cut.localAfter) =
      RegistrationNativeWorldCache.cache cut.localAfter.2.2 from rfl).symm.trans
      (congrArg RegistrationNativeWorldCache.cache cut.nativeEq)
  rw [finalCache] at extension
  have original : Receipt setup cut.cut.owner cut.cut.published.pending cut.cut.oneTime
      (RegistrationNativeWorldCache.cache cut.cut.afterPublication.2.2) :=
    ⟨started, hashing, digest, view, validated, fixed, attached, cached, control, pin, identity, initHash, fields, retained⟩
  exact transport setup cut.cut.owner cut.current cut.cut.published.pending cut.cut.oneTime _ _ cut.metadataEq extension original

/-- Actual successful complete source execution supplies both its literal selected-owner/publication/writer cut and the stored pending tuple/cache receipt. -/
theorem bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (bytes : Pqxdh.Bytes)
    (supported : ((.ok (some bytes), after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    ∃ cut : RegistrationNativePlatformBundleOwnerPhase.Stored coins setup checks representation created writer index before after previous next bytes,
      Nonempty (Receipt setup cut.current cut.cut.published.pending cut.cut.oneTime (RegistrationNativeWorldCache.cache after)) := by
  obtain ⟨cut⟩ := RegistrationNativePlatformBundleOwnerPhase.native_bundle coins setup checks representation created writer index before after previous next bytes supported
  exact ⟨cut, stored coins setup checks representation created writer index before after previous next bytes cut⟩

/-- Completing the binding retained by this original source publication selects the exact generated Ed key from the same owner, through its original validation and full raw Init receipt. -/
theorem completed_identity (setup : Setup base KemSK) (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (cache : CtxRomAuth.CtxRO.QueryCache)
    (receipt : Receipt setup owner pending oneTime cache)
    (digest : Std.Array U8 64#usize) (completed : session.CompletedRegistrationBinding)
    (resumed : pending.binding.complete digest = .ok completed) :
    completed.beacon_identity_public_key =
      PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  exact RegistrationNativeInitOwnerIdentity.completed_identity receipt.started receipt.hashing.state owner.pin _
    pending.binding _ digest completed receipt.fixed receipt.identity receipt.validated resumed

/-- Two successful completed bindings from these same source owner receipts can share the owned identity only when the owners' actual generated Ed keys agree. This implication precedes the separate collision probability reduction. -/
theorem same_generated_identity (setup : Setup base KemSK) (first second : RegistrationNativeBeaconFrontend.Owner source)
    (firstPending secondPending : registration.BeaconPending)
    (firstOneTime secondOneTime : PqxdhJointGapDh.ScalarBytes)
    (firstCache secondCache : CtxRomAuth.CtxRO.QueryCache)
    (firstReceipt : Receipt setup first firstPending firstOneTime firstCache)
    (secondReceipt : Receipt setup second secondPending secondOneTime secondCache)
    (firstDigest secondDigest : Std.Array U8 64#usize)
    (firstCompleted secondCompleted : session.CompletedRegistrationBinding)
    (firstResumed : firstPending.binding.complete firstDigest = .ok firstCompleted)
    (secondResumed : secondPending.binding.complete secondDigest = .ok secondCompleted)
    (same : firstCompleted.beacon_identity_public_key = secondCompleted.beacon_identity_public_key) :
    (setup.joint.publicKeys first.identitySeed).ed25519 =
      (setup.joint.publicKeys second.identitySeed).ed25519 := by
  have firstKey := completed_identity setup first firstPending firstOneTime firstCache firstReceipt
    firstDigest firstCompleted firstResumed
  have secondKey := completed_identity setup second secondPending secondOneTime secondCache secondReceipt
    secondDigest secondCompleted secondResumed
  exact RegistrationNativeInitOwnerIdentity.public_key_eq _ _ (firstKey.symm.trans (same.trans secondKey))

end BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.transport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.stored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.completed_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.completed_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.same_generated_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple.same_generated_identity
