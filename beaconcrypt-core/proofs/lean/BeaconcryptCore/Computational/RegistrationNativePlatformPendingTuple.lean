-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase

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
  fingerprint : registration.BeaconFingerprint
  digest : CtxRomAuth.CtxDigest
  view : registration.SignedInitView
  validated : pqxdh.validate_init_kex started.message = .ok (.Ok {
    beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
    beacon_prekey_public_key := owner.prekeyPublic,
    beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
    beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic })
  fixed : RegistrationNativeInitTupleSource.Fixed started owner.pin
    (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519) owner.mldsa.publicKey fingerprint.state
  attached : RegistrationNativeInitTupleSource.Attached started fingerprint.state
  cached : cache ((), (RegistrationNativeInitStageContents.sourcePayload fingerprint.state).transcript) = some digest
  control : pending.control = fingerprint.state.started.state
  pin : pending.binding.server_pin = fingerprint.state.server_pin
  identity : pending.binding.beacon_identity_public_key = fingerprint.state.beacon_identity
  initHash : pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest
  fields : view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields fingerprint.state

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
  have sameMldsa : after.mldsa = before.mldsa := by
    simpa only [metadata] using congrArg (fun value : Owner source => value.mldsa) same
  refine ⟨⟨receipt.started, receipt.fingerprint, receipt.digest, receipt.view, ?_, ?_, receipt.attached,
    extension receipt.cached, receipt.control, receipt.pin, receipt.identity, receipt.initHash, receipt.fields⟩⟩
  · simpa only [sameIdentity, samePrekey, sameKem] using receipt.validated
  · simpa only [sameIdentity, samePin, sameMldsa] using receipt.fixed

/-- The literal stored source cut yields its original pending tuple in the actual whole-bundle final shared cache. -/
theorem stored (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (bytes : Pqxdh.Bytes)
    (cut : RegistrationNativePlatformBundleOwnerPhase.Stored coins setup checks representation created writer index before after previous next bytes) :
    Nonempty (Receipt setup cut.current cut.cut.published.pending cut.cut.oneTime (RegistrationNativeWorldCache.cache after)) := by
  obtain ⟨started, _pending, fingerprint, _atFingerprint, digest, view, _encodedView, _atWriter,
    _began, validated, _leading, fixed, attached, _source, cached, initHash, control, pin, identity, fields, _written⟩ :=
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
    ⟨started, fingerprint, digest, view, validated, fixed, attached, cached, control, pin, identity, initHash, fields⟩
  exact transport setup cut.cut.owner cut.current cut.cut.published.pending cut.cut.oneTime _ _ cut.metadataEq extension original

/-- Actual successful complete source execution supplies both its literal selected-owner/publication/writer cut and the stored pending tuple/cache receipt. -/
theorem bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (bytes : Pqxdh.Bytes)
    (supported : ((.ok (some bytes), after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    ∃ cut : RegistrationNativePlatformBundleOwnerPhase.Stored coins setup checks representation created writer index before after previous next bytes,
      Nonempty (Receipt setup cut.current cut.cut.published.pending cut.cut.oneTime (RegistrationNativeWorldCache.cache after)) := by
  obtain ⟨cut⟩ := RegistrationNativePlatformBundleOwnerPhase.native_bundle coins setup checks representation created writer index before after previous next bytes supported
  exact ⟨cut, stored coins setup checks representation created writer index before after previous next bytes cut⟩

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
