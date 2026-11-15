-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames

/-! The actual source SDK build retains every earlier native hash-cache entry through pure configured pin selection, capacity checks, source first-record allocation, ML publication and peer installation. Each structural control premise is discharged by the literal source body, including failed prefixes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformSdkCache (Keeps serverCache localCache)
variable {n : Nat} {E Platform Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Pure configured pin selection retains every earlier shared-cache entry without issuing a hash query. -/
theorem pin (coins : QueryImpl unifSpec (StateT Platform ProbComp)) :
    Keeps (serverCache (n := n)) (RegistrationNativePlatformSourceBuild.pin coins) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  have native : inner.1 ∈ support ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous inner.2 called
  rw [RegistrationNativeServerPinRecompute.native_run] at native
  have unchanged := eq_of_mem_support_pure _ native
  change before.world.world.1.primitive.2 ≤ inner.1.2.primitive.2
  simpa only [unchanged] using (le_refl before.world.world.1.primitive.2)

/-- External source capacity decisions retain the complete native cache, including on failure. -/
theorem reserve (work : StateT Platform ProbComp Bool) :
    Keeps (serverCache (n := n)) (StateT.lift work) := by
  intro before previous result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  exact le_refl _

/-- Actual peer occupancy extends the same native cache through its trusted capability. -/
theorem present (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (keyId : U64) :
    Keeps (serverCache (n := n)) (RegistrationNativePlatformCompletionSdk.nativePresent coins keyId) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformCompletionSdk.nativePresent, RegistrationNativePlatformServerSdk.world,
    StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  have actual : inner.1 ∈ support ((RegistrationWorldServerCompletion.capability (.peerPresent keyId)).run before.world) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous inner.2 called
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
  obtain ⟨queried, possible, same⟩ := actual
  have cacheEq := congrArg (fun value => value.2.world.1.primitive.2) same
  change before.world.world.1.primitive.2 ≤ inner.1.2.world.1.primitive.2
  rw [← cacheEq]
  exact RegistrationWorldCache.effects_cache (.inr (.peerPresent keyId)) before.world.world.1 queried possible

private theorem local_pure (value : Value) :
    Keeps (Platform := Platform) (localCache (n := n)) (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact le_refl _

private theorem local_bind {Next : Type}
    (work : StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) Value)
    (next : Value → StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) Next)
    (first : Keeps localCache work) (rest : ∀ value, Keeps localCache (next value)) :
    Keeps localCache (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (first before previous middle called).trans
    (rest middle.1.1 middle.1.2 middle.2 result continued)

private theorem local_capability (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (query : PqxdhRecordLiftInterface.Capability n) :
    Keeps localCache (RegistrationNativePlatformServerCompletion.capability coins query) := by
  intro before previous result supported
  have actual : result.1 ∈ support ((RegistrationWorldServerCompletion.capability query).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
  obtain ⟨inner, called, same⟩ := actual
  have cacheEq := congrArg (fun value => value.2.world.1.primitive.2) same
  change before.world.1.primitive.2 ≤ result.1.2.world.1.primitive.2
  rw [← cacheEq]
  exact RegistrationWorldCache.effects_cache (.inr query) before.world.1 inner called

/-- The actual reached AD hash extends the shared cache and retains its real failure poststate. -/
theorem adHash (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (pending : registration.ServerAdHash) :
    Keeps (serverCache (n := n)) (RegistrationNativePlatformCompletionSdk.nativeAdHash coins pending) := by
  apply RegistrationNativePlatformSdkCache.world
  unfold RegistrationNativePlatformServerCompletion.adHash RegistrationNativePlatformServerCompletion.adHashWith RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div => exact local_pure _
  | ok request =>
      simp only [bind_assoc, pure_bind]
      apply local_bind _ _ (local_capability coins (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))
      intro _digest
      exact local_pure _

variable [primitive : AdapterSealPrimitive.Operations]

/-- Literal complete source SDK build extends its earlier cache for every returned result and actual external poststate. -/
theorem build (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps (serverCache (n := n))
      (RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer sign helper writer handle application) := by
  unfold RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformSourceBuild.buildSource
  apply RegistrationNativePlatformSdkCache.build _ (adHash coins) _ (pin coins) _ (reserve reservePeer) _ (present coins)
  intro control initial before previous result supported
  exact RegistrationNativePlatformSourceFrames.finish_cache coins setup codec view failure allocation erased sign helper writer
    control initial before previous result.1 result.2 supported

end BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.reserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.reserve

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.present

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.adHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache.adHash
