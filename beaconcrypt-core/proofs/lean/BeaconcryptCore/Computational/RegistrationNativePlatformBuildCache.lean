-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames

/-! The actual source SDK build retains every earlier native hash-cache entry through repeated pin recomputation, capacity checks, source first-record allocation, ML publication and peer installation. Each structural control premise is discharged by the literal source body, including failed prefixes. -/
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

/-- The actual repeated fingerprint call retains all earlier shared-cache entries, without requiring a cached hit. -/
theorem pin (coins : QueryImpl unifSpec (StateT Platform ProbComp)) :
    Keeps (serverCache (n := n)) (RegistrationNativePlatformSourceBuild.pin coins) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  have native : inner.1 ∈ support ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous inner.2 called
  rw [RegistrationNativeServerPinRecompute.native_run, mem_support_bind_iff] at native
  obtain ⟨hashed, queried, returned⟩ := native
  simp only [support_pure, Set.mem_singleton_iff] at returned
  change before.world.world.1.primitive.2 ≤ inner.1.2.primitive.2
  rw [congrArg Prod.snd returned]
  exact RegistrationWorldCache.effects_cache (.inr (.hash (PqxdhRefinement.absBytes before.pin.public_key))) before.world.world.1 hashed queried

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
  apply RegistrationNativePlatformSdkCache.build _ (pin coins) _ (reserve reservePeer) _ (present coins)
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
