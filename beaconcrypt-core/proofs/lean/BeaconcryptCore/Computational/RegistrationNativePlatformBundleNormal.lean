-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
import BeaconcryptCore.Refinement.RegistrationSigning
import BeaconcryptCore.Refinement.AdapterPublicBundlePublication
import BeaconcryptCore.Computational.RegistrationNativeBundleLifetime
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Outgoing source publication returns normally from total primitive reply types and the individual writer's normal-return contract. Reservation rejection remains an ordinary business result, with its complete reached state. No complete bundle or SDK execution law is assumed. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal
open RegistrationNativePlatformBeaconPublication
open BeaconcryptCore.Refinement
variable {S Platform Encoded : Type}
def Normal {A : Type} (work : StateT S (StateT Platform ProbComp) (RustM A)) : Prop :=
  ∀before previous result,result∈support ((work.run before).run previous) →∃value,result.1.1=.ok value
variable (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S (StateT Platform ProbComp)))
variable (encode : registration.SignedInitView →StateT S (StateT Platform ProbComp) (RustM (core.option.Option Encoded)))
variable (encoded : ∀view,Normal (encode view))
include encoded in
theorem ready (pending : registration.BeaconInitReady) : Normal (RegistrationNativePlatformBeaconPublication.ready encode pending) := by
  obtain ⟨view,message⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_message_total pending
  intro before previous result reached
  simp only [RegistrationNativePlatformBeaconPublication.ready,continueWith,message,
    StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨written,called,finished⟩ := reached
  obtain ⟨optional,normal⟩ := encoded view before previous written called
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at finished
  subst result
  rw [normal]
  cases optional <;> exact ⟨_,rfl⟩
include encoded in
theorem signing (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) : Normal (fromSigning impl encode payload digest pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconMldsaSigning_request_total pending
  intro before previous result reached
  simp only [fromSigning,continueWith,requested,StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨replied,called,continued⟩ := reached
  cases signatureEq : replied.1.1 with
  | none=>
      simp only [signatureEq,registration.BeaconMldsaSigning.resume,StateT.run_pure,
        support_pure,Set.mem_singleton_iff] at continued
      exact ⟨_,congrArg (fun value=>value.1.1) continued⟩
  | some signature=>
      obtain ⟨effect,resumed,progress⟩ := RegistrationSigningContinuations.beacon_mldsa_signature_exact pending signature
      rw [signatureEq,resumed] at continued
      cases effect with
      | Rejected previous=>
          simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at continued
          exact ⟨_,congrArg (fun value=>value.1.1) continued⟩
      | Ready selected=>exact ready encode encoded selected replied.1.2 replied.2 result continued
      | Ed25519SigningRequested next | FingerprintRequested next | HashRequested next | MldsaSigningRequested next=>exact progress.elim
include encoded in
theorem hash (pending : registration.BeaconInitHash) : Normal (fromHash impl encode pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitHash_request_total pending
  intro before previous result reached
  simp only [fromHash,continueWith,requested,StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨replied,called,continued⟩ := reached
  obtain ⟨next,resumed,_⟩ := RegistrationSigningContinuations.beacon_init_hash_some_exact pending (RegistrationAuthenticationShared.digestArray replied.1.1)
  rw [resumed] at continued
  exact signing impl encode encoded _ _ next replied.1.2 replied.2 result continued
include encoded in
theorem fingerprint (pending : registration.BeaconFingerprint) : Normal (fromFingerprint impl encode pending) := by
  obtain ⟨request,requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconFingerprint_request_total pending
  intro before previous result reached
  simp only [fromFingerprint,continueWith,requested,StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨replied,called,continued⟩ := reached
  obtain ⟨next,resumed,_⟩ := RegistrationSigningContinuations.beacon_fingerprint_some_exact pending (RegistrationAuthenticationShared.digestArray replied.1.1)
  rw [resumed] at continued
  exact hash impl encode encoded next replied.1.2 replied.2 result continued
include encoded in
theorem ed (pending : registration.BeaconEd25519Signing) : Normal (fromEd impl encode pending) := by
  obtain ⟨request,requested,_⟩ := RegistrationSigning.ed_request_exact pending
  intro before previous result reached
  rw [fromEd.eq_def] at reached
  simp only [continueWith,requested,StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨replied,called,continued⟩ := reached
  obtain ⟨effect,resumed,progress⟩ := RegistrationSigning.ed_resume_refines pending replied.1.1
  rw [resumed] at continued
  cases effect with
  | Rejected previous=>
      simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at continued
      exact ⟨_,congrArg (fun value=>value.1.1) continued⟩
  | Ed25519SigningRequested next=>
      exact ed next replied.1.2 replied.2 result continued
  | FingerprintRequested next=>exact fingerprint impl encode encoded next replied.1.2 replied.2 result continued
  | HashRequested next | MldsaSigningRequested next | Ready next=>exact progress.elim
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending replied.1.1 next resumed
include encoded in
theorem begin (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Normal (RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin mldsa) := by
  obtain ⟨started,_started,begun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
  intro before previous result reached
  simp only [RegistrationNativePlatformBeaconPublication.begin,continueWith,begun] at reached
  split_ifs at reached
  · simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at reached
    exact ⟨_,congrArg (fun value=>value.1.1) reached⟩
  · exact ed impl encode encoded _ before previous result reached
variable {n : Nat} {I KemSK E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (reserve : Usize →StateT Platform ProbComp (core.result.Result Unit E))
theorem encoder (view : registration.SignedInitView) :
    Normal (RegistrationNativeBundleInterpretation.encoder (n:=n) (source:=source) coins setup checks representation created
      (RegistrationNativePlatformConcreteSource.writer reserve) view) := by
  intro before previous result reached
  rw [RegistrationNativeBundleInterpretation.encoder_source,RegistrationNativePlatformConcreteSource.init_writer] at reached
  simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,Functor.map_map,support_map] at reached
  obtain ⟨allocation,called,same⟩ := reached
  subst result
  exact ⟨_,rfl⟩
theorem tree (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    Normal (RegistrationNativeBundleLifetime.tree (n:=n) coins setup checks representation created
      (RegistrationNativePlatformConcreteSource.writer reserve) index owner scalar) := by
  rw [RegistrationNativeBundleLifetime.tree_lower]
  exact begin _ _ (encoder coins setup checks representation created reserve) _ _ _ _ _
theorem fresh (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : ((PqxdhJointGapDh.ScalarBytes ×RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) ×RegistrationNativeExperiment.State n KemSK source) ×Platform)
    (reached : result∈support (((RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created
      (RegistrationNativePlatformConcreteSource.writer reserve) index owner).run before).run previous)) :
    ∃value,result.1.1.2=.ok value := by
  simp only [RegistrationNativeBundleLifetime.fresh_tree,StateT.run_bind,
    bind_pure_comp,mem_support_bind_iff,StateT.run_map,support_map] at reached
  obtain ⟨sampled,drawn,published,called,same⟩ := reached
  subst result
  exact tree coins setup checks representation created reserve index owner sampled.1.1 sampled.1.2 sampled.2 published called
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]
omit platform in
theorem publication_install {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (rng : R) (publication : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)))
    (normal : ∃value,publication=.ok value) :
    ∃returned,AdapterPublicBundlePublication.install self prekey oneTime kem rng publication=.ok returned := by
  obtain ⟨value,rfl⟩ := normal
  cases value <;> exact ⟨_,rfl⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.ready

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.fingerprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.ed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.begin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.encoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.encoder

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.tree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.publication_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal.publication_install
