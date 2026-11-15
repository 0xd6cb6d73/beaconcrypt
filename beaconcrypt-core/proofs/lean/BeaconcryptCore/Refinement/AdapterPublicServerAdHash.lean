-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCutPin
import BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
/-! The actual AD hash uses the existing global hash interpreter and its private source cut. The owned continuation consumes that actual digest before reservation; erasure drops only the auxiliary cut. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAdHash
open BeaconcryptCore.Computational
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT Platform ProbComp
local notation "NativeM" => StateT Native Base
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)

noncomputable def native (pending : registration.ServerAdHash) : NativeM RegistrationServerAdHash.Result :=
  match pending.request with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok request => do
    let digest ← AdapterPublicServerCutPin.outgoing coins sign (.hash request)
    pure (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)))

theorem hash_outgoing {Auxiliary : Type} (request : registration.HashRequest) :
    RegistrationNativePlatformServerCompletion.outgoing (n := n) (Auxiliary := Auxiliary) coins sign (.hash request) =
      RegistrationNativePlatformServerCompletion.capability coins (.hash (RegistrationInputs.hashBytes request)) := by
  funext before
  simp only [RegistrationNativePlatformServerCompletion.outgoing,
    RegistrationNativePlatformServerCompletion.capability, RegistrationNativePlatformServerCompletion.liftNative,
    RegistrationNativePlatformServerCompletion.nativeOutgoing, RegistrationWorldSigning.outgoing,
    RegistrationWorldServerCompletion.capability, StateT.run, simulateQ_map, Functor.map_map]

theorem native_source (pending : registration.ServerAdHash) :
    native (n := n) (KemSK := KemSK) (mlSource := mlSource) coins sign pending =
      RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformCompletionSdk.nativeAdHash coins pending) := by
  change native coins sign pending = AdapterPublicServerLocalLens.localState
    (RegistrationNativePlatformServerCompletion.adHash coins pending)
  unfold native RegistrationNativePlatformServerCompletion.adHash
    RegistrationNativePlatformServerCompletion.adHashWith RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div => exact (AdapterPublicServerLocalLens.local_pure _).symm
  | ok request =>
    simp only [AdapterPublicServerLocalLens.local_bind, AdapterPublicServerLocalLens.local_pure,
      bind_assoc, pure_bind]
    rw [← hash_outgoing coins sign request]
    rfl

theorem hash_run (request : registration.HashRequest) (before : Cut) :
    (AdapterPublicServerCutPin.hash coins sign request).run before =
      (fun result =>
        (RustM.ok (.Some (RegistrationAuthenticationShared.digestArray result.1)),
          (result.2, some (⟨request, result.1⟩ : RegistrationNativePlatformSigningJournal.Cut)))) <$>
        (AdapterPublicServerCutPin.outgoing coins sign (.hash request)).run before.1 := by
  unfold AdapterPublicServerCutPin.hash
  rw [StateT.run_map, RegistrationNativePlatformCutJournal.hash_run]
  simp only [Functor.map_map]

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

theorem hash_material (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before after : Native)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (request : registration.HashRequest) (digest : CtxRomAuth.CtxDigest)
    (previous next : Platform)
    (supported : ((digest, after), next) ∈ support
      (((AdapterPublicServerCutPin.outgoing coins sign (.hash request)).run before).run previous)) :
    AdapterPublicWrapperState.Server view views created credential self after.server := by
  unfold AdapterPublicServerCutPin.outgoing at supported
  rw [AdapterPublicServerLocalLens.local_run] at supported
  simp only [RegistrationNativePlatformServerCompletion.outgoing,
    StateT.run_map, support_map] at supported
  obtain ⟨inner, sampled, equal⟩ := supported
  have reached := RegistrationNativePlatformHashReceipt.native_support coins _ inner.1 previous inner.2 sampled
  change (inner.1.1, inner.1.2) ∈ support
    ((RegistrationNativePlatformServerCompletion.nativeOutgoing sign (.hash request)).run before.server.world) at reached
  simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing, StateT.run, support_map] at reached
  obtain ⟨raw, called, same⟩ := reached
  simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at called
  obtain ⟨world, hashed, worldEq⟩ := called
  have server := AdapterPublicServerAuthenticationFrame.hash_server _
    before.server.world.world.1 world.2 world.1 hashed
  have afterEq : AdapterPublicServerLocalLens.putLocal before inner.1.2 = after :=
    congrArg (fun result => result.1.2) equal
  have localEq :
      { auxiliary := before.server.world.auxiliary, requests := before.server.world.requests,
        recordRequests := before.server.world.recordRequests, world := raw.2 } = inner.1.2 :=
    congrArg Prod.snd same
  have signingEq : (world.2, before.server.world.world.2) = raw.2 :=
    congrArg Prod.snd worldEq
  rw [← afterEq, ← localEq, ← signingEq]
  exact AdapterPublicServerPrefixMaterial.related_world view views created credential self before related world.2 server

end BeaconcryptCore.Refinement.AdapterPublicServerAdHash

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAdHash.hash_outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAdHash.hash_outgoing

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAdHash.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAdHash.native_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAdHash.hash_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAdHash.hash_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAdHash.hash_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAdHash.hash_material
