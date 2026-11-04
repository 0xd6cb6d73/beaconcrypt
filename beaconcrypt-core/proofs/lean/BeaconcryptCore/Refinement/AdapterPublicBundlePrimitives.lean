-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation
import BeaconcryptCore.Refinement.AdapterPublicBundleNative
/-! Individual source Ed signing, key gates and private hash cuts implement the actual shared-state native bundle publication. The extracted writer remains in the same continuation and retains every platform failure. Only the private hash-cut annotation is erased. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives
open BeaconcryptCore.Computational
variable [ed : AdapterInitEdPrimitive.Operations]

def result (failure : ed.Error) (reply : RegistrationSigningShared.SignReply) : core.result.Result (alloc.vec.Vec U8) ed.Error :=
  match AdapterPublicBundleNative.vector reply with
  | none => .Err failure
  | some bytes => .Ok bytes

theorem result_borrowed (failure : ed.Error) (reply : RegistrationSigningShared.SignReply) :
    AdapterPublicInitPublication.borrowed (AdapterPublicInitPublication.resultOption (result failure reply)) = reply := by
  cases reply <;> rfl

variable {n : Nat} {I KemSK E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)

noncomputable def sign (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error) (message : Slice U8) :
    RegistrationNativePlatformExperiment.M n KemSK source m (core.result.Result (alloc.vec.Vec U8) ed.Error) := do
  let bytes := TranscriptAuthParts.absSlice message
  let signature := setup.joint.sign owner.identitySeed bytes
  let _ ← RegistrationNativePlatformFrontend.interpret
    (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
      (RegistrationNativeBeaconFrontend.logEd index bytes signature))
  pure (result failure (RegistrationAuthenticationShared.openedBytes (some (signature.toList ++ bytes))))

theorem sign_reply (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error) (message : Slice U8) :
    (fun reply => AdapterPublicInitPublication.borrowed (AdapterPublicInitPublication.resultOption reply)) <$>
      sign (n := n) coins setup checks representation created writer index owner failure message =
    RegistrationNativePlatformFrontend.interpret
      (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift (do
        let bytes := TranscriptAuthParts.absSlice message
        let signature := setup.joint.sign owner.identitySeed bytes
        RegistrationNativeBeaconFrontend.logEd index bytes signature
        pure (RegistrationAuthenticationShared.openedBytes (some (signature.toList ++ bytes))))) := by
  simp only [sign, map_bind, map_pure, result_borrowed]
  rw [RegistrationNativePlatformGenericBundle.liftLegacy_bind,
    RegistrationNativePlatformFrontend.bind_interpret _ _
      (RegistrationNativePlatformFrontend.bundle_atomic coins setup checks representation created writer) _ _
      (fun _ => by
        rw [RegistrationNativePlatformGenericBundle.liftLegacy_pure]
        exact RegistrationNativePlatformFrontend.pure_work _ _)]
  simp only [RegistrationNativePlatformGenericBundle.liftLegacy_pure, RegistrationNativePlatformFrontend.pure_interpret]

omit ed in
private theorem array_equal {length : Usize} (left right : Std.Array U8 length) (same : left.val = right.val) : left = right := by
  cases left
  cases right
  cases same
  rfl

theorem ed_method (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)
    (request : registration.Ed25519SigningRequest) :
    AdapterPublicInitPublication.edMethod (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
      (sign (n := n) coins setup checks representation created writer index owner failure) request =
    RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner (.inr request) := by
  classical
  by_cases owns : request.public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519
  · have views := congrArg (fun bytes : Std.Array U8 32#usize => bytes.val) owns.symm
    simpa only [AdapterPublicInitPublication.edMethod, RegistrationNativeBundleInterpretation.outgoing,
      RegistrationNativeBeaconFrontend.outgoing, owns, views, decide_true, ite_true] using
      sign_reply coins setup checks representation created writer index owner failure request.message
  · have views : (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519).val ≠ request.public_key.val := by
      intro same
      exact owns (array_equal _ _ same).symm
    simp only [AdapterPublicInitPublication.edMethod, RegistrationNativeBundleInterpretation.outgoing,
      RegistrationNativeBeaconFrontend.outgoing, owns, views, decide_false, Bool.false_eq_true, ite_false,
      RegistrationNativePlatformGenericBundle.liftLegacy_pure, RegistrationNativePlatformFrontend.pure_interpret]


noncomputable def signing (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) :
    QueryImpl RegistrationSigningShared.Spec (RegistrationNativePlatformExperiment.M n KemSK source m) :=
  fun query => RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner (.inl query)

theorem publication (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)
    (fallback : registration.MldsaSigningRequest → RegistrationNativePlatformExperiment.M n KemSK source m RegistrationSigningShared.SignReply)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (before : RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformBeaconPublication.begin
        (AdapterPublicBundleNative.outgoing (signing coins setup checks representation created writer index owner) fallback
          (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
          (sign coins setup checks representation created writer index owner failure))
        (fun view => RegistrationNativePlatformCutErasure.liftWorld (RegistrationNativeBundleInterpretation.encoder coins setup checks representation created writer view))
        control inputs scalar pin mldsa).run before =
      (RegistrationNativePlatformFrontend.interpret
        (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
        (RegistrationNativePlatformBeaconPublication.begin
          (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
            (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
          (RegistrationNativePlatformGenericBundle.encoder E) control inputs scalar pin mldsa)).run before.1 := by
  rw [AdapterPublicBundleNative.publication, RegistrationNativeBundleInterpretation.publication]
  have callbacks :
      (RegistrationNativePlatformCutWorld.beaconOutgoing
      (signing coins setup checks representation created writer index owner)
      (AdapterPublicInitPublication.edMethod (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
        (sign coins setup checks representation created writer index owner failure)) :
        QueryImpl RegistrationBeaconInitExecutor.Spec (RegistrationNativePlatformExperiment.M n KemSK source m)) =
      RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner := by
    funext query
    cases query with
    | inl query => rfl
    | inr request => exact ed_method (n := n) coins setup checks representation created writer index owner failure request
  rw [callbacks]


end BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives.result_borrowed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives.result_borrowed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives.sign_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives.sign_reply

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives.ed_method' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives.ed_method

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives.publication
