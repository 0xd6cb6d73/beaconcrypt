-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps
/-! Actual corrected callback material bills survive private root relocation and literal generated startup. Independent challenges, native local draws and external allocator coins introduce no material demand. The resulting cap is derived from original build/finish resource bounds. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedCaps
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
private theorem ordinary_free {k : Nat} {SK A : Type} (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M k SK A) (before : RegistrationNativePublicInterpreter.State k SK) :
    ((RegistrationNativePublicRetained.ordinary hmac work).run before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand 0 := by
  unfold RegistrationNativePublicRetained.ordinary
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationNativePublicRetained.coins, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]

private theorem step (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    ((RegistrationNativePlatformPublicRetained.compiler setup wire route sign query).run before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand
      (if (RegistrationNativePlatformPublicMaterialCaps.IsDemand (n := n) (KemSK := KemSK)) query then 1 else 0) := by
  cases query with
  | inl query =>
    rcases query with (message | (message | query) | query) | query
    · simp [RegistrationNativePlatformPublicRetained.compiler, RegistrationNativePublicRetained.compiler, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, RegistrationNativeRetainedService.IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand,
        RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]
    · simp [RegistrationNativePlatformPublicRetained.compiler, RegistrationNativePublicRetained.compiler, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, RegistrationNativeRetainedService.IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand,
        RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]
    · exact ordinary_free _ _ before
    · exact ordinary_free _ _ before
    · exact ordinary_free _ _ before
  | inr coin =>
      simp [RegistrationNativePlatformPublicRetained.compiler, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, RegistrationNativeRetainedService.IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand,
        isQueryBoundP_query_iff]

/-- Moving private roots into the service retains the literal actual corrected query-tree material cap. -/
theorem retained_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK)
    (count : Nat) (bounded : work.IsQueryBoundP (RegistrationNativePlatformPublicMaterialCaps.IsDemand (n := n) (KemSK := KemSK)) count) :
    (RegistrationNativePlatformPublicRetained.client setup wire route sign work before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand count := by
  unfold RegistrationNativePlatformPublicRetained.client
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using step setup wire route sign query current
  · intro query free current
    simpa only [ite_eq_right free] using step setup wire route sign query current

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)

/-- Generated startup, failed constructors and separate allocator coins add no material demand to the actual original build-plus-finish allowance. -/
theorem client_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) (previous : Platform) :
    (RegistrationNativePlatformPublicRetainedProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand (budget.cap 4 + budget.cap 5) := by
  unfold RegistrationNativePlatformPublicRetainedProfile.client
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) ?_ ?_).mono (by omega)
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro coin
    simp [RegistrationNativePublicRetained.coins, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]
  · intro initialized _reached
    cases initialized.1 with
    | none => trivial
    | some started =>
        apply retained_bound
        rw [RegistrationNativePlatformPublicRetainedProfile.observed, isQueryBoundP_map_iff]
        exact RegistrationNativePlatformPublicMaterialCaps.run_bound setup checks wire source
          (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicValue.prekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
          (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget (bounded _) (started.frontend, previous)
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedCaps.retained_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedCaps.retained_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedCaps.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedCaps.client_bound
