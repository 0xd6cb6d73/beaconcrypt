-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialCaps
/-! Syntactic demand bills are transported through the exact routed Word embeddings. Native source effects, KEM replies and public platform coins cannot manufacture a material demand. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport
open RegistrationNativeSecretWordInterpreterCaps (IsDemand)
open RegistrationNativeSecretWordFrontendCapsLocal (IsDemand)
variable {n : Nat} {KemSK Platform E A : Type}

private theorem routed_free (work : OracleComp (RegistrationNativeSecretWordKemInterface.Routed KemSK) A) :
    (simulateQ (RegistrationNativeSecretWordInterface.routedKem (n := n)) work).IsQueryBoundP
      (RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false work 0)
  intro query
  simp [RegistrationNativeSecretWordInterface.routedKem, RegistrationNativeSecretWordInterpreterCaps.IsDemand, isQueryBoundP_query_iff]

/-- Local material addresses retain their exact count under selected and unselected routed KEM embeddings. -/
theorem local_bound (selected : Bool) (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (KemSK := KemSK)) cap) :
    (simulateQ (RegistrationNativeSecretWordInterface.liftLocal selected) work).IsQueryBoundP
      (RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  rcases query with message | (message | common) | kem
  · simp [RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordInterpreterCaps.IsDemand,
      RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]
  · simp [RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordInterpreterCaps.IsDemand,
      RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]
  · simp [RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordInterpreterCaps.IsDemand,
      RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]
  · exact routed_free _

/-- The actual source local envelope's realization preserves its material-demand allowance, including every KEM and coin reply. -/
theorem base_bound (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformPublicMaterialLocal.IsLocalDemand (KemSK := KemSK)) cap) :
    (simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base candidate) work).IsQueryBoundP
      (RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  rcases query with (message | (message | common) | kem) | coin
  · simp [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordCheckedFrontend.realization,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsLocalDemand,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · simp [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordCheckedFrontend.realization,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsLocalDemand,
      isQueryBoundP_query_iff]
  · simp [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordCheckedFrontend.realization,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsLocalDemand,
      isQueryBoundP_query_iff]
  · exact routed_free _
  · simp [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordFrontend.effect,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsLocalDemand,
      isQueryBoundP_query_iff]

/-- External platform sampling retains all mutable outcomes and contributes no root-material demand. -/
theorem platform_zero (work : StateT Platform ProbComp A) (before : Platform) :
    ((RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP
      (RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false (work.run before) 0)
  intro coin
  simp [RegistrationNativeSecretWordFrontend.effect, RegistrationNativeSecretWordInterpreterCaps.IsDemand, isQueryBoundP_query_iff]

def IsBuildDemand : (RegistrationNativePlatformSecretWordBuild.Spec n).Domain → Prop
  | .inl _ => True
  | .inr _ => False
instance : DecidablePred (IsBuildDemand (n := n)) := fun query => by
  cases query <;> dsimp only [IsBuildDemand] <;> infer_instance

/-- Address evaluation forwards exactly one original demand or effect query with its original reply type, so it also reflects the bound. -/
theorem build_reflect (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (RegistrationNativePlatformSecretWordBuild.Spec n) A) (cap : Nat)
    (bounded : (simulateQ (RegistrationNativePlatformSecretWordBuild.realize candidate) work).IsQueryBoundP
      (RegistrationNativePlatformServerMaterialCaps.IsDemand (n := n)) cap) :
    work.IsQueryBoundP (IsBuildDemand (n := n)) cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => trivial
  | query_bind query next ih =>
    cases query with
    | inl message =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformSecretWordBuild.realize,
        isQueryBoundP_query_bind_iff, IsBuildDemand, RegistrationNativePlatformServerMaterialCaps.IsDemand] at bounded ⊢
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
    | inr effect =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformSecretWordBuild.realize,
        isQueryBoundP_query_bind_iff, IsBuildDemand, RegistrationNativePlatformServerMaterialCaps.IsDemand] at bounded ⊢
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

section Build
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)

/-- The literal new symbolic build derives its single demand from the exact source compiler, retaining all stateful allocation and writer failures. -/
theorem body_bound (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeSecretWordMessage.ServerState) (previous : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    (((RegistrationNativePlatformSecretWordBuild.body (n := n) source view failure allocation erased helper sign writer reserve handle application).run before).run previous).IsQueryBoundP
      (IsBuildDemand (n := n)) 1 := by
  have native := RegistrationNativePlatformServerMaterialCaps.build (n := n) source view failure allocation erased helper sign writer reserve
    handle application (before.eval RegistrationNativeSecretWordMessage.zero) previous
  rw [← RegistrationNativePlatformSecretWordBuild.body_source source view failure allocation erased helper sign writer reserve
    RegistrationNativeSecretWordMessage.zero handle application before previous, isQueryBoundP_map_iff] at native
  exact build_reflect RegistrationNativeSecretWordMessage.zero _ 1 native
end Build

/-- The source material/effect/coin embedding preserves the symbolic build's original demand budget. -/
theorem build_embedding_bound (work : OracleComp (RegistrationNativePlatformSecretWordBuild.Spec n) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (IsBuildDemand (n := n)) cap) :
    (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ
      RegistrationNativePlatformSecretWordBuild.wordEmbedding (KemSK := KemSK)) work).IsQueryBoundP
      (RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK)) cap := by
  rw [QueryImpl.simulateQ_compose]
  apply local_bound false _ _
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  rcases query with message | environment | coin
  all_goals simp [RegistrationNativePlatformSecretWordBuild.wordEmbedding,
    RegistrationNativeSecretWordInterface.demand, RegistrationNativeSecretWordInterface.effect,
    RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, IsBuildDemand, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.local_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.base_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.base_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.platform_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.platform_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.build_reflect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.build_reflect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.body_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.body_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.build_embedding_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport.build_embedding_bound
