-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts
import BeaconcryptCore.Computational.RegistrationBoundSourceCompiler

/-! Effect bills for the actual publication primitive compiler. Every actual raw/typed commitment and response hash reaches the existing shared CTX capability; deterministic HKDF, detached AEAD and optional frame writing add no World query. ML signing retains all supplied primitive draws and the chronological receipt even if its continuation later fails. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePublicationCosts
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open RegistrationNativePrimitiveCosts (coinCost)
variable {n : Nat}

def hashCost : EffectKind → Nat
  | .hash => 1
  | .coin | .administrative => 0

/-- One actual forwarded hash uses precisely one shared cache capability. -/
theorem hash_bound (bytes : Pqxdh.Bytes) (kind : EffectKind) :
    (PqxdhDeploymentEnvironment.request (n := n) (.hash bytes)).IsQueryBoundP
      (fun query => effectKind query = kind) (hashCost kind) := by
  apply (isQueryBoundP_query_iff (spec := EnvEffects n) (p := fun query => effectKind query = kind) (.inr (.hash bytes)) (hashCost kind)).mpr
  cases kind <;> simp [effectKind, hashCost]

/-- The complete native raw primitive compiler makes at most one shared hash, with zero coins and administrative requests. -/
theorem raw_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RegistrationRawSealBridge.Spec.Domain) (kind : EffectKind) :
    (RegistrationBoundSourceCompiler.rawCompiler (n := n) source writer query).IsQueryBoundP
      (fun query => effectKind query = kind) (hashCost kind) := by
  rcases query with request | (input | (bytes | body))
  · cases request with
    | rootKdf request | initialKdf request =>
        simp only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
          RegistrationBoundSourceCompiler.rawCallbacks, RegistrationRecordPrimitives.callbacks, simulateQ_pure]
        trivial
    | ratchetKdf request | «seal» request | openAead request =>
        simp only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
          RegistrationBoundSourceCompiler.rawCallbacks, RegistrationRecordPrimitives.callbacks,
          MldsaSharedNative.recordLift, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
          RegistrationBoundSourceCompiler.sharedCompiler, PqxdhDeploymentEnvironment.sharedFwd,
          RawCtxMixedShared.sharedAdapter, simulateQ_pure]
        trivial
    | adHash request =>
        simpa only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
          RegistrationBoundSourceCompiler.rawCallbacks, RegistrationRecordPrimitives.callbacks,
          RegistrationAuthenticationShared.callbacks, MldsaSharedNative.authLift,
          bind_pure_comp, simulateQ_map, simulateQ_spec_query, RegistrationBoundSourceCompiler.sharedCompiler,
          isQueryBoundP_map_iff] using hash_bound
            (n := n) (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) kind
    | hash transcript =>
        simpa only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
          RegistrationBoundSourceCompiler.rawCallbacks, RegistrationRecordPrimitives.callbacks,
          RegistrationAuthenticationShared.callbacks, MldsaSharedNative.authLift,
          bind_pure_comp, simulateQ_map, simulateQ_spec_query, RegistrationBoundSourceCompiler.sharedCompiler,
          isQueryBoundP_map_iff] using hash_bound
            (n := n) (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes (.Single (Std.Array.to_slice transcript.bytes))) kind
    | write request =>
        cases request <;>
          simp only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
            RegistrationBoundSourceCompiler.rawCallbacks, RegistrationRecordPrimitives.callbacks,
            MldsaSharedNative.recordLift, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
            RegistrationBoundSourceCompiler.sharedCompiler, PqxdhDeploymentEnvironment.sharedFwd,
            RawCtxMixedShared.sharedAdapter, simulateQ_pure]
        all_goals trivial
  · simp only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
      RegistrationBoundSourceCompiler.rawCallbacks, MldsaSharedNative.recordLift,
      bind_pure_comp, simulateQ_map, simulateQ_spec_query, RegistrationBoundSourceCompiler.sharedCompiler,
      PqxdhDeploymentEnvironment.sharedFwd, RawCtxMixedShared.sharedAdapter, simulateQ_pure]
    trivial
  · simpa only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
      RegistrationBoundSourceCompiler.rawCallbacks, MldsaSharedNative.authLift,
      bind_pure_comp, simulateQ_map, simulateQ_spec_query, RegistrationBoundSourceCompiler.sharedCompiler,
      isQueryBoundP_map_iff] using hash_bound (n := n) bytes kind
  · simp only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.apply_compose,
      RegistrationBoundSourceCompiler.rawCallbacks, simulateQ_pure]
    trivial

/-- Literal primitive bills distinguish hashes from signing draws instead of charging every publication request as both. -/
def bill (qSign : Nat) : RegistrationBoundPublication.Spec.Domain → EffectKind → Nat
  | .inl _, kind | .inr (.hash _), kind => hashCost kind
  | .inr (.sign _ _ _), kind => coinCost qSign kind

/-- Every publication callback satisfies its literal bill on its full original receipt state. -/
theorem compiler_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) (qSign : Nat)
    (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
    (query : RegistrationBoundPublication.Spec.Domain) (log : List RegistrationSigningShared.Receipt) (kind : EffectKind) :
    ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run log).IsQueryBoundP
      (fun query => effectKind query = kind) (bill qSign query kind) := by
  cases query with
  | inl query =>
      simpa only [RegistrationBoundSourceCompiler.compiler, StateT.run, isQueryBoundP_map_iff, bill]
        using raw_bound source writer query kind
  | inr query =>
      cases query with
      | hash request =>
          simpa only [RegistrationBoundSourceCompiler.compiler, StateT.run, isQueryBoundP_map_iff, bill]
            using hash_bound (n := n) (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) kind
      | sign request payload digest =>
          simp only [RegistrationBoundSourceCompiler.compiler, StateT.run, isQueryBoundP_map_iff, bill]
          exact RegistrationNativePrimitiveCosts.coins_bound (n := n) (sign request) qSign (signing request) kind


end BeaconcryptCore.Computational.RegistrationNativePublicationCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicationCosts.hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicationCosts.hash_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicationCosts.raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicationCosts.raw_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicationCosts.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicationCosts.compiler_bound
