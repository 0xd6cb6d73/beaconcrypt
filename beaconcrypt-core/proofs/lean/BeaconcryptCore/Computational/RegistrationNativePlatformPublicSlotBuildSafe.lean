-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe
/-! The corrected public build embeds the actual moved-token Server controller and all stateful publication callbacks into the literal paired observer. This is only same-demand installation safety, including failed allocations and insertions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBuildSafe
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



/-- The literal new public build tree uses only its actual most recent material choice for installation. -/
theorem build (handle : Nat) (application : Option (Slice U8)) (before : State source Platform) :
    RegistrationNativePlatformPublicSlotKind.Safe (simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      ((executeLocal (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper implementation reservePeer handle application source)).run before)) := by
  simp only [executeLocal, RegistrationNativePlatformPublicFrontend.build, StateT.run, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have joined : (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK) ∘ₛ embedLocal) ∘ₛ buildEmbedding =
      RegistrationNativePlatformPublicSlotServerSafe.embed := by
    funext query
    cases query with
    | inl message => simp only [QueryImpl.compose, buildEmbedding, localQuery, embedLocal,
        simulateQ_spec_query, RegistrationNativePlatformPublicCoinEmbedding.embed,
        RegistrationNativePlatformPublicSlotServerSafe.embed, RegistrationNativePlatformPublicSlotEffects.demand]
    | inr query => cases query with
      | inl query => simp [QueryImpl.compose, buildEmbedding, effect, localQuery, embedLocal,
          RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePlatformPublicSlotServerSafe.embed,
          RegistrationNativePlatformPublicSlotEffects.effects, RegistrationNativePairedCompile.effects]
      | inr coin => simp [QueryImpl.compose, buildEmbedding, localCoin, embedLocal, publicCoin,
          RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect,
          RegistrationNativePublicFrontend.liftLocal, RegistrationNativePlatformPublicSlotServerSafe.embed,
          RegistrationNativePlatformPublicSlotEffects.effects, RegistrationNativePairedCompile.effects]
  rw [joined, map_eq_bind_pure_comp]
  exact RegistrationNativePlatformPublicSlotKind.bind_safe _ _
    (RegistrationNativePlatformPublicSlotServerSafe.program setup.source view failure allocation erased helper sign implementation reservePeer _ (before.1.environment.receipts,before.2))
    (fun _ => RegistrationNativePlatformPublicSlotKind.pure_safe _)
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBuildSafe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBuildSafe.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBuildSafe.build
