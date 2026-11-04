-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFree
/-! Literal zero demand and installation bills discharge materialization for every corrected nonmaterial callback, including public allocator coins and failed ongoing sends. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedOrdinary
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι}

private theorem embedded_bound (work : OracleComp (Spec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformPublicMaterialCaps.IsDemand (n := n) (KemSK := KemSK)) count) :
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed work).IsQueryBoundP
      (RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl query =>
      by_cases counted : RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK) query
      · simp only [RegistrationNativePlatformPublicCoinEmbedding.embed,
          RegistrationNativePlatformPublicMaterialLocal.IsDemand, ite_eq_left counted, isQueryBoundP_query_iff]
        intro _
        decide
      · simp only [RegistrationNativePlatformPublicCoinEmbedding.embed,
          RegistrationNativePlatformPublicMaterialLocal.IsDemand, ite_eq_right counted, isQueryBoundP_query_iff]
        intro impossible
        exact (counted impossible).elim
  | inr coin =>
      simp [RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect,
        RegistrationNativePublicFrontend.liftLocal, RegistrationNativePlatformPublicMaterialLocal.IsDemand,
        RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]

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


/-- Both fixed-seed translations preserve the entire actual ordinary callback tree. -/
theorem handler_source (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (ordinary : ¬ RegistrationNativePublicCaps.IsMaterial query) (before : State source Platform) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation query).run before)) =
      simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation query).run before) := by
  apply RegistrationNativePlatformMaterializedFree.program_free
  · apply embedded_bound
    simpa only [RegistrationNativePlatformPublicMaterialCaps.IsMaterial, ite_eq_right ordinary] using
      RegistrationNativePlatformPublicMaterialCaps.handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper implementation query before
  · intro role
    exact RegistrationNativePlatformPublicOrdinaryInstall.handler_free setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation role query ordinary before
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedOrdinary.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedOrdinary.handler_source
