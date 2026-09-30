import BeaconcryptCore.Computational.PqxdhServerAuthGapDh

/-!
The actual Server build and Beacon post-root receive each make at most one commitment-hash request and therefore sample at most 64 bytes through the existing shared cache. All real KDF, AEAD, optional codec and failure effects remain in the source computation. Deterministic does not mean computationally free.
-/

open OracleComp OracleSpec
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthTailCosts
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

def registrationHash (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) : Bool :=
  PqxdhServerRegistrationPublication.leftPredicate (RawCtxSourceSeal.category .hash) query

/-- Only actual native hash requests can sample, and each retains the existing shared-cache 64-byte cap. All real KDF, sealing, writer and auxiliary callbacks remain in the same execution. -/
theorem registration_step_uniform {A : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.NativeSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState A) :
    ((PqxdhRegistrationProtocolState.registrationImpl setup.source codec.frameWrite (tailAux codec checks) query).run state).IsTotalQueryBound
      (if registrationHash query then 64 else 0) := by
  rcases query with (request | (input | (bytes | frame))) | aux
  all_goals simp only [PqxdhRegistrationProtocolState.registrationImpl, QueryImpl.apply_compose,
    RawCtxMixedOwner.sendLift, simulateQ_spec_query]
  · exact RawCtxSourceHkdf.kdf_uniform setup.source request state
  · trivial
  · rw [RawCtxMixedShared.shared_hash, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.2
  · trivial
  · cases aux <;> trivial

/-- The whole actual native builder charges every attempted commitment, retaining its complete auxiliary/cache state and all optional replies. -/
theorem registration_uniform {A α : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks)
    (work : OracleComp PqxdhServerRegistrationPublication.NativeSpec α) (qHash : Nat)
    (bounded : work.IsQueryBoundP (fun query => registrationHash query = true) qHash)
    (state : RawCtxSharedPrimitive.SharedState A) :
    ((simulateQ (PqxdhRegistrationProtocolState.registrationImpl setup.source codec.frameWrite
      (tailAux codec checks)) work).run state).IsTotalQueryBound (64 * qHash) := by
  induction work using OracleComp.inductionOn generalizing qHash state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_query_bind, StateT.run_bind]
      have tail := fun (result : PqxdhServerRegistrationPublication.NativeSpec.Range query × RawCtxSharedPrimitive.SharedState A) => ih result.1 _ (bounded.2 result.1) result.2
      apply (isTotalQueryBound_bind (registration_step_uniform setup codec checks query state) tail).mono
      by_cases present : registrationHash query = true
      · have positive : 0 < qHash := bounded.1.resolve_left (not_not.mpr present)
        simp only [present, ite_true]
        omega
      · simp only [present, Bool.false_eq_true, ite_false, Nat.zero_add, le_refl]

/-- Logging the complete actual build adds no random draw; at most one attempted native commitment costs 64 byte samples even on failed serialization. -/
theorem build_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    ((simulateQ (tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () server)).run state).IsTotalQueryBound 64 := by
  rw [IsTotalQueryBound, ← isQueryBound_map_iff (f := Prod.map id forgetAux),
    tail_native, ← IsTotalQueryBound]
  exact registration_uniform setup codec checks _ 1
    ((PqxdhServerRegistrationPublication.native_build_bounds setup.source pending root payload () server).2.1 .hash) _

set_option backward.isDefEq.respectTransparency false in
/-- The actual complete Beacon post-root tail performs at most one attempted CTX hash. Real initial/ratchet HKDF calls and optional opening retain their original effects. -/
theorem beacon_after_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (prepared : PqxdhPhase2DhMetadata.Prepared Response) (root : Std.Array Std.U8 32#usize)
    (state : RawCtxSharedPrimitive.SharedState Unit) :
    ((simulateQ (beaconNative setup codec)
      (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead prepared root)).run state).IsTotalQueryBound 64 := by
  unfold PqxdhPhase2DhRootConsumer.afterRoot PqxdhBeaconPhase2Publication.afterRoot
    PqxdhBeaconPhase2Publication.initialRun
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query,
    PqxdhBeaconPhase2Publication.nativeTailAdapter, beaconNative]
  cases found : codec.application (PqxdhPhase2DhRootConsumer.cleared prepared).response with
  | none => simp only [simulateQ_pure]; trivial
  | some raw =>
      simp only [bind_pure_comp, simulateQ_map, PqxdhBeaconPhase2Bounds.native_raw_lift,
        StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
      rw [← QueryImpl.simulateQ_compose]
      have handler : beaconNative setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeRawLift =
          RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source) := by
        funext query
        simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeRawLift,
          simulateQ_spec_query, beaconNative]
      rw [handler]
      change ((simulateQ (RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source))
        (simulateQ RawCtxSourceOpen.nativeAdapter _)).run state).IsTotalQueryBound 64
      exact RawCtxSharedPrimitive.native_uniform_bound setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source)
        0 (RawCtxSourceHkdf.kdf_uniform setup.source) _ 51 1
        (RawCtxKdfBudget.raw_bound codec.frameRead raw _) (RawCtxSourceOpen.raw_primitive_bounds codec.frameRead raw _).1 state

end BeaconcryptCore.Computational.PqxdhServerAuthTailCosts

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTailCosts.registration_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTailCosts.registration_step_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTailCosts.registration_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTailCosts.registration_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTailCosts.build_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTailCosts.build_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTailCosts.beacon_after_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTailCosts.beacon_after_uniform
