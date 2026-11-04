-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
import BeaconcryptCore.Computational.RegistrationNativeBuildCosts

/-! Literal all-replies query caps for the original concrete first-record source. Fixed HKDF, AEAD and writer bodies remain their actual source interpretations. A conservative64-draw allowance per callback includes the shared-cache miss without a successful-record or signing premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServerPrimitives
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {Auxiliary ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

private theorem native_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run before).IsTotalQueryBound 64 := by
  have bounded := RawCtxMixedShared.shared_uniform source.crypto writer (RawCtxSourceHkdf.kdfImpl source)
    0 (RawCtxSourceHkdf.kdf_uniform source) (RawCtxMixedOwner.NativeSpec.query query) 1 1
    (by simp [isQueryBoundP_query_iff]) (by simp [isQueryBoundP_query_iff]) before
  simpa only [simulateQ_spec_query, Nat.zero_mul, Nat.zero_add, Nat.mul_one] using bounded

private theorem shared_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : MldsaSharedNative.Spec.Domain)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((MldsaSharedSource.implementation source writer query).run before).IsTotalQueryBound 64 := by
  cases query with
  | inl query =>
      simpa only [MldsaSharedSource.implementation, MldsaSharedNative.primitives, MldsaSharedNative.authentication,
        StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
        CtxComputationalSecurity.ctxRandomOracle_total_query_bound query before.2
  | inr query => exact native_bound source writer query before

private theorem callbacks_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : RegistrationRecordPrimitives.Spec.Domain) :
    (RegistrationRecordPrimitives.callbacks source query).IsTotalQueryBound 1 := by
  cases query with
  | write request => cases request <;>
      simp [RegistrationRecordPrimitives.callbacks, MldsaSharedNative.recordLift, IsTotalQueryBound, isQueryBound_map_iff]
  | hash transcript =>
      simp [RegistrationRecordPrimitives.callbacks, RegistrationAuthenticationShared.callbacks,
        MldsaSharedNative.authLift, IsTotalQueryBound, isQueryBound_map_iff]
  | _ => simp [RegistrationRecordPrimitives.callbacks, MldsaSharedNative.recordLift, IsTotalQueryBound, isQueryBound_map_iff]

private theorem simulated {Query State Result : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (StateT State ProbComp))
    (step : ∀ query before, ((implementation query).run before).IsTotalQueryBound 64)
    (work : OracleComp queries Result) (cap : Nat) (bounded : work.IsTotalQueryBound cap) (before : State) :
    ((simulateQ implementation work).run before).IsTotalQueryBound (cap * 64) := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply (isTotalQueryBound_bind (step query before) (fun result => ih result.1 _ (bounded.2 result.1) result.2)).mono
      have positive : 0 < cap := bounded.1
      omega

/-- Every original typed first-record callback pays at most its64-byte shared-cache miss. -/
theorem record_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationWorldRecords.handler setup codec query).run before).IsTotalQueryBound 64 := by
  have bounded : ((RegistrationRecordPrimitives.implementation setup.source codec.frameWrite query).run
      (RegistrationWorldAgreement.project before)).IsTotalQueryBound 64 := by
    simpa only [RegistrationRecordPrimitives.implementation, QueryImpl.apply_compose, Nat.one_mul] using
      simulated (MldsaSharedSource.implementation setup.source codec.frameWrite)
        (shared_bound setup.source codec.frameWrite) _ 1 (callbacks_bound setup.source query)
        (RegistrationWorldAgreement.project before)
  rw [← RegistrationWorldRecords.handler_project setup codec query before] at bounded
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bounded

private theorem record_continue {Input : Type} (action : RustM Input)
    (next : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result))
    (count : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationServerRecordExecutor.continueWith action next).IsTotalQueryBound count := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => trivial

private theorem record_result {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result))
    (count : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationServerRecordExecutor.continueResult action next).IsTotalQueryBound count := by
  cases action with
  | ok value => cases value with
    | Ok value => exact bounded value
    | Err previous => trivial
  | fail error | div => trivial

private theorem ratchet_bound (pending : registration.ServerInitialSeal) :
    (RegistrationServerRecordExecutor.fromRatchet pending).IsTotalQueryBound 4 := by
  apply record_continue
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun reply => record_result _ _ 3 RegistrationNativeBuildCosts.aead_bound⟩

private theorem initial_bound (pending : registration.ServerInitialKdf) :
    (RegistrationServerRecordExecutor.fromInitial pending).IsTotalQueryBound 5 := by
  apply record_continue
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun reply => record_result _ _ 4 ratchet_bound⟩

/-- The complete initial record has five literal callback slots, without any successful-KDF/AEAD/writer premise. -/
theorem fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (pending : registration.ServerInitialKdf) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((simulateQ (RegistrationWorldRecords.handler setup codec) (RegistrationServerRecordExecutor.fromInitial pending)).run before).IsTotalQueryBound 320 :=
  simulated (RegistrationWorldRecords.handler setup codec) (record_query setup codec) _ 5 (initial_bound pending) before
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServerPrimitives

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServerPrimitives.record_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServerPrimitives.record_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServerPrimitives.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServerPrimitives.fromInitial
