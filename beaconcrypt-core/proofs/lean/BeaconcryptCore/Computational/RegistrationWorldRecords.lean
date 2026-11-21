-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAgreement

/-! Actual first-record callbacks use the instrumented World's original fixed HKDF, AEAD and shared hash cache. Their chronological public request-kind ledger is separate from ongoing-record counters. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldRecords
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State project)
variable {n : Nat} {Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- The fixed source does not inspect the unrelated auxiliary coordinate; all native optional replies and cache effects agree. -/
theorem native_auxiliary (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2.2))) <$>
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run ((), cache) := by
  rcases query with request | (sealed | (opened | (bytes | frame)))
  · simp [RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, QueryImpl.compose,
      StateT.run, RawCtxSharedPrimitive.nativeImpl, RawCtxSourceHkdf.kdfImpl]
    rfl
  · simp only [RawCtxMixedShared.shared_sealing, map_pure]
  · simp [RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, QueryImpl.compose,
      StateT.run, RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl]
  · simp only [RawCtxMixedShared.shared_hash, bind_pure_comp, Functor.map_map]
  · simp only [RawCtxMixedShared.shared_writing, map_pure]

/-- Ordinary native record callbacks retain full World state while updating its actual primitive counters and cache. -/
noncomputable def record (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT (State n Auxiliary) ProbComp) := fun query state =>
  (fun result => (result.1, { state with world :=
    ({ state.world.1 with primitive := result.2 }, state.world.2) })) <$>
      (PqxdhRecordLiftWorld.primitives setup codec query).run state.world.1.primitive

/-- The actual instrumented native callback projects to the same source HKDF and cache. -/
theorem record_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : State n Auxiliary) :
    Prod.map id project <$> (record setup codec query).run state =
      (RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) query).run
        (project state) := by
  have same := congrArg (fun work => (fun result => (result.1, (state.auxiliary, result.2))) <$> work)
    (PqxdhRecordLiftWorld.primitives_forget setup codec query state.world.1.primitive)
  change Prod.map id project <$> (record setup codec query).run state =
    (RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) query).run
      (state.auxiliary, state.world.1.primitive.2)
  rw [native_auxiliary setup.source codec.frameWrite query state.auxiliary state.world.1.primitive.2]
  simpa only [record, project, StateT.run, Functor.map_map, Prod.map, id_eq,
    PqxdhDeploymentNative.primitives] using same

/-- Authentication-style hashing and first-record callbacks use the same one actual World cache. -/
noncomputable def shared (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl MldsaSharedNative.Spec (StateT (State n Auxiliary) ProbComp)
  | .inl query => fun state =>
      (fun result => (result.1, { state with world := (result.2, state.world.2) })) <$>
        (PqxdhRecordLiftWorld.effects (.inr (.hash query.2))).run state.world.1
  | .inr query => record setup codec query

/-- Both typed hash and ordinary native primitive branches retain the original source reply and complete private state. -/
theorem shared_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (state : State n Auxiliary) :
    Prod.map id project <$> (shared setup codec query).run state =
      (MldsaSharedSource.implementation setup.source codec.frameWrite query).run (project state) := by
  cases query with
  | inr query => exact record_project setup codec query state
  | inl query =>
    rcases query with ⟨tag, bytes⟩
    cases tag
    have same := congrArg (fun work => (fun result => (result.1, (state.auxiliary, result.2.2))) <$> work)
      (RegistrationWorldAuthentication.hash_project bytes state.world.1)
    simpa only [shared, project, RegistrationWorldAuthentication.project, StateT.run, Functor.map_map,
      Prod.map, id_eq, MldsaSharedSource.implementation, MldsaSharedNative.primitives,
      MldsaSharedNative.authentication, bind_pure_comp] using same

/-- Every actual extracted first-record callback kind is recorded before its continuation, including failure; private KDF operands remain inside the native interpretation. -/
noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RegistrationRecordPrimitives.Spec (StateT (State n Auxiliary) ProbComp) := fun query state =>
  (fun result => (result.1, { result.2 with recordRequests := state.recordRequests ++ [RegistrationWorldAgreement.recordCall query] })) <$>
    (simulateQ (shared setup codec) (RegistrationRecordPrimitives.callbacks setup.source query)).run state

/-- The chronological public marker records precisely the reached actual callback kind, including optional failure. -/
theorem handler_records (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (state : State n Auxiliary)
    (result : RegistrationRecordPrimitives.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((handler setup codec query).run state)) :
    result.2.recordRequests = state.recordRequests ++ [RegistrationWorldAgreement.recordCall query] := by
  simp only [handler, StateT.run, support_map] at supported
  obtain ⟨inner, _possible, rfl⟩ := supported
  rfl

/-- The full typed callback is the existing concrete first-record interpreter after instrumentation is forgotten. -/
theorem handler_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (state : State n Auxiliary) :
    Prod.map id project <$> (handler setup codec query).run state =
      (RegistrationRecordPrimitives.implementation setup.source codec.frameWrite query).run (project state) := by
  have same := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (shared_project setup codec) (RegistrationRecordPrimitives.callbacks setup.source query) state
  simp only [handler, project, StateT.run, Functor.map_map, Prod.map, id_eq,
    RegistrationRecordPrimitives.implementation, QueryImpl.apply_compose]
  exact same

/-- Entire native initial-record controllers retain their actual primitive replies, AD, consumed kernel and complete shared state. -/
theorem program_project {Result : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Result) (state : State n Auxiliary) :
    Prod.map id project <$> (simulateQ (handler setup codec) work).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation setup.source codec.frameWrite) work).run (project state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (handler_project setup codec) work state

end BeaconcryptCore.Computational.RegistrationWorldRecords

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRecords.native_auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRecords.native_auxiliary

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRecords.record_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRecords.record_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRecords.shared_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRecords.shared_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRecords.handler_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRecords.handler_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRecords.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRecords.program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRecords.handler_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRecords.handler_records
