-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer

/-! Actual source first-record execution ignores erased private accounting inputs. The complete external platform state, shared cache, signing history, optional replies, allocation failures and writer failures remain in the execution. No source success or primitive correctness premise is used for this input-independence result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationNativeMldsaCountServer (localProject)
open RegistrationNativePlatformPackedState (pack)
open RegistrationNativeKemCounterIndependence (Stable pure_stable bind_stable program_stable)
variable {n : Nat} {E Platform Value Next Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem local_idempotent (before : RegistrationWorldAgreement.State n Auxiliary) :
    localProject (localProject before) = localProject before := by
  simp only [localProject, RegistrationNativeMldsaWorldView.idempotent]

private theorem packed_idempotent (before : Local n × Platform) :
    Prod.map localProject id (Prod.map localProject id before) = Prod.map localProject id before := by
  simp only [Prod.map, id_eq, local_idempotent]

private abbrev PackedStable (work : StateT (Local n) (StateT Platform ProbComp) Value) : Prop :=
  Stable (Prod.map localProject id) (pack work)

private theorem pure_packed (value : Value) :
    PackedStable (pure value : StateT (Local n) (StateT Platform ProbComp) Value) := by
  unfold PackedStable
  rw [RegistrationNativePlatformPackedState.pure_pack]
  exact pure_stable _ packed_idempotent value

private theorem bind_packed (work : StateT (Local n) (StateT Platform ProbComp) Value)
    (next : Value → StateT (Local n) (StateT Platform ProbComp) Next)
    (first : PackedStable work) (rest : ∀ value, PackedStable (next value)) : PackedStable (work >>= next) := by
  unfold PackedStable
  rw [RegistrationNativePlatformPackedState.bind_pack]
  exact bind_stable _ _ _ first rest

private theorem map_packed (observe : Value → Next) (work : StateT (Local n) (StateT Platform ProbComp) Value)
    (law : PackedStable work) : PackedStable (observe <$> work) := by
  rw [← bind_pure_comp]
  exact bind_packed work _ law (fun _ => pure_packed _)

private theorem simulate_packed {I : Type} {spec : OracleSpec I}
    (handler : QueryImpl spec (StateT (Local n) (StateT Platform ProbComp)))
    (laws : ∀ query, PackedStable (handler query)) (work : OracleComp spec Value) :
    PackedStable (simulateQ handler work) := by
  unfold PackedStable
  rw [RegistrationNativePlatformPackedState.simulate_pack]
  exact program_stable _ packed_idempotent _ laws work

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem external_packed (work : StateT Platform ProbComp Value) :
    PackedStable (StateT.lift work : StateT (Local n) (StateT Platform ProbComp) Value) := by
  intro before
  simp only [pack, StateT.run, lift_apply, map_apply, Functor.map_map, Prod.map, id_eq, local_idempotent]

private theorem native_packed (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (work : StateT (Local n) ProbComp Value) (law : Stable localProject work) :
    PackedStable (RegistrationNativePlatformServerCompletion.liftNative coins work) := by
  intro before
  have interpreted := congrArg (fun action => simulateQ coins action) (law before.1)
  simp only [simulateQ_map] at interpreted
  have same := congrArg (fun action => (fun result : (Value × Local n) × Platform =>
    (result.1.1, (result.1.2, result.2))) <$> action.run before.2) interpreted
  simpa only [pack, RegistrationNativePlatformServerCompletion.liftNative, StateT.run,
    map_apply, Functor.map_map, Prod.map, id_eq] using same

private theorem compose_stable {S Answer : Type} (first second : S → S)
    (commuting : ∀ before, first (second before) = second (first before)) (work : StateT S ProbComp Answer)
    (left : Stable first work) (right : Stable second work) :
    Stable (fun before => second (first before)) work := by
  intro before
  have initial := congrArg (fun action => Prod.map id second <$> action) (left before)
  have following := congrArg (fun action => Prod.map id first <$> action) (right (first before))
  simp only [Functor.map_map, Prod.map, id_eq] at initial following ⊢
  simp only [commuting] at following
  exact initial.trans following

private theorem raw_uniform (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) :
    Stable (RegistrationNativeKemWorldAgreement.mask (Auxiliary := Auxiliary))
      (RegistrationWorldRecords.record (n := n) setup codec query) := by
  intro before
  have law := congrArg (fun work => (fun result => (result.1,
      { before with world := ({ before.world.1 with primitive := result.2 }, before.world.2) })) <$> work)
    (RegistrationNativeKemWorldRecordUniform.primitive_input setup codec query before.world.1.primitive)
  simp only [RegistrationWorldRecords.record, StateT.run, Functor.map_map, Prod.map, id_eq,
    RegistrationNativeKemWorldAgreement.mask, RegistrationNativeKemWorldUniform.mask,
    RegistrationNativeKemWorldRecordUniform.primitiveMask] at law ⊢
  convert law using 1

private theorem raw_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) :
    Stable (localProject (n := n) (Auxiliary := Auxiliary)) (RegistrationWorldRecords.record setup codec query) := by
  exact compose_stable RegistrationServerRecordWorldSource.project RegistrationNativeKemWorldAgreement.mask (fun _ => rfl) _
    (RegistrationNativeLocalView.record_input setup codec query) (raw_uniform setup codec query)

/-- Actual native first-record primitives retain their complete operational state under the packed private accounting view. -/
theorem records (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (query : RegistrationRecordPrimitives.Spec.Domain) :
    PackedStable (RegistrationNativePlatformServerCompletion.records (n := n) coins setup codec query) := by
  apply native_packed
  exact compose_stable RegistrationServerRecordWorldSource.project RegistrationNativeKemWorldAgreement.mask (fun _ => rfl) _
    (RegistrationNativeLocalView.handler_input setup codec query)
    (RegistrationNativeKemCompletionPrimitives.record_handler_input setup codec query)

variable [primitive : AdapterSealPrimitive.Operations]

private theorem aead_packed (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitive.Nonce) (key : primitive.Key) :
    PackedStable (RegistrationNativePlatformSourceSeal.aead (n := n) coins setup codec view failure plaintext associated nonce key) := by
  have same : RegistrationNativePlatformSourceSeal.aead (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup codec view failure plaintext associated nonce key =
      (fun reply => RustM.ok (RegistrationNativePlatformSourceSeal.detached failure reply)) <$>
        RegistrationNativePlatformServerCompletion.liftNative coins
          (RegistrationWorldRecords.record setup codec (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)))) := by
    funext before
    simp only [RegistrationNativePlatformSourceSeal.aead, RegistrationNativePlatformServerCompletion.liftNative,
      StateT.run, map_apply]
    rfl
  rw [same]
  exact map_packed _ _ (native_packed coins _ (raw_native setup codec _))

private theorem seal_handler (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (query : (AdapterSealNative.Spec E).Domain) :
    PackedStable (RegistrationNativePlatformSourceSeal.handler (n := n) coins setup codec view failure allocation query) := by
  cases query with
  | reserve before capacity => exact external_packed _
  | aead plaintext associated nonce key => exact aead_packed coins setup codec view failure plaintext associated nonce key

omit primitive in
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

omit primitive in
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (update : S → S) (before : S) :
    (modify update : StateT S m Unit) before = pure ((), update before) := rfl

omit primitive in
private theorem marker_packed (request : RegistrationRecordPrimitives.Spec.Domain) :
    PackedStable (modify fun before : Local n => { before with recordRequests := before.recordRequests ++
      [RegistrationWorldAgreement.recordCall request] } : StateT (Local n) (StateT Platform ProbComp) Unit) := by
  intro before
  simp only [StateT.run, pack, modify_apply, pure_apply, map_pure, localProject,
    Prod.map, id_eq, RegistrationNativeMldsaWorldView.idempotent]

/-- Source allocation, exact AEAD dispatch and seal logging retain failures and arbitrary persistent platform state under accounting input erasure. -/
theorem sealing (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) :
    PackedStable (RegistrationNativePlatformSourceSeal.sealing (n := n) coins setup codec view failure allocation request) := by
  unfold RegistrationNativePlatformSourceSeal.sealing
  apply bind_packed _ _ (simulate_packed _ (seal_handler coins setup codec view failure allocation) _)
  intro result
  exact bind_packed _ _ (marker_packed (.seal request)) (fun _ => pure_packed result)

omit primitive in
/-- The mutable source hash callback retains its actual digest and replacement transcript under the complete accounting view. -/
theorem hash (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) :
    PackedStable (RegistrationNativePlatformSourceSeal.hash (n := n) coins setup codec erased transcript) := by
  unfold RegistrationNativePlatformSourceSeal.hash
  exact bind_packed _ _ (records coins setup codec (.hash transcript)) (fun _ => pure_packed _)

omit primitive in
/-- The actual helper AST and writer marker can inspect the external platform state while retaining native accounting independence. -/
theorem write (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest) :
    PackedStable (RegistrationNativePlatformSourceBuild.write (n := n) helper request) := by
  intro before
  simp only [pack, RegistrationNativePlatformSourceBuild.write, StateT.run,
    map_apply, Functor.map_map, Prod.map, id_eq, localProject,
    RegistrationNativeMldsaWorldView.idempotent]

omit primitive in
private theorem continueWith_packed {Input : Type} (action : RustM Input)
    (next : Input → StateT (Local n) (StateT Platform ProbComp) (RustM RegistrationServerRecordExecutor.Result))
    (law : ∀ value, PackedStable (next value)) :
    PackedStable (RegistrationNativePlatformServerRecord.continueWith action next) := by
  cases action with
  | ok value => exact law value
  | fail error | div => exact pure_packed _

omit primitive in
private theorem continueResult_packed {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT (Local n) (StateT Platform ProbComp) (RustM RegistrationServerRecordExecutor.Result))
    (law : ∀ value, PackedStable (next value)) :
    PackedStable (RegistrationNativePlatformServerRecord.continueResult action next) := by
  cases action with
  | ok result => cases result with
    | Ok value => exact law value
    | Err previous => exact pure_packed _
  | fail error | div => exact pure_packed _

omit primitive in
private theorem fromWrite_packed
    (write : record_effects.RecordWriteRequest → StateT (Local n) (StateT Platform ProbComp) (RustM (core.option.Option (Slice U8))))
    (law : ∀ request, PackedStable (write request)) (pending : registration.ServerRecordWrite) :
    PackedStable (RegistrationNativePlatformServerRecord.fromWrite write pending) := by
  unfold RegistrationNativePlatformServerRecord.fromWrite
  apply continueWith_packed
  intro request
  exact bind_packed _ _ (law request) (fun _ => pure_packed _)

omit primitive in
private theorem fromCommitment_packed
    (hash : commitment.CommitmentTranscript → StateT (Local n) (StateT Platform ProbComp) RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT (Local n) (StateT Platform ProbComp) (RustM (core.option.Option (Slice U8))))
    (hashLaw : ∀ transcript, PackedStable (hash transcript)) (writeLaw : ∀ request, PackedStable (write request))
    (pending : registration.ServerRecordCommitment) :
    PackedStable (RegistrationNativePlatformCommitment.fromCommitment hash write pending) := by
  rw [RegistrationNativePlatformCommitment.normalize]
  apply bind_packed _ _ (hashLaw _)
  intro result
  exact continueResult_packed _ _ (fromWrite_packed write writeLaw)

omit primitive in
private theorem fromAead_packed
    (sealing : record_effects.AeadSealRequest → StateT (Local n) (StateT Platform ProbComp)
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) (StateT Platform ProbComp) RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT (Local n) (StateT Platform ProbComp) (RustM (core.option.Option (Slice U8))))
    (sealLaw : ∀ request, PackedStable (sealing request))
    (hashLaw : ∀ transcript, PackedStable (hash transcript)) (writeLaw : ∀ request, PackedStable (write request))
    (pending : registration.ServerRecordAead) :
    PackedStable (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash
  apply continueWith_packed
  intro request
  apply bind_packed _ _ (sealLaw request)
  intro result
  exact continueResult_packed _ _ (fromCommitment_packed hash write hashLaw writeLaw)

omit primitive in
private theorem fromRatchet_packed
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT (Local n) (StateT Platform ProbComp)))
    (sealing : record_effects.AeadSealRequest → StateT (Local n) (StateT Platform ProbComp)
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) (StateT Platform ProbComp) RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT (Local n) (StateT Platform ProbComp) (RustM (core.option.Option (Slice U8))))
    (recordLaw : ∀ query, PackedStable (record query)) (sealLaw : ∀ request, PackedStable (sealing request))
    (hashLaw : ∀ transcript, PackedStable (hash transcript)) (writeLaw : ∀ request, PackedStable (write request))
    (pending : registration.ServerInitialSeal) :
    PackedStable (RegistrationNativePlatformSourceRecord.fromRatchetWithHash record sealing hash write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromRatchetWithHash
  apply continueWith_packed
  intro request
  apply bind_packed _ _ (recordLaw (.ratchetKdf request))
  intro result
  exact continueResult_packed _ _ (fromAead_packed sealing hash write sealLaw hashLaw writeLaw)

omit primitive in
private theorem fromInitial_packed
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT (Local n) (StateT Platform ProbComp)))
    (sealing : record_effects.AeadSealRequest → StateT (Local n) (StateT Platform ProbComp)
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) (StateT Platform ProbComp) RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT (Local n) (StateT Platform ProbComp) (RustM (core.option.Option (Slice U8))))
    (recordLaw : ∀ query, PackedStable (record query)) (sealLaw : ∀ request, PackedStable (sealing request))
    (hashLaw : ∀ transcript, PackedStable (hash transcript)) (writeLaw : ∀ request, PackedStable (write request))
    (pending : registration.ServerInitialKdf) :
    PackedStable (RegistrationNativePlatformSourceRecord.fromInitialWithHash record sealing hash write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromInitialWithHash
  apply continueWith_packed
  intro request
  apply bind_packed _ _ (recordLaw (.initialKdf request))
  intro result
  exact continueResult_packed _ _ (fromRatchet_packed record sealing hash write recordLaw sealLaw hashLaw writeLaw)

/-- The literal complete source first-record computation retains all operational native and external coordinates under private accounting erasure, including all failure and divergence branches. -/
theorem record (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) :
    Stable (Prod.map localProject id)
      (pack (RegistrationNativePlatformSourceSealTrace.record (n := n) coins setup codec view failure allocation erased helper initial)) := by
  exact fromInitial_packed _ _ _ _ (records coins setup codec)
    (sealing coins setup codec view failure allocation) (hash coins setup codec erased) (write helper) initial

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.sealing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.write

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordView.record
