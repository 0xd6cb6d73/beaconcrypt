-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealLower
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceHashLower
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace
/-! The actual first-record suffix lowers its stateful source seal and writer to local/common-platform work, and its mutable commitment to the one shared public hash capability. Every failure and divergence remains in the result. The explicit source view omits separately billed native and chronological instrumentation, retaining operational World and uniform/hash/admin accounting. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRecordWorldSource (project)
open RegistrationNativePlatformServerRecord (continueWith continueResult)
variable {n : Nat} {E Auxiliary A B ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private abbrev Related (source target : StateT (RegistrationWorldAgreement.State n Auxiliary) m A) : Prop :=
  ∀ before, Prod.map id project <$> source.run before = target.run (project before)

private theorem pure_related (value : A) : Related (n := n) (Auxiliary := Auxiliary) (pure value : StateT _ m A) (pure value) := by
  intro before
  simp only [StateT.run_pure, map_pure]
  rfl

private theorem bind_related (source target : StateT (RegistrationWorldAgreement.State n Auxiliary) m A)
    (first : Related source target)
    (left right : A → StateT (RegistrationWorldAgreement.State n Auxiliary) m B)
    (next : ∀ value, Related (left value) (right value)) : Related (source >>= left) (target >>= right) := by
  intro before
  simp only [StateT.run_bind, map_bind]
  calc
    _ = ((Prod.map id project <$> source.run before) >>= fun result => (right result.1).run result.2) := by
      simp only [bind_map_left]
      apply bind_congr
      rintro ⟨value, current⟩
      exact next value current
    _ = _ := by rw [first]

private theorem continueWith_related {Input : Type} (action : RustM Input)
    (source target : Input → StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM RegistrationServerRecordExecutor.Result))
    (law : ∀ value, Related (source value) (target value)) :
    Related (continueWith action source) (continueWith action target) := by
  cases action with
  | fail error | div => exact pure_related _
  | ok value => exact law value

private theorem continueResult_related {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (source target : Input → StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM RegistrationServerRecordExecutor.Result))
    (law : ∀ value, Related (source value) (target value)) :
    Related (continueResult action source) (continueResult action target) := by
  cases action with
  | fail error | div => exact pure_related _
  | ok result => cases result with
    | Err previous => exact pure_related _
    | Ok value => exact law value

private theorem fromWrite_related
    (source target : record_effects.RecordWriteRequest → StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM (core.option.Option (Slice U8))))
    (law : ∀ request, Related (source request) (target request)) (pending : registration.ServerRecordWrite) :
    Related (RegistrationNativePlatformServerRecord.fromWrite source pending)
      (RegistrationNativePlatformServerRecord.fromWrite target pending) := by
  unfold RegistrationNativePlatformServerRecord.fromWrite
  apply continueWith_related
  intro request
  exact bind_related _ _ (law request) _ _ (fun _ => pure_related _)

private theorem fromCommitment_related
    (sourceHash targetHash : commitment.CommitmentTranscript → StateT (RegistrationWorldAgreement.State n Auxiliary) m RegistrationNativePlatformCommitment.HashReply)
    (sourceWrite targetWrite : record_effects.RecordWriteRequest → StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM (core.option.Option (Slice U8))))
    (hashLaw : ∀ transcript, Related (sourceHash transcript) (targetHash transcript))
    (writeLaw : ∀ request, Related (sourceWrite request) (targetWrite request)) (pending : registration.ServerRecordCommitment) :
    Related (RegistrationNativePlatformCommitment.fromCommitment sourceHash sourceWrite pending)
      (RegistrationNativePlatformCommitment.fromCommitment targetHash targetWrite pending) := by
  rw [RegistrationNativePlatformCommitment.normalize, RegistrationNativePlatformCommitment.normalize]
  apply bind_related _ _ (hashLaw _)
  intro reply
  exact continueResult_related _ _ _ (fromWrite_related sourceWrite targetWrite writeLaw)

private theorem fromAead_related
    (sourceSeal targetSeal : record_effects.AeadSealRequest → StateT (RegistrationWorldAgreement.State n Auxiliary) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (sourceHash targetHash : commitment.CommitmentTranscript → StateT (RegistrationWorldAgreement.State n Auxiliary) m RegistrationNativePlatformCommitment.HashReply)
    (sourceWrite targetWrite : record_effects.RecordWriteRequest → StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM (core.option.Option (Slice U8))))
    (sealLaw : ∀ request, Related (sourceSeal request) (targetSeal request))
    (hashLaw : ∀ transcript, Related (sourceHash transcript) (targetHash transcript))
    (writeLaw : ∀ request, Related (sourceWrite request) (targetWrite request)) (pending : registration.ServerRecordAead) :
    Related (RegistrationNativePlatformSourceRecord.fromAeadWithHash sourceSeal sourceHash sourceWrite pending)
      (RegistrationNativePlatformSourceRecord.fromAeadWithHash targetSeal targetHash targetWrite pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash
  apply continueWith_related
  intro request
  apply bind_related _ _ (sealLaw request)
  intro reply
  exact continueResult_related _ _ _ (fromCommitment_related sourceHash targetHash sourceWrite targetWrite hashLaw writeLaw)

private theorem write_related
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (request : record_effects.RecordWriteRequest) :
    Related (RegistrationNativePlatformSourceBuild.write (n := n) helper request)
      (StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request)) := by
  intro before
  simp only [RegistrationNativePlatformSourceBuild.write_run, StateT.run_lift, bind_pure_comp, Functor.map_map]
  rfl

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

/-- All actual source first-record sealing, mutable hashing and raw writing are the same restricted-effect/local suffix after the explicit instrumentation view, including every failed or divergent source branch. -/
theorem aead (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (pending : registration.ServerRecordAead) (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id project <$> (RegistrationNativePlatformSourceRecord.fromAeadWithHash
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
      (RegistrationNativePlatformSourceBuild.write helper) pending).run before =
      (RegistrationNativePlatformSourceRecord.fromAeadWithHash
        (fun request => StateT.lift (RegistrationNativePlatformSourceSealLower.sealing setup.source view failure allocation request))
        (RegistrationNativePlatformSourceHashLower.hashing (RegistrationNativePlatformPairedServerService.nativeEffects coins) erased)
        (fun request => StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending).run (project before) := by
  apply fromAead_related _ _ _ _ _ _
  · intro request current
    have source := RegistrationNativePlatformSourceSealLower.source coins setup codec view failure allocation request current
    simpa only [BeaconcryptCore.Refinement.AdapterSealNative.Output, alloc.vec.Vec, rust_primitives.sequence.Seq, Slice, StateT.run_lift, bind_pure_comp] using source
  · exact RegistrationNativePlatformSourceHashLower.source coins setup codec erased
  · exact write_related helper

section Bound
variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)

noncomputable def lowered (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    StateT (RegistrationServerRootCompiler.Local n) m (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationNativePlatformBoundPublication.record
    (fun request => StateT.lift (RegistrationNativePlatformSourceSealLower.sealing setup.source view failure allocation request))
    (RegistrationNativePlatformSourceHashLower.hashing (RegistrationNativePlatformPairedServerService.nativeEffects coins) erased)
    (fun request => StateT.lift (RegistrationNativePlatformSourceCompletion.writeWith helper request)) initial output

/-- A public-initial supplied-material source record lowers every actual seal/hash/raw-writer outcome without exposing a root request to the environment. -/
theorem bound (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id project <$> (RegistrationNativePlatformBoundPublication.record
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
      (RegistrationNativePlatformSourceBuild.write helper) initial output).run before =
      (lowered coins setup view failure allocation erased helper initial output).run (project before) := by
  unfold lowered RegistrationNativePlatformBoundPublication.record
  cases stage : RegistrationSeedErasure.selected (RegistrationBoundKeySchedule.restore initial)
      (RawCtxSelectedInitialConstructor.response64 (RegistrationBoundKeySchedule.zero ++ output.2))
      (RawCtxKdfRequestTable.fullResponse output.1) with
  | fail error => exact pure_related _ before
  | div => exact pure_related _ before
  | ok result => cases result with
    | Err previous => exact pure_related _ before
    | Ok pending => exact aead coins setup codec view failure allocation erased helper pending before

/-- The entire literal source first record, including its two actual private KDF calls, lowers to the public-initial material service and the same persistent platform/hash effects under the explicit accounting view. -/
theorem source (initial : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id project <$> (RegistrationNativePlatformSourceRecord.fromInitialWithHash
      (RegistrationNativePlatformServerCompletion.records coins setup codec)
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
      (RegistrationNativePlatformSourceBuild.write helper) initial).run before =
      (lowered coins setup view failure allocation erased helper (RegistrationBoundKeySchedule.publicInitial initial)
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root)).run (project before) := by
  rw [RegistrationNativePlatformPrivateKdfState.source coins setup codec
    (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
    (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
    (RegistrationNativePlatformSourceBuild.write helper) initial root role before]
  have actual := bound coins setup codec view failure allocation erased helper (RegistrationBoundKeySchedule.publicInitial initial)
    (PqxdhServerAuthKeySchedule.fromRoot setup.source root)
    (RegistrationNativePlatformPrivateKdfState.ratchetState (RegistrationNativePlatformPrivateKdfState.initialState before))
  have erased_state : project (RegistrationNativePlatformPrivateKdfState.ratchetState
      (RegistrationNativePlatformPrivateKdfState.initialState before)) = project before := rfl
  rw [erased_state] at actual
  exact actual

end Bound

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower.aead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower.aead

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower.source
