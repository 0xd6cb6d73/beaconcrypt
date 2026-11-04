-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler
/-! The actual stateful first-record and response-publication compilers never install a peer. Their actual allocation, mutable hash, primitive, signature and writer effects remain in the free tree. The one installation is retained outside publication in the supplied-slot continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
variable {n : Nat} {S A B E Platform : Type}

def Allowed : (Spec n).Domain → Prop
  | .inl query => ∀ role, ¬ InstallEnv role query
  | .inr _ => True

def Quiet (work : StateT S (OracleComp (Spec n)) A) : Prop :=
  ∀ before, (work.run before).AllQueriesSatisfy Allowed

private theorem mapped {I A B : Type} {queries : OracleSpec I} (work : OracleComp queries A)
    (change : A → B) (predicate : I → Prop) (prior : work.AllQueriesSatisfy predicate) :
    (change <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind prior (fun _ => allQueriesSatisfy_pure _ _)

theorem pure_quiet (value : A) : Quiet (n := n) (pure value : StateT S (OracleComp (Spec n)) A) :=
  fun _ => allQueriesSatisfy_pure _ _

theorem bind_quiet (work : StateT S (OracleComp (Spec n)) A) (next : A → StateT S (OracleComp (Spec n)) B)
    (prior : Quiet work) (later : ∀ value, Quiet (next value)) : Quiet (work >>= next) := by
  intro before
  rw [StateT.run_bind]
  exact allQueriesSatisfy_bind (prior before) (fun result => later result.1 result.2)

theorem map_quiet (work : StateT S (OracleComp (Spec n)) A) (observe : A → B) (prior : Quiet work) : Quiet (observe <$> work) := by
  intro before
  rw [StateT.run_map]
  exact mapped _ _ _ (prior before)

theorem program_quiet {I : Type} {queries : OracleSpec I}
    (implementation : QueryImpl queries (StateT S (OracleComp (Spec n))))
    (leaf : ∀ query, Quiet (implementation query)) (work : OracleComp queries A) :
    Quiet (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_quiet value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_quiet _ _ (leaf query) ih

theorem platform_quiet (work : StateT S ProbComp A) :
    Quiet (RegistrationNativePlatformEffectCompiler.compile (n := n) work) := by
  intro before
  change (simulateQ RegistrationNativePlatformEffectCompiler.publicCoin (work.run before)).AllQueriesSatisfy Allowed
  induction work.run before using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind coin next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformEffectCompiler.publicCoin]
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨trivial, ih⟩

private theorem role_zero (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A)
    (bounded : ∀ role, work.IsQueryBoundP (InstallEnv role) 0) :
    work.AllQueriesSatisfy (fun query => ∀ role, ¬ InstallEnv role query) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff]
    have head := fun role => (isQueryBoundP_query_bind_iff _ _ _ _).mp (bounded role)
    refine ⟨fun role => (head role).1.resolve_right (by omega), ?_⟩
    intro reply
    exact ih reply (fun role => by simpa only [Nat.zero_sub, ite_self] using (head role).2 reply)

private theorem effect_quiet (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (allowed : ∀ role, ¬ InstallEnv role query) :
    Quiet (RegistrationNativePlatformEffectCompiler.effect (Platform := S) query) := by
  intro before
  simp only [RegistrationNativePlatformEffectCompiler.effect, StateT.run_lift, bind_pure_comp]
  apply mapped
  exact (allQueriesSatisfy_query_iff _ _).mpr allowed

private theorem continue_record {Input : Type} (action : RustM Input)
    (next : Input → StateT S (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result))
    (allowed : ∀ value, Quiet (next value)) :
    Quiet (RegistrationNativePlatformServerRecord.continueWith action next) := by
  cases action with
  | fail error | div => exact pure_quiet _
  | ok value => exact allowed value

private theorem result_record {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT S (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result))
    (allowed : ∀ value, Quiet (next value)) :
    Quiet (RegistrationNativePlatformServerRecord.continueResult action next) := by
  cases action with
  | fail error | div => exact pure_quiet _
  | ok result => cases result with
    | Err previous => exact pure_quiet _
    | Ok value => exact allowed value

private theorem record_write
    (write : record_effects.RecordWriteRequest → StateT S (OracleComp (Spec n)) (RustM (core.option.Option (Slice U8))))
    (allowed : ∀ request, Quiet (write request)) (pending : registration.ServerRecordWrite) :
    Quiet (RegistrationNativePlatformServerRecord.fromWrite write pending) := by
  unfold RegistrationNativePlatformServerRecord.fromWrite
  apply continue_record
  intro request
  exact bind_quiet _ _ (allowed request) (fun _ => pure_quiet _)

private theorem record_commitment
    (hash : commitment.CommitmentTranscript → StateT S (OracleComp (Spec n)) RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT S (OracleComp (Spec n)) (RustM (core.option.Option (Slice U8))))
    (hashed : ∀ transcript, Quiet (hash transcript)) (written : ∀ request, Quiet (write request))
    (pending : registration.ServerRecordCommitment) :
    Quiet (RegistrationNativePlatformCommitment.fromCommitment hash write pending) := by
  unfold RegistrationNativePlatformCommitment.fromCommitment
  apply continue_record
  intro selected
  exact bind_quiet _ _ (hashed selected.1) (fun _ => result_record _ _ (record_write write written))

private theorem record_aead
    (sealing : record_effects.AeadSealRequest → StateT S (OracleComp (Spec n)) (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT S (OracleComp (Spec n)) RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT S (OracleComp (Spec n)) (RustM (core.option.Option (Slice U8))))
    (sealed : ∀ request, Quiet (sealing request)) (hashed : ∀ transcript, Quiet (hash transcript))
    (written : ∀ request, Quiet (write request)) (pending : registration.ServerRecordAead) :
    Quiet (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash
  apply continue_record
  intro request
  exact bind_quiet _ _ (sealed request) (fun _ => result_record _ _ (record_commitment hash write hashed written))

private theorem env_forward (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A)
    (allowed : work.AllQueriesSatisfy (fun query => ∀ role, ¬ InstallEnv role query)) :
    (simulateQ RegistrationNativePlatformSigningCompiler.forward work).AllQueriesSatisfy (Allowed (n := n)) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformSigningCompiler.forward]
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨allowed.1, fun reply => ih reply (allowed.2 reply)⟩

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

theorem record (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Quiet (RegistrationNativePlatformRecordCompiler.record (n := n) source view failure allocation erased helper initial output) := by
  unfold RegistrationNativePlatformRecordCompiler.record RegistrationNativePlatformBoundPublication.record
  apply result_record
  intro pending
  apply record_aead
  · intro request
    exact platform_quiet _
  · intro transcript
    unfold RegistrationNativePlatformSourceHashLower.hashing
    exact bind_quiet _ _ (effect_quiet _ (fun _ => by simp [InstallEnv])) (fun _ => pure_quiet _)
  · intro request
    exact platform_quiet _

omit primitive in
theorem signing (query : RegistrationSigningShared.Spec.Domain) :
    Quiet (RegistrationNativePlatformSigningCompiler.signing (n := n) source (fun _ => none) sign query :
      StateT (RegistrationNativePlatformSigningCompiler.State Platform) (OracleComp (Spec n)) _) := by
  intro before
  simp only [RegistrationNativePlatformSigningCompiler.signing, StateT.run]
  apply mapped
  exact env_forward _ (role_zero _ (fun role =>
    RegistrationNativeSecretWordAtomInstallCompiler.publication_free role source (fun _ => none) sign (.inr query) before.1))

omit primitive in
theorem encoding (signedView : registration.SignedResponseView) :
    Quiet (RegistrationNativePlatformPublicationCompiler.encoding (n := n) writer signedView) := by
  intro before
  simp only [RegistrationNativePlatformPublicationCompiler.encoding, StateT.run]
  apply mapped
  exact platform_quiet (RegistrationNativePlatformSourceCompletion.encodeWith writer signedView) before.2

omit primitive in
theorem publication (response : registration.ServerResponseHash) :
    Quiet (simulateQ (RegistrationNativePlatformPublicationCompiler.target (n := n) source (fun _ => none) sign writer)
      (RegistrationNativePlatformPublicationCompiler.program response)) := by
  apply program_quiet
  intro query
  cases query with
  | inl query => exact signing source sign query
  | inr signedView => exact encoding writer signedView

theorem compile (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Quiet (RegistrationNativePlatformBoundCompiler.compile (n := n) source view failure allocation erased helper sign writer initial output) := by
  apply program_quiet
  intro query
  cases query with
  | inl request =>
    intro before
    simp only [RegistrationNativePlatformBoundCompiler.target, RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run]
    exact mapped _ _ _ (record source view failure allocation erased helper initial output before.2)
  | inr response => exact publication source sign writer response

end BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.pure_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.pure_quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.bind_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.bind_quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.map_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.map_quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.program_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.program_quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.platform_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.platform_quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.encoding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree.compile
