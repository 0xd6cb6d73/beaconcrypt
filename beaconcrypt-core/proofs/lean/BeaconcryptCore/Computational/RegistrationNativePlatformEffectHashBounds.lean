-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompiler
/-! Actual restricted source leaves distinguish shared CTX requests from native signing draws and external platform coins. Arbitrary randomized platform work contributes no shared hash call; actual signing contributes its literal hash request only. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds
open RegistrationNativePlatformEffectCompiler (Spec)
variable {n : Nat} {Platform Value E : Type}
def IsHash : (Spec n).Domain → Prop
  | .inl (.inr (.hash _)) => True
  | _ => False
instance : DecidablePred (IsHash (n := n)) := fun query => by
  rcases query with query | coin
  · cases query with
    | inl coin => simp only [IsHash]; infer_instance
    | inr query => cases query <;> simp only [IsHash] <;> infer_instance
  · simp only [IsHash]; infer_instance

private theorem external_zero (work : ProbComp Value) :
    (simulateQ (RegistrationNativePlatformEffectCompiler.publicCoin (n := n)) work).IsQueryBoundP IsHash 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp only [RegistrationNativePlatformEffectCompiler.publicCoin, isQueryBoundP_query_iff, IsHash]
  intro impossible
  exact impossible.elim

/-- Every reached randomized external platform program has zero shared CTX queries, retaining its complete coin tree. -/
theorem platform (work : StateT Platform ProbComp Value) (before : Platform) :
    ((RegistrationNativePlatformEffectCompiler.compile (n := n) work).run before).IsQueryBoundP IsHash 0 :=
  external_zero (work.run before)

private theorem native_coins_zero (work : ProbComp Value) :
    (simulateQ (RegistrationNativePlatformSigningCompiler.forward (n := n)) (PqxdhDeploymentEnvironment.coins work)).IsQueryBoundP IsHash 0 := by
  unfold PqxdhDeploymentEnvironment.coins
  rw [← QueryImpl.simulateQ_compose]
  apply (isQueryBoundP_false work 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp only [QueryImpl.apply_compose, PqxdhDeploymentEnvironment.coinFx,
    simulateQ_spec_query, RegistrationNativePlatformSigningCompiler.forward, isQueryBoundP_query_iff, IsHash]
  intro impossible
  exact impossible.elim

/-- The source signer contributes exactly its separate transcript-hash leaf; signing draws remain native coins. -/
theorem signing (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationNativePlatformSigningCompiler.State Platform) :
    ((RegistrationNativePlatformSigningCompiler.signing (n := n) source writer sign query).run before).IsQueryBoundP IsHash
      (match query with | .hash _ => 1 | .sign _ _ _ => 0) := by
  cases query with
  | hash request =>
    simp only [RegistrationNativePlatformSigningCompiler.signing, StateT.run,
      RegistrationBoundSourceCompiler.compiler, simulateQ_map, isQueryBoundP_map_iff,
      PqxdhDeploymentEnvironment.request, simulateQ_spec_query,
      RegistrationNativePlatformSigningCompiler.forward, isQueryBoundP_query_iff, IsHash]
    decide
  | sign request payload digest =>
    simp only [RegistrationNativePlatformSigningCompiler.signing, StateT.run,
      RegistrationBoundSourceCompiler.compiler, simulateQ_map, isQueryBoundP_map_iff]
    exact native_coins_zero (sign request)

/-- The actual source response encoder uses only the separate external coin branch. -/
theorem encoding
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) (before : RegistrationNativePlatformPublicationCompiler.PublicState Platform) :
    ((RegistrationNativePlatformPublicationCompiler.encoding (n := n) writer view).run before).IsQueryBoundP IsHash 0 := by
  simp only [RegistrationNativePlatformPublicationCompiler.encoding, StateT.run, isQueryBoundP_map_iff]
  exact external_zero _

private theorem pub_with {Input : Type} (head : RustM Input)
    (next : Input → OracleComp RegistrationNativePlatformPublicationCompiler.WorkSpec
      (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))))
    (cap : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound cap) :
    (RegistrationNativePlatformServerPublication.continueWith head next).IsTotalQueryBound cap := by
  cases head with
  | fail error | div => trivial
  | ok value => exact bounded value

private theorem pub_result {Input : Type} (head : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp RegistrationNativePlatformPublicationCompiler.WorkSpec
      (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))))
    (cap : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound cap) :
    (RegistrationNativePlatformServerPublication.continueResult head next).IsTotalQueryBound cap := by
  cases head with
  | fail error | div => trivial
  | ok answer => cases answer with
    | Err previous => trivial
    | Ok value => exact bounded value

private theorem pub_ready (pending : registration.ServerResponseReady) :
    (RegistrationNativePlatformServerPublication.ready RegistrationNativePlatformPublicationCompiler.encodeLift pending).IsTotalQueryBound 1 := by
  apply pub_with
  intro view
  simp only [RegistrationNativePlatformPublicationCompiler.encodeLift]
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

private theorem pub_signing (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    (RegistrationNativePlatformServerPublication.signing RegistrationNativePlatformPublicationCompiler.signLift
      RegistrationNativePlatformPublicationCompiler.encodeLift payload digest pending).IsTotalQueryBound 2 := by
  apply pub_with
  intro request
  simp only [RegistrationNativePlatformPublicationCompiler.signLift]
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun signature => pub_result _ _ 1 pub_ready⟩

private theorem pub_syntax (pending : registration.ServerResponseHash) :
    (RegistrationNativePlatformPublicationCompiler.program pending).IsTotalQueryBound 3 := by
  unfold RegistrationNativePlatformPublicationCompiler.program
  apply pub_with
  intro request
  simp only [RegistrationNativePlatformPublicationCompiler.signLift]
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun digest => pub_result _ _ 2 (pub_signing _ digest)⟩

/-- The complete actual stateful response publisher has a source-derived finite shared-hash allowance; its signer and encoder retain all native and external coin histories. -/
theorem publication (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseHash) (before : RegistrationNativePlatformPublicationCompiler.PublicState Platform) :
    ((simulateQ (RegistrationNativePlatformPublicationCompiler.target (n := n) source frame sign writer)
      (RegistrationNativePlatformPublicationCompiler.program pending)).run before).IsQueryBoundP IsHash 3 := by
  apply ((isQueryBoundP_true_iff _ _).mpr (pub_syntax pending)).simulateQ_run_of_step
  · intro query _ previous
    cases query with
    | inl query => cases query with
      | hash request => exact signing source frame sign (.hash request) previous
      | sign request payload digest =>
        have bounded := signing (n := n) source frame sign (.sign request payload digest) previous
        change (_ : OracleComp (Spec n) _).IsQueryBoundP IsHash 0 at bounded
        exact bounded.mono (by decide)
    | inr view => exact (encoding writer view previous).mono (by omega)
  · intro query impossible
    exact (impossible trivial).elim

def Bounded {S A : Type} (work : StateT S (OracleComp (Spec n)) A) (cap : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP IsHash cap
private theorem pure_bound {S A : Type} (value : A) (cap : Nat) :
    Bounded (pure value : StateT S (OracleComp (Spec n)) A) cap := fun _ => isQueryBoundP_pure _ _ _
private theorem bind_bound {S A B : Type} (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (first later : Nat)
    (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) :
    Bounded (work >>= next) (first + later) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (bounded before) (fun result _ => rest result.1 result.2)
private theorem rec_with {S Input : Type} (head : RustM Input)
    (next : Input → StateT S (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result))
    (cap : Nat) (bounded : ∀ value, Bounded (next value) cap) :
    Bounded (RegistrationNativePlatformServerRecord.continueWith head next) cap := by
  cases head with
  | fail error | div => exact pure_bound _ _
  | ok value => exact bounded value
private theorem rec_result {S Input : Type} (head : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT S (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result))
    (cap : Nat) (bounded : ∀ value, Bounded (next value) cap) :
    Bounded (RegistrationNativePlatformServerRecord.continueResult head next) cap := by
  cases head with
  | fail error | div => exact pure_bound _ _
  | ok answer => cases answer with
    | Err previous => exact pure_bound _ _
    | Ok value => exact bounded value

private theorem write_record (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerRecordWrite) :
    Bounded (n := n) (RegistrationNativePlatformServerRecord.fromWrite
      (fun request => RegistrationNativePlatformEffectCompiler.compile (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) 0 := by
  unfold RegistrationNativePlatformServerRecord.fromWrite
  apply rec_with
  intro request
  exact bind_bound _ _ 0 0 (fun previous => platform _ previous) (fun _ => pure_bound _ _)

private theorem hash_record (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerRecordCommitment) :
    Bounded (RegistrationNativePlatformCommitment.fromCommitment
      (RegistrationNativePlatformSourceHashLower.hashing (RegistrationNativePlatformEffectCompiler.effect (n := n)) erased)
      (fun request => RegistrationNativePlatformEffectCompiler.compile (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) 1 := by
  rw [RegistrationNativePlatformCommitment.normalize]
  apply bind_bound _ _ 1 0
  · intro previous
    change OracleComp.IsQueryBoundP
      (((fun (digest : CtxRomAuth.CtxDigest) => ((RustM.ok (.Some (RegistrationAuthenticationShared.digestArray digest), erased) : RegistrationNativePlatformCommitment.HashReply), previous)) <$>
        ((Spec n).query (.inl (.inr (.hash (PqxdhRefinement.absBytes pending.pending.transcript.bytes)))))) :
          OracleComp (Spec n) (RegistrationNativePlatformCommitment.HashReply × Platform)) IsHash 1
    simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsHash]
    decide
  · intro result
    exact rec_result _ _ 0 (write_record helper)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
private theorem aead_record (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerRecordAead) :
    Bounded (RegistrationNativePlatformSourceRecord.fromAeadWithHash
      (fun request => RegistrationNativePlatformEffectCompiler.compile (RegistrationNativePlatformSourceSealLower.sealing source view failure allocation request))
      (RegistrationNativePlatformSourceHashLower.hashing (RegistrationNativePlatformEffectCompiler.effect (n := n)) erased)
      (fun request => RegistrationNativePlatformEffectCompiler.compile (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) 1 := by
  apply rec_with
  intro request
  exact bind_bound _ _ 0 1 (fun previous => platform _ previous)
    (fun result => rec_result _ _ 1 (hash_record erased helper))

/-- The actual stateful first-record compiler reaches at most one shared CTX commitment request, with every allocation and source writer prefix retained. -/
theorem record (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded (RegistrationNativePlatformRecordCompiler.record (n := n) source view failure allocation erased helper initial output) 1 := by
  unfold RegistrationNativePlatformRecordCompiler.record RegistrationNativePlatformBoundPublication.record
  exact rec_result _ _ 1 (aead_record source view failure allocation erased helper)

/-- Actual first-record and response publication together have a finite source-derived shared-hash bill, including all failed allocator and writer continuations. -/
theorem publication_with_record (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded (RegistrationNativePlatformBoundCompiler.compile (n := n) source view failure allocation erased helper sign writer initial output) 4 := by
  unfold RegistrationNativePlatformBoundCompiler.compile RegistrationNativePlatformBoundCompiler.program
  rw [simulateQ_bind, simulateQ_spec_query]
  apply bind_bound _ _ 1 3
  · intro previous
    simp only [RegistrationNativePlatformBoundCompiler.target, RegistrationNativePlatformBoundCompiler.liftPlatform,
      StateT.run, isQueryBoundP_map_iff]
    exact record source view failure allocation erased helper initial output previous.2
  · intro completed
    cases completed with
    | fail error | div => exact pure_bound _ _
    | ok answer => cases answer with
      | Err previous => exact pure_bound _ _
      | Ok pending =>
        simp only [RegistrationNativePlatformServerPublication.continueResult, simulateQ_spec_query,
          RegistrationNativePlatformBoundCompiler.target]
        exact publication source (fun _ => none) sign writer pending
end BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.platform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.encoding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.publication_with_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformEffectHashBounds.publication_with_record
