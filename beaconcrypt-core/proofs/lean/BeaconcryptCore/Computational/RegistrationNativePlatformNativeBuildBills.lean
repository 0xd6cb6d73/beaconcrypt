-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills
import BeaconcryptCore.Computational.RegistrationNativePublicationCosts
import BeaconcryptCore.Computational.RegistrationNativeBuildCosts
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills
open BeaconcryptCore.Refinement
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open RegistrationNativePlatformEffectCompiler (Spec compile effect)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_mono weighted_simulate weighted_run weighted_indicator)
variable {n : Nat} {E Platform A B S : Type}
def effectCost (kind : EffectKind) : (Spec n).Domain → Nat
  | .inl query => if effectKind query = kind then 1 else 0
  | .inr _ => 0
private def Bounded (kind : EffectKind) (work : StateT S (OracleComp (Spec n)) A) (cap : Nat) : Prop :=
  ∀ before, Weighted (effectCost kind) (work.run before) cap
private theorem map_iff {I X Y : Type} {spec : OracleSpec I}
    (cost : I → Nat) (work : OracleComp spec X) (change : X → Y) (cap : Nat) :
    Weighted cost (change <$> work) cap ↔ Weighted cost work cap :=
  isQueryBound_map_iff work change cap _ _
private theorem pure_bound (kind : EffectKind) (value : A) (cap : Nat) :
    Bounded kind (pure value : StateT S (OracleComp (Spec n)) A) cap := by
  intro before
  trivial
private theorem bind_bound (kind : EffectKind) (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (firstCap laterCap : Nat)
    (first : Bounded kind work firstCap) (later : ∀ value, Bounded kind (next value) laterCap) :
    Bounded kind (work >>= next) (firstCap + laterCap) := by
  intro before
  simp only [StateT.run_bind]
  exact weighted_bind _ _ _ firstCap laterCap (first before) (fun result => later result.1 result.2)
private theorem bind_zero (kind : EffectKind) (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (cap : Nat)
    (first : Bounded kind work 0) (later : ∀ value, Bounded kind (next value) cap) :
    Bounded kind (work >>= next) cap := by
  simpa only [Nat.zero_add] using bind_bound kind work next 0 cap first later
private theorem bind_tail_zero (kind : EffectKind) (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (cap : Nat)
    (first : Bounded kind work cap) (later : ∀ value, Bounded kind (next value) 0) :
    Bounded kind (work >>= next) cap := by
  simpa only [Nat.add_zero] using bind_bound kind work next cap 0 first later
private theorem external_zero (kind : EffectKind) (work : ProbComp A) :
    Weighted (effectCost (n := n) kind) (simulateQ RegistrationNativePlatformEffectCompiler.publicCoin work) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformEffectCompiler.publicCoin]
    rw [Weighted, isQueryBound_query_bind_iff]
    exact ⟨by simp [effectCost], fun value => ih value⟩
/-- Arbitrary public platform samplers have zero old/global effect cost; their separately derived external bill remains available. -/
theorem compile_zero (kind : EffectKind) (work : StateT Platform ProbComp A) :
    Bounded kind (compile (n := n) work) 0 := fun before => external_zero kind (work.run before)
private theorem effect_bound (kind : EffectKind) (query : (EnvEffects n).Domain) :
    Bounded kind (effect (Platform := S) query) (if effectKind query = kind then 1 else 0) := by
  intro before
  simp only [effect, StateT.run_lift, bind_pure_comp, map_iff]
  exact RegistrationNativeWeightedContext.query_bound (effectCost kind) (.inl query)
private theorem hash_bound (kind : EffectKind) (erased transcript : commitment.CommitmentTranscript) :
    Bounded kind (RegistrationNativePlatformSourceHashLower.hashing (effect (n := n) (Platform := S)) erased transcript) (hashCost kind) := by
  unfold RegistrationNativePlatformSourceHashLower.hashing
  apply bind_tail_zero kind _ _ (hashCost kind)
  · have actual := effect_bound (n := n) (S := S) kind (.inr (.hash (PqxdhRefinement.absBytes transcript.bytes)))
    cases kind <;> simpa [effectKind, hashCost] using actual
  · intro digest
    exact pure_bound kind _ 0

private theorem recordWith_bound {X : Type} (kind : EffectKind) (action : RustM X)
    (next : X → StateT S (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result))
    (cap : Nat) (bounded : ∀ value, Bounded kind (next value) cap) :
    Bounded kind (RegistrationNativePlatformServerRecord.continueWith action next) cap := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => exact pure_bound kind _ cap
private theorem recordResult_bound {X : Type} (kind : EffectKind) (action : RustM (core.result.Result X pqxdh.ServerState))
    (next : X → StateT S (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result))
    (cap : Nat) (bounded : ∀ value, Bounded kind (next value) cap) :
    Bounded kind (RegistrationNativePlatformServerRecord.continueResult action next) cap := by
  cases action with
  | ok value => cases value with
    | Ok value => exact bounded value
    | Err previous => exact pure_bound kind _ cap
  | fail error | div => exact pure_bound kind _ cap
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
private theorem fromWrite_bound (kind : EffectKind) (pending : registration.ServerRecordWrite) :
    Bounded kind (RegistrationNativePlatformServerRecord.fromWrite
      (fun request => compile (n := n) (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) 0 := by
  unfold RegistrationNativePlatformServerRecord.fromWrite
  apply recordWith_bound
  intro request
  exact bind_tail_zero kind _ _ 0 (compile_zero kind _) (fun _ => pure_bound kind _ 0)
private theorem commitment_bound (kind : EffectKind) (erased : commitment.CommitmentTranscript) (pending : registration.ServerRecordCommitment) :
    Bounded kind (RegistrationNativePlatformCommitment.fromCommitment
      (RegistrationNativePlatformSourceHashLower.hashing (effect (n := n) (Platform := Platform)) erased)
      (fun request => compile (n := n) (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) (hashCost kind) := by
  rw [RegistrationNativePlatformCommitment.normalize]
  apply bind_tail_zero kind _ _ (hashCost kind) (hash_bound kind _ _)
  intro result
  apply recordResult_bound
  intro ready
  exact fromWrite_bound helper kind ready
variable [primitive : AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
private theorem first_record_bound (kind : EffectKind) (erased : commitment.CommitmentTranscript) (pending : registration.ServerRecordAead) :
    Bounded kind (RegistrationNativePlatformSourceRecord.fromAeadWithHash
      (fun request => compile (n := n) (RegistrationNativePlatformSourceSealLower.sealing source view failure allocation request))
      (RegistrationNativePlatformSourceHashLower.hashing (effect (n := n) (Platform := Platform)) erased)
      (fun request => compile (n := n) (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) (hashCost kind) := by
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash
  apply recordWith_bound
  intro request
  apply bind_zero kind _ _ (hashCost kind) (compile_zero kind _)
  intro result
  apply recordResult_bound
  intro ready
  exact commitment_bound helper kind erased ready
/-- The literal corrected first-record client has one shared commitment hash. Its actual AEAD, allocator and writer stay in the distinct platform computation, on all RustM outcomes. -/
theorem record_bound (kind : EffectKind) (erased : commitment.CommitmentTranscript)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded kind (RegistrationNativePlatformRecordCompiler.record (n := n) source view failure allocation erased helper initial output) (hashCost kind) := by
  unfold RegistrationNativePlatformRecordCompiler.record RegistrationNativePlatformBoundPublication.record
  apply recordResult_bound
  intro pending
  exact first_record_bound helper source view failure allocation kind erased pending

omit primitive in
private theorem env_weighted (kind : EffectKind) (work : OracleComp (EnvEffects n) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => effectKind query = kind) cap) :
    Weighted (fun query => if effectKind query = kind then 1 else 0) work cap := by
  simpa only [Nat.one_mul] using weighted_indicator (fun query => effectKind query = kind) 1 work cap bounded
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (qSign : Nat) (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
omit primitive in
include signing in
private theorem signing_bound (kind : EffectKind) (query : RegistrationSigningShared.Spec.Domain) :
    Bounded kind (RegistrationNativePlatformSigningCompiler.signing (n := n) (Platform := Platform) source (fun _ => none) sign query)
      (RegistrationNativePublicationCosts.bill qSign (.inr query) kind) := by
  intro before
  simp only [RegistrationNativePlatformSigningCompiler.signing, StateT.run, map_iff]
  apply weighted_simulate (fun query => if effectKind query = kind then 1 else 0)
  · exact env_weighted kind _ _ (RegistrationNativePublicationCosts.compiler_bound source (fun _ => none) sign qSign signing (.inr query) before.1 kind)
  · intro query
    exact RegistrationNativeWeightedContext.query_bound (effectCost kind) (.inl query)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
omit primitive in
private theorem encoding_zero (kind : EffectKind) (encoded : registration.SignedResponseView) :
    Bounded kind (RegistrationNativePlatformPublicationCompiler.encoding (n := n) writer encoded) 0 := by
  intro before
  simp only [RegistrationNativePlatformPublicationCompiler.encoding, StateT.run, map_iff]
  exact external_zero kind _
omit primitive in
private theorem publication_count (response : registration.ServerResponseHash) :
    (RegistrationNativePlatformPublicationCompiler.program response).IsTotalQueryBound 3 := by
  simp only [RegistrationNativePlatformPublicationCompiler.program, RegistrationNativePlatformServerPublication.program,
    RegistrationNativePlatformServerPublication.continueWith, RegistrationNativePlatformServerPublication.continueResult,
    RegistrationNativePlatformServerPublication.signing, RegistrationNativePlatformServerPublication.ready,
    RegistrationNativePlatformPublicationCompiler.signLift, RegistrationNativePlatformPublicationCompiler.encodeLift]
  repeat' first
    | split
    | (rw [isTotalQueryBound_query_bind_iff]; refine ⟨by omega, fun value => ?_⟩)
    | trivial
omit primitive in
private theorem scaled {J V : Type} {input : OracleSpec J}
    (kind : EffectKind) (implementation : QueryImpl input (StateT S (OracleComp (Spec n))))
    (stepCap : Nat) (step : ∀ query, Bounded kind (implementation query) stepCap)
    (work : OracleComp input V) (cap : Nat) (bounded : work.IsTotalQueryBound cap) :
    Bounded kind (simulateQ implementation work) (stepCap * cap) := by
  intro before
  apply weighted_run (fun _ => stepCap) (effectCost kind) implementation work _ before
  · have weighted := weighted_indicator (fun _ => True) stepCap work cap ((isQueryBoundP_true_iff _ _).mpr bounded)
    simpa only [ite_true] using weighted
  · exact step
omit primitive in
include signing in
/-- The actual source response publication has at most three native hash/sign leaves. Its stateful packet writer contributes zero old/global effects, with all failure states retained. -/
theorem publication_bound (kind : EffectKind) (response : registration.ServerResponseHash) :
    Bounded kind (simulateQ (RegistrationNativePlatformPublicationCompiler.target (n := n) source (fun _ => none) sign writer)
      (RegistrationNativePlatformPublicationCompiler.program response))
      ((hashCost kind + coinCost qSign kind) * 3) := by
  apply scaled kind _ (hashCost kind + coinCost qSign kind) _ _ 3 (publication_count response)
  intro query
  cases query with
  | inl query =>
    intro before
    apply weighted_mono _ _ _ _ (signing_bound source sign qSign signing kind query before)
    cases query <;> simp only [RegistrationNativePublicationCosts.bill] <;> omega
  | inr encoded =>
    intro before
    exact weighted_mono _ _ 0 _ (encoding_zero writer kind encoded before) (Nat.zero_le _)
include signing in
/-- The complete corrected first-record and response client has an explicit native hash/sign bill, discharged from the literal source continuations and the primitive signing sampler cap. -/
theorem bound_publication (kind : EffectKind) (erased : commitment.CommitmentTranscript)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded kind (RegistrationNativePlatformBoundCompiler.compile (n := n) source view failure allocation erased helper sign writer initial output)
      (hashCost kind + (hashCost kind + coinCost qSign kind) * 3) := by
  have record : Bounded kind (RegistrationNativePlatformBoundCompiler.target (n := n) source view failure allocation erased helper sign writer initial output (.inl ())) (hashCost kind) := by
    intro before
    simp only [RegistrationNativePlatformBoundCompiler.target, RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run, map_iff]
    exact record_bound helper source view failure allocation kind erased initial output before.2
  unfold RegistrationNativePlatformBoundCompiler.compile RegistrationNativePlatformBoundCompiler.program
  simp only [simulateQ_bind, simulateQ_spec_query]
  apply bind_bound kind _ _ (hashCost kind) ((hashCost kind + coinCost qSign kind) * 3) record
  intro completed
  cases completed with
  | fail error | div => exact pure_bound kind _ _
  | ok value => cases value with
    | Err previous => exact pure_bound kind _ _
    | Ok response =>
      simpa only [RegistrationNativePlatformServerPublication.continueResult, simulateQ_spec_query,
        RegistrationNativePlatformBoundCompiler.target] using publication_bound source sign qSign signing writer kind response
end BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills.compile_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills.compile_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills.record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills.record_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills.publication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills.publication_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills.bound_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills.bound_publication
