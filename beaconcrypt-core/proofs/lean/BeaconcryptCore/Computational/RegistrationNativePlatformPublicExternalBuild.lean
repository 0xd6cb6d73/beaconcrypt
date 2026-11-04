-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild
open BeaconcryptCore.Refinement
open RegistrationNativePlatformEffectCompiler (Spec compile effect)
variable {n : Nat} {E Platform A B S I : Type} {input : OracleSpec I}
def IsExternal : (Spec n).Domain → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred (IsExternal (n := n)) := fun query => by
  cases query <;> dsimp [IsExternal] <;> infer_instance
private theorem total_map_iff {J X Y : Type} {queries : OracleSpec J}
    (work : OracleComp queries X) (change : X → Y) (cap : Nat) :
    (change <$> work).IsTotalQueryBound cap ↔ work.IsTotalQueryBound cap :=
  isQueryBound_map_iff work change cap _ _
private def Bounded (work : StateT S (OracleComp (Spec n)) A) (cap : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP IsExternal cap
private theorem pure_bound (value : A) (cap : Nat) :
    Bounded (pure value : StateT S (OracleComp (Spec n)) A) cap := by
  intro before
  trivial
private theorem bind_bound (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (firstCap laterCap : Nat)
    (first : Bounded work firstCap) (later : ∀ value, Bounded (next value) laterCap) :
    Bounded (work >>= next) (firstCap + laterCap) := by
  intro before
  simp only [StateT.run_bind]
  exact isQueryBoundP_bind (first before) (fun result _ => later result.1 result.2)
private theorem bind_zero (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (cap : Nat)
    (first : Bounded work 0) (later : ∀ value, Bounded (next value) cap) :
    Bounded (work >>= next) cap := by
  simpa only [Nat.zero_add] using bind_bound work next 0 cap first later
private theorem bind_tail_zero (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (cap : Nat)
    (first : Bounded work cap) (later : ∀ value, Bounded (next value) 0) :
    Bounded (work >>= next) cap := by
  simpa only [Nat.add_zero] using bind_bound work next cap 0 first later
/-- A finite source request count multiplies only its individual reached primitive allowance; no whole-controller cap is a premise. -/
theorem simulate_scaled {J V : Type} {output : OracleSpec J}
    (counted : J → Prop) [DecidablePred counted]
    (implementation : QueryImpl input (StateT S (OracleComp output)))
    (stepCap : Nat) (step : ∀ query before, ((implementation query).run before).IsQueryBoundP counted stepCap)
    (work : OracleComp input V) (cap : Nat) (bounded : work.IsTotalQueryBound cap) (before : S) :
    ((simulateQ implementation work).run before).IsQueryBoundP counted (cap * stepCap) := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply (isQueryBoundP_bind (step query before) (fun result _ => ih result.1 _ (bounded.2 result.1) result.2)).mono
    rw [Nat.sub_one_mul, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left stepCap bounded.1)]
/-- Reification of one P primitive uses its actual supplied coin allowance. -/
theorem compile_bound (work : StateT Platform ProbComp A) (cap : Nat)
    (bounded : ∀ before, (work.run before).IsTotalQueryBound cap) : Bounded (compile (n := n) work) cap := by
  intro before
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ _ cap ((isQueryBoundP_true_iff _ _).mpr (bounded before))
  intro query
  simp [RegistrationNativePlatformEffectCompiler.publicCoin, IsExternal, isQueryBoundP_query_iff]
private theorem effect_zero (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Bounded (effect (Platform := S) query) 0 := by
  intro before
  simp [effect, StateT.run_lift, IsExternal, isQueryBoundP_query_iff]
private theorem native_zero (implementation : QueryImpl input (StateT S (OracleComp (Spec n))))
    (step : ∀ query, Bounded (implementation query) 0) (work : OracleComp input A) :
    Bounded (simulateQ implementation work) 0 := by
  intro before
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible
    exact impossible.elim
  · intro query _ current
    exact step query current

variable [primitive : AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E))
variable (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (byteCap packetCap : Nat)
variable (bytesBound : ∀ amount before, ((reserveBytes amount).run before).IsTotalQueryBound byteCap)
variable (packetsBound : ∀ amount before, ((reservePackets amount).run before).IsTotalQueryBound packetCap)
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
omit primitive in
include bytesBound in
/-- The actual three-chunk source helper uses at most two request leaves, each discharged from its capacity-only reservation or pure serializer. -/
theorem write_bound (request : record_effects.RecordWriteRequest) (before : Platform) :
    ((RegistrationNativePlatformSourceCompletion.writeWith helper request).run before).IsTotalQueryBound (2 * byteCap) := by
  unfold RegistrationNativePlatformSourceCompletion.writeWith
  simp only [StateT.run_map, total_map_iff]
  apply (isQueryBoundP_true_iff _ _).mp
  exact simulate_scaled (fun _ => True) helper byteCap
    (fun query current => (isQueryBoundP_true_iff _ _).mpr
      (RegistrationNativePlatformPublicExternalWriters.helper_bound reserveBytes byteCap bytesBound query current))
    _ 2 (RegistrationNativePlatformPublicHelperCounts.route request) before

include bytesBound in
/-- Functional native AEAD is pure in this public layer; the only P sampler inside sealing is its concrete capacity-only allocator. The factor two is the conservative source syntax bound. -/
theorem seal_bound (request : record_effects.AeadSealRequest) (before : Platform) :
    ((RegistrationNativePlatformSourceSealLower.sealing source view failure allocation request).run before).IsTotalQueryBound (2 * byteCap) := by
  unfold RegistrationNativePlatformSourceSealLower.sealing
  rw [← AdapterSealNative.source_native]
  unfold AdapterSealNative.source
  rw [← QueryImpl.simulateQ_compose]
  apply (isQueryBoundP_true_iff _ _).mp
  apply simulate_scaled (fun _ => True) _ byteCap _ _ 2
    (RegistrationNativePlatformPublicHelperCounts.Seal.source request) before
  intro query current
  cases query with
  | reserve original capacity =>
    simpa only [QueryImpl.apply_compose, AdapterSealNative.native, simulateQ_spec_query,
      RegistrationNativePlatformSourceSealLower.handler, RegistrationNativePlatformSourceSeal.reserve,
      RegistrationNativePlatformConcreteSource.rawAllocation, StateT.run_map, Functor.map_map,
      isQueryBoundP_map_iff, isQueryBoundP_true_iff, total_map_iff] using bytesBound capacity.val current
  | aead plaintext associated nonce key =>
    simp only [QueryImpl.apply_compose, AdapterSealNative.native, simulateQ_map, simulateQ_spec_query,
      RegistrationNativePlatformSourceSealLower.handler, StateT.run_pure, map_pure]
    trivial

omit primitive in
private theorem recordWith_bound {X : Type} (action : RustM X)
    (next : X → StateT S (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result))
    (cap : Nat) (bounded : ∀ value, Bounded (next value) cap) :
    Bounded (RegistrationNativePlatformServerRecord.continueWith action next) cap := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => exact pure_bound _ cap
omit primitive in
private theorem recordResult_bound {X : Type} (action : RustM (core.result.Result X pqxdh.ServerState))
    (next : X → StateT S (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result))
    (cap : Nat) (bounded : ∀ value, Bounded (next value) cap) :
    Bounded (RegistrationNativePlatformServerRecord.continueResult action next) cap := by
  cases action with
  | ok value => cases value with
    | Ok value => exact bounded value
    | Err previous => exact pure_bound _ cap
  | fail error | div => exact pure_bound _ cap
omit primitive in
include bytesBound in
private theorem fromWrite_bound (pending : registration.ServerRecordWrite) :
    Bounded (RegistrationNativePlatformServerRecord.fromWrite
      (fun request => compile (n := n) (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) (2 * byteCap) := by
  unfold RegistrationNativePlatformServerRecord.fromWrite
  apply recordWith_bound
  intro request
  exact bind_tail_zero _ _ (2 * byteCap)
    (compile_bound _ _ (write_bound reserveBytes byteCap bytesBound request)) (fun _ => pure_bound _ 0)
omit primitive in
private theorem hash_zero (erased transcript : commitment.CommitmentTranscript) :
    Bounded (RegistrationNativePlatformSourceHashLower.hashing (effect (n := n) (Platform := S)) erased transcript) 0 := by
  unfold RegistrationNativePlatformSourceHashLower.hashing
  exact bind_tail_zero _ _ 0 (effect_zero _) (fun _ => pure_bound _ 0)
omit primitive in
include bytesBound in
private theorem commitment_bound (erased : commitment.CommitmentTranscript) (pending : registration.ServerRecordCommitment) :
    Bounded (RegistrationNativePlatformCommitment.fromCommitment
      (RegistrationNativePlatformSourceHashLower.hashing (effect (n := n) (Platform := Platform)) erased)
      (fun request => compile (n := n) (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) (2 * byteCap) := by
  rw [RegistrationNativePlatformCommitment.normalize]
  apply bind_zero _ _ (2 * byteCap) (hash_zero _ _)
  intro result
  apply recordResult_bound
  intro ready
  exact fromWrite_bound reserveBytes byteCap bytesBound ready
include bytesBound in
private theorem first_record_bound (erased : commitment.CommitmentTranscript) (pending : registration.ServerRecordAead) :
    Bounded (RegistrationNativePlatformSourceRecord.fromAeadWithHash
      (fun request => compile (n := n) (RegistrationNativePlatformSourceSealLower.sealing source view failure allocation request))
      (RegistrationNativePlatformSourceHashLower.hashing (effect (n := n) (Platform := Platform)) erased)
      (fun request => compile (n := n) (RegistrationNativePlatformSourceCompletion.writeWith helper request)) pending) (4 * byteCap) := by
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash
  apply recordWith_bound
  intro request
  have sum : 2 * byteCap + 2 * byteCap = 4 * byteCap := by omega
  rw [← sum]
  apply bind_bound _ _ (2 * byteCap) (2 * byteCap)
    (compile_bound _ _ (seal_bound source view failure reserveBytes byteCap bytesBound request))
  intro result
  apply recordResult_bound
  intro ready
  exact commitment_bound reserveBytes byteCap bytesBound erased ready
include bytesBound in
/-- The literal corrected first-record compiler has an explicit conservative external bill, four capacity-sampler allowances. Native commitment hashing and functional AEAD remain separate. -/
theorem record_bound (erased : commitment.CommitmentTranscript)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded (RegistrationNativePlatformRecordCompiler.record (n := n) source view failure allocation erased helper initial output) (4 * byteCap) := by
  unfold RegistrationNativePlatformRecordCompiler.record RegistrationNativePlatformBoundPublication.record
  apply recordResult_bound
  intro pending
  exact first_record_bound source view failure reserveBytes byteCap bytesBound erased pending

omit primitive in
include packetsBound in
private theorem encodeP_bound (encoded : registration.SignedResponseView) (before : Platform) :
    ((RegistrationNativePlatformSourceCompletion.encodeWith writer encoded).run before).IsTotalQueryBound packetCap := by
  unfold RegistrationNativePlatformSourceCompletion.encodeWith
  by_cases admitted : RegistrationSerializerResponseBytes.totalLength (RegistrationNativeSourceEncoders.responseSyntax encoded) ≤ CborSizing.maxMessageSize
  · obtain ⟨capacity, _sized, exactSource⟩ := RegistrationNativePlatformConcreteSource.response_writer reservePackets encoded admitted
    rw [exactSource]
    simpa only [StateT.run_map, total_map_iff] using packetsBound capacity before
  · rw [RegistrationNativePlatformConcreteSource.response_rejected reservePackets encoded (Nat.lt_of_not_ge admitted)]
    trivial
omit primitive in
include packetsBound in
private theorem encoding_bound (encoded : registration.SignedResponseView) :
    Bounded (RegistrationNativePlatformPublicationCompiler.encoding (n := n) writer encoded) packetCap := by
  intro before
  simp only [RegistrationNativePlatformPublicationCompiler.encoding, StateT.run, isQueryBoundP_map_iff]
  exact compile_bound _ packetCap (encodeP_bound reservePackets packetCap packetsBound encoded) before.2
omit primitive in
private theorem signing_zero (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) :
    Bounded (RegistrationNativePlatformSigningCompiler.signing (n := n) (Platform := Platform) source (fun _ => none) sign query) 0 := by
  intro before
  simp only [RegistrationNativePlatformSigningCompiler.signing, StateT.run, isQueryBoundP_map_iff]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro effect
  simp [RegistrationNativePlatformSigningCompiler.forward, IsExternal, isQueryBoundP_query_iff]
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
include packetsBound in
/-- Actual response publication has at most three literal leaves; only source packet reservation can use external coins. Native ML signing/hash draws keep their separate bill. -/
theorem publication_bound (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (response : registration.ServerResponseHash) :
    Bounded (simulateQ (RegistrationNativePlatformPublicationCompiler.target (n := n) source (fun _ => none) sign writer)
      (RegistrationNativePlatformPublicationCompiler.program response)) (3 * packetCap) := by
  intro before
  apply simulate_scaled IsExternal _ packetCap _ _ 3 (publication_count response) before
  intro query current
  cases query with
  | inl query => exact (signing_zero source sign query current).mono (Nat.zero_le packetCap)
  | inr encoded => exact encoding_bound reservePackets packetCap packetsBound encoded current

include bytesBound packetsBound in
/-- The actual source first-record and response-publication client retains its explicit byte/packet sampler allowances on every continuation. -/
theorem bound_publication (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (erased : commitment.CommitmentTranscript) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded (RegistrationNativePlatformBoundCompiler.compile (n := n) source view failure allocation erased helper sign writer initial output)
      (4 * byteCap + 3 * packetCap) := by
  have record : Bounded (RegistrationNativePlatformBoundCompiler.target (n := n) source view failure allocation erased helper sign writer initial output (.inl ())) (4 * byteCap) := by
    intro before
    simp only [RegistrationNativePlatformBoundCompiler.target, RegistrationNativePlatformBoundCompiler.liftPlatform,
      StateT.run, isQueryBoundP_map_iff]
    exact record_bound source view failure reserveBytes byteCap bytesBound erased initial output before.2
  unfold RegistrationNativePlatformBoundCompiler.compile RegistrationNativePlatformBoundCompiler.program
  simp only [simulateQ_bind, simulateQ_spec_query]
  apply bind_bound _ _ (4 * byteCap) (3 * packetCap) record
  intro completed
  cases completed with
  | fail error | div => exact pure_bound _ _
  | ok value => cases value with
    | Err previous => exact pure_bound _ _
    | Ok response =>
        simpa only [RegistrationNativePlatformServerPublication.continueResult, simulateQ_spec_query,
          RegistrationNativePlatformBoundCompiler.target] using publication_bound source reservePackets packetCap packetsBound sign response
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.simulate_scaled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.simulate_scaled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.compile_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.write_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.write_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.seal_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.record_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.publication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.publication_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.bound_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild.bound_publication
