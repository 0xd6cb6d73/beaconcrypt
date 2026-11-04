-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
/-! Source sealing retains its exact allocation/AEAD request tree and common platform poststate. The AEAD leaf routes through the full Local native primitive lens; no CTX query is hidden inside a closed sampler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformCtxBackend (Spec)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork publicWork)
open RegistrationNativePlatformCtxLocal (realize attach)
open RegistrationNativePlatformCtxCacheFrame (replace)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Reader Response Auxiliary Platform E A : Type} {base : OracleSpec I}

noncomputable def aead (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitive.Nonce) (key : primitive.Key) :
    StateT (State n Auxiliary) (OracleComp Spec) AdapterSealNative.NativeReply := fun before =>
  (fun result => (.ok (RegistrationNativePlatformSourceSeal.detached failure result.1), result.2)) <$>
    (RegistrationNativePlatformCtxLocal.record setup codec
      (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)))).run before

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) :
    QueryImpl (AdapterSealNative.Spec E) (M (State n Auxiliary) Platform)
  | .reserve before capacity => publicWork (RegistrationNativePlatformSourceSeal.reserve allocation before capacity)
  | .aead plaintext associated nonce key => privateWork (aead setup codec view failure plaintext associated nonce key)

noncomputable def sealing (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) : M (State n Auxiliary) Platform (RustM AdapterSealNative.Output) := do
  let result ← simulateQ (handler setup codec view failure allocation) (AdapterSealNative.execute E request)
  modify fun before => {before with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall (.seal request)]}
  pure result

omit primitive in
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (query : (AdapterSealNative.Spec E).Domain) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (handler setup codec view failure allocation query)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformSourceSeal.handler RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation query)).run (realize before) := by
  cases query with
  | reserve buffer capacity =>
    rw [show handler setup codec view failure allocation (.reserve buffer capacity) =
      publicWork (RegistrationNativePlatformSourceSeal.reserve allocation buffer capacity) from rfl,
      RegistrationNativePlatformCtxRunner.public_run]
    simp only [RegistrationAgreementNestedState.flatten, RegistrationNativePlatformSourceSeal.handler,
      StateT.run, state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq]
  | aead plaintext associated nonce key =>
    have source := RegistrationNativePlatformCtxLocal.record_source setup codec
      (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key))) before
    rw [RegistrationNativePlatformCtxRunner.private_run] at source
    change Prod.map id realize <$> (interpret (privateWork (aead setup codec view failure plaintext associated nonce key))).run before = _
    rw [RegistrationNativePlatformCtxRunner.private_run]
    have mapped := congrArg (fun action => (fun (result : Option (Pqxdh.Bytes × Pqxdh.Bytes) ×
        (State n Auxiliary × Platform)) =>
      ((.ok (RegistrationNativePlatformSourceSeal.detached failure result.1) : AdapterSealNative.NativeReply), result.2)) <$> action) source
    simpa only [aead, RegistrationNativePlatformSourceSeal.handler, RegistrationNativePlatformSourceSeal.aead,
      RegistrationAgreementNestedState.flatten, StateT.run, simulateQ_map,
      RegistrationNativePlatformMldsaProgram.lift_coins, state_map_apply, state_lift_apply,
      bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq] using mapped

theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (work : OracleComp (AdapterSealNative.Spec E) A) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (simulateQ (handler setup codec view failure allocation) work)).run before =
      (RegistrationAgreementNestedState.flatten
        (simulateQ (RegistrationNativePlatformSourceSeal.handler RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation) work)).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.simulate]
  have same := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun request => interpret (handler setup codec view failure allocation request))
    (RegistrationAgreementNestedState.implementation (RegistrationNativePlatformSourceSeal.handler RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation))
    realize (query_source setup codec view failure allocation) work before
  rw [RegistrationAgreementNestedState.program] at same
  exact same
omit primitive in
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let reply ← work before; next reply.1 reply.2) := rfl

omit primitive in
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (update : S → S) (before : S) :
    (modify update : StateT S m Unit) before = pure ((), update before) := rfl

omit primitive in
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

/-- Every source allocation and AEAD outcome, the complete consumed Local state and the original seal request marker survive the physical CTX interpretation. -/
theorem sealing_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (sealing setup codec view failure allocation request)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation request)).run (realize before) := by
  have source := program_source setup codec view failure allocation (AdapterSealNative.execute E request) before
  have mapped := congrArg (fun action => (fun result =>
    (result.1, ({result.2.1 with recordRequests := result.2.1.recordRequests ++ [RegistrationWorldAgreement.recordCall (.seal request)]}, result.2.2))) <$> action) source
  simpa only [sealing, RegistrationNativePlatformSourceSeal.sealing, RegistrationNativePlatformCtxRunner.interpret,
    RegistrationAgreementNestedState.flatten, StateT.run, state_bind_apply, state_map_apply, state_modify_apply, state_pure_apply,
    simulateQ_bind, simulateQ_pure, simulateQ_map, map_bind, map_pure, bind_pure_comp, Functor.map_map,
    realize, attach, replace, Prod.map_def, id_eq] using mapped
noncomputable def hash (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) :
    M (State n Auxiliary) Platform RegistrationNativePlatformCommitment.HashReply :=
  privateWork (do
    let reply ← RegistrationNativePlatformCtxLocal.records setup codec (.hash transcript)
    pure (.ok (reply, erased)))

omit primitive in
theorem hash_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (hash setup codec erased transcript)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased transcript)).run (realize before) := by
  have source := RegistrationNativePlatformCtxLocal.records_source setup codec (.hash transcript) before
  unfold hash
  rw [RegistrationNativePlatformCtxRunner.private_run] at source ⊢
  have mapped := congrArg (fun action => (fun (result : core.option.Option (Std.Array U8 64#usize) ×
      (State n Auxiliary × Platform)) =>
    ((.ok (result.1, erased) : RegistrationNativePlatformCommitment.HashReply), result.2)) <$> action) source
  simpa only [RegistrationNativePlatformSourceSeal.hash, RegistrationNativePlatformServerCompletion.records,
    RegistrationNativePlatformServerCompletion.liftNative, RegistrationAgreementNestedState.flatten,
    StateT.run, state_bind_apply, state_pure_apply, simulateQ_map,
    RegistrationNativePlatformMldsaProgram.lift_coins, state_map_apply, state_lift_apply,
    bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal.sealing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal.sealing_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSeal.hash_source
