-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBoundPublication
import BeaconcryptCore.Computational.PqxdhEnvironmentForward
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry

/-! The actual bound record and ML publication program compiles into the existing environment effects: deterministic source HKDF, AEAD and optional writing remain real local work, every CTX hash uses the same World hash capability, and every ML signing draw uses the existing coin effects. The chronological attempt receipt is appended before any subsequent native continuation can reject. Factoring is proved query by query and then for arbitrary adaptive programs. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationBoundSourceCompiler

open PqxdhRecordLiftInterface (EnvEffects CapabilitySpec)
open PqxdhDeploymentEnvironment (ctxEffects)
open RegistrationSigningShared (SignReply State Receipt)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (replyBytes)
variable {n : Nat}

def sharedCompiler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl MldsaSharedNative.Spec (OracleComp (EnvEffects n))
  | .inl query => PqxdhDeploymentEnvironment.request (.hash query.2)
  | .inr query => PqxdhDeploymentEnvironment.sharedFwd source.crypto writer source query

theorem shared_query {Auxiliary : Type}
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : MldsaSharedNative.Spec.Domain) (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (MldsaSharedSource.implementation source writer query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ (ctxEffects admin) (sharedCompiler source writer query)).run cache := by
  cases query with
  | inl query =>
      rcases query with ⟨tag, bytes⟩
      cases tag
      simp only [sharedCompiler, PqxdhDeploymentEnvironment.request, simulateQ_spec_query, ctxEffects,
        MldsaSharedSource.implementation, MldsaSharedNative.primitives]
      rfl
  | inr query =>
      simp only [sharedCompiler, PqxdhDeploymentEnvironment.sharedFwd, MldsaSharedSource.implementation,
        MldsaSharedNative.primitives, RawCtxMixedShared.sharedImpl, QueryImpl.apply_compose]
      exact PqxdhDeploymentEnvironment.factor_stateless admin _ _
        (fun query auxiliary cache => PqxdhDeploymentEnvironment.primFwd_factor admin source.crypto source query auxiliary cache)
        _ auxiliary cache

theorem shared_program {Auxiliary Output : Type}
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp MldsaSharedNative.Spec Output) (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (MldsaSharedSource.implementation source writer) work).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ (ctxEffects admin) (simulateQ (sharedCompiler source writer) work)).run cache :=
  PqxdhDeploymentEnvironment.factor_stateless admin _ _ (shared_query admin source writer) work auxiliary cache

def rawCallbacks (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl RegistrationRawSealBridge.Spec (OracleComp MldsaSharedNative.Spec)
  | .inl request => RegistrationRecordPrimitives.callbacks source request
  | .inr (.inl input) => do
      let result ← MldsaSharedNative.recordLift (.inr (.inl input))
      pure (RegistrationRecordPrimitives.sealedBytes result)
  | .inr (.inr (.inl bytes)) => do
      let digest ← MldsaSharedNative.authLift ((), bytes)
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .inr (.inr (.inr bytes)) => pure (RegistrationAuthenticationShared.openedBytes (some bytes))

theorem raw_callbacks {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : RegistrationRawSealBridge.Spec.Domain)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (MldsaSharedSource.implementation source writer) (rawCallbacks source query)).run state =
      (RegistrationRawSealBridge.implementation source writer query).run state := by
  cases query with
  | inl request => rfl
  | inr request => rcases request with input | (bytes | body) <;> rfl

def rawCompiler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RegistrationRawSealBridge.Spec (OracleComp (EnvEffects n)) :=
  sharedCompiler source writer ∘ₛ rawCallbacks source

theorem raw_query {Auxiliary : Type}
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RegistrationRawSealBridge.Spec.Domain) (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (RegistrationRawSealBridge.implementation source writer query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ (ctxEffects admin) (rawCompiler source writer query)).run cache := by
  rw [← raw_callbacks]
  exact shared_program admin source writer (rawCallbacks source query) auxiliary cache

theorem raw_factor {Auxiliary Output : Type}
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp RegistrationRawSealBridge.Spec Output) (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (RegistrationRawSealBridge.implementation source writer) work).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ (ctxEffects admin) (simulateQ (rawCompiler source writer) work)).run cache :=
  PqxdhDeploymentEnvironment.factor_stateless admin _ _ (raw_query admin source writer) work auxiliary cache

noncomputable def implementation (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply) :
    QueryImpl RegistrationBoundPublication.Spec (StateT State ProbComp)
  | .inl query => RegistrationRawSealBridge.implementation source writer query
  | .inr query => RegistrationSigningShared.implementation sign query

def compiler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply) :
    QueryImpl RegistrationBoundPublication.Spec (StateT (List Receipt) (OracleComp (EnvEffects n)))
  | .inl query => fun log => (fun reply => (reply, log)) <$> rawCompiler source writer query
  | .inr (.hash request) => fun log => (fun digest => (digest, log)) <$>
      PqxdhDeploymentEnvironment.request (.hash (hashBytes request))
  | .inr (.sign request payload digest) => fun log =>
      (fun reply => (reply, log ++ [⟨⟨request.public_key, payload, replyBytes reply⟩, digest⟩])) <$>
        PqxdhDeploymentEnvironment.coins (sign request)

theorem raw_program {Output : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (work : OracleComp RegistrationRawSealBridge.Spec Output) (state : State) :
    (simulateQ (implementation source writer sign) (simulateQ RegistrationBoundPublication.rawLift work)).run state =
      (simulateQ (RegistrationRawSealBridge.implementation source writer) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationBoundPublication.rawLift,
        implementation, StateT.run_bind, ih]

theorem signing_program {Output : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Output) (state : State) :
    (simulateQ (implementation source writer sign) (simulateQ RegistrationBoundPublication.signingLift work)).run state =
      (simulateQ (RegistrationSigningShared.implementation sign) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationBoundPublication.signingLift,
        implementation, StateT.run_bind, ih]

def liftedCompiler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply) :
    QueryImpl RegistrationBoundPublication.Spec (StateT State (OracleComp (EnvEffects n))) := fun query state =>
  (fun result => (result.1, (result.2, state.2))) <$> (compiler source writer sign query).run state.1

private theorem liftedCompiler_apply (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (state : State) :
    (liftedCompiler (n := n) source writer sign query).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (compiler source writer sign query).run state.1 := rfl

theorem compiler_frame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (state : State) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (liftedCompiler (n := n) source writer sign query).run (state.1, cache) =
      (fun result => (result.1, (result.2.1, cache))) <$> (liftedCompiler source writer sign query).run state := by
  simp only [liftedCompiler, StateT.run, Functor.map_map]

theorem compiler_run {Output : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (work : OracleComp RegistrationBoundPublication.Spec Output) (state : State) :
    (simulateQ (liftedCompiler (n := n) source writer sign) work).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (simulateQ (compiler source writer sign) work).run state.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liftedCompiler_apply,
        bind_map_left, ih, map_bind]

private theorem map_state_apply {S Input Output : Type} (f : Input → Output) (work : StateT S ProbComp Input) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := by
  change (work state >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem coins_apply {Output : Type}
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
    (work : ProbComp Output) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (ctxEffects admin) (PqxdhDeploymentEnvironment.coins work)) cache =
      (fun value => (value, cache)) <$> work :=
  PqxdhDeploymentEnvironment.ctxEffects_coins admin work cache

theorem query_factor
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (log : List Receipt) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (implementation source writer sign query).run (log, cache) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (ctxEffects admin) ((compiler source writer sign query).run log)).run cache := by
  cases query with
  | inl query =>
      rw [show (implementation source writer sign (.inl query)).run (log, cache) =
        (RegistrationRawSealBridge.implementation source writer query).run (log, cache) from rfl,
        raw_query admin source writer query log cache]
      simp only [compiler, StateT.run, simulateQ_map, map_state_apply, Functor.map_map]
      rfl
  | inr query =>
      cases query with
      | hash request =>
          simp only [implementation, RegistrationSigningShared.implementation, compiler, StateT.run,
            simulateQ_map, map_state_apply, PqxdhDeploymentEnvironment.request,
            simulateQ_spec_query, ctxEffects, Functor.map_map]
          rfl
      | sign request payload digest =>
          simp only [implementation, RegistrationSigningShared.implementation, compiler, StateT.run,
            simulateQ_map, map_state_apply, coins_apply, Functor.map_map]
          rfl

/-- Every adaptive bound publication program is the concrete shared-cache native source, with the same complete result and chronological signing log. -/
theorem factor {Output : Type}
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (work : OracleComp RegistrationBoundPublication.Spec Output) (log : List Receipt) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (implementation source writer sign) work).run (log, cache) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (ctxEffects admin) ((simulateQ (compiler source writer sign) work).run log)).run cache := by
  have factored := PqxdhDeploymentEnvironment.factor_program admin
    (PqxdhDeploymentHiddenEntry.sharedLens (List Receipt))
    (implementation source writer sign) (liftedCompiler source writer sign)
    (fun query state cache => by
      simpa only [PqxdhDeploymentHiddenEntry.sharedLens, LazyOracleDiscard.StateLens.snd] using
        compiler_frame (n := n) source writer sign query state cache)
    (fun query state => by
      simpa only [PqxdhDeploymentHiddenEntry.sharedLens, LazyOracleDiscard.StateLens.snd,
        liftedCompiler_apply, simulateQ_map, StateT.run_map, Functor.map_map] using
        query_factor admin source writer sign query state.1 state.2)
    work (log, cache)
  rw [factored, compiler_run, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationBoundSourceCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.shared_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.shared_query
/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.shared_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.shared_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.raw_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.raw_callbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.raw_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.raw_query

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.raw_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.raw_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.raw_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.raw_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.signing_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.signing_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.compiler_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.compiler_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.compiler_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.compiler_run

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.query_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.query_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundSourceCompiler.factor
