import BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls

/-! Surrounding ordinary source work uses the selected CTX component's actual shared commitment cache. Uniform draws are forwarded, fixed HKDF and locally known AEAD work remain real, and optional writers retain their exact result. This compiler does not receive the selected key; that fact alone makes no independence or nonexposure claim for arbitrary supplied inputs. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient
open PqxdhSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedReceiveCompiler (State project evaluated)


private theorem state_map_apply {X Y σ : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT σ m X) (state : σ) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := by
  change (f <$> work).run state = _
  rw [StateT.run_map]
  rfl

private theorem state_lift_apply {X σ : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (work : m X) (state : σ) :
    (monadLift work : StateT σ m X) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

noncomputable def coin : QueryImpl unifSpec (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) :=
  fun query => AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inl query)))

noncomputable def hash (bytes : Pqxdh.Bytes) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec CtxRomAuth.CtxDigest :=
  AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inl ((), bytes)))))

/-- The actual forwarded uniform draw preserves the entire source auxiliary/cache pair and returns the original oracle sample. -/
theorem coin_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (query : unifSpec.Domain) (state : State A) :
    Prod.map id project <$> (evaluated source key read (coin query)).run state =
      (fun value => (value, project state)) <$> (unifSpec.query query : ProbComp _) := by
  simp [coin, evaluated, AdaptiveCtxDynamicKnownKeys.sourceImpl,
    AdaptiveCtxSharedModes.localImpl, AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.hashImpl,
    StateT.run, state_map_apply, state_lift_apply, project, Prod.map_def]

/-- Public and known-operation commitment requests use the same actual component cache as selected sealing and opening. -/
theorem hash_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (state : State A) :
    Prod.map id project <$> (evaluated source key read (hash bytes)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2.cache := by
  simp [hash, evaluated, AdaptiveCtxDynamicKnownKeys.sourceImpl,
    AdaptiveCtxSharedModes.localImpl, AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.hashImpl,
    StateT.run, state_map_apply, project, Prod.map_def]

/-- Forwarding a coin retains every selected and known-key component field, not only the cache projection. -/
theorem coin_full {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (query : unifSpec.Domain) (state : State A) :
    (evaluated source key read (coin query)).run state =
      (fun value => (value, state)) <$> (unifSpec.query query : ProbComp _) := by
  simp [coin, evaluated, AdaptiveCtxDynamicKnownKeys.sourceImpl,
    AdaptiveCtxSharedModes.localImpl, AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.hashImpl,
    StateT.run, state_map_apply, state_lift_apply]

/-- The actual complete probabilistic source computation forwards all adaptive uniform draws and keeps the complete component state unchanged. -/
theorem coin_program {A Result : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : ProbComp Result) (state : State A) :
    (evaluated source key read (simulateQ coin work)).run state =
      (fun value => (value, state)) <$> work := by
  rw [← RawCtxSelectedReceiveCompiler.evaluated_program]
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, coin_full,
        bind_map_left, map_bind, ih]

/-- Actual known-material native operations: real fixed HKDF and AEAD, the original optional writer, and a forwarded shared commitment query. -/
noncomputable def native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)
  | .inl request => pure (RawCtxSourceHkdf.response source.crypto request)
  | .inr (.inl input) => pure (some (source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext))
  | .inr (.inr (.inl input)) => pure (RawCtxSourceOpen.baseOpen source.crypto input)
  | .inr (.inr (.inr (.inl bytes))) => (fun digest : CtxRomAuth.CtxDigest => some digest.toList) <$> hash bytes
  | .inr (.inr (.inr (.inr frame))) => pure (writer frame)

/-- Each actual source native callback uses the same full auxiliary state and common cache as the concrete compiler. -/
theorem native_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (state : State A) :
    (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run (project state) =
      Prod.map id project <$> (evaluated source key read (native source writer query)).run state := by
  rcases query with request | (input | (input | (bytes | frame)))
  · rfl
  · simp only [native, RawCtxMixedShared.shared_sealing]
    rfl
  · simp only [native, RawCtxMixedShared.sharedImpl, QueryImpl.apply_compose,
      RawCtxMixedShared.sharedAdapter, simulateQ_spec_query]
    rfl
  · rw [RawCtxMixedShared.shared_hash]
    have exactHash := congrArg (fun work => (fun result => (some result.1.toList, result.2)) <$> work)
      (hash_source source key read bytes state)
    simp only [native, RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map, Functor.map_map]
    simpa only [Functor.map_map, Prod.map_def, id_eq, project, bind_pure_comp] using exactHash.symm
  · simp only [native, RawCtxMixedShared.shared_writing]
    rfl

/-- A complete adaptive native source program retains all optional replies, deterministic work and shared-cache effects through the compiled component interface. -/
theorem native_program {A Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : State A) :
    (simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) work).run (project state) =
      Prod.map id project <$> (evaluated source key read (simulateQ (native source writer) work)).run state := by
  rw [← RawCtxSelectedReceiveCompiler.evaluated_program]
  exact (map_run_simulateQ_eq_of_query_map_eq
    (fun query => evaluated source key read (native source writer query))
    (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) project
    (fun query before => (native_source source writer key read query before).symm) work state).symm

/-- Every original coin query is forwarded once; arbitrary surrounding source randomness is charged by its actual total uniform allowance. -/
theorem coin_bound {Result : Type} (work : ProbComp Result) (bound : Nat)
    (bounded : work.IsTotalQueryBound bound) :
    (simulateQ coin work).IsTotalQueryBound bound := by
  apply (isQueryBoundP_true_iff _ _).mp
  apply RawCtxSourceOpen.simulate_bound coin (fun _ => True) (fun _ => True) work bound
    ((isQueryBoundP_true_iff _ _).mpr bounded)
  intro query
  simp only [ite_true]
  exact (isQueryBoundP_query_iff (spec := AdaptiveCtxDynamicKnownKeys.Spec) (fun _ => True) _ _).2 (by simp)

/-- Forwarded source randomness has no hash, selected seal or selected raw request, regardless of how later draws depend on earlier samples. -/
theorem coin_other {Result : Type} (work : ProbComp Result) :
    (simulateQ coin work).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 0 ∧
      (simulateQ coin work).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (simulateQ coin work).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  constructor
  · apply RawCtxSourceOpen.simulate_bound coin (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
    intro query
    simp [coin, AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxQueryBounds.SourceHash]
  · constructor
    all_goals
      apply RawCtxSourceOpen.simulate_bound coin (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
      intro query
      simp [coin, AdaptiveCtxDynamicKnownBounds.TargetClass,
        AdaptiveCtxQueryBounds.SourceSeal, AdaptiveCtxReceive.IsRawQuery]

/-- Every reached source hash, including a rejected known-key attempt, contributes one shared hash request; other known native operations contribute none. -/
theorem native_hash {Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (bound : Nat)
    (bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) bound) :
    (simulateQ (native source writer) work).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute bound := by
  apply RawCtxSourceOpen.simulate_bound (native source writer) _ _ work bound bounded
  rintro (request | (sealing | (opening | (bytes | frame))))
  all_goals simp [native, hash, RawCtxMixedOwner.callKind,
    AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxQueryBounds.SourceHash]

/-- Real locally known KDF/AEAD/writer work and forwarded hashing issue no selected seal, selected raw or explicit uniform requests; their local work and hash allowance remain separate. -/
theorem native_other {Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) :
    (simulateQ (native source writer) work).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (simulateQ (native source writer) work).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      (simulateQ (native source writer) work).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  constructor
  · apply RawCtxSourceOpen.simulate_bound (native source writer) (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
    rintro (request | (sealing | (opening | (bytes | frame))))
    all_goals simp [native, hash, AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal]
  · constructor
    all_goals
      apply RawCtxSourceOpen.simulate_bound (native source writer) (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
      rintro (request | (sealing | (opening | (bytes | frame))))
      all_goals simp [native, hash, AdaptiveCtxDynamicKnownBounds.TargetClass,
        AdaptiveCtxReceive.IsRawQuery, AdaptiveCtxDynamicKnownBounds.UniformRoute, AdaptiveCtxQueryBounds.SourceUniform]

end BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.hash_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_full

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_program

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.native_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.native_program

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.coin_other

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.native_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.native_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.native_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient.native_other
