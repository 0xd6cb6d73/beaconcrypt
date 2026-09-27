import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput
import BeaconcryptCore.Computational.PqxdhInitialSourceReal

/-!
The instrumented accepted-root continuation executes the same complete source callbacks before observing publication and freshness. Its executable target handler has no selected KEM secret-key argument. The selected secret is supplied only to the private CCA/root interpreter. All local primitive work is kept as its original probabilistic computation.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpandHybrid
open PqxdhInitialBeaconAmbient PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle
open PqxdhInitializerSecrecy PqxdhPhase2SourceAux PqxdhChallengeSecretRouting
variable {ι I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

abbrev Spec := PqxdhInitialNativeLog.Spec (SelectorSpec baseSpec) RatchetChain
  (IdentityHandle I) D (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted)
  Response PqxdhPhase2DecapsulationRouting.Shared S B

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))
    (challenge : MlKem768Ciphertext)

noncomputable def target : QueryImpl
    (Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B))
    (StateT (RawCtxSharedPrimitive.SharedState A × BareState count) (OracleComp (LocalPostSpec baseSpec)))
  | .inl query => fun state => PqxdhPrivateAcceptedRoot.localCoins ((fun result => (result.1, (result.2, state.2))) <$>
      (RawCtxPendingRetainedExecution.retained source writer (productionStream source.crypto) query).run state.1)
  | .inr (.inl query) => fun state =>
      PqxdhInitialRootFreeCallbacks.work attachedVerify primitives count source localImpl challenge (.inl query) state
  | .inr (.inr (.inl reply)) => fun state =>
      PqxdhInitialRootFreeCallbacks.work attachedVerify primitives count source localImpl challenge (.inr (.inr reply)) state
  | .inr (.inr (.inr (.inl secrets))) => fun state => do
      let root ← PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4
      pure (root.map (fun root => (PqxdhInitialRootAudit.kernel
        (PqxdhPhase2InputBytes.word root, PqxdhInitialRootLabelService.realInitial source (PqxdhPhase2InputBytes.word root))).refined), state)
  | .inr (.inr (.inr (.inr (.inl query)))) => fun state =>
      (fun result => (result.1, (state.1, result.2))) <$>
        PqxdhPhase2PostScheduler.publicWork ((borrowedSelector attachedVerify primitives count query).run state.2)
  | .inr (.inr (.inr (.inr (.inr query)))) => fun state =>
      PqxdhPrivateAcceptedRoot.localCoins ((fun result => (result.1, (result.2, state.2))) <$> (aux query).run state.1)

variable (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

noncomputable def evaluated : QueryImpl
    (Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B))
    (Ambient A (BareState count) RootOracle.QueryCache) := fun query state =>
  simulateQ uniformImpl (simulateQ (rootPost source baseImpl kem secret challenge)
    ((target source writer attachedVerify primitives count localImpl aux challenge query).run state))

/-- Original local coins retain the full root cache under the composed CCA/root interpreter. -/
theorem coins_uniform (work : ProbComp Result) (cache : RootOracle.QueryCache) :
    (simulateQ uniformImpl (simulateQ (rootPost source baseImpl kem secret challenge)
      (PqxdhPrivateAcceptedRoot.localCoins work))).run cache =
      (fun result => (result, cache)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [PqxdhPrivateAcceptedRoot.localCoins, simulateQ_bind, StateT.run_bind]
    change (do
      let answer ← (unifSpec.query query : ProbComp _)
      (simulateQ uniformImpl (simulateQ (rootPost source baseImpl kem secret challenge)
        (PqxdhPrivateAcceptedRoot.localCoins (next answer)))).run cache) = _
    simp only [ih, map_bind]

/-- The target's source root-then-initializer callback is the same actual root-family program, with its complete optional kernel and ambient state retained. -/
theorem initial_program
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) :
    simulateQ (rootPost source baseImpl kem secret challenge)
      ((target (S := S) (B := B) source writer attachedVerify primitives count localImpl aux challenge
        (.inr (.inr (.inr (.inl secrets))))).run state) =
      (fun response => (response.map (fun value => (PqxdhInitialRootAudit.kernel
        (List.Vector.replicate 32 0, value)).refined), state)) <$>
        PqxdhInitialRootLabelBridge.rootThenInitial source baseImpl kem secret challenge secrets := by
  simp only [target, StateT.run, bind_pure_comp, simulateQ_map,
    PqxdhInitialRootLabelBridge.rootThenInitial, bind_pure_comp]
  simp only [Functor.map_map]
  congr 1
  funext response
  cases response with
  | none => rfl
  | some root =>
    simp only [Option.map_some, PqxdhInitialRootLabelService.realInitial, PqxdhInitialResponseService.pending, Bool.false_eq_true, if_false, PqxdhPhase2InputBytes.word_roundtrip]
    rw [PqxdhInitialNativeInitializer.kernel_input_unused (PqxdhPhase2InputBytes.word root) (List.Vector.replicate 32 0)]
    rfl

/-- The complete actual initializer callback reconstructs the selected root cache privately, including every nonselected family lookup and every recovered-key request. -/
theorem initial_cache (selected : Message) (root : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) (cache : RootOracle.QueryCache) :
    (fun result => (result.1, PqxdhInitialRootLabelService.completeCache selected root result.2)) <$>
      (((Prod.snd <$> PqxdhInitialNativeInitializer.initial source selected root
        (PqxdhInitialRootLabelService.realInitial source root) secrets) state).run cache) =
    (evaluated (S := S) (B := B) source writer attachedVerify primitives count localImpl aux challenge
      baseImpl kem secret (.inr (.inr (.inr (.inl secrets)))) state).run
        (PqxdhInitialRootLabelService.completeCache selected root cache) := by
  simp only [evaluated, initial_program, simulateQ_map, StateT.run_map]
  rw [← PqxdhInitialRootLabelBridge.labelled_source source baseImpl kem secret challenge secrets selected root cache]
  change (fun result => (result.1, PqxdhInitialRootLabelService.completeCache selected root result.2)) <$>
    (((Prod.snd <$> PqxdhInitialNativeInitializer.initial source selected root
      (PqxdhInitialRootLabelService.realInitial source root) secrets).run state).run cache) = _
  rw [StateT.run_map, StateT.run_map]
  simpa only [StateT.run, Functor.map_map, Prod.map, Option.map_some] using
    congrArg (fun work => (fun result => (result.1, PqxdhInitialRootLabelService.completeCache selected root result.2)) <$> work)
      (PqxdhInitialNativeInitializer.initial_erase source selected root
        (PqxdhInitialRootLabelService.realInitial source root) secrets state cache)

/-- Every complete public continuation, including adaptive decapsulation requests, retains the standard CCA block and leaves the root-family cache untouched. -/
theorem public_uniform (work : OracleComp (MlKemCCAOracleSpec baseSpec) Result) (cache : RootOracle.QueryCache) :
    (simulateQ uniformImpl (simulateQ (rootPost source baseImpl kem secret challenge)
      (PqxdhPhase2PostScheduler.publicWork work))).run cache =
      (fun result => (result, cache)) <$>
        simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
          (PqxdhPhase2PostScheduler.publicWork work) := by
  have noRoot : (PqxdhPhase2PostScheduler.publicWork work).IsQueryBoundP
      (PqxdhChallengeSecretQueryBounds.IsPrivateRoot (baseSpec := baseSpec)) 0 := by
    apply PqxdhPhase2PostSchedulerBounds.publicWork_bound .root
    induction work using OracleComp.inductionOn with
    | pure value => simp
    | query_bind query next ih => simp [PqxdhPhase2PostSchedulerBounds.publicPredicate]
  rw [PqxdhInitialRootFreeCallbacks.root_free source baseImpl kem secret challenge _ noRoot,
    PqxdhInitialRootContext.coins_complete]

noncomputable def sourceExternal (selected : Message) (root : RootOutput) :
    QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain
      (IdentityHandle I) D (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted)
      Response PqxdhPhase2DecapsulationRouting.Shared)
      (Ambient A (BareState count) RootOracle.QueryCache)
  | .inl query => PqxdhInitialCurrentBeacon.preparation attachedVerify primitives count source localImpl baseImpl kem secret challenge query
  | .inr (.inl reply) => PqxdhInitialCurrentBeacon.application attachedVerify primitives count source localImpl baseImpl kem secret challenge reply
  | .inr (.inr (.inl secrets)) => Prod.snd <$> PqxdhInitialNativeInitializer.initial source selected root
      (PqxdhInitialRootLabelService.realInitial source root) secrets
  | .inr (.inr (.inr (.inl query))) => PqxdhInitialPendingAmbient.selectorLift
      (PqxdhInitialPendingCurrent.selector attachedVerify primitives count baseImpl kem secret challenge) query
  | .inr (.inr (.inr (.inr query))) => lift (aux query)

noncomputable def sourceHandler (selected : Message) (root : RootOutput) : QueryImpl
    (Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B))
    (Ambient A (BareState count) RootOracle.QueryCache)
  | .inl query => lift (RawCtxPendingRetainedExecution.retained source writer (productionStream source.crypto) query)
  | .inr query => sourceExternal source attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root query

/-- Every complete source callback has the same reply and shared/private state under reconstruction of the selected root-cache entry. -/
theorem step_cache (selected : Message) (root : RootOutput)
    (query : (Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)).Domain)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) (cache : RootOracle.QueryCache) :
    (fun result => (result.1, PqxdhInitialRootLabelService.completeCache selected root result.2)) <$>
      ((sourceHandler source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root query state).run cache) =
    (evaluated source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret query state).run
      (PqxdhInitialRootLabelService.completeCache selected root cache) := by
  cases query with
  | inl query =>
    have same := coins_uniform source challenge baseImpl kem secret
      ((fun result => (result.1, (result.2, state.2))) <$>
        (RawCtxPendingRetainedExecution.retained source writer (productionStream source.crypto) query).run state.1)
      (PqxdhInitialRootLabelService.completeCache selected root cache)
    simp only [sourceHandler, PqxdhInitialBeaconAmbient.lift, evaluated, target, StateT.run, Functor.map_map] at same ⊢
    exact same.symm
  | inr query =>
    rcases query with query | (reply | (secrets | (query | query)))
    · have same := PqxdhInitialRootFreeCallbacks.cache_source attachedVerify primitives count source localImpl baseImpl kem secret challenge
        (.inl query) state (PqxdhInitialRootLabelService.completeCache selected root cache)
      simp only [sourceHandler, sourceExternal, evaluated, target, StateT.run,
        PqxdhInitialCurrentBeacon.preparation, Functor.map_map] at same ⊢
      exact same.symm
    · have same := PqxdhInitialRootFreeCallbacks.cache_source attachedVerify primitives count source localImpl baseImpl kem secret challenge
        (.inr (.inr reply)) state (PqxdhInitialRootLabelService.completeCache selected root cache)
      simp only [sourceHandler, sourceExternal, evaluated, target, StateT.run,
        PqxdhInitialCurrentBeacon.application, Functor.map_map] at same ⊢
      exact same.symm
    · exact initial_cache source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root secrets state cache
    · have same := public_uniform source challenge baseImpl kem secret
        ((borrowedSelector attachedVerify primitives count query).run state.2)
        (PqxdhInitialRootLabelService.completeCache selected root cache)
      have mapped := congrArg (fun work => (fun result => ((result.1.1, (state.1, result.1.2)), result.2)) <$> work) same
      simp only [sourceHandler, sourceExternal, evaluated, target, StateT.run,
        PqxdhInitialPendingAmbient.selectorLift,
        simulateQ_map, Functor.map_map] at mapped ⊢
      change (fun result => (result.1, PqxdhInitialRootLabelService.completeCache selected root result.2)) <$>
        ((fun result => (result.1, (state.1, result.2))) <$>
          (PqxdhInitialPendingCurrent.selector attachedVerify primitives count baseImpl kem secret challenge query).run state.2).run cache =
        ((fun result => (result.1, (state.1, result.2))) <$>
          simulateQ uniformImpl (simulateQ (rootPost source baseImpl kem secret challenge)
            (PqxdhPhase2PostScheduler.publicWork ((borrowedSelector attachedVerify primitives count query).run state.2)))).run
              (PqxdhInitialRootLabelService.completeCache selected root cache)
      rw [StateT.run_map, StateT.run_map]
      simp only [PqxdhInitialPendingCurrent.selector, StateT.run, Functor.map_map]
      exact mapped.symm
    · have same := coins_uniform source challenge baseImpl kem secret
        ((fun result => (result.1, (result.2, state.2))) <$> (aux query).run state.1)
        (PqxdhInitialRootLabelService.completeCache selected root cache)
      simp only [sourceHandler, sourceExternal, PqxdhInitialBeaconAmbient.lift, evaluated, target, StateT.run, Functor.map_map] at same ⊢
      exact same.symm

/-- Cache reconstruction commutes with the whole adaptive instrumented source client, retaining its complete result and final ambient state. -/
theorem program_cache (selected : Message) (root : RootOutput)
    (client : OracleComp (Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)) Result)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) (cache : RootOracle.QueryCache) :
    (fun result => (result.1, PqxdhInitialRootLabelService.completeCache selected root result.2)) <$>
      (((simulateQ (sourceHandler source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root) client).run state).run cache) =
    ((simulateQ (evaluated source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret) client).run state).run
      (PqxdhInitialRootLabelService.completeCache selected root cache) := by
  induction client using OracleComp.inductionOn generalizing state cache with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have step := step_cache source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root query state cache
    change (fun result => (result.1, PqxdhInitialRootLabelService.completeCache selected root result.2)) <$>
      ((sourceHandler source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root query).run state).run cache =
      ((evaluated source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret query).run state).run
        (PqxdhInitialRootLabelService.completeCache selected root cache) at step
    rw [← step]
    simp only [bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1.1 result.1.2 result.2

/-- Interpreting every compiled source callback is exactly interpreting the entire executable target continuation after it runs. -/
theorem program_evaluated
    (client : OracleComp (Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)) Result)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) :
    (simulateQ (evaluated source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret) client).run state =
      simulateQ uniformImpl (simulateQ (rootPost source baseImpl kem secret challenge)
        ((simulateQ (target source writer attachedVerify primitives count localImpl aux challenge) client).run state)) := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, QueryImpl.simulateQ_mapStateTBase_run]
  rfl

/-- Reassociating the same shared/private/cache state identifies the concrete source handler with the fixed-function retained source interpreter. -/
theorem program_source (selected : Message) (root : RootOutput)
    (client : OracleComp (Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)) Result)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) (cache : RootOracle.QueryCache) :
    (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
      (((simulateQ (sourceHandler source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root) client).run state).run cache) =
    (simulateQ (PqxdhInitialNativeRetained.retained source writer (productionStream source.crypto)
      (sourceExternal source attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root)) client).run
        (state.1, (state.2, cache)) := by
  induction client using OracleComp.inductionOn generalizing state cache with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have step : (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
        ((sourceHandler source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root query).run state).run cache =
      (PqxdhInitialNativeRetained.retained source writer (productionStream source.crypto)
        (sourceExternal source attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root) query).run
          (state.1, (state.2, cache)) := by
      cases query with
      | inl query =>
        simp only [sourceHandler, PqxdhInitialBeaconAmbient.lift, PqxdhInitialNativeRetained.retained, StateT.run, Functor.map_map]
        rfl
      | inr query => rfl
    rw [← step]
    simp only [bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1.1 result.1.2 result.2

/-- A final observation of the complete instrumented source result is preserved by the executable target continuation and private selected-cache reconstruction. -/
theorem observed_uniform (selected : Message) (root : RootOutput)
    (client : OracleComp (Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)) Result)
    (observe : Result → Bool)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) (cache : RootOracle.QueryCache) :
    (fun result => observe result.1) <$>
      (simulateQ (PqxdhInitialNativeRetained.retained source writer (productionStream source.crypto)
        (sourceExternal source attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root)) client).run
          (state.1, (state.2, cache)) =
    (simulateQ uniformImpl (simulateQ (rootPost source baseImpl kem secret challenge)
      ((fun result => observe result.1) <$>
        (simulateQ (target source writer attachedVerify primitives count localImpl aux challenge) client).run state))).run'
          (PqxdhInitialRootLabelService.completeCache selected root cache) := by
  rw [← program_source source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root client state cache]
  have same := congrArg (fun work => (fun result => observe result.1.1) <$> work)
    (program_cache source writer attachedVerify primitives count localImpl aux challenge baseImpl kem secret selected root client state cache)
  rw [program_evaluated] at same
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] at same ⊢
  exact same

end BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.coins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.coins_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.initial_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.initial_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.initial_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.initial_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.public_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.public_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.step_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.step_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.program_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.program_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.program_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.program_evaluated

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.program_source


/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.observed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler.observed_uniform
