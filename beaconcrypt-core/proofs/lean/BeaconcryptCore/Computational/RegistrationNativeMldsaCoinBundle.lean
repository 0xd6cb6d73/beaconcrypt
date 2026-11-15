-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
import BeaconcryptCore.Computational.RegistrationNativeInitCosts
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundle

/-! Literal ordinary-randomness bounds for free outgoing Beacon publication. Three attached Ed signatures precede the retained request hash; optional one-time scalar sampling and publication effects retain their actual source schedules. The Beacon controller issues no ML signing query. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeMldsaCoinPrimitives (IsCoin ordinary)
open RegistrationNativeBeaconFrontend (Owner)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) :
    (observe <$> work) state = Prod.map observe id <$> work state := StateT.run_map observe work state

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (state : S) : (modify change : StateT S m Unit) state = pure ((), change state) := rfl

private theorem update (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) (before : Local n KemSK source) :
    ((RegistrationNativeMldsaBundle.native setup checks representation created
      (RegistrationNativeBeaconFrontend.updatePhase index phase)).run before).IsQueryBoundP IsCoin 0 := by
  apply ordinary _ 0
  simp only [lower, RegistrationNativeBeaconFrontend.updatePhase, StateT.run, state_modify_apply,
    state_pure_apply, simulateQ_pure, map_pure, IsTotalQueryBound, isQueryBound_pure]

private theorem advance (owner : Nat) (before : Local n KemSK source) :
    ((RegistrationNativeMldsaBundle.native setup checks representation created
      (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner .initSent)))).run before).IsQueryBoundP IsCoin 0 := by
  apply ordinary _ 0
  simp only [lower, RegistrationNativeBeaconFrontend.effect, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff, state_lift_apply, state_map_apply, simulateQ_map,
    simulateQ_spec_query, RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server]
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
    StateT.run, PqxdhRecordLiftWorld.chargeEffect]
  cases before.2.2.server.world.world.1.owners[owner]? with
  | none => trivial
  | some phase => cases phase with
    | established shell kernel => trivial
    | inactive phase => simp only; split <;> trivial

private theorem native_outgoing (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : Local n KemSK source)
    (bounded : ((RegistrationNativeMldsaShared.implementation setup owner query).run
      (RegistrationNativeMldsaShared.project before)).IsTotalQueryBound 64) :
    ((RegistrationNativeMldsaBundle.native setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)).run before).IsQueryBoundP IsCoin 64 := by
  apply ordinary _ 64
  rw [← RegistrationNativeMldsaShared.outgoing setup checks representation created index owner query before] at bounded
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bounded

/-- Each outgoing source callback has at most64 ordinary draws; a raw ML signing reply adds none. -/
theorem outgoing (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : Local n KemSK source) :
    ((RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner query).run before).IsQueryBoundP IsCoin 64 := by
  cases query with
  | inl query => cases query with
    | hash request =>
        apply native_outgoing setup checks representation created index owner (.inl (.hash request)) before
        simpa only [RegistrationNativeMldsaShared.implementation, RegistrationSigningShared.implementation,
          MldsaSharedNative.authentication, StateT.run, bind_pure_comp, IsTotalQueryBound,
          isQueryBound_map_iff] using CtxComputationalSecurity.ctxRandomOracle_total_query_bound
            ((), BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) (RegistrationNativeMldsaShared.project before).2
    | sign request payload digest =>
        apply native_outgoing setup checks representation created index owner (.inl (.sign request payload digest)) before
        simp only [RegistrationNativeMldsaShared.implementation, StateT.run_pure, IsTotalQueryBound, isQueryBound_pure]
  | inr request =>
      apply native_outgoing setup checks representation created index owner (.inr request) before
      simp only [RegistrationNativeMldsaShared.implementation, StateT.run_pure, IsTotalQueryBound, isQueryBound_pure]

private theorem simulated (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) (cap : Nat)
    (bounded : work.IsTotalQueryBound cap) (before : Local n KemSK source) :
    ((simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner) work).run before).IsQueryBoundP
      IsCoin (cap * 64) := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply (isQueryBoundP_bind (outgoing setup checks representation created index owner query before)
        (fun result _ => ih result.1 _ (bounded.2 result.1) result.2)).mono
      have positive : 0 < cap := bounded.1
      omega

private theorem afterPublished (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes))
    (before : Local n KemSK source) :
    ((RegistrationNativeMldsaBundle.afterPublished setup checks representation created index owner oneTime published).run before).IsQueryBoundP IsCoin 0 := by
  cases published with
  | fail error | div => trivial
  | ok answer => cases answer with
    | Err previous => trivial
    | Ok completed =>
        simp only [RegistrationNativeMldsaBundle.afterPublished, StateT.run_bind]
        apply isQueryBoundP_bind (n := 0) (m := 0) (update setup checks representation created _ _ before)
        intro middle _
        exact isQueryBoundP_bind (n := 0) (m := 0)
          (advance setup checks representation created _ middle.2) (fun _ _ => isQueryBoundP_pure _ _ _)

private theorem lower_sample (draw : ProbComp Value) (before : Local n KemSK source) :
    (lower setup checks representation created (RegistrationNativeBeaconFrontend.sample draw)).run before =
      (fun result => (result.1, (before.1, (before.2.1,
        RegistrationBeaconReferenceNativeEffects.embed before.2.2 result.2)))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin draw)).run
          before.2.2.server.world.world.1 := by
  rw [RegistrationNativeScalarSource.sample_effects]
  have restriction : RegistrationNativeExperiment.trusted (n := n) setup checks representation created source ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK) =
      RegistrationBeaconReferenceNativeEffects.native setup checks representation created := by
    funext selected
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, RegistrationBeaconReferenceNativeEffects.native]
  simp only [lower, StateT.run, state_lift_apply, state_map_apply, simulateQ_map, Functor.map_map,
    Prod.map, id_eq]
  rw [← QueryImpl.simulateQ_compose, restriction]
  have closed := RegistrationBeaconReferenceNativeEffects.program setup checks representation created
    (simulateQ RegistrationWorldCoinCompiler.envCoin draw) before.2.2
  simp only [StateT.run] at closed
  rw [closed]
  simp only [Functor.map_map, Prod.map, id_eq]

private theorem scalar (before : Local n KemSK source) :
    ((RegistrationNativeMldsaBundle.native setup checks representation created
      (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run before).IsQueryBoundP IsCoin 32 := by
  apply ordinary _ 32
  simp only [lower_sample, IsTotalQueryBound, isQueryBound_map_iff]
  have bounded := RegistrationNativeMldsaCoinPrimitives.sampled PqxdhJointGapDh.sampleScalar 32
    PqxdhJointIdentity.sampleSeed_uniform_bound before.2.2.server.world.world.1
  have mapped : (Prod.map id RegistrationWorldCoinCompiler.eraseCoin <$>
      (PqxdhRecordLiftWorld.sampled PqxdhJointGapDh.sampleScalar).run before.2.2.server.world.world.1).IsTotalQueryBound 32 := by
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bounded
  rw [← RegistrationWorldCoinCompiler.coins_erase] at mapped
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using mapped

private theorem native_get (before : Local n KemSK source) :
    (RegistrationNativeMldsaBundle.native setup checks representation created get).run before = pure (before.1, before) := rfl

/-- Every free source bundle has at most32 optional scalar draws plus four source callbacks (three Ed signatures and the request hash) of at most64 ordinary draws, within the retained 416-draw allowance. -/
theorem bundle (wire : RegistrationNativeWire.Wire) (index : Nat) (before : Local n KemSK source) :
    ((RegistrationNativeMldsaBundle.bundle setup checks wire representation created index).run before).IsQueryBoundP IsCoin 416 := by
  simp only [RegistrationNativeMldsaBundle.bundle, StateT.run_bind, native_get setup checks representation created, pure_bind]
  cases found : before.1[index]? with
  | none => trivial
  | some owner =>
      have continuation (oneTime : PqxdhJointGapDh.ScalarBytes) (current : Local n KemSK source) :
          ((do
            let published ← simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner)
              (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
                (RegistrationNativeBeaconFrontend.inputs setup owner)
                ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
            RegistrationNativeMldsaBundle.afterPublished setup checks representation created index owner oneTime published).run current).IsQueryBoundP IsCoin 384 := by
        rw [StateT.run_bind]
        apply isQueryBoundP_bind (n := 384) (m := 0)
        · exact (simulated setup checks representation created index owner _ 4
            (RegistrationNativeInitCosts.begin_bound wire.encodeInit _ _ _ _) current).mono (by decide)
        · intro result _
          exact afterPublished setup checks representation created index owner oneTime result.1 result.2
      cases phase : owner.phase <;> simp only [phase]
      all_goals first
        | trivial
        | exact (continuation _ before).mono (by decide)
        | exact isQueryBoundP_bind (scalar setup checks representation created before)
            (fun result _ => continuation result.1 result.2)

/-- The complete native-state wrapper preserves that actual all-replies free uniform cap. -/
theorem sourceBundle (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index).run before).IsQueryBoundP IsCoin 416 := by
  simpa only [RegistrationNativeMldsaBundle.sourceBundle, StateT.run, isQueryBoundP_map_iff] using
    bundle setup checks representation created wire index _
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle.sourceBundle
