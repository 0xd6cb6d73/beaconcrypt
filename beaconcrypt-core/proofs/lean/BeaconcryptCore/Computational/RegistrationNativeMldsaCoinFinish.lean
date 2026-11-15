-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinishSyntax
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
import BeaconcryptCore.Computational.RegistrationNativeResponseCosts
import BeaconcryptCore.Computational.RegistrationResponseHashBounds
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords
import BeaconcryptCore.Computational.RegistrationNativeMldsaProfile

/-! Literal ordinary-randomness receipts for the original Beacon finish source. Its response authentication, actual indexed decapsulation, first-record receive loop, known-kernel installation and all failed continuations retain the same source state. The only external cost receipt constrains the actual KEM decapsulation program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinish
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeMldsaCoinPrimitives (IsCoin)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
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
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let middle ← work state; next middle.1 middle.2) := rfl
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private def Total (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (cap : Nat) : Prop := ∀ before : Local n KemSK source,
  ((lower setup checks representation created work).run before).IsTotalQueryBound cap
local notation "B" => Total (n := n) (source := source) setup checks representation created

private theorem pure_bound (value : Value) (cap : Nat) : B (pure value) cap := by
  intro before
  simp only [lower, StateT.run, state_pure_apply, simulateQ_pure, map_pure, IsTotalQueryBound, isQueryBound_pure]

private theorem lower_bind
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Next) :
    lower setup checks representation created (work >>= next) =
      (lower setup checks representation created work >>= fun value => lower setup checks representation created (next value)) := by
  funext before
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, map_bind, bind_map_left]

private theorem bind_bound
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Next)
    (first rest : Nat) (bounded : B work first) (continued : ∀ value, B (next value) rest) :
    B (work >>= next) (first + rest) := by
  intro before
  rw [lower_bind, StateT.run_bind]
  exact isTotalQueryBound_bind (bounded before) (fun middle => continued middle.1 middle.2)

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (state : S) : (get : StateT S m S) state = pure (state, state) := rfl
private theorem state_set_apply {S : Type} {m : Type → Type} [Monad m]
    (updated state : S) : (set updated : StateT S m Unit) state = pure ((), updated) := rfl

private theorem get_bound : B get 0 := by
  intro before
  simp only [lower, StateT.run, state_get_apply, state_pure_apply, simulateQ_pure, map_pure,
    IsTotalQueryBound, isQueryBound_pure]

private theorem set_bound (updated : RegistrationNativeBeaconFrontend.State source) : B (set updated) 0 := by
  intro before
  simp only [lower, StateT.run, state_set_apply, state_pure_apply, simulateQ_pure, map_pure,
    IsTotalQueryBound, isQueryBound_pure]

private theorem effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (cap : Nat)
    (bounded : ∀ before : PqxdhRecordLiftWorld.State n,
      ((PqxdhRecordLiftWorld.effects query).run before).IsTotalQueryBound cap) :
    B (RegistrationNativeBeaconFrontend.effect query) cap := by
  intro before
  simpa only [lower, RegistrationNativeBeaconFrontend.effect, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff, state_lift_apply, state_map_apply, simulateQ_map,
    simulateQ_spec_query, RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server] using bounded before.2.2.server.world.world.1

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

private theorem sample (draw : ProbComp Value) (cap : Nat) (bounded : draw.IsTotalQueryBound cap) :
    B (RegistrationNativeBeaconFrontend.sample draw) cap := by
  intro before
  simp only [lower_sample, IsTotalQueryBound, isQueryBound_map_iff]
  have native := RegistrationNativeMldsaCoinPrimitives.sampled draw cap bounded before.2.2.server.world.world.1
  have mapped : (Prod.map id RegistrationWorldCoinCompiler.eraseCoin <$>
      (PqxdhRecordLiftWorld.sampled draw).run before.2.2.server.world.world.1).IsTotalQueryBound cap := by
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using native
  rw [← RegistrationWorldCoinCompiler.coins_erase] at mapped
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using mapped

private theorem hash (request : registration.HashRequest) : B (RegistrationNativeBeaconFrontend.hash request) 64 :=
  effect setup checks representation created _ 64
    (RegistrationNativeMldsaCoinPrimitives.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))

private theorem lower_map
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (observe : Value → Next) :
    lower setup checks representation created (observe <$> work) = observe <$> lower setup checks representation created work := by
  funext before
  simp only [lower, StateT.run, state_map_apply, simulateQ_map, Functor.map_map, Prod.map, id_eq]

private theorem map_bound
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (observe : Value → Next) (cap : Nat) (bounded : B work cap) : B (observe <$> work) cap := by
  intro before
  simpa only [lower_map, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff] using bounded before

private theorem decap (qDecap : Nat)
    (bounded : ∀ secret ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (handle : Nat) (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) :
    B (RegistrationNativeBeaconFrontend.kem (.inr (.inl (.decapsulate handle ciphertext)))) qDecap := by
  intro before
  simp only [lower, RegistrationNativeBeaconFrontend.kem, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff, state_lift_apply, state_map_apply, simulateQ_map,
    simulateQ_spec_query, RegistrationNativeExperiment.trusted]
  apply isTotalQueryBound_bind (n₂ := 0)
  · apply RegistrationNativeMldsaCoinPrimitives.sampled
    simp only [RegistrationNativeKemInterface.source, PqxdhLiveKemBirth.poolImpl, StateT.run,
      IsTotalQueryBound, isQueryBound_map_iff]
    cases found : before.2.2.pool.keys[handle]? with
    | none => simp only [pure_bind, isQueryBound_pure]
    | some key => simpa only [found, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using bounded key.2 ciphertext
  · intro result
    trivial

private theorem other (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationNativeKemInterface.OtherRequest) :
    ((RegistrationNativeKemBackend.beaconOther setup owner.prekeyScalar query).run
      ⟨owner.identitySeed, some oneTime, some owner.kemHandle⟩).IsTotalQueryBound 0 := by
  cases query with
  | convertPublic key => simp [RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive,
      RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend, StateT.run,
      StateT.monad_pure_def, StateT.pure, IsTotalQueryBound]
  | convertSecret role => cases role <;> simp [RegistrationNativeKemBackend.beaconOther,
      RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, IsTotalQueryBound]
  | generate role => cases role; simp [RegistrationNativeKemBackend.beaconOther,
      RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, IsTotalQueryBound]
  | dh request => cases role : request.secret_role <;> simp [RegistrationNativeKemBackend.beaconOther,
      RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, role, StateT.run, StateT.monad_pure_def, StateT.pure, IsTotalQueryBound]

private theorem mono
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (first rest : Nat) (bounded : B work first) (larger : first ≤ rest) : B work rest :=
  fun before => (bounded before).mono larger

private theorem other_source (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationNativeKemInterface.OtherRequest) (cap : Nat) :
    B (RegistrationNativeBeaconFrontend.sample (Prod.fst <$>
      (RegistrationNativeKemBackend.beaconOther setup owner.prekeyScalar query).run
        ⟨owner.identitySeed, some oneTime, some owner.kemHandle⟩)) cap := by
  apply mono setup checks representation created _ 0 cap _ (Nat.zero_le cap)
  apply sample setup checks representation created _ 0
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using other setup owner oneTime query

private theorem primitive (qDecap : Nat)
    (bounded : ∀ secret ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    B (RegistrationNativeBeaconFrontend.primitive setup owner oneTime query) qDecap := by
  cases query with
  | convertPublic key =>
      convert other_source setup checks representation created owner oneTime (.convertPublic key) qDecap using 1
      · rfl
      · simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
          RegistrationNativeKemInterface.other, simulateQ_spec_query]
        rfl
  | convertSecret role =>
      convert other_source setup checks representation created owner oneTime (.convertSecret role) qDecap using 1
      · rfl
      · simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
          RegistrationNativeKemInterface.other, simulateQ_spec_query]
        rfl
  | generate role =>
      convert other_source setup checks representation created owner oneTime (.generate role) qDecap using 1
      · rfl
      · simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
          RegistrationNativeKemInterface.other, simulateQ_spec_query]
        rfl
  | dh request =>
      convert other_source setup checks representation created owner oneTime (.dh request) qDecap using 1
      · rfl
      · simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
          RegistrationNativeKemInterface.other, simulateQ_spec_query]
        rfl
  | encapsulate key =>
      simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]
      exact pure_bound setup checks representation created _ _
  | decapsulate ciphertext =>
      cases ciphertext with
      | none =>
          simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]
          exact pure_bound setup checks representation created _ _
      | some ciphertext =>
          simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon, simulateQ_map, simulateQ_spec_query]
          exact map_bound setup checks representation created _ _ _
            (decap setup checks representation created qDecap bounded owner.kemHandle (PqxdhPhase2InputBytes.ciphertext ciphertext))

private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (state : S) : (modify change : StateT S m Unit) state = pure ((), change state) := rfl

private theorem updateEnv (change : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State →
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    B (RegistrationNativeBeaconFrontend.updateEnv change) 0 := by
  intro before
  simp only [lower, RegistrationNativeBeaconFrontend.updateEnv, StateT.run, state_lift_apply, state_map_apply,
    state_modify_apply, state_pure_apply, simulateQ_pure, map_pure, IsTotalQueryBound, isQueryBound_pure]

private theorem updatePhase (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    B (RegistrationNativeBeaconFrontend.updatePhase index phase) 0 := by
  intro before
  simp only [lower, RegistrationNativeBeaconFrontend.updatePhase, StateT.run, state_modify_apply,
    state_pure_apply, simulateQ_pure, map_pure, IsTotalQueryBound, isQueryBound_pure]

private theorem agreementCore (qDecap : Nat)
    (bounded : ∀ secret ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) :
    B (RegistrationNativeBeaconFrontend.agreementCore setup owner oneTime query) qDecap := by
  cases query with
  | convertPublic key => convert primitive setup checks representation created qDecap bounded owner oneTime (.convertPublic key) using 1 <;> rfl
  | convertSecret role => convert primitive setup checks representation created qDecap bounded owner oneTime (.convertSecret role) using 1 <;> rfl
  | generate role => convert primitive setup checks representation created qDecap bounded owner oneTime (.generate role) using 1 <;> rfl
  | encapsulate key => convert primitive setup checks representation created qDecap bounded owner oneTime (.encapsulate key) using 1 <;> rfl
  | decapsulate ciphertext => convert primitive setup checks representation created qDecap bounded owner oneTime (.decapsulate ciphertext) using 1 <;> rfl
  | dh request => convert primitive setup checks representation created qDecap bounded owner oneTime (.dh request) using 1 <;> rfl
  | root request => exact pure_bound setup checks representation created _ _

private theorem agreement (qDecap : Nat)
    (bounded : ∀ secret ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) :
    B (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query) qDecap := by
  unfold RegistrationNativeBeaconFrontend.agreement
  simpa only [Nat.zero_add] using bind_bound setup checks representation created _ _ 0 qDecap
    (updateEnv setup checks representation created _) (fun _ => agreementCore setup checks representation created qDecap bounded owner oneTime query)

private theorem authentication (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    B (RegistrationNativeBeaconFrontend.authentication setup source query)
      (if RegistrationResponseHashBounds.IsHash query then 64 else 0) := by
  unfold RegistrationNativeBeaconFrontend.authentication
  cases query with
  | hash request =>
      change B _ 64
      exact bind_bound setup checks representation created _ _ 64 0
        (hash setup checks representation created request) (fun _ => pure_bound setup checks representation created _ _)
  | mldsa request | ed25519 request => exact pure_bound setup checks representation created _ _

private theorem simulated {Query : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))
    (cost : Nat) (step : ∀ query, B (implementation query) cost)
    (work : OracleComp queries Value) (cap : Nat) (bounded : work.IsTotalQueryBound cap) :
    B (simulateQ implementation work) (cap * cost) := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => exact pure_bound setup checks representation created _ _
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query]
      have rest := bind_bound setup checks representation created _ _ cost ((cap - 1) * cost)
        (step query) (fun reply => ih reply _ (bounded.2 reply))
      have same : cost + (cap - 1) * cost = cap * cost := by
        simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using
          congrArg (fun count => count * cost) (Nat.sub_add_cancel bounded.1)
      simpa only [same] using rest

private theorem simulated_authentication
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP RegistrationResponseHashBounds.IsHash cap) :
    B (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) work) (64 * cap) := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => exact pure_bound setup checks representation created _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query]
      apply mono setup checks representation created _ _ (64 * cap)
        (bind_bound setup checks representation created _ _
          (if RegistrationResponseHashBounds.IsHash query then 64 else 0)
          (64 * (if RegistrationResponseHashBounds.IsHash query then cap - 1 else cap))
          (authentication setup checks representation created query) (fun reply => ih reply _ (bounded.2 reply)))
      by_cases active : RegistrationResponseHashBounds.IsHash query
      · have positive := bounded.1.resolve_left (not_not.mpr active)
        simp only [active, ite_true]
        omega
      · simp only [active, ite_false, Nat.zero_add]
        exact le_rfl

private theorem native_record (wire : RegistrationNativeWire.Wire) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (cache : CtxRomAuth.CtxRO.QueryCache) :
    ((MldsaSharedSource.implementation setup.source wire.frameWrite (.inr query)).run ((), cache)).IsTotalQueryBound
      (64 * if RawCtxMixedOwner.callKind query = .hash then 1 else 0) := by
  simpa only [MldsaSharedSource.implementation, MldsaSharedNative.primitives, PqxdhDeploymentNative.primitives,
    RegistrationNativeWire.ledgerCodec] using
    PqxdhRecordLiftWorldBudget.primitive_uniform_bound setup (RegistrationNativeWire.ledgerCodec wire) query cache

private theorem record_impl (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    ((RegistrationRecordPrimitives.implementation setup.source wire.frameWrite query).run ((), ∅)).IsTotalQueryBound
      (if RegistrationNativeMldsaCoinFinishSyntax.IsHash query then 64 else 0) := by
  cases query with
  | rootKdf request => trivial
  | initialKdf request => trivial
  | adHash request =>
      rw [RegistrationRecordPrimitives.ad_hash_exact]
      simpa only [RegistrationNativeMldsaCoinFinishSyntax.IsHash, ite_true, IsTotalQueryBound, isQueryBound_map_iff] using
        CtxComputationalSecurity.ctxRandomOracle_total_query_bound
          ((), BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) ∅
  | hash transcript =>
      rw [RegistrationRecordPrimitives.hash_exact]
      simpa only [RegistrationNativeMldsaCoinFinishSyntax.IsHash, ite_true, IsTotalQueryBound, isQueryBound_map_iff] using
        CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), PqxdhRefinement.absBytes transcript.bytes) ∅
  | ratchetKdf request =>
      simpa only [RegistrationRecordPrimitives.implementation, QueryImpl.apply_compose,
        RegistrationRecordPrimitives.callbacks, MldsaSharedNative.recordLift, simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_map, StateT.run_pure, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff,
        RegistrationNativeMldsaCoinFinishSyntax.IsHash, RawCtxMixedOwner.callKind, reduceCtorEq, ite_false, Nat.mul_zero] using
        native_record setup wire (.inl request) ∅
  | «seal» request =>
      simpa only [RegistrationRecordPrimitives.implementation, QueryImpl.apply_compose,
        RegistrationRecordPrimitives.callbacks, MldsaSharedNative.recordLift, simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_map, StateT.run_pure, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff,
        RegistrationNativeMldsaCoinFinishSyntax.IsHash, RawCtxMixedOwner.callKind, reduceCtorEq, ite_false, Nat.mul_zero] using
        native_record setup wire (.inr (.inl (RegistrationRecordPrimitives.sealInput request))) ∅
  | openAead request =>
      simpa only [RegistrationRecordPrimitives.implementation, QueryImpl.apply_compose,
        RegistrationRecordPrimitives.callbacks, MldsaSharedNative.recordLift, simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_map, StateT.run_pure, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff,
        RegistrationNativeMldsaCoinFinishSyntax.IsHash, RawCtxMixedOwner.callKind, reduceCtorEq, ite_false, Nat.mul_zero] using
        native_record setup wire (.inr (.inr (.inl (RegistrationRecordPrimitives.openInput request)))) ∅
  | write request => cases request with
    | Raw parts => trivial
    | Frame parts sequence sender =>
      simpa only [RegistrationRecordPrimitives.implementation, QueryImpl.apply_compose,
        RegistrationRecordPrimitives.callbacks, MldsaSharedNative.recordLift, simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_map, StateT.run_pure, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff,
        RegistrationNativeMldsaCoinFinishSyntax.IsHash, RawCtxMixedOwner.callKind, reduceCtorEq, ite_false, Nat.mul_zero] using
        native_record setup wire (.inr (.inr (.inr (.inr ⟨sequence, sender, RegistrationRecordPrimitives.partsBytes parts⟩)))) ∅

private noncomputable def recordLeaf (wire : RegistrationNativeWire.Wire) :
    QueryImpl RegistrationRecordPrimitives.Spec
      (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)
  | .adHash request => do
      let digest ← RegistrationNativeBeaconFrontend.hash request
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .hash transcript => do
      let digest ← RegistrationNativeBeaconFrontend.hash (.Single (Std.Array.to_slice transcript.bytes))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | query => RegistrationNativeBeaconFrontend.sample (Prod.fst <$>
      (RegistrationRecordPrimitives.implementation setup.source wire.frameWrite query).run ((), ∅))

private theorem recordSample (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain)
    (notHash : ¬ RegistrationNativeMldsaCoinFinishSyntax.IsHash query) :
    B (RegistrationNativeBeaconFrontend.sample (Prod.fst <$>
      (RegistrationRecordPrimitives.implementation setup.source wire.frameWrite query).run ((), ∅))) 0 := by
  apply sample setup checks representation created _ 0
  simpa only [IsTotalQueryBound, isQueryBound_map_iff, notHash, ite_false] using record_impl setup wire query

private theorem recordLeaf_bound (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    B (recordLeaf setup wire query) (if RegistrationNativeMldsaCoinFinishSyntax.IsHash query then 64 else 0) := by
  cases query with
  | hash transcript =>
      exact bind_bound setup checks representation created _ _ 64 0 (hash setup checks representation created _)
        (fun _ => pure_bound setup checks representation created _ _)
  | adHash request =>
      exact bind_bound setup checks representation created _ _ 64 0 (hash setup checks representation created _)
        (fun _ => pure_bound setup checks representation created _ _)
  | rootKdf request => exact recordSample setup checks representation created wire (.rootKdf request) (fun impossible => impossible.elim)
  | initialKdf request => exact recordSample setup checks representation created wire (.initialKdf request) (fun impossible => impossible.elim)
  | ratchetKdf request => exact recordSample setup checks representation created wire (.ratchetKdf request) (fun impossible => impossible.elim)
  | «seal» request => exact recordSample setup checks representation created wire (.seal request) (fun impossible => impossible.elim)
  | openAead request => exact recordSample setup checks representation created wire (.openAead request) (fun impossible => impossible.elim)
  | write request => exact recordSample setup checks representation created wire (.write request) (fun impossible => impossible.elim)

private theorem record (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    B (RegistrationNativeBeaconFrontend.record setup wire query)
      (if RegistrationNativeMldsaCoinFinishSyntax.IsHash query then 64 else 0) := by
  have same : RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) setup wire query = (do
        RegistrationNativeBeaconFrontend.updateEnv fun env =>
          { env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query] }
        recordLeaf setup wire query) := rfl
  rw [same]
  simpa only [Nat.zero_add] using bind_bound setup checks representation created _ _ 0
    (if RegistrationNativeMldsaCoinFinishSyntax.IsHash query then 64 else 0)
    (updateEnv setup checks representation created _) (fun _ => recordLeaf_bound setup checks representation created wire query)

private theorem simulated_hash (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativeMldsaCoinFinishSyntax.IsHash cap) :
    B (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) work) (64 * cap) := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => exact pure_bound setup checks representation created _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query]
      apply mono setup checks representation created _ _ (64 * cap)
        (bind_bound setup checks representation created _ _
          (if RegistrationNativeMldsaCoinFinishSyntax.IsHash query then 64 else 0)
          (64 * (if RegistrationNativeMldsaCoinFinishSyntax.IsHash query then cap - 1 else cap))
          (record setup checks representation created wire query) (fun reply => ih reply _ (bounded.2 reply)))
      by_cases active : RegistrationNativeMldsaCoinFinishSyntax.IsHash query
      · have positive := bounded.1.resolve_left (not_not.mpr active)
        simp only [active, ite_true]
        omega
      · simp only [active, ite_false, Nat.zero_add]
        exact le_rfl

private theorem advance (owner : Nat) (phase : PqxdhRecordLiftInterface.InactivePhase) :
    B (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner phase))) 0 := by
  apply effect setup checks representation created _ 0
  intro before
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run, PqxdhRecordLiftWorld.chargeEffect]
  cases before.owners[owner]? with
  | none => trivial
  | some selected => cases selected with
    | established shell kernel => trivial
    | inactive previous => simp only; split <;> trivial

private theorem install (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    B (RegistrationNativeBeaconFrontend.effect (.inr (.installBeacon owner shell (.known kernel)))) 0 := by
  apply effect setup checks representation created _ 0
  intro before
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
    PqxdhRecordLiftWorld.installBeacon, StateT.run]
  split
  · simp only [PqxdhRecordLiftWorld.resolve, state_pure_apply, pure_bind,
      IsTotalQueryBound, isQueryBound_pure]
  · trivial

private theorem abort (owner : RegistrationNativeBeaconFrontend.Owner source) :
    B (RegistrationNativeBeaconFrontend.abort owner) 0 :=
  bind_bound setup checks representation created _ _ 0 0 (advance setup checks representation created owner.worldOwner .aborted)
    (fun _ => pure_bound setup checks representation created _ _)

private theorem abort_return (owner : RegistrationNativeBeaconFrontend.Owner source) (value : Value) :
    B (RegistrationNativeBeaconFrontend.abort owner *> pure value) 0 := by
  simpa only [seqRight_eq_bind] using bind_bound setup checks representation created _ _ 0 0
    (abort setup checks representation created owner) (fun _ => pure_bound setup checks representation created value 0)

private noncomputable def fromRecord (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (opened : RustM RegistrationBeaconRecordExecutor.Result) :
    RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Pqxdh.Bytes)) :=
  match opened with
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok established) => do
      let shell : PqxdhRecordLiftInterface.BeaconShell :=
        ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩
      let installed : Bool ← RegistrationNativeBeaconFrontend.effect
        (.inr (.installBeacon owner.worldOwner shell (.known established.kernel)))
      if installed then
        RegistrationNativeBeaconFrontend.updatePhase index
          (.established ⟨established.control, established.binding, established.application⟩)
        pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
      else RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)

private theorem fromRecord_bound (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (opened : RustM RegistrationBeaconRecordExecutor.Result) : B (fromRecord index owner opened) 0 := by
  cases opened with
  | fail error | div => exact abort_return setup checks representation created owner _
  | ok result => cases result with
    | Err aborted => exact abort_return setup checks representation created owner _
    | Ok established =>
      unfold fromRecord
      apply bind_bound setup checks representation created _ _ 0 0 (install setup checks representation created _ _ _)
      intro installed
      cases installed with
      | false => exact abort_return setup checks representation created owner _
      | true =>
          exact bind_bound setup checks representation created _ _ 0 0
            (updatePhase setup checks representation created _ _) (fun _ => pure_bound setup checks representation created _ _)

private noncomputable def fromAgreement (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (agreed : RustM agreement.AgreementEffect) :
    RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Pqxdh.Bytes)) :=
  match agreed with
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok (.BeaconComplete completed) => do
      let opened ← simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
      fromRecord index owner opened
  | .ok _ => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)

private theorem fromAgreement_bound (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (agreed : RustM agreement.AgreementEffect) :
    B (fromAgreement setup wire index owner agreed) 64 := by
  cases agreed with
  | fail error | div =>
      exact mono setup checks representation created _ 0 64
        (abort_return setup checks representation created owner _) (by omega)
  | ok phase => cases phase with
    | BeaconComplete completed =>
      exact bind_bound setup checks representation created _ _ 64 0
        (simulated_hash setup checks representation created wire _ 1
          (RegistrationNativeMldsaCoinFinishSyntax.begin_bound completed))
        (fun _ => fromRecord_bound setup checks representation created index owner _)
    | _ =>
        exact mono setup checks representation created _ 0 64
          (abort_return setup checks representation created owner _) (by omega)

private noncomputable def fromAuthentication (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : RustM RegistrationResponseExecutor.ResponseResult) :
    RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Pqxdh.Bytes)) :=
  match authenticated with
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok accepted) => do
      let agreed ← simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime)
        (RegistrationAgreementExecutor.beacon accepted)
      fromAgreement setup wire index owner agreed

private theorem fromAuthentication_bound (qDecap : Nat)
    (bounded : ∀ secret ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : RustM RegistrationResponseExecutor.ResponseResult) :
    B (fromAuthentication setup wire index owner oneTime authenticated) (9 * qDecap + 64) := by
  cases authenticated with
  | fail error | div =>
      exact mono setup checks representation created _ 0 _
        (abort_return setup checks representation created owner _) (by omega)
  | ok result => cases result with
    | Err aborted =>
        exact mono setup checks representation created _ 0 _
          (abort_return setup checks representation created owner _) (by omega)
    | Ok accepted =>
      exact bind_bound setup checks representation created _ _ (9 * qDecap) 64
        (simulated setup checks representation created _ qDecap
          (agreement setup checks representation created qDecap bounded owner oneTime) _ 9
          (RegistrationNativeMldsaCoinAgreementSyntax.beacon accepted))
        (fun _ => fromAgreement_bound setup checks representation created wire index owner _)

private theorem finish (qDecap : Nat)
    (bounded : ∀ secret ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    B (RegistrationNativeBeaconFrontend.finish setup source wire index packet) (128 + (9 * qDecap + 64)) := by
  unfold RegistrationNativeBeaconFrontend.finish
  rw [← Nat.zero_add (128 + (9 * qDecap + 64))]
  apply bind_bound setup checks representation created _ _ 0 _ (get_bound setup checks representation created)
  intro owners
  cases owners[index]? with
  | none => exact pure_bound setup checks representation created _ _
  | some owner =>
    simp only
    cases owner.phase with
    | fresh | freshWithCoins _ | established _ | aborted _ => exact pure_bound setup checks representation created _ _
    | initSent pending oneTime =>
      simp only
      cases pending.aborted_state with
      | fail error | div => exact pure_bound setup checks representation created _ _
      | ok aborted =>
        rw [← Nat.zero_add (128 + (9 * qDecap + 64))]
        apply bind_bound setup checks representation created _ _ 0 _ (updatePhase setup checks representation created _ _)
        intro unused
        change B ((simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))) >>=
            fromAuthentication setup wire index owner oneTime) (128 + (9 * qDecap + 64))
        apply bind_bound setup checks representation created _ _ 128 (9 * qDecap + 64)
        · exact simulated_authentication setup checks representation created _ 2
            (RegistrationResponseHashBounds.begin_hash_bound pending _)
        · exact fromAuthentication_bound setup checks representation created qDecap bounded wire index owner oneTime

private theorem source_lower
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- The original finish controller has two response-authentication hash slots, nine agreement slots and one shared first-record hash. Only indexed decapsulation can add primitive uniforms. -/
def bill (qDecap : Nat) : Nat := 192 + 9 * qDecap

/-- The complete free original typed finish callback obeys its literal ordinary-sampling bill for all raw ML replies and all failed source continuations. -/
theorem handler (source : Source) (setup : Setup base KemSK) (checks : Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source) (qDecap : Nat)
    (decapsulation : ∀ secret ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential
      (.inr (.finish index packet))).run before).IsQueryBoundP IsCoin (bill qDecap) := by
  apply RegistrationNativeMldsaCoinPrimitives.ordinary
  change ((RegistrationNativeExperiment.beacon setup checks representation created
    (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before).IsTotalQueryBound (bill qDecap)
  rw [source_lower]
  apply IsTotalQueryBound.mono (n₁ := 128 + (9 * qDecap + 64)) _ (by unfold bill; omega)
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using finish setup checks representation created qDecap decapsulation wire index packet
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))

end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinish.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinish.handler
