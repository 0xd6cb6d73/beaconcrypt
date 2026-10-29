-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface

/-! The actual CommonCompiler material service is interpreted on the current environment and has the exact independent-key/full-Common representation. Every query returns its actual new chronological receipt log. The whole-component lift preserves the other environment fields because the concrete service never modifies them; arbitrary outer environment continuations still use the separately proved lower_bind. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePairedServerService (Common PublicSpec)
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec)
open RegistrationNativeG3MaterializedTracedServerInterface (Private Local interface source lower_run put effect)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {KemSK KeyState Auxiliary Value : Type}

private theorem state_map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

noncomputable def nativeEffect : QueryImpl (EnvEffects n)
    (StateT (RegistrationNativeG2Trace.State × PqxdhRecordLiftWorld.State n) ProbComp) := fun query before =>
  (fun result => (result.1, (before.1, result.2))) <$> (PqxdhRecordLiftWorld.effects query).run before.2

private theorem native_program (work : OracleComp (EnvEffects n) Value)
    (before : RegistrationNativeG2Trace.State × PqxdhRecordLiftWorld.State n) :
    (simulateQ nativeEffect work).run before =
      (fun result => (result.1, (before.1, result.2))) <$> (simulateQ PqxdhRecordLiftWorld.effects work).run before.2 :=
  (OracleComp.map_run_simulateQ_eq_of_query_map_eq PqxdhRecordLiftWorld.effects nativeEffect
    (fun world => (before.1, world)) (fun _ _ => rfl) work before.2).symm

noncomputable def target (full : Bool)
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) :
    QueryImpl (PublicSpec n) (StateT (RegistrationNativeG3MaterializedTracedServerFrontend.State n KeyState) ProbComp) :=
  if full then RegistrationNativeG3MaterializedTracedServerFrontend.known hkdf writer sign seeds service
  else RegistrationNativeG3MaterializedTracedServerFrontend.thin hkdf writer sign seeds service

/-- Every actual environment AST reaches the same full World while retaining the independently owned key state. -/
theorem effects_source (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (work : OracleComp (EnvEffects n) Value) (before : Private n KeyState) :
    (simulateQ (interface full seeds service fallback) (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run before =
      (fun result => (result.1, (before.1, result.2))) <$> (simulateQ (effect full seeds) work).run before.2 := by
  rw [← QueryImpl.simulateQ_compose]
  have step : interface full seeds service fallback ∘ₛ RegistrationBeaconReferenceCompiler.effect =
      (fun query current => (fun result => (result.1, (current.1, result.2))) <$> (effect full seeds query).run current.2 :
        QueryImpl (EnvEffects n) (StateT (Private n KeyState) ProbComp)) := by
    funext query
    simp only [QueryImpl.compose, RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query, interface]
  rw [step]
  exact (OracleComp.map_run_simulateQ_eq_of_query_map_eq (effect full seeds) _
    (fun world => (before.1, world)) (fun _ _ => rfl) work before.2).symm

/-- Native publication's actual hash/coin effects are unchanged by fixed-table installation materialization. -/
theorem effect_primitive (full : Bool) (seeds : Seeds n) (query : (EnvEffects n).Domain)
    (primitive : RegistrationNativeG3Common.Primitive query) : effect full seeds query = nativeEffect query := by
  funext before
  cases query with
  | inl coin =>
      cases full <;> simp [effect, nativeEffect, RegistrationNativeG3MaterializedTracedServerCommon.effect,
        RegistrationNativeG3MaterializedTracedServerCommon.effectQuery, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
        RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.effect, Functor.map_map, StateT.run]
  | inr query => cases query with
    | hash bytes =>
        cases full <;> simp [effect, nativeEffect, RegistrationNativeG3MaterializedTracedServerCommon.effect,
          RegistrationNativeG3MaterializedTracedServerCommon.effectQuery, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
          RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.effect, Functor.map_map, StateT.run]
    | _ => exact primitive.elim

private theorem primitive_program (full : Bool) (seeds : Seeds n) (work : OracleComp (EnvEffects n) Value)
    (primitive : AllQueriesSatisfy work RegistrationNativeG3Common.Primitive) :
    simulateQ (effect full seeds) work = simulateQ nativeEffect work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp primitive
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [effect_primitive full seeds query first]
      congr 1
      funext reply
      exact ih reply (later reply)

private theorem publication_source (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (before : Local n Auxiliary KeyState) :
    (source full seeds service fallback hkdf writer sign (.inr (.inl query))).run before =
      (fun result => (result.1, put before (before.2.1, result.2))) <$>
        (RegistrationNativeG3MaterializedTracedServerCommon.onCommon
          (RegistrationNativeG3Common.publication hkdf writer sign query)).run
          (before.2.2.1, (before.1.receipts, before.2.2.2)) := by
  change (RegistrationNativeG3MaterializedTracedServerInterface.lower (interface full seeds service fallback)
    (RegistrationNativeCommonCompiler.publication RegistrationBeaconReferenceCompiler.effect hkdf writer sign query)).run before = _
  rw [lower_run]
  have compiled : (RegistrationNativeCommonCompiler.publication (RegistrationBeaconReferenceCompiler.effect (n := n) (KemSK := KemSK)) hkdf writer sign query).run before.1 =
      (fun result => (result.1, { before.1 with receipts := result.2 })) <$>
        simulateQ (RegistrationBeaconReferenceCompiler.effect (n := n) (KemSK := KemSK)) ((RegistrationBoundSourceCompiler.compiler hkdf writer sign query).run before.1.receipts) := rfl
  rw [compiled, simulateQ_map, StateT.run_map, effects_source]
  rw [primitive_program full seeds _ (RegistrationNativeG3Common.compiler_primitive hkdf writer sign query before.1.receipts)]
  rw [native_program]
  simp only [RegistrationNativeG3Common.publication, RegistrationNativeG3MaterializedTracedServerCommon.onCommon, StateT.run, Functor.map_map, put]
  simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk, Functor.map_map]

private theorem effect_common (full : Bool) (seeds : Seeds n) (query : (EnvEffects n).Domain)
    (before : RegistrationNativeG3MaterializedTracedServerCommon.State n) :
    (fun result => (result.1, (result.2.1, (before.2.1, result.2.2)))) <$>
      (effect full seeds query).run (before.1, before.2.2) =
      (RegistrationNativeG3MaterializedTracedServerCommon.effect full seeds query).run before := by
  cases full <;> cases query with
  | inl coin => simp [effect, RegistrationNativeG3MaterializedTracedServerCommon.effect, RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.effect, Functor.map_map, StateT.run]
  | inr query => cases query with
    | installServer keyId binding kernel => cases kernel <;> simp [effect, RegistrationNativeG3MaterializedTracedServerCommon.effect,
        RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.effect, Functor.map_map, StateT.run]
    | installBeacon owner shell kernel => cases kernel <;> simp [effect, RegistrationNativeG3MaterializedTracedServerCommon.effect,
        RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.effect, Functor.map_map, StateT.run]
    | _ => simp [effect, RegistrationNativeG3MaterializedTracedServerCommon.effect,
        RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.effect, Functor.map_map, StateT.run]

/-- Every actual service query preserves its complete current environment and matches the shared key/receipt/World representation. -/
theorem query (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (PublicSpec n).Domain) (before : Local n Auxiliary KeyState) :
    (source full seeds service fallback hkdf writer sign query).run before =
      (fun result => (result.1, put before result.2)) <$> (target full hkdf writer sign seeds service query).run (RegistrationNativeG3MaterializedTracedServerInterface.get before) := by
  have env_same : { before.1 with receipts := before.1.receipts } = before.1 := by
    cases before.1
    rfl
  rcases query with message | publication | query
  · change (RegistrationNativeG3MaterializedTracedServerInterface.lower (interface full seeds service fallback)
      (StateT.lift (RegistrationServerOpenReferenceCompiler.demand message))).run before = _
    rw [lower_run, StateT.run_lift, bind_pure_comp]
    cases full <;> simp only [RegistrationServerOpenReferenceCompiler.demand,
      simulateQ_map, simulateQ_spec_query, interface,
      StateT.run_map, target, Bool.false_eq_true, ite_false, ite_true,
      RegistrationNativeG3MaterializedTracedServerFrontend.known, RegistrationNativeG3MaterializedTracedServerFrontend.thin,
      Functor.map_map, RegistrationNativeG3MaterializedTracedServerInterface.get, put]
    all_goals
      unfold RegistrationNativeG3MaterializedTracedServerInterface.keys RegistrationNativeG3MaterializedTracedServerFrontend.keys
      simp only [StateT.run, Functor.map_map, Bool.false_eq_true, ite_false, ite_true]
  · rw [publication_source]
    cases full <;> simp only [target, Bool.false_eq_true, ite_false, ite_true,
      RegistrationNativeG3MaterializedTracedServerFrontend.known, RegistrationNativeG3MaterializedTracedServerFrontend.thin,
      RegistrationNativeG3MaterializedTracedServerInterface.get, put]
    all_goals
      unfold RegistrationNativeG3MaterializedTracedServerFrontend.common
      simp only [RegistrationNativeG3MaterializedTracedServerCommon.handler, RegistrationNativeG3MaterializedTracedServerCommon.onCommon,
        StateT.run, Functor.map_map, StateT.run]
      rfl
  · change (RegistrationNativeG3MaterializedTracedServerInterface.lower (interface full seeds service fallback)
      (StateT.lift (RegistrationBeaconReferenceCompiler.effect query))).run before = _
    rw [lower_run, StateT.run_lift, bind_pure_comp]
    simp only [RegistrationBeaconReferenceCompiler.effect, simulateQ_map, simulateQ_spec_query, interface, StateT.run]
    have actual := congrArg (fun distribution => (fun result => (result.1, put before (before.2.1, result.2))) <$> distribution)
      (effect_common full seeds query (before.2.2.1, (before.1.receipts, before.2.2.2)))
    cases full <;>
      simp only [target, Bool.false_eq_true, ite_false, ite_true,
        RegistrationNativeG3MaterializedTracedServerInterface.get, put,
        RegistrationNativeG3MaterializedTracedServerFrontend.known, RegistrationNativeG3MaterializedTracedServerFrontend.thin]
    all_goals
      unfold RegistrationNativeG3MaterializedTracedServerFrontend.common
      simp only [StateT.run, Functor.map_map, put, RegistrationNativeG3MaterializedTracedServerCommon.handler, env_same] at actual ⊢
      simp only [state_map_apply, Functor.map_map, Prod.map_def, id_eq, Prod.eta] at actual ⊢
      convert actual using 1; rfl

/-- Pure material components preserve every other environment field while threading their actual current chronological receipts. -/
theorem program (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (PublicSpec n) Value) (before : Local n Auxiliary KeyState) :
    (simulateQ (source full seeds service fallback hkdf writer sign) work).run before =
      (fun result => (result.1, put before result.2)) <$> (simulateQ (target full hkdf writer sign seeds service) work).run (RegistrationNativeG3MaterializedTracedServerInterface.get before) := by
  have get_put (current : RegistrationNativeG3MaterializedTracedServerFrontend.State n KeyState) :
      RegistrationNativeG3MaterializedTracedServerInterface.get (put before current) = current := rfl
  have put_put (current next : RegistrationNativeG3MaterializedTracedServerFrontend.State n KeyState) :
      put (put before current) next = put before next := rfl
  have put_get : put before (RegistrationNativeG3MaterializedTracedServerInterface.get before) = before := by
    cases before with
    | mk env privateState => cases env; rfl
  have mapped := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (target full hkdf writer sign seeds service) (source full seeds service fallback hkdf writer sign) (put before)
    (fun request current => by
      change (fun result => (result.1, put before result.2)) <$> (target full hkdf writer sign seeds service request).run current = _
      simpa only [get_put, put_put] using
        (query full seeds service fallback hkdf writer sign request (put before current)).symm)
    work (RegistrationNativeG3MaterializedTracedServerInterface.get before)
  change (simulateQ (source full seeds service fallback hkdf writer sign) work).run before =
    Prod.map id (put before) <$> (simulateQ (target full hkdf writer sign seeds service) work).run (RegistrationNativeG3MaterializedTracedServerInterface.get before)
  simpa only [put_get] using mapped.symm


end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource.effects_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource.effect_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource.effect_primitive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerSource.program
