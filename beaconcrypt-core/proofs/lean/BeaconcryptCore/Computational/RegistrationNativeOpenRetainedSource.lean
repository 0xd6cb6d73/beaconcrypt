-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenRetained
import BeaconcryptCore.Computational.RegistrationNativeProviderRetainedFrame
import BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter

/-! The open retained client and the counted provider interpreter use the same literal KEM provider. The executable client holds an empty placeholder pool; this source map moves the actual pool and provider state to the external service and forgets only the private uniform counter. Ordinary World components use their proved bilateral mask laws. No equality between a real encapsulation and a candidate reply is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State)
open RegistrationNativeProviderInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev External (KemSK ProviderState : Type) := PqxdhLiveKemBirth.Pool KemSK × ProviderState
abbrev SourceState (n : Nat) (KemSK ProviderState : Type) := State n KemSK × ProviderState
abbrev OpenState (n : Nat) (KemSK ProviderState : Type) := State n KemSK × External KemSK ProviderState

def project (before : SourceState n KemSK ProviderState) : OpenState n KemSK ProviderState :=
  (RegistrationNativeOpenRetained.mask before.1, (before.1.pool, before.2))

def withBase (work : StateT (State n KemSK) (OracleComp RegistrationNativeRetainedService.Spec) Value) :
    StateT (SourceState n KemSK ProviderState) (OracleComp RegistrationNativeRetainedService.Spec) Value :=
  fun before => (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

noncomputable def routed (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) :
    StateT (SourceState n KemSK ProviderState) (OracleComp RegistrationNativeRetainedService.Spec)
      ((RegistrationNativePublicFrontend.RoutedKem KemSK).Range query) := fun before =>
  (fun result => (result.1.1,
    ({ before.1 with world := result.2, pool := result.1.2.1 }, result.1.2.2))) <$>
      simulateQ RegistrationNativePublicRetained.coins
        ((PqxdhRecordLiftWorld.sampled ((provider query).run (before.1.pool, before.2))).run before.1.world)

noncomputable def source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (SourceState n KemSK ProviderState) (OracleComp RegistrationNativeRetainedService.Spec))
  | .inl (.inr (.inr query)) => routed provider query
  | query => withBase (RegistrationNativePublicRetained.compiler setup wire route sign query)

def close (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativeOpenRetained.Spec KemSK)
      (StateT (External KemSK ProviderState) (OracleComp RegistrationNativeRetainedService.Spec))
  | .inl query => StateT.lift (RegistrationNativeRetainedService.Spec.query query)
  | .inr query => fun before => simulateQ RegistrationNativePublicRetained.coins ((provider query).run before)

noncomputable def reference (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (OpenState n KemSK ProviderState) (OracleComp RegistrationNativeRetainedService.Spec)) :=
  ((close provider).mapStateTBase (RegistrationNativeOpenRetained.compiler setup wire route sign)).flattenStateT

/-- Closing the base branch preserves the full external private pool/provider state through arbitrary adaptive base work. -/
theorem base_program (provider : Provider KemSK ProviderState)
    (work : OracleComp RegistrationNativeRetainedService.Spec Value) (before : External KemSK ProviderState) :
    (simulateQ (close provider) (simulateQ RegistrationNativeOpenRetained.baseLift work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : close provider ∘ₛ RegistrationNativeOpenRetained.baseLift =
      (QueryImpl.ofLift RegistrationNativeRetainedService.Spec (OracleComp RegistrationNativeRetainedService.Spec)).liftTarget
        (StateT (External KemSK ProviderState) (OracleComp RegistrationNativeRetainedService.Spec)) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- The counted provider's reply, pool and provider state are exact after the stated uniform-counter projection. -/
theorem routed_project (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : SourceState n KemSK ProviderState) :
    Prod.map id project <$> (routed provider query).run before =
      (fun result => (result.1, (RegistrationNativeOpenRetained.mask before.1, result.2))) <$>
        simulateQ RegistrationNativePublicRetained.coins ((provider query).run (before.1.pool, before.2)) := by
  have actual := congrArg (fun work => simulateQ RegistrationNativePublicRetained.coins work)
    (RegistrationNativeKemWorldUniform.sampled_mask ((provider query).run (before.1.pool, before.2)) before.1.world)
  simp only [simulateQ_map] at actual
  have mapped := congrArg (fun work => (fun result =>
    (result.1.1, ({ before.1 with world := result.2, pool := (PqxdhLiveKemBirth.empty : PqxdhLiveKemBirth.Pool KemSK) }, result.1.2))) <$> work) actual
  simp only [routed, StateT.run, Functor.map_map, project, RegistrationNativeOpenRetained.mask, Prod.map_def, id_eq]
  simp only [Functor.map_map, Prod.map_def, id_eq] at mapped
  convert mapped using 1 <;> rfl

private def replacePool (pool : PqxdhLiveKemBirth.Pool KemSK) (before : State n KemSK) : State n KemSK :=
  { before with pool := pool }

private theorem world_pool (pool : PqxdhLiveKemBirth.Pool KemSK)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) (before : State n KemSK) :
    Prod.map id (replacePool pool) <$> (RegistrationNativePublicInterpreter.world work).run before =
      (RegistrationNativePublicInterpreter.world work).run (replacePool pool before) := by
  simp only [RegistrationNativePublicInterpreter.world, StateT.run, replacePool, Functor.map_map, Prod.map_def, id_eq]

private theorem effects_pool (pool : PqxdhLiveKemBirth.Pool KemSK)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) (before : State n KemSK) :
    Prod.map id (replacePool pool) <$> (simulateQ RegistrationNativePublicInterpreter.effect work).run before =
      (simulateQ RegistrationNativePublicInterpreter.effect work).run (replacePool pool before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (replacePool pool)
    (fun _ current => world_pool pool _ current) work before

private theorem publication_pool (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (query : RegistrationBoundPublication.Spec.Domain) (before : State n KemSK) :
    Prod.map id (replacePool pool) <$> (RegistrationNativePublicInterpreter.publication setup wire sign query).run before =
      (RegistrationNativePublicInterpreter.publication setup wire sign query).run (replacePool pool before) := by
  simp only [RegistrationNativePublicInterpreter.publication, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp]
  rw [← effects_pool pool _ before]
  simp only [Functor.map_map, replacePool, Prod.map_def, id_eq]

private theorem common_pool (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (query : (RegistrationNativePairedServerService.Common n).Domain)
    (before : State n KemSK) :
    Prod.map id (replacePool pool) <$> (RegistrationNativePublicInterpreter.common setup wire sign query).run before =
      (RegistrationNativePublicInterpreter.common setup wire sign query).run (replacePool pool before) := by
  cases query with
  | inl query => exact publication_pool setup wire sign pool query before
  | inr query => exact world_pool pool _ before

private theorem ordinary_pool (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value)
    (framed : ∀ pool before, Prod.map id (replacePool pool) <$> work.run before = work.run (replacePool pool before))
    (before : State n KemSK) :
    Prod.map id (replacePool before.pool) <$> (RegistrationNativePublicRetained.ordinary hmac work).run before =
      (RegistrationNativePublicRetained.ordinary hmac work).run before := by
  have same := congrArg (fun distribution => simulateQ RegistrationNativePublicRetained.coins
    (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac) distribution)) (framed before.pool before)
  have restored : replacePool before.pool before = before := by cases before; rfl
  rw [restored] at same
  simpa only [RegistrationNativePublicRetained.ordinary, StateT.run, simulateQ_map] using same

private theorem ordinary_project (provider : Provider KemSK ProviderState)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (work : RegistrationNativePublicInterpreter.M n KemSK Value)
    (framed : ∀ pool before, Prod.map id (replacePool pool) <$> work.run before = work.run (replacePool pool before))
    (natural : ∀ before, Prod.map id RegistrationNativeOpenRetained.mask <$>
      (RegistrationNativePublicRetained.ordinary hmac work).run before =
      Prod.map id RegistrationNativeOpenRetained.mask <$>
        (RegistrationNativePublicRetained.ordinary hmac work).run (RegistrationNativeOpenRetained.mask before))
    (before : SourceState n KemSK ProviderState) :
    Prod.map id project <$> (withBase (RegistrationNativePublicRetained.ordinary hmac work)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (close provider) ((RegistrationNativeOpenRetained.ordinary hmac work).run
          (RegistrationNativeOpenRetained.mask before.1))).run (before.1.pool, before.2) := by
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (close provider) (Prod.map id RegistrationNativeOpenRetained.mask <$>
      simulateQ RegistrationNativeOpenRetained.baseLift
        ((RegistrationNativePublicRetained.ordinary hmac work).run (RegistrationNativeOpenRetained.mask before.1)))).run
          (before.1.pool, before.2)
  rw [simulateQ_map, StateT.run_map, base_program]
  simp only [withBase, StateT.run, Functor.map_map]
  have kept := congrArg (fun distribution =>
    (fun result => (result.1, project (result.2, before.2))) <$> distribution)
    (ordinary_pool hmac work framed before.1)
  have actual := congrArg (fun distribution =>
    (fun result => (result.1, (result.2, (before.1.pool, before.2)))) <$> distribution) (natural before.1)
  simp only [Functor.map_map, project, replacePool, RegistrationNativeOpenRetained.mask, Prod.map_def, id_eq] at kept actual ⊢
  exact kept.symm.trans actual

/-- The complete concrete dispatch has the same provider callbacks and semantic World state on both sides. -/
theorem query_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : SourceState n KemSK ProviderState) :
    Prod.map id project <$> (source setup wire route sign provider query).run before =
      (reference setup wire route sign provider query).run (project before) := by
  simp only [reference, project, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rcases query with (message | (message | query) | query) | query
  · rfl
  · rfl
  · exact ordinary_project provider setup.hmac _ (fun pool current => common_pool setup wire sign pool query current)
      (RegistrationNativeProviderRetainedFrame.ordinary_common setup wire sign query) before
  · change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (close provider) ((fun value => (value, RegistrationNativeOpenRetained.mask before.1)) <$>
        RegistrationNativeOpenRetained.kemLift query)).run (before.1.pool, before.2)
    rw [simulateQ_map, StateT.run_map]
    simp only [RegistrationNativeOpenRetained.kemLift, simulateQ_spec_query, close]
    change Prod.map id project <$> (routed provider query).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((fun result => ((result.1, RegistrationNativeOpenRetained.mask before.1), result.2)) <$>
          simulateQ RegistrationNativePublicRetained.coins ((provider query).run (before.1.pool, before.2)))
    simpa only [Functor.map_map] using routed_project provider query before
  · exact ordinary_project provider setup.hmac _ (fun pool current => world_pool pool _ current)
      (RegistrationNativeProviderRetainedFrame.ordinary_guarded setup wire route (.inr (.inr query))) before

/-- The same literal provider source law holds for every adaptive frontend program, with its entire projected poststate. -/
theorem program_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : SourceState n KemSK ProviderState) :
    Prod.map id project <$> (simulateQ (source setup wire route sign provider) work).run before =
      (simulateQ (reference setup wire route sign provider) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_project setup wire route sign provider) work before

end BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource.base_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource.base_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource.routed_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource.routed_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource.program_project
