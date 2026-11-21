-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldCoinCompiler

/-! Native auxiliary agreement callbacks compile to EnvEffects without embedding the record World in environment state. Exact replies, auxiliary state, request instrumentation, signing receipts, CTX cache and all private record coordinates are retained. Only the additional EnvEffects coin-effect ledger is projected, with its exact relation to uniform draws proved separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open RegistrationWorldCoinCompiler (eraseCoin envCoin)
open RegistrationWorldAgreement (recorded)
variable {n : Nat} {Auxiliary : Type}

/-- Native auxiliary state and receipt logs are separate from the actual record World. -/
structure EnvState (Auxiliary : Type) where
  auxiliary : Auxiliary
  requests : List RegistrationAgreementExecutor.Request
  recordRequests : List RegistrationWorldAgreement.RecordCall
  receipts : List RegistrationSigningShared.Receipt

def join (state : EnvState Auxiliary) (world : PqxdhRecordLiftWorld.State n) :
    RegistrationWorldAgreement.State n Auxiliary :=
  ⟨state.auxiliary, state.requests, state.recordRequests, (world, state.receipts)⟩

def erase (state : RegistrationWorldAgreement.State n Auxiliary) : EnvState Auxiliary :=
  ⟨state.auxiliary, state.requests, state.recordRequests, state.world.2⟩

def mask (state : RegistrationWorldAgreement.State n Auxiliary) : RegistrationWorldAgreement.State n Auxiliary :=
  { state with world := (eraseCoin state.world.1, state.world.2) }

def compiler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (EnvState Auxiliary) (OracleComp (EnvEffects n))) :=
  fun query state =>
    (fun result => (result.1, { state with auxiliary := result.2, requests := state.requests ++ recorded query })) <$>
      simulateQ envCoin ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary)

noncomputable def run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : EnvState Auxiliary) (world : PqxdhRecordLiftWorld.State n) :=
  (simulateQ PqxdhRecordLiftWorld.effects ((compiler source primitive query).run state)).run world

private theorem compiler_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : EnvState Auxiliary) :
    (compiler (n := n) source primitive query).run state =
      (fun result => (result.1, { state with auxiliary := result.2, requests := state.requests ++ recorded query })) <$>
        simulateQ envCoin ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary) := rfl

private theorem native_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : EnvState Auxiliary) (world : PqxdhRecordLiftWorld.State n) :
    (RegistrationWorldAgreement.agreement source primitive query).run (join state world) =
      (fun result => (result.1.1, RegistrationWorldAgreement.State.mk result.1.2
        (state.requests ++ recorded query) state.recordRequests (result.2, state.receipts))) <$>
        (PqxdhRecordLiftWorld.sampled
          ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary)).run world := rfl

/-- Splitting only the native environment and record World is exact on all fields. -/
theorem join_erase (state : RegistrationWorldAgreement.State n Auxiliary) : join (erase state) state.world.1 = state := by
  cases state
  rfl

/-- The actual typed agreement callback has the same complete reply/state after its proved additional coin-effect projection. -/
theorem query_native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : EnvState Auxiliary) (world : PqxdhRecordLiftWorld.State n) :
    (fun result => (result.1.1, mask (join result.1.2 result.2))) <$>
      run source primitive query state world =
    Prod.map id mask <$> (RegistrationWorldAgreement.agreement source primitive query).run (join state world) := by
  rw [native_run]
  have represented := congrArg (fun work =>
    (fun result => (result.1.1, RegistrationWorldAgreement.State.mk result.1.2
      (state.requests ++ recorded query) state.recordRequests (result.2, state.receipts))) <$> work)
    (RegistrationWorldCoinCompiler.coins_erase
      ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary) world)
  simpa only [run, compiler_run, join, mask, simulateQ_map, StateT.run_map,
    Functor.map_map, Prod.map, id_eq] using represented

/-- The environment's added coin-effect increment is exactly its underlying native uniform increment, on every actual supported reply. -/
theorem query_accounting (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : EnvState Auxiliary) (world : PqxdhRecordLiftWorld.State n)
    (result : (RegistrationAgreementExecutor.Spec.Range query × EnvState Auxiliary) × PqxdhRecordLiftWorld.State n)
    (reached : result ∈ support (run source primitive query state world)) :
    result.2.primitive.1.effects .coin + world.primitive.1.uniform =
      world.primitive.1.effects .coin + result.2.primitive.1.uniform := by
  simp only [run, compiler_run, simulateQ_map, StateT.run_map, support_map] at reached
  obtain ⟨inner, actual, rfl⟩ := reached
  rw [RegistrationWorldCoinCompiler.env_program] at actual
  exact RegistrationWorldCoinCompiler.coin_accounting _ world inner actual

/-- A concrete auxiliary primitive draw cap gives its exact environment coin bill and zero hash/administrative bill. -/
theorem query_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : EnvState Auxiliary) (cap : Nat)
    (bounded : ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary).IsTotalQueryBound cap)
    (kind : EffectKind) :
    ((compiler (n := n) source primitive query).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .coin then cap else 0) := by
  simpa only [compiler_run, isQueryBoundP_map_iff] using
    RegistrationWorldCoinCompiler.env_bound (n := n)
      ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary) cap bounded kind

end BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler.join_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler.join_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler.query_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler.query_native
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler.query_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler.query_accounting
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler.query_bound
