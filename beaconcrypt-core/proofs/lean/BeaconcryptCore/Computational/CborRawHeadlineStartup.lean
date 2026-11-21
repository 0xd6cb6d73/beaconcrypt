-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawWorldCoreHandoff

/-! Probability composition through actual counted World startup draws. These generic lemmas retain the startup World and establish its freshness from the actual coin interpreter; a caller supplies only the already-proved continuation bound for each drawn value. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineStartup
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentEnvironmentJoin (uncount)
variable {ι KemSK Reader Response Value : Type} {baseSpec : OracleSpec ι} {n : Nat}
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def coins (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n) :=
  (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
    (simulateQ PqxdhRecordLiftInterface.coinLift draw)).run state

/-- Early record admission does not change any startup coin. -/
theorem guarded_coins (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n) :
    (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
      (simulateQ PqxdhRecordLiftInterface.coinLift draw)).run state = coins setup codec route draw state := by
  have same : (CborRecordWorldSimulation.guarded setup codec route (n := n)) ∘ₛ
      PqxdhRecordLiftInterface.coinLift = (PqxdhRecordLiftWorld.handler setup codec route) ∘ₛ
        PqxdhRecordLiftInterface.coinLift := by
    funext coin
    simp only [QueryImpl.apply_compose, PqxdhRecordLiftInterface.coinLift, simulateQ_spec_query]
    rfl
  rw [← QueryImpl.simulateQ_compose, same, QueryImpl.simulateQ_compose]
  rfl

/-- Counted startup draws return exactly the original draw. -/
theorem coins_projection (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n) :
    Prod.fst <$> coins setup codec route draw state = draw := by
  have counted := PqxdhDeploymentEnvironmentJoin.coins_world setup codec route draw state
  have projected := congrArg (fun work => Prod.fst <$> work) counted
  simpa only [coins, Functor.map_map, Prod.map_fst, id_eq, id_map'] using projected

/-- Every supported counted startup result retains all non-counting World coordinates. -/
theorem coins_fresh (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n)
    (result : Value × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support (coins setup codec route draw state)) :
    uncount result.2 = uncount state := by
  have counted := PqxdhDeploymentEnvironmentJoin.coins_world setup codec route draw state
  have projected : Prod.map id uncount result ∈ support (Prod.map id uncount <$>
      coins setup codec route draw state) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [coins, counted, support_map] at projected
  obtain ⟨value, _, same⟩ := projected
  exact (congrArg Prod.snd same).symm

/-- Pointwise bounds lift through the actual counted startup, without discarding its World state. -/
theorem bind_le (draw : ProbComp Value) (left : Value → ProbComp Bool)
    (right : Value → PqxdhRecordLiftWorld.State n → ProbComp Bool)
    (state : PqxdhRecordLiftWorld.State n)
    (bounded : ∀ value ∈ support draw, ∀ world, uncount world = uncount state →
      𝒟[left value] {true} ≤ 𝒟[right value world] {true}) :
    𝒟[draw >>= left] {true} ≤
      𝒟[coins setup codec route draw state >>= fun value => right value.1 value.2] {true} := by
  have initialDraw : draw >>= left = coins setup codec route draw state >>= fun value => left value.1 := by
    calc draw >>= left = (Prod.fst <$> coins setup codec route draw state) >>= left :=
        congrArg (fun work : ProbComp Value => work >>= left) (coins_projection setup codec route draw state).symm
      _ = _ := by rw [bind_map_left]
  rw [initialDraw, ← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro value reached
  have original : value.1 ∈ support draw := by
    rw [← coins_projection setup codec route draw state, support_map]
    exact ⟨value, reached, rfl⟩
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
  exact bounded value.1 original value.2 (coins_fresh setup codec route draw state value reached)

end BeaconcryptCore.Computational.CborRawHeadlineStartup

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineStartup.guarded_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineStartup.guarded_coins

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineStartup.coins_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineStartup.coins_projection

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineStartup.coins_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineStartup.coins_fresh

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineStartup.bind_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineStartup.bind_le
