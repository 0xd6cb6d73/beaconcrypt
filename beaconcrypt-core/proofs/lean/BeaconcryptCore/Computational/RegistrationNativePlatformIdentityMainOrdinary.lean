-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain

/-! Ordinary already-counted native/platform work executes under the same indexed joint client without exposing or modifying its private generated identity table. Candidate reports use public handles and leave all source state unchanged. This exact interpretation algebra retains allocator failures and every actual P/counter/cache coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project)
open RegistrationNativeIdentityMainOrdinary (attach)
open RegistrationNativeIdentityWorld (Context)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {KemSK Platform Value Next : Type} {source : RegistrationNativeMldsa.Source}

def ordinary (work : StateT (Context n KemSK × Platform) ProbComp Value) : M n KemSK Platform source Value := fun before =>
  (fun result => (result.1, ({ before.1 with context := result.2.1 }, result.2.2))) <$>
    simulateQ RegistrationNativeIdentityMain.coins (work.run (before.1.context, before.2))

/-- Exact original pure replies and native/external state are preserved by private source interpretation. -/
theorem interpret_pure (joint : PqxdhJointIdentity.Primitives) (value : Value) :
    interpret joint (pure value : M n KemSK Platform source Value) = pure value := by
  funext before
  simp only [interpret, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

/-- The source interpreter threads complete reached states through arbitrary adaptive continuations. -/
theorem interpret_bind (joint : PqxdhJointIdentity.Primitives) (work : M n KemSK Platform source Value)
    (next : Value → M n KemSK Platform source Next) :
    interpret joint (work >>= next) = (interpret joint work >>= fun value => interpret joint (next value)) := by
  funext before
  simp only [interpret, StateT.run, StateT.monad_bind_def, StateT.bind, simulateQ_bind, map_bind, bind_map_left]

/-- Native and platform ordinary draws are literal; only the indexed service's extra uniform transcript entries are removed. -/
theorem ordinary_source (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (Context n KemSK × Platform) ProbComp Value)
    (before : (State n KemSK source × Platform) × SourceState) :
    Prod.map id project <$> (interpret joint (ordinary work)).run before =
      (fun result => (result.1, (attach (RegistrationNativeIdentityRealization.owners before.2 before.1.1.beacons) result.2.1, result.2.2))) <$>
        work.run (before.1.1.context, before.1.2) := by
  have law := congrArg (fun distribution => (fun result => (result.1.1,
    project (({ before.1.1 with context := result.1.2.1 }, result.1.2.2), result.2))) <$> distribution)
    (RegistrationNativeIdentityMainSource.coins_source joint (work.run (before.1.1.context, before.1.2)) before.2)
  simp only [interpret, ordinary, StateT.run, simulateQ_map, RegistrationNativeIdentityMainOrdinary.map_apply,
    Functor.map_map, Prod.map, id_eq, project, RegistrationNativeIdentityMainSource.project, attach] at law ⊢
  exact law

/-- Public candidate reports are source ghost operations and retain the complete external state. -/
theorem report_source (joint : PqxdhJointIdentity.Primitives) (packet : beaconcrypt_core.registration.InitPacket)
    (before : (State n KemSK source × Platform) × SourceState) :
    (interpret joint (RegistrationNativePlatformIdentityMain.liftMain (RegistrationNativeIdentityMain.report packet))).run before = pure ((), before) := by
  rw [RegistrationNativePlatformIdentityMain.interpret_lift, RegistrationNativeIdentityMainOrdinary.report_source, map_pure]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary.interpret_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary.interpret_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary.ordinary_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary.report_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary.report_source
