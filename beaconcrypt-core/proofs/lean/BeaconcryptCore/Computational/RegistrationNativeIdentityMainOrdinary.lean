-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource

/-! Ordinary native SDK and World operations retain their exact already-counted source effects while the opaque identity table remains private. Candidate reporting preserves source state exactly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary
open RegistrationNativeIdentityMain (State M)
open RegistrationNativeIdentityMainSource (interpret project)
open RegistrationNativeIdentityWorld (Context)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {KemSK Value Result : Type} {mlSource : RegistrationNativeMldsa.Source}

def attach (owners : RegistrationNativeBeaconFrontend.State mlSource) (context : Context n KemSK) :
    RegistrationNativeExperiment.State n KemSK mlSource := ⟨context.server, owners, context.kem, context.parsedAccepts⟩

/-- Private source interpretation preserves literal pure API replies and every source state coordinate. -/
theorem interpret_pure (joint : PqxdhJointIdentity.Primitives) (value : Value) :
    interpret joint (pure value : M n KemSK mlSource Value) = pure value := by
  funext before
  simp only [interpret, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

/-- Actual adaptive whole-client continuations retain their complete private joint source state. -/
theorem interpret_bind (joint : PqxdhJointIdentity.Primitives) (work : M n KemSK mlSource Value)
    (next : Value → M n KemSK mlSource Result) :
    interpret joint (work >>= next) = (interpret joint work >>= fun value => interpret joint (next value)) := by
  funext before
  simp only [interpret, StateT.run, StateT.monad_bind_def, StateT.bind,
    simulateQ_bind, map_bind, bind_map_left]

theorem map_apply {S A B : Type} (change : A → B) (work : StateT S ProbComp A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := by
  change (work before >>= fun result => pure (change result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Native random operations retain literal replies and actual World counts while their extra joint-game transcript entries are omitted only in private projection. -/
theorem ordinary_source (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (Context n KemSK) ProbComp Value) (before : State n KemSK mlSource × SourceState) :
    Prod.map id project <$> (interpret joint (RegistrationNativeIdentityMain.ordinary work)).run before =
      Prod.map id (attach (RegistrationNativeIdentityRealization.owners before.2 before.1.beacons)) <$>
        work.run before.1.context := by
  have law := congrArg (fun distribution => (fun result => (result.1.1,
    project ({ before.1 with context := result.1.2 }, result.2))) <$> distribution)
    (RegistrationNativeIdentityMainSource.coins_source joint (work.run before.1.context) before.2)
  simp only [interpret, RegistrationNativeIdentityMain.ordinary, StateT.run,
    simulateQ_map, map_apply, Functor.map_map, Prod.map, id_eq,
    project] at law ⊢
  exact law

private theorem report_run (packet : beaconcrypt_core.registration.InitPacket) (before : State n KemSK mlSource) :
    (RegistrationNativeIdentityMain.report packet).run before =
      (fun reply => (reply, before)) <$>
        RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityMain.reports packet before.beacons) := by
  change (RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityMain.reports packet before.beacons) >>=
    fun reply => pure (reply, before)) = _
  simp only [bind_pure_comp]

/-- Candidate reporting executes before native authentication and leaves the entire source frontend, private identities, KEM pool and World unchanged. -/
theorem report_source (joint : PqxdhJointIdentity.Primitives) (packet : beaconcrypt_core.registration.InitPacket)
    (before : State n KemSK mlSource × SourceState) :
    (interpret joint (RegistrationNativeIdentityMain.report packet)).run before = pure ((), before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeIdentityMainSource.implementation joint)
      ((RegistrationNativeIdentityMain.report packet).run before.1)).run before.2 = _
  rw [report_run, simulateQ_map, StateT.run_map, RegistrationNativeIdentityMainSource.emit_source]
  simp only [map_pure]

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.interpret_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.interpret_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.map_apply' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.map_apply
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.ordinary_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.report_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary.report_source
