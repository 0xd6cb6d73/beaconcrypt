-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection

/-! Native callback counters are private proof instrumentation. The source view below omits exactly that native-call map and the separately accounted Env coin-effect ledger, while retaining the whole cache, uniform/hash/admin bills, protocol state, produced log, raw counters and hidden material. Per-controller bills are proved separately; this view is not a claim that those omitted counters are equal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeWorldView
variable {n : Nat} {Value : Type}

def eraseNative (before : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  { before with primitive := ({ before.primitive.1 with native := fun _ => 0 }, before.primitive.2) }

def project (before : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  eraseNative (RegistrationWorldCoinCompiler.eraseCoin before)

/-- Reapplying the source view preserves its complete operational state. -/
theorem project_idempotent (before : PqxdhRecordLiftWorld.State n) :
    project (project before) = project before := by
  simp only [project, eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]

/-- This projection retains the literal CTX cache and actual number of native uniform draws. -/
theorem cache_uniform (before : PqxdhRecordLiftWorld.State n) :
    (project before).primitive.2 = before.primitive.2 ∧
      (project before).primitive.1.uniform = before.primitive.1.uniform := ⟨rfl, rfl⟩

/-- The native sampled computation ignores the unrelated native-call counter map. -/
theorem sampled_native (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseNative <$> (PqxdhRecordLiftWorld.sampled work).run before =
      (PqxdhRecordLiftWorld.sampled work).run (eraseNative before) := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map_def, id_eq, eraseNative]

/-- The complete source sampler commutes with the explicitly stated analysis view. -/
theorem sampled (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (PqxdhRecordLiftWorld.sampled work).run before =
      (PqxdhRecordLiftWorld.sampled work).run (project before) := by
  have same := congrArg (fun distribution => Prod.map id eraseNative <$> distribution)
    (RegistrationWorldCoinCompiler.sampled_erase work before)
  rw [sampled_native] at same
  simpa only [Functor.map_map, Prod.map_def, id_eq, project] using same

/-- Compiled signing coins and the actual native sampler have the same complete source-view state and literal replies. -/
theorem coins (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$>
      (simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin work)).run before =
      (PqxdhRecordLiftWorld.sampled work).run (project before) := by
  have same := congrArg (fun distribution => Prod.map id eraseNative <$> distribution)
    (RegistrationWorldCoinCompiler.coins_erase work before)
  calc
    _ = Prod.map id project <$> (PqxdhRecordLiftWorld.sampled work).run before := by
      simpa only [Functor.map_map, Prod.map_def, id_eq, project] using same
    _ = _ := sampled work before

private theorem native_charge_hash (bytes : List UInt8) (before : PqxdhRecordLiftWorld.State n) :
    eraseNative (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before) =
      PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) (eraseNative before) := rfl

/-- Actual commitment/fingerprint hashing retains its complete cache and uniform/hash bill under native-call erasure. -/
theorem hash_native (bytes : List UInt8) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseNative <$> (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before =
      (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run (eraseNative before) := by
  have sample := sampled_native ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.primitive.2)
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before)
  rw [native_charge_hash] at sample
  have lifted := congrArg (fun distribution => (fun result => (result.1.1,
    { result.2 with primitive := (result.2.primitive.1, result.1.2) })) <$> distribution) sample
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, eraseNative,
    PqxdhRecordLiftWorld.chargeEffect] at lifted ⊢
  exact lifted

/-- The real hash service commutes with the stated two-coordinate view, retaining all protocol and shared-cache state. -/
theorem hash (bytes : List UInt8) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before =
      (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run (project before) := by
  have same := congrArg (fun distribution => Prod.map id eraseNative <$> distribution)
    (RegistrationAuthenticationCoinProjection.hash_mask bytes before)
  rw [hash_native] at same
  simpa only [Functor.map_map, Prod.map_def, id_eq, project] using same

end BeaconcryptCore.Computational.RegistrationNativeWorldView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldView.cache_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldView.cache_uniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldView.sampled_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldView.sampled_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldView.sampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldView.sampled
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldView.hash_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldView.hash_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldView.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldView.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldView.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldView.coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldView.project_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldView.project_idempotent
