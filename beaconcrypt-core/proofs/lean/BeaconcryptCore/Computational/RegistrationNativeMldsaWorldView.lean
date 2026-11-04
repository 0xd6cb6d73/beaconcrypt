-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence
import BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform
import BeaconcryptCore.Computational.RegistrationNativeWorldViewRecords
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram

/-! External ML challengers do not reveal private source draw counts. This analysis view explicitly erases uniform, native-call and Env coin accounting while retaining all operational World state and non-coin effect bills. Actual primitive bills remain separate theorems of the original counted execution. The local laws below do not assert whole-profile equality for different capability accounting receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State)
open RegistrationNativeKemCounterIndependence (Stable)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def project (before : State n) : State n :=
  RegistrationNativeKemWorldUniform.mask (RegistrationNativeWorldView.project before)

private theorem commute (before : State n) :
    RegistrationNativeWorldView.project (RegistrationNativeKemWorldUniform.mask before) =
      RegistrationNativeKemWorldUniform.mask (RegistrationNativeWorldView.project before) := rfl

/-- Reapplying the ML accounting view changes no further operational state. -/
theorem idempotent (before : State n) : project (project before) = project before := by
  simp only [project, ← commute, RegistrationNativeWorldView.project_idempotent,
    RegistrationNativeKemWorldUniform.mask_idempotent]

/-- Cache, record routing, raw attempts, frame history and hidden material remain literal. -/
theorem operational (before : State n) :
    (project before).primitive.2 = before.primitive.2 ∧ (project before).server = before.server ∧
      (project before).owners = before.owners ∧ (project before).ownerRaw = before.ownerRaw ∧
      (project before).produced = before.produced ∧ (project before).seeds = before.seeds ∧
      (project before).used = before.used := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The view erases precisely the private ML draw-accounting changes for either native or Env leaves. -/
theorem advance (accounting : RegistrationNativeMldsaCapability.Accounting) (before : State n) (count : Nat) :
    project (RegistrationNativeMldsaCapability.advance accounting before count) = project before := by
  cases accounting <;>
    simp only [project, RegistrationNativeKemWorldUniform.mask, RegistrationNativeWorldView.project,
      RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
      RegistrationNativeMldsaCapability.advance, Function.update_idem]

/-- Actual counted sampling has its original literal source output under the stated accounting erasure. -/
theorem sampled (draw : ProbComp Value) (before : State n) :
    Prod.map id project <$> (PqxdhRecordLiftWorld.sampled draw).run before =
      (fun value => (value, project before)) <$> draw := by
  have same := congrArg (fun work => Prod.map id RegistrationNativeWorldView.project <$> work)
    (RegistrationNativeKemWorldUniform.sampled_mask draw before)
  simp only [Functor.map_map, Prod.map, id_eq, commute] at same
  simp only [project]
  exact same

private theorem compose_stable {S Answer : Type} (first second : S → S)
    (commuting : ∀ before, first (second before) = second (first before)) (work : StateT S ProbComp Answer)
    (left : Stable first work) (right : Stable second work) : Stable (fun before => second (first before)) work := by
  intro before
  have initial := congrArg (fun action => Prod.map id second <$> action) (left before)
  have following := congrArg (fun action => Prod.map id first <$> action) (right (first before))
  simp only [Functor.map_map, Prod.map, id_eq] at initial following ⊢
  simp only [commuting] at following
  exact initial.trans following

/-- All actual environment effects retain their complete replies and operational state under the additional uniform erasure. -/
theorem effects (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable project (PqxdhRecordLiftWorld.effects query) :=
  compose_stable RegistrationNativeWorldView.project RegistrationNativeKemWorldUniform.mask commute _
    (RegistrationNativeWorldViewEffects.effects_input query)
    (RegistrationNativeKemWorldEffects.effects_input query)

/-- Every actual World operation, including record failures and hidden installations, ignores the omitted private accounting input. -/
theorem world (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) :
    Stable project (PqxdhRecordLiftWorld.handler setup codec route query) :=
  compose_stable RegistrationNativeWorldView.project RegistrationNativeKemWorldUniform.mask commute _
    (RegistrationNativeWorldViewRecords.handler_input setup codec route query)
    (RegistrationNativeKemWorldRecordUniform.handler_input setup codec route query)

/-- Named ML leaves expose their exact optional result while their private accounting receipt has no operational World effect. -/
theorem call {source : RegistrationNativeMldsa.Source} (accounting : RegistrationNativeMldsaCapability.Accounting)
    (query : RegistrationNativeMldsaCapability.Request source) (before : State n) :
    Prod.map id project <$> (RegistrationNativeMldsaProgram.call accounting query).run before =
      (fun result => (result.1, project before)) <$>
        (RegistrationNativeMldsaProgram.Spec source).query (.inr query) := by
  simp only [RegistrationNativeMldsaProgram.call, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map, id_eq, advance]
  rfl
end BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.operational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.operational

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.advance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.sampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.sampled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.effects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView.call
