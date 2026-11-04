-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish
/-! Exact state reassociation for a persistent public callback interpreted below its common platform state. This algebra retains both complete states and every returned value. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift
variable {J P S A B : Type} {spec : OracleSpec J}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
noncomputable def interpret (implementation : QueryImpl spec (StateT S m))
    (work : StateT P (OracleComp spec) A) : StateT (P × S) m A := fun before =>
  (fun result => (result.1.1,(result.1.2,result.2))) <$>
    (simulateQ implementation (work.run before.1)).run before.2

omit [LawfulMonad m] in
theorem run (implementation : QueryImpl spec (StateT S m)) (work : StateT P (OracleComp spec) A)
    (previous : P) (before : S) :
    (interpret implementation work).run (previous,before) =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ implementation (work.run previous)).run before := rfl

theorem hom (implementation : QueryImpl spec (StateT S m)) :
    Cslib.IsMonadHom (StateT P (OracleComp spec)) (StateT (P × S) m) (interpret implementation) := by
  apply Cslib.IsMonadHom.mk'
  · intro A value
    apply StateT.ext
    rintro ⟨previous,before⟩
    simp only [run,StateT.run_pure,simulateQ_pure,map_pure]
  · intro A B work next
    apply StateT.ext
    rintro ⟨previous,before⟩
    simp only [run,StateT.run_bind,simulateQ_bind,map_bind,bind_map_left]

theorem lifted (implementation : QueryImpl spec (StateT S m)) (work : OracleComp spec A) (previous : P) (before : S) :
    (interpret implementation (StateT.lift work)).run (previous,before) =
      (fun result => (result.1,(previous,result.2))) <$> (simulateQ implementation work).run before := by
  simp only [run,StateT.run_lift,bind_pure_comp,simulateQ_map,StateT.run_map,Functor.map_map]
theorem simulate {K : Type} {target : OracleSpec K}
    (implementation : QueryImpl spec (StateT S m))
    (inner : QueryImpl target (StateT P (OracleComp spec))) (work : OracleComp target A) :
    interpret implementation (simulateQ inner work) =
      simulateQ (fun query => interpret implementation (inner query)) work := by
  have natural := hom (P := P) implementation
  induction work using OracleComp.inductionOn with
  | pure value => exact natural.map_pure _
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,natural.map_bind,ih]

theorem thread {K : Type} {target : OracleSpec K}
    (implementation : QueryImpl target (OracleComp spec)) (work : OracleComp target A) (previous : P) :
    (simulateQ (fun query => (StateT.lift (implementation query) : StateT P (OracleComp spec) _)) work).run previous =
      (fun value => (value,previous)) <$> simulateQ implementation work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,StateT.run_lift,
      bind_pure_comp,bind_map_left,map_bind]
    apply bind_congr
    intro reply
    exact ih reply
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.hom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.hom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.lifted' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.lifted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.simulate' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.thread' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift.thread
