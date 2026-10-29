-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicScalarMap

/-! Scalar reconstruction is natural for the concrete sampling, signing-log and lifecycle-phase operations used by native bundle publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeBeaconFrontend (Owner State M Trusted)
open RegistrationNativePublicScalarMap (Equivariant change alter)
open RegistrationWorldAgreementCompiler (EnvState)
variable {source : RegistrationNativeMldsa.Source} {n : Nat} {KemSK Auxiliary Value Next : Type}
variable (selected : Nat) (scalar : ScalarBytes)

theorem pure_equivariant (value : Value) : Equivariant selected scalar (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env
  simp only [StateT.run_pure, map_pure, Prod.map_def, id_eq]

theorem bind_equivariant (work : M n KemSK source Auxiliary Value) (next : Value → M n KemSK source Auxiliary Next)
    (first : Equivariant selected scalar work) (rest : ∀ value, Equivariant selected scalar (next value)) :
    Equivariant selected scalar (work >>= next) := by
  intro owners env
  simp only [StateT.run_bind, map_bind]
  rw [← first owners env, bind_map_left]
  apply bind_congr
  intro middle
  exact rest middle.1.1 middle.1.2 middle.2

theorem lift_equivariant (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Equivariant selected scalar (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]
  rfl

theorem program_equivariant {I : Type} {spec : OracleSpec I}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (step : ∀ query, Equivariant selected scalar (implementation query)) (work : OracleComp spec Value) :
    Equivariant selected scalar (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_equivariant selected scalar value
  | query_bind query next ih =>
      simpa only [simulateQ_bind, simulateQ_spec_query] using bind_equivariant selected scalar _ _ (step query) ih

theorem sample_equivariant (work : ProbComp Value) :
    Equivariant selected scalar (RegistrationNativeBeaconFrontend.sample work : M n KemSK source Auxiliary Value) :=
  program_equivariant selected scalar _ (fun _ => lift_equivariant selected scalar _) work

theorem current_equivariant (index : Nat) (update : Owner source → Owner source)
    (commutes : ∀ owner, alter selected scalar index (update owner) = update (alter selected scalar index owner)) :
    Equivariant selected scalar ((modify fun owners => match owners[index]? with
      | none => owners | some owner => owners.set index (update owner)) : M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure, map_pure, Prod.map_def, id_eq,
    RegistrationNativePublicScalarMap.lookup]
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      simp only [Option.map_some, RegistrationNativePublicScalarMap.set, commutes]

theorem phase_equivariant (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Equivariant selected scalar (RegistrationNativeBeaconFrontend.updatePhase index phase : M n KemSK source Auxiliary Unit) := by
  apply current_equivariant selected scalar index (fun owner => { owner with phase })
  intro owner
  by_cases chosen : index = selected <;> simp only [alter, chosen, ite_true, ite_false]

theorem log_equivariant (index : Nat) (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Equivariant selected scalar (RegistrationNativeBeaconFrontend.logEd index message signature : M n KemSK source Auxiliary Unit) := by
  apply current_equivariant selected scalar index (fun owner => { owner with edHistory := owner.edHistory ++ [.signed message signature] })
  intro owner
  by_cases chosen : index = selected <;> simp only [alter, chosen, ite_true, ite_false]

end BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.pure_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.pure_equivariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.bind_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.bind_equivariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.lift_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.lift_equivariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.program_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.program_equivariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.sample_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.sample_equivariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.current_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.current_equivariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.phase_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.phase_equivariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.log_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws.log_equivariant
