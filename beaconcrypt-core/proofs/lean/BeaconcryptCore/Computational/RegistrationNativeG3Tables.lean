-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout
import BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-! Independent finite G2 output tables split into a material44 table and a seed64 table by the actual byte-layout equivalence. This is a sampler law through arbitrary continuations after the G2 key hop; it asserts no independence of an earlier root/PRK context and no whole native-client substitution. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeG3Tables
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material joinOutput splitOutput)
open PqxdhRecordLiftSeed (Seed)
open PqxdhServerAuthKeySchedule (Output)
open LazyOracleDiscard (LawEq)
variable {n : Nat}

abbrev OutputTable (n : Nat) := Slot n → Output
abbrev MaterialTable (n : Nat) := Slot n → Material
abbrev SeedTable (n : Nat) := Slot n → Seed

def join (materials : MaterialTable n) (seeds : SeedTable n) : OutputTable n :=
  fun point => joinOutput (materials point) (seeds point)

/-- The complete finite table equivalence uses the exact source108 layout at every slot. -/
def tableEquiv : (MaterialTable n × SeedTable n) ≃ OutputTable n where
  toFun tables := join tables.1 tables.2
  invFun outputs := (fun point => (splitOutput (outputs point)).1, fun point => (splitOutput (outputs point)).2)
  left_inv := by
    rintro ⟨materials, seeds⟩
    apply Prod.ext
    · funext point
      exact congrArg Prod.fst (PqxdhDeploymentHiddenLayout.split_join (materials point) (seeds point))
    · funext point
      exact congrArg Prod.snd (PqxdhDeploymentHiddenLayout.split_join (materials point) (seeds point))
  right_inv := by
    intro outputs
    funext point
    exact PqxdhDeploymentHiddenLayout.join_split (outputs point)

/-- A fixed slot retains its literal complete source108 output after joining the two tables. -/
theorem split_join (materials : MaterialTable n) (seeds : SeedTable n) (point : Slot n) :
    splitOutput (join materials seeds point) = (materials point, seeds point) :=
  PqxdhDeploymentHiddenLayout.split_join (materials point) (seeds point)

/-- The complete uniform108 table has the same law as independent material44 and seed64 tables through every subsequent continuation. -/
theorem uniform_tables {Result : Type} (next : OutputTable n → ProbComp Result) :
    LawEq ($ᵗ OutputTable n >>= next)
      (do let materials ← $ᵗ MaterialTable n; let seeds ← $ᵗ SeedTable n; next (join materials seeds)) := by
  intro ResultSpace _ continuation
  let : MeasurableSpace (MaterialTable n × SeedTable n) := ⊤
  let : DiscreteMeasurableSpace (MaterialTable n × SeedTable n) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSpace (OutputTable n) := ⊤
  let : DiscreteMeasurableSpace (OutputTable n) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have pair : (($ᵗ (MaterialTable n × SeedTable n)) >>= fun tables => next (tableEquiv tables) >>= continuation) =
      ((do
        let materials ← $ᵗ MaterialTable n
        let seeds ← $ᵗ SeedTable n
        next (join materials seeds)) >>= continuation) := by
    rw [← PqxdhFullSecretInputKdf.pairSample (A := MaterialTable n) (B := SeedTable n)]
    simp only [bind_assoc, pure_bind]
    rfl
  rw [← pair, bind_assoc]
  exact (evalDist_bind_bijective_uniform_cross _ _ SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample tableEquiv tableEquiv.bijective
    (fun output => next output >>= continuation)).symm

end BeaconcryptCore.Computational.RegistrationNativeG3Tables

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Tables.tableEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Tables.tableEquiv
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Tables.split_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Tables.split_join
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Tables.uniform_tables' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Tables.uniform_tables
