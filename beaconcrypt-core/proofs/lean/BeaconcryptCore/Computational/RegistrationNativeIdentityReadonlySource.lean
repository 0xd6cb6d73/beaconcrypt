-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation

/-! Existing native programs already factored through Env execute on the same mutable Env/context after ambient lifting. The adapter's temporary empty owner roster is irrelevant because these programs are explicitly lifted and cannot inspect it. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReadonlySource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem liftOld_lift
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value) :
    RegistrationNativeIdentityFrontend.liftOld (source := source) (StateT.lift work) = liftAmbient work := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [RegistrationNativeIdentityFrontend.liftOld, liftAmbient, StateT.run_lift,
    StateT.run_map, bind_pure_comp, Functor.map_map, id_map']
  all_goals rfl

/-- Lifting an actual owner-independent native Env program retains its whole source execution. -/
theorem source_lift (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value) :
    Related (source := source) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.liftOld (StateT.lift work)) (StateT.lift work) := by
  rw [liftOld_lift]
  exact related_lift setup checks representation created seeds work

theorem keeps_lift (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value) :
    Keeps (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.liftOld (StateT.lift work)) := by
  rw [liftOld_lift]
  exact RegistrationNativeIdentitySourceSimulation.keeps_lift setup checks representation created work

end BeaconcryptCore.Computational.RegistrationNativeIdentityReadonlySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReadonlySource.source_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReadonlySource.source_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReadonlySource.keeps_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReadonlySource.keeps_lift
