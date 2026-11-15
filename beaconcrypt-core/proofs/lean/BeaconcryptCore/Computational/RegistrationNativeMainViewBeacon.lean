-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMainViewLift
import BeaconcryptCore.Computational.RegistrationNativeBeaconEnvFinish

/-! Concrete Beacon owner/Env programs retain their entire native Main outcome when interpreted over the actual private generated KEM service and shared World. Only the explicitly named private accounting coordinates are projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMainViewBeacon
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (nativeView)
open RegistrationNativeBeaconFrontend (Trusted)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

def assemble (result : ((Value × RegistrationNativeBeaconFrontend.State mlSource) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×
      RegistrationNativeExperiment.State n KemSK mlSource) : Value × RegistrationNativeExperiment.State n KemSK mlSource :=
  (result.1.1.1, { result.2 with
    beacons := result.1.1.2
    server := { result.2.server with world :=
      RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })

private theorem assemble_view (result : ((Value × RegistrationNativeBeaconFrontend.State mlSource) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×
      RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeView (assemble result) =
      assemble (Prod.map (Prod.map id RegistrationNativeBeaconEnvView.erase) nativeView result) := rfl

/-- Main's actual Beacon wrapper preserves the whole literal owner/Env reply and native poststate from proved concrete callback nonread laws. -/
theorem beacon_input (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (stable : RegistrationNativeBeaconEnvView.Stable work) :
    RegistrationStateView.Stable nativeView (RegistrationNativeExperiment.beacon setup checks representation created work) := by
  intro before
  let implementation := RegistrationNativeExperiment.trusted (n := n) setup checks representation created mlSource
  let env := RegistrationWorldAgreementCompiler.erase before.server.world
  let script := (work.run before.beacons).run env
  have first := congrArg (fun distribution =>
    Prod.map (Prod.map id RegistrationNativeBeaconEnvView.erase) id <$> distribution)
    (RegistrationNativeMainViewLift.trusted_program setup checks representation created script before)
  have envLaw := RegistrationNativeBeaconEnvView.run_input work stable before.beacons env
  have interpreted := congrArg (fun program => (simulateQ implementation program).run (nativeView before)) envLaw
  simp only [simulateQ_map, StateT.run_map] at interpreted
  have second := congrArg (fun distribution => Prod.map id nativeView <$> distribution) interpreted
  simp only [Functor.map_map, Prod.map, id_eq] at first second
  have combined := first.trans second
  have final := congrArg (fun distribution => assemble <$> distribution) combined
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp,
    Functor.map_map, implementation, script, env] at final ⊢
  simp only [assemble, Prod.map, id_eq, nativeView, RegistrationServerMaterialSourceState.nativeView,
    RegistrationServerRecordWorldSource.project, RegistrationWorldAgreementCompiler.erase,
    RegistrationNativeBeaconEnvView.erase, RegistrationWorldAgreementCompiler.join] at final ⊢
  exact final

end BeaconcryptCore.Computational.RegistrationNativeMainViewBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainViewBeacon.beacon_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainViewBeacon.beacon_input
