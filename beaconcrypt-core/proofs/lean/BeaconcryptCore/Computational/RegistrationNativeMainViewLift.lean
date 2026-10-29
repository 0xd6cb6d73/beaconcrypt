-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerViewBuild
import BeaconcryptCore.Computational.RegistrationNativePublicSourceState

/-! Actual native Main lifting retains the whole private generated KEM pool, owner roster, parsed attempts, Server control and shared World. The view changes only separately accounted private instrumentation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMainViewLift
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (nativeView)
open RegistrationStateView (Stable)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- The entire native Main view is idempotent. -/
theorem view_idempotent (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    nativeView (nativeView before) = nativeView before := by
  simp only [nativeView, RegistrationNativeServerViewAccept.view_idempotent]

/-- The actual Main Server lift retains every current Beacon, pool entry and parsed counter. -/
theorem server_input (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (stable : Stable RegistrationServerMaterialSourceState.nativeView work) :
    Stable (nativeView (KemSK := KemSK) (mlSource := mlSource)) (RegistrationNativeExperiment.server work) := by
  intro before
  have law := congrArg (fun distribution => (fun result => (result.1,
    { nativeView before with server := result.2 })) <$> distribution) (stable before.server)
  simpa only [RegistrationNativeExperiment.server, StateT.run, Functor.map_map, Prod.map,
    id_eq, nativeView, Function.comp_def] using law

/-- Main's actual World lift leaves the complete frontend and literal private KEM roster intact. -/
theorem world_input (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (stable : Stable RegistrationNativeWorldView.project work) :
    Stable (nativeView (KemSK := KemSK) (mlSource := mlSource)) (RegistrationNativeExperiment.world work) := by
  intro before
  have law := congrArg (fun distribution => (fun result => (result.1,
    { nativeView before with server := { (nativeView before).server with world :=
      { (nativeView before).server.world with world := (result.2, before.server.world.world.2) } } })) <$> distribution)
    (stable before.server.world.world.1)
  simpa only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run,
    Functor.map_map, Prod.map, id_eq, nativeView, RegistrationServerMaterialSourceState.nativeView,
    RegistrationServerRecordWorldSource.project, Function.comp_def] using law

/-- Real indexed KEM and ambient World requests ignore omitted bookkeeping while keeping all actual generated key and auxiliary state. -/
theorem trusted_input (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Stable (nativeView (mlSource := mlSource))
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource query) := by
  cases query with
  | inl effect => exact world_input _ (RegistrationNativeWorldViewEffects.effects_input effect)
  | inr query =>
      intro before
      let work := (RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
        (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run
          (before.server.world.auxiliary, before.pool)
      have first := RegistrationNativeWorldView.sampled work before.server.world.world.1
      have second := RegistrationNativeWorldView.sampled work (RegistrationNativeWorldView.project before.server.world.world.1)
      rw [RegistrationNativeWorldView.project_idempotent] at second
      have law := congrArg (fun distribution => (fun result => (result.1.1,
        { nativeView before with
          pool := result.1.2.2
          server := { (nativeView before).server with world := { (nativeView before).server.world with
            auxiliary := result.1.2.1
            world := (result.2, before.server.world.world.2) } } })) <$> distribution) (first.trans second.symm)
      simpa only [RegistrationNativeExperiment.trusted, work, StateT.run, bind_pure_comp,
        Functor.map_map, Prod.map, id_eq, nativeView, RegistrationServerMaterialSourceState.nativeView,
        RegistrationServerRecordWorldSource.project, Function.comp_def] using law

/-- Any adaptive trusted source program retains its complete literal outcome under the stated Main view. -/
theorem trusted_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    Stable (nativeView (mlSource := mlSource))
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) work) :=
  RegistrationStateView.program_stable nativeView view_idempotent _
    (trusted_input setup checks representation created) work

end BeaconcryptCore.Computational.RegistrationNativeMainViewLift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainViewLift.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainViewLift.view_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainViewLift.server_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainViewLift.server_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainViewLift.world_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainViewLift.world_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainViewLift.trusted_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainViewLift.trusted_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainViewLift.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainViewLift.trusted_program
