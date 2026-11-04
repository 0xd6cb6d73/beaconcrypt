-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted

/-! An arbitrary actual Beacon frontend continuation is interpreted through private indexed KEM leaves while retaining the entire source state and every actual draw count. Reassembling the client state with its private pool recovers the literal original native execution. This applies to corrected finish bodies without identifying old and corrected complete profiles. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemServerState (State ofNative toNative)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationNativeKemCountedTrusted (execute project)
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Client" => State n source

noncomputable def program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) :
    StateT Client (OracleComp (Spec KemSK)) Value := fun before => do
  let result ← (simulateQ (RegistrationNativeKemCountedTrusted.implementation setup checks representation created)
    ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before
  pure (result.1.1.1, { result.2 with beacons := result.1.1.2, server := { result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

/-- All actual Beacon frontend control and native/private state are retained through the counted indexed source. -/
theorem source_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) (before : Native) :
    (execute setup (program setup checks representation created work)).run (project before) =
      Prod.map id project <$> (RegistrationNativeExperiment.beacon setup checks representation created work).run before := by
  have law := congrArg (fun distribution => (fun result => (result.1.1.1,
      ({ result.2.1 with beacons := result.1.1.2, server := { result.2.1.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.1.server.world.world.1 } }, result.2.2))) <$> distribution)
    (RegistrationNativeKemCountedTrusted.program_source setup checks representation created
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) before)
  simp only [execute, RegistrationNativeKemCountedProgram.runState, RegistrationNativeKemCountedProgram.evaluate,
    program, StateT.run, bind_pure_comp, simulateQ_map, map_apply, Functor.map_map,
    RegistrationNativeExperiment.beacon, project, RegistrationNativeKemCountedTrusted.arrange, ofNative, Prod.map, id_eq] at law ⊢
  exact law

def restore (before : Client × Pool KemSK) : Native := toNative before.1 before.2

/-- Reassembling the full private pool recovers the literal complete actual native Beacon execution and all its counters. -/
theorem native_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) (before : Native) :
    Prod.map id restore <$> (execute setup (program setup checks representation created work)).run (project before) =
      (RegistrationNativeExperiment.beacon setup checks representation created work).run before := by
  rw [source_program, Functor.map_map]
  change id <$> _ = _
  exact id_map _

end BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon.source_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon.native_source
