-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFinishFactor
import BeaconcryptCore.Computational.RegistrationNativeFinishTerminal
/-! The actual raw terminal tree has exact abort and successful known-kernel installation poststates. Complete frontend metadata, private KEM pool, World cache and counters are retained; the early aborted phase fuses with the completed phase. No successful-install premise is used: native readiness is derived by the lifecycle composition. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree
open RegistrationNativeBeaconFrontend (M Owner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def assemble (owners : List (Owner source)) (env : EnvState RegistrationServerRoleBackend.State) (state : Native) : Native :=
  {state with
    beacons := owners
    server := {state.server with world := RegistrationWorldAgreementCompiler.join env state.server.world.world.1}}

noncomputable def execute (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (reply : RustM (Option registration.CompletedBeacon))
    (owners : List (Owner source)) (env : EnvState RegistrationServerRoleBackend.State) (before : Native) :
    ProbComp (RustM (Option Pqxdh.Bytes) × Native) :=
  (fun result => (result.1.1.1, assemble result.1.1.2 result.1.2 result.2)) <$>
    (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      (((do
        RegistrationNativeBeaconFrontend.updatePhase index (.aborted control)
        RegistrationNativeFinishFactor.terminal index owner reply : M n KemSK source RegistrationServerRoleBackend.State _).run owners).run env)).run before

def bytes (reply : RustM (Option registration.CompletedBeacon)) : RustM (Option Pqxdh.Bytes) :=
  match reply with
  | .fail error => .fail error
  | .div => .div
  | .ok none => .ok none
  | .ok (some completed) => .ok (some (TranscriptAuthParts.absSlice completed.application))

def after (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted)
    (reply : RustM (Option registration.CompletedBeacon)) (before : Native) : Native :=
  match reply with
  | .ok (some completed) => RegistrationNativeFinishTerminal.installed index owner completed before
  | _ => RegistrationNativeFinishTerminal.aborted index owner control before

theorem abort_tree (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (value : RustM (Option Pqxdh.Bytes))
    (owners : List (Owner source)) (env : EnvState RegistrationServerRoleBackend.State) (before : Native)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    (fun result => (result.1.1.1, assemble result.1.1.2 result.1.2 result.2)) <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
        (((do
          RegistrationNativeBeaconFrontend.updatePhase index (.aborted control)
          RegistrationNativeBeaconFrontend.abort owner
          pure value : M n KemSK source RegistrationServerRoleBackend.State _).run owners).run env)).run before =
      pure (value, RegistrationNativeFinishTerminal.aborted index owner control (assemble owners env before)) := by
  simp only [RegistrationNativeBeaconFrontend.updatePhase, RegistrationNativeBeaconFrontend.abort,
    RegistrationNativeBeaconFrontend.effect, StateT.run_bind, StateT.run_map, StateT.run_lift,
    StateT.run_modify, bind_pure_comp, pure_bind, Functor.map_map, simulateQ_map, simulateQ_spec_query]
  rw [RegistrationNativeFinishTerminal.abort_native_effect setup checks representation created owner.worldOwner before ready]
  simp only [map_pure]
  rfl

theorem install_tree (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (completed : registration.CompletedBeacon)
    (owners : List (Owner source)) (env : EnvState RegistrationServerRoleBackend.State) (before : Native)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    execute setup checks representation created index owner control (.ok (some completed)) owners env before =
      pure (.ok (some (TranscriptAuthParts.absSlice completed.application)),
        RegistrationNativeFinishTerminal.installed index owner completed (assemble owners env before)) := by
  unfold execute
  simp only [RegistrationNativeFinishFactor.terminal, RegistrationNativePlatformBeaconFinish.install_exact]
  simp only [RegistrationNativeBeaconFrontend.updatePhase, RegistrationNativeBeaconFrontend.effect,
    StateT.run_bind, StateT.run_modify, StateT.run_map, StateT.run_lift,
    bind_pure_comp, pure_bind, Functor.map_map, simulateQ_map, simulateQ_bind, simulateQ_spec_query]
  rw [BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall.native setup checks representation created owner.worldOwner _ completed.kernel before ready]
  simp only [map_pure, pure_bind, ite_true]
  change (pure (RustM.ok (some (TranscriptAuthParts.absSlice completed.application)), assemble (RegistrationNativeFinishTerminal.setPhase index (.established ⟨completed.control, completed.binding, completed.application⟩)
    (RegistrationNativeFinishTerminal.setPhase index (.aborted control) owners)) env _) : ProbComp (RustM (Option Pqxdh.Bytes) × Native)) = _
  rw [RegistrationNativeFinishTerminal.phase_fusion]
  rfl


theorem execute_exact (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (reply : RustM (Option registration.CompletedBeacon))
    (owners : List (Owner source)) (env : EnvState RegistrationServerRoleBackend.State) (before : Native)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    execute setup checks representation created index owner control reply owners env before =
      pure (bytes reply, after index owner control reply (assemble owners env before)) := by
  cases reply with
  | fail error => simpa only [execute, RegistrationNativeFinishFactor.terminal, bytes, after, seqRight_eq_bind] using abort_tree setup checks representation created index owner control (.fail error) owners env before ready
  | div => simpa only [execute, RegistrationNativeFinishFactor.terminal, bytes, after, seqRight_eq_bind] using abort_tree setup checks representation created index owner control .div owners env before ready
  | ok optional => cases optional with
    | none => simpa only [execute, RegistrationNativeFinishFactor.terminal, bytes, after, seqRight_eq_bind] using abort_tree setup checks representation created index owner control (.ok none) owners env before ready
    | some completed => exact install_tree setup checks representation created index owner control completed owners env before ready


end BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree.abort_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree.abort_tree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree.install_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree.install_tree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree.execute_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree.execute_exact
