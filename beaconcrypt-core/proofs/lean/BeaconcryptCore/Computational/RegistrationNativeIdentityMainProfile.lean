-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainFull
import BeaconcryptCore.Computational.RegistrationNativeScalarRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityFinalReports

/-! The ordinary joint-service native client starts at the actual native Server constructor, including initialization and ML failure. Generated Beacon identity ownership starts at its empty public roster. Native CE observations use the unchanged complete secrecy ledger; no generated Beacon seed enters the executable client or its observer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (project Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

def ledgerOnly {NativeState : Type} (result : RegistrationNativeEvents.Observed Value NativeState) :
    RegistrationNativeEvents.Observed Value Unit := (result.1, (result.2.1, ()))

def fromInitial (initial : RegistrationNativeExperiment.Initial n KemSK mlSource) : State n KemSK mlSource :=
  ⟨RegistrationNativeIdentityWorld.project initial.state, []⟩

/-- Actual generated startup establishes credential ownership for every private joint source table. -/
theorem initial_owned (joint : PqxdhJointIdentity.Primitives)
    (initial : RegistrationNativeExperiment.Initial n KemSK mlSource) (pool : SourceState) :
    Owned joint (fromInitial initial, pool) := RegistrationNativeIdentitySourceCreateOwned.empty_owned joint pool

/-- The empty native owner roster from actual startup restores to exactly the complete original initial native state. -/
theorem initial_project (initial : RegistrationNativeExperiment.Initial n KemSK mlSource)
    (empty : initial.state.beacons = []) (pool : SourceState) :
    project (fromInitial initial, pool) = initial.state := by
  rcases initial with ⟨created, credential, state⟩
  rcases state with ⟨server, owners, kem, parsed⟩
  dsimp only at empty
  subst owners
  rfl

/-- Bare native randomness has its original exact value distribution in the ordinary joint source. -/
theorem coins_value (joint : PqxdhJointIdentity.Primitives) (work : ProbComp Value) (before : SourceState) :
    Prod.fst <$>
      (simulateQ (RegistrationNativeIdentityMainSource.implementation joint)
        (simulateQ RegistrationNativeIdentityMain.coins work)).run before = work := by
  have same := congrArg (fun distribution => Prod.fst <$> distribution)
    (RegistrationNativeIdentityMainSource.coins_source joint work before)
  simp only [Functor.map_map, Prod.map, id_eq] at same
  change _ = (id : Value → Value) <$> work at same
  rw [id_map] at same
  exact same

/-- A native ledger observer has its exact original distribution after complete raw-CBOR source realization. -/
theorem run_event_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool)
    (before : State n KemSK mlSource × SourceState) (owned : Owned setup.joint before) :
    (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
      ((fun result => event (ledgerOnly result)) <$>
        RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work before.1)).run' before.2 =
      (fun result => event (ledgerOnly result)) <$>
        RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work (project before) := by
  have same := congrArg (fun distribution => (fun result => event (ledgerOnly result)) <$> distribution)
    (RegistrationNativeIdentityMainFull.full_source setup checks wire route representation created credential bounds mode work before owned)
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    RegistrationNativeIdentityMainFull.observedProject, ledgerOnly] at same ⊢
  exact same

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) : OracleComp PqxdhJointPhase1Reports.ProtocolSpec Bool := do
  let initialized ← simulateQ RegistrationNativeIdentityMain.coins
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure false
  | some initial =>
      let result ← RegistrationNativeIdentityMain.run setup checks wire route representation initial.created initial.credential bounds mode
        (adversary initial.public) (fromInitial initial)
      let _ ← RegistrationNativeIdentityMain.emit
        (RegistrationNativeIdentityFinalReports.reports wire result.2.1.transcript result.2.2.beacons)
      pure (event (ledgerOnly result))

/-- The complete actual generated native profile, including every constructor failure, is realized by one concrete ordinary joint-service client with the original native ledger event. -/
theorem client_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (before : SourceState) :
    (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
      (client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary event)).run' before =
      RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary
        (fun result => event (ledgerOnly result)) := by
  unfold client RegistrationNativeExperiment.profile
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  conv_rhs => rw [← coins_value setup.joint (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) before]
  rw [bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨initialized, privatePool⟩ reached
  have actual : initialized ∈ support (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) := by
    rw [← coins_value setup.joint (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) before, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  cases initialized with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | some initial =>
      have empty := RegistrationNativeScalarRun.start_empty setup source ensureInit identityIndex serverKeyId initial actual
      have same := run_event_source setup checks wire route representation initial.created initial.credential bounds mode
        (adversary initial.public) event (fromInitial initial, privatePool) (initial_owned setup.joint initial privatePool)
      rw [initial_project initial empty privatePool] at same
      simpa only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
        RegistrationNativeIdentityMainSource.emit_source, map_pure, pure_bind, bind_pure_comp,
        Functor.map_map, map_bind] using same

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.initial_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.initial_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.initial_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.initial_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.coins_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.coins_value
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.run_event_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.run_event_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile.client_source
