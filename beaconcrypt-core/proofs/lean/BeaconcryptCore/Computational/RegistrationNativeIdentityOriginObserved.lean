-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportProfile

/-! A public execution observer retains the same actual startup, native ledger and final opaque-identity roster before the retrospective origin report batch. Private interpretation restores the original complete native outcome; no selected signing seed is part of the executable client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginObserved
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainProfile (fromInitial ledgerOnly)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    OracleComp PqxdhJointPhase1Reports.ProtocolSpec (Option (RegistrationNativeEvents.Observed Value (State n KemSK source))) := do
  let initialized ← simulateQ RegistrationNativeIdentityMain.coins
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure none
  | some initial =>
      let result ← RegistrationNativeIdentityMain.run setup checks wire route representation initial.created initial.credential bounds mode
        (adversary initial.public) (fromInitial initial)
      let _ ← RegistrationNativeIdentityMain.emit
        (RegistrationNativeIdentityFinalReports.reports wire result.2.1.transcript result.2.2.beacons)
      pure (some result)

def sourceProject {source : RegistrationNativeMldsa.Source}
    (result : Option (RegistrationNativeEvents.Observed Value (State n KemSK source)) × SourceState) :
    Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)) :=
  result.1.map fun observed => RegistrationNativeIdentityMainFull.observedProject (observed, result.2)

noncomputable def native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    ProbComp (Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))) := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure none
  | some initial => some <$> (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential
      bounds mode (adversary initial.public) initial.state)

/-- The ordinary client differs from this retained public execution only in its final public ledger observation. -/
theorem client_map (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) :
    RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary event =
      (fun result => result.any (fun observed => event (ledgerOnly observed))) <$>
        client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary := by
  unfold RegistrationNativeIdentityMainProfile.client client
  simp only [map_bind]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial => simp only [map_bind, map_pure, Option.any_some]

/-- Actual source interpretation retains every original native poststate and ledger, including every optional constructor failure. -/
theorem client_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : SourceState) :
    sourceProject <$> (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
      (client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary)).run before =
        native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary := by
  unfold client native
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  conv_rhs => rw [← RegistrationNativeIdentityMainProfile.coins_value setup.joint
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) before]
  rw [bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨initialized, privatePool⟩ reached
  have actual : initialized ∈ support (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) := by
    rw [← RegistrationNativeIdentityMainProfile.coins_value setup.joint
      (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) before, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  cases initialized with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure, sourceProject, Option.map_none]
  | some initial =>
      have empty := RegistrationNativeScalarRun.start_empty setup source ensureInit identityIndex serverKeyId initial actual
      have same := RegistrationNativeIdentityMainFull.full_source setup checks wire route representation initial.created initial.credential
        bounds mode (adversary initial.public) (fromInitial initial, privatePool)
        (RegistrationNativeIdentityMainProfile.initial_owned setup.joint initial privatePool)
      rw [RegistrationNativeIdentityMainProfile.initial_project initial empty privatePool] at same
      have optional := congrArg (fun distribution => some <$> distribution) same
      simpa only [simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
        RegistrationNativeIdentityMainSource.emit_source, map_pure, pure_bind, bind_pure_comp,
        Functor.map_map, map_bind, sourceProject, Option.map_some] using optional

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginObserved

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginObserved.client_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginObserved.client_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginObserved.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginObserved.client_source
