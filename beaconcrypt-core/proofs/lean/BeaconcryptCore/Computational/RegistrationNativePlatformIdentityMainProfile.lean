-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainFull
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile

/-! The complete current dynamic-writer native profile is interpreted by one executable ordinary joint-Ed client. Startup constructs the independent Server/ML/KEM auxiliary state internally; the challenged Beacon Ed seed is supplied only by its generated indexed service. Every constructor/API failure and full shared P poststate is retained. This is source correspondence, not yet a publication-security reduction or restricted-root confidentiality client. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project liftMain)
open RegistrationNativePlatformIdentityMainOwned (Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

def fromInitial (initial : RegistrationNativeExperiment.Initial n KemSK source) (previous : Platform) : State n KemSK source × Platform :=
  (RegistrationNativeIdentityMainProfile.fromInitial initial, previous)

omit primitives in
/-- Actual startup begins with no Beacon identities, so every private joint source table has the generated-row invariant. -/
theorem initial_owned (joint : PqxdhJointIdentity.Primitives) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (previous : Platform) (pool : SourceState) : Owned joint (fromInitial initial previous, pool) :=
  RegistrationNativeIdentityMainProfile.initial_owned joint initial pool

omit primitives in
/-- The complete actual generated initial native/platform state is restored, including private startup counters/cache and the original P. -/
theorem initial_project (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (empty : initial.state.beacons = []) (previous : Platform) (pool : SourceState) :
    project (fromInitial initial previous, pool) = (initial.state, previous) :=
  congrArg (fun native => (native, previous)) (RegistrationNativeIdentityMainProfile.initial_project initial empty pool)

noncomputable def client (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (previous : Platform) :
    OracleComp PqxdhJointPhase1Reports.ProtocolSpec (Bool × Platform) := do
  let initialized ← simulateQ RegistrationNativeIdentityMain.coins
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure (false, previous)
  | some initial =>
    let result ← (RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public)).run (fromInitial initial previous)
    let _ ← RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityFinalReports.reports
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) result.1.2.transcript result.2.1.beacons)
    pure (event (result.1.1, (result.1.2, ())), result.2.2)

/-- One executable ordinary joint client realizes the complete actual initialized current runtime, retaining the original ledger event and complete P state with no source-game equality premise. -/
theorem client_source (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (previous : Platform) (before : SourceState) :
    (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
      (client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary event previous)).run' before =
      ((RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        (fun result => event (result.1, (result.2.1, ())))).run previous) := by
  unfold client RegistrationNativePlatformOrdinaryExperiment.profile
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, StateT.run_lift,
    map_bind, bind_assoc, pure_bind]
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
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | some initial =>
    have empty := RegistrationNativeScalarRun.start_empty setup source ensureInit identityIndex serverKeyId initial actual
    have same := RegistrationNativePlatformIdentityMainFull.run_event_joint setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) event
      (fromInitial initial previous, privatePool) (initial_owned setup.joint initial previous privatePool)
    rw [initial_project initial empty previous privatePool] at same
    simpa only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
      RegistrationNativeIdentityMainSource.emit_source, map_pure, pure_bind, bind_pure_comp,
      Functor.map_map, map_bind] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile.initial_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile.initial_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile.initial_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile.initial_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainProfile.client_source
