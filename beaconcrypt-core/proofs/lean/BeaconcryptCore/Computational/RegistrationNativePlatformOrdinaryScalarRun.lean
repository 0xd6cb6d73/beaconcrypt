-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarProgram
import BeaconcryptCore.Computational.RegistrationNativeScalarRun
/-! The actual corrected raw/secrecy compiler and generated-startup profile preserve the complete original observation, Native poststate and persistent P when the selected birth scalar is moved to an independent private early draw. Dynamic registration/ordinary failures and source counter observations are unrestricted. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeExperiment (State Public)
variable {n : Nat} {Platform E Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "ordinary" => RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer


local notation "eagerHandler" => RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer




/-- The actual canonical-wire raw run retains its full ledger, native state and common P law in every mode. -/
theorem run (selected : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (previous : Platform) (short : before.beacons.length ≤ selected) :
    (RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous =ᵈ
      (do let scalar ← PqxdhJointGapDh.sampleScalar
          (RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation created source credential view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer selected scalar bounds mode work before).run previous) :=
  RegistrationNativePlatformOrdinaryScalarProgram.eager setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer selected
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      created.server.server.metadata.sender bounds mode work) before previous short

attribute [local irreducible] RegistrationNativePlatformOrdinaryExperiment.run RegistrationNativePlatformOrdinaryScalarEager.run RegistrationNativeExperiment.start

/-- Actual generated startup derives the waiting premise and preserves the entire Bool/P profile law for every adversary/event. -/
theorem profile (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selected : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) (previous : Platform) :
    (RegistrationNativePlatformOrdinaryExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event).run previous =ᵈ
      (RegistrationNativePlatformOrdinaryScalarEager.profile setup checks wire route representation source ensureInit identityIndex serverKeyId
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected bounds mode adversary event).run previous := by
  unfold RegistrationNativePlatformOrdinaryExperiment.profile RegistrationNativePlatformOrdinaryScalarEager.profile
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointGapDh.sampleScalar
    (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)
    (fun (scalar : PqxdhJointGapDh.ScalarBytes) (initialized : Option (RegistrationNativeExperiment.Initial n KemSK source)) =>
      ((match initialized with
        | none => pure false
        | some initial =>
          (fun result => event (result.1.1, result.1.2, result.2)) <$>
            RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation initial.created source initial.credential
              view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected scalar bounds mode
              (adversary initial.public) initial.state) : StateT Platform ProbComp Bool).run previous)).symm
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro initialized present
  cases initialized with
  | none =>
    simp only [StateT.run_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | some initial =>
    have short : initial.state.beacons.length ≤ selected := by
      rw [RegistrationNativeScalarRun.start_empty setup source ensureInit identityIndex serverKeyId initial present]
      simp only [List.length_nil, Nat.zero_le]
    simpa only [StateT.run_map, map_bind] using
      (run setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer selected bounds mode (adversary initial.public) initial.state previous short).map
          (fun result => (event (result.1.1.1, (result.1.1.2, result.1.2)), result.2))

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRun.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRun.profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRun.profile
