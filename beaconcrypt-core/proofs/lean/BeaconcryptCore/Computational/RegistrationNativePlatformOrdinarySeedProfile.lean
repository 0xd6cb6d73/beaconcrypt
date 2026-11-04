-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRun
import BeaconcryptCore.Computational.RegistrationNativeSeedStart
/-! Actual generated runtime startup commutes with the independent private Server seed and selected owner scalar. The original constructor draws, all failures, the exact Native observation and persistent platform state remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySeedProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Public)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selected : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool)

noncomputable def profile : StateT Platform ProbComp Bool := do
  let seed ← StateT.lift PqxdhJointIdentity.sampleSeed
  let scalar ← StateT.lift PqxdhJointGapDh.sampleScalar
  let initialized ← StateT.lift (RegistrationNativeSeedStart.start setup source ensureInit identityIndex serverKeyId seed)
  match initialized with
  | none => pure false
  | some initial =>
      (fun result => event (result.1.1, (result.1.2, result.2))) <$>
        RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation initial.created source initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selected scalar bounds mode (adversary initial.public) initial.state

/-- The literal actual source-runtime profile has the same full event/P law under independently sampled private source challenges. -/
theorem source_law (previous : Platform) :
    (RegistrationNativePlatformOrdinaryExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event).run previous =ᵈ
      (profile setup checks wire route representation source ensureInit identityIndex serverKeyId selected view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event).run previous := by
  refine (RegistrationNativePlatformOrdinaryScalarRun.profile setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId selected bounds mode adversary event previous).trans ?_
  unfold RegistrationNativePlatformOrdinaryScalarEager.profile profile
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointIdentity.sampleSeed PqxdhJointGapDh.sampleScalar
    (fun seed scalar => do
      let initialized ← RegistrationNativeSeedStart.start setup source ensureInit identityIndex serverKeyId seed
      ((match initialized with
        | none => pure false
        | some initial =>
          (fun result => event (result.1.1, (result.1.2, result.2))) <$>
            RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation initial.created source initial.credential view failure allocation
              reserveRegistration reservePeer reserveFrame erased helper writer selected scalar bounds mode (adversary initial.public) initial.state) : StateT Platform ProbComp Bool).run previous)).symm
  apply _root_.EvalDistEq.bind_right
  intro scalar
  have changed := (RegistrationNativeSeedStart.eager (n := n) setup source ensureInit identityIndex serverKeyId).bind_left
    (fun initialized => ((match initialized with
      | none => pure false
      | some initial =>
        (fun result => event (result.1.1, (result.1.2, result.2))) <$>
          RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation initial.created source initial.credential view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer selected scalar bounds mode (adversary initial.public) initial.state) : StateT Platform ProbComp Bool).run previous)
  simp only [bind_assoc] at changed
  convert changed using 1
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySeedProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySeedProfile.source_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySeedProfile.source_law
