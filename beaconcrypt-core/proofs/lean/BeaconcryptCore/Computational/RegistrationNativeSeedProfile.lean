-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedStart
import BeaconcryptCore.Computational.RegistrationNativeScalarRun

/-! The original generated native profile samples the private Server identity and selected owner scalar independently before its actual counted constructor work. The source program still performs both original discarded draws at their actual positions, preserving complete original raw/secrecy observations and all source failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedProfile
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Public)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selected : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let initialized ← RegistrationNativeSeedStart.start setup source ensureInit identityIndex serverKeyId seed
  match initialized with
  | none => pure false
  | some initial => event <$> (RegistrationNativeScalarEager.run setup checks wire route representation initial.created source initial.credential
      selected scalar bounds mode (adversary initial.public) initial.state)

/-- Actual original generated-startup execution equals the concrete independent private identity/scalar challenge profile, retaining the complete original observation and source failure distribution. -/
theorem source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selected : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) :
    RegistrationNativeExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary event =ᵈ
      profile setup checks wire route representation source ensureInit identityIndex serverKeyId selected bounds mode adversary event := by
  refine (RegistrationNativeScalarRun.profile setup checks wire route representation source ensureInit identityIndex serverKeyId selected bounds mode adversary event).trans ?_
  unfold RegistrationNativeScalarEager.profile profile
  refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointIdentity.sampleSeed PqxdhJointGapDh.sampleScalar
    (fun seed scalar => do
      let initialized ← RegistrationNativeSeedStart.start setup source ensureInit identityIndex serverKeyId seed
      match initialized with
      | none => pure false
      | some initial => event <$> (RegistrationNativeScalarEager.run setup checks wire route representation initial.created source initial.credential
          selected scalar bounds mode (adversary initial.public) initial.state))).symm
  apply _root_.EvalDistEq.bind_right
  intro scalar
  have changed := (RegistrationNativeSeedStart.eager (n := n) setup source ensureInit identityIndex serverKeyId).bind_left
    (fun initialized => match initialized with
      | none => pure false
      | some initial => event <$> (RegistrationNativeScalarEager.run setup checks wire route representation initial.created source initial.credential
          selected scalar bounds mode (adversary initial.public) initial.state))
  simp only [bind_assoc] at changed ⊢
  exact changed

end BeaconcryptCore.Computational.RegistrationNativeSeedProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedProfile.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedProfile.source
