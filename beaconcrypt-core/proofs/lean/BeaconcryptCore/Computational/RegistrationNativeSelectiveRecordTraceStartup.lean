-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup
import BeaconcryptCore.Computational.RegistrationNativeG2Trace

/-! The actual selective startup and original ledger retain the complete native installation trace as reduction-owned observation. Erasing that trace recovers the identical original World program, including constructor failures, ML credential generation and the shared pin hash. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev Extra (n : Nat) (KemSK ProviderState : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source × RegistrationNativeG2Trace.State

abbrev Outcome (n : Nat) (KemSK ProviderState Value : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeEntropyRun.Outcome (Extra n KemSK ProviderState source) Value

def forget {source : RegistrationNativeMldsa.Source} (result : Outcome n KemSK ProviderState Value source) :
    RegistrationNativeEntropyRun.Outcome (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) Value :=
  result.map (fun finished => (finished.1, finished.2.1, finished.2.2.1))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

noncomputable def after (started : RegistrationNativeHiddenStartup.Started source) : OracleComp (WorldSpec n)
    (Outcome n KemSK ProviderState Value source) :=
  (fun observed => some (PqxdhRegistrationJointServerBirth.encode started.created, observed.1.1.1,
    ((observed.1.1.2, observed.2), observed.1.2))) <$>
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire (RegistrationNativeMldsa.owned source started.native.credential)
      seed scalar candidate provider)
      (RegistrationNativeG2Trace.program (RegistrationNativePublicFrontend.run setup checks wire source
        (RegistrationNativeMldsa.owned source started.native.credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
        serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed, started.native.credential.publicKey, serverKeyId⟩)
        started.native.frontend))).run (RegistrationNativeSelectiveHiddenInterpreter.initial providerState)

noncomputable def program : OracleComp (WorldSpec n) (Outcome n KemSK ProviderState Value source) := do
  let initialized ← RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
  match initialized with
  | none => pure none
  | some started => after setup checks wire source serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary started

/-- The trace observer changes no actual selective startup or original-ledger World callback. -/
theorem erase :
    forget <$> program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary =
      RegistrationNativeSelectiveRecordStartup.program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary := by
  unfold program RegistrationNativeSelectiveRecordStartup.program RegistrationNativeSelectiveHiddenStartup.program
  rw [map_bind, map_bind]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some started =>
      have erased := congrArg (fun work => (simulateQ
        (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire (RegistrationNativeMldsa.owned source started.native.credential)
          seed scalar candidate provider) work).run (RegistrationNativeSelectiveHiddenInterpreter.initial providerState))
        (RegistrationNativeG2Trace.program_erase
          (RegistrationNativePublicFrontend.run (n := n) setup checks wire source (RegistrationNativeMldsa.owned source started.native.credential)
            selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode
            (adversary ⟨setup.joint.publicKeys seed, started.native.credential.publicKey, serverKeyId⟩) started.native.frontend)
          RegistrationNativeG2Trace.initial)
      simp only [simulateQ_map, StateT.run_map] at erased
      simp only [after, RegistrationNativeSelectiveRecordStartup.outcome, RegistrationNativeSelectiveHiddenInterpreter.run,
        bind_pure_comp, Functor.map_map]
      rw [← erased]
      simp only [Functor.map_map]
      rfl

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceStartup.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceStartup.erase
