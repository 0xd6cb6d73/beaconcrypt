-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyBackend
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRaw
import BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized

/-! The selective restricted environment retains actual frontend metadata, selected material44, cached nonselected known108 outputs, opaque KEM state and signing receipts. Only the selected hidden64 record seeds and their kernels remain private to the shared World; ordinary known output material stays environment-owned. Actual effectful startup is supplied separately, and initialized entropy statements never invoke this environment's pure-start field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyEnvironment
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK ProviderState : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePublicFrontend.State source × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState

noncomputable def step (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) :
    QueryImpl RegistrationNativeEntropyInterface.EnvSpec
      (StateT (State n KemSK ProviderState source) (OracleComp (EnvEffects n))) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeSelectiveEntropyBackend.restricted setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider)
      ((RegistrationNativeHiddenEnvironmentRaw.frontend setup checks wire source (RegistrationNativeMldsa.owned source credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar) (.inr query.val)).run before.1)).run before.2

noncomputable def environment (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState source))) :
    RegistrationNativeEntropyInterface.Environment n (State n KemSK ProviderState source) :=
  ⟨startup, step setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept⟩

/-- The actual raw native registration callback, including every failure poststate, has exactly the restricted environment AST after embedding in the shared World. -/
theorem step_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : State n KemSK ProviderState source) :
    simulateQ effectLift ((step setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept query).run before) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider)
          ((RegistrationNativeHiddenEnvironmentRaw.frontend setup checks wire source (RegistrationNativeMldsa.owned source credential)
            selectedOwner selectedAccept (setup.dh.publicKey scalar) (.inr query.val)).run before.1)).run before.2 := by
  simp only [step, StateT.run, simulateQ_map]
  have sourceLaw := RegistrationNativeSelectiveEntropyBackend.program_local setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider _ (RegistrationNativeHiddenEnvironmentRaw.raw_zero setup checks wire source
      (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar) query before.1) before.2
  simpa only [StateT.run] using congrArg (fun distribution =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) sourceLaw

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyEnvironment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyEnvironment.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyEnvironment.step_source
