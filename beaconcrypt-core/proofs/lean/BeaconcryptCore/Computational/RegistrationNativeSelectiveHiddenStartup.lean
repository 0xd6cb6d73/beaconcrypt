-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter

/-! Selective G3 retains the literal effectful native constructor, ML credential generation, Server import and same-World ML-pin hash. Only the subsequent private material-service state adds reduction-owned nonselected uniform108-byte outputs. Failed initialization remains absent, and every original secrecy-ledger command remains inside the actual native frontend run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev Started := RegistrationNativeHiddenStartup.Started
noncomputable abbrev start := @RegistrationNativeHiddenStartup.start

noncomputable def program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) := do
  let initialized ← RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
  match initialized with
  | none => pure none
  | some started =>
      let observed ← RegistrationNativeSelectiveHiddenInterpreter.run setup checks wire source started.native.credential seed scalar candidate provider
        selectedOwner selectedAccept serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys seed, started.native.credential.publicKey, serverKeyId⟩)
        started.native.frontend (RegistrationNativeSelectiveHiddenInterpreter.initial providerState)
      pure (some (started.created, observed))

/-- Selective startup uses the same actual native initialization AST, retaining all constructor and ML failure probabilities. -/
theorem start_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) :
    start (n := n) setup source ensureInit identityIndex serverKeyId identity =
      RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity := rfl

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenStartup.start_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenStartup.start_source
