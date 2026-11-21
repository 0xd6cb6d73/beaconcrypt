-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderSource
import BeaconcryptCore.Computational.RegistrationNativePublicStartup

/-! The executable provider reference client contains no Server seed or selected scalar. It performs the actual public constructor and ML startup, then draws provider data at the reserved-provider position before entering the unchanged full native ledger. The distinct candidate-source projection is not supplied by this generic root-family distance theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderStartup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRelatedRoot (RootSpec)
open RegistrationNativeProviderInterpreter (Provider)
variable {n : Nat} {ι KemSK Data ProviderState Value : Type} {base : OracleSpec ι}

/-- Provider data are sampled after successful actual startup and before the first public query; the original private ledger and decision are retained literally. -/
noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (draw : ProbComp Data) (provider : Data → Provider KemSK ProviderState) (providerInitial : Data → ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (decision : Value × RegistrationNativeLedger.State → Bool)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp RootSpec Bool := do
  let initialized ← (RegistrationNativePublicStartup.start (n := n) setup source ensureInit identityIndex serverKeyId
    publicValue.identity).run RegistrationNativePublicInterpreter.initial
  match initialized.1 with
  | none => pure false
  | some started => do
      let reserved ← (RegistrationNativePublicInterpreter.world (KemSK := KemSK)
        (PqxdhRecordLiftWorld.sampled draw)).run initialized.2
      let observed ← RegistrationNativeProviderInterpreter.run setup checks wire route source
        (RegistrationNativeMldsa.owned source started.credential) (provider reserved.1)
        selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
        (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend
        (reserved.2, providerInitial reserved.1)
      pure (decision observed.1.1)

/-- The concrete provider client pays exactly the native related-root advantage, with all provider data, coins and original ledger inside that executable client. -/
theorem family_distance (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (draw : ProbComp Data) (provider : Data → Provider KemSK ProviderState) (providerInitial : Data → ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (decision : Value × RegistrationNativeLedger.State → Bool)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    (RegistrationNativeRelatedRoot.sourceGame setup.source setup.hmac setup.joint setup.dh
      (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId draw provider providerInitial
        selectedOwner selectedAccept bounds mode decision adversary)).boolDistance
      (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId draw provider providerInitial
          selectedOwner selectedAccept bounds mode decision adversary)) =
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId draw provider providerInitial
            selectedOwner selectedAccept bounds mode decision adversary publicValue)) :=
  RegistrationNativeRelatedRoot.advantage_exact setup.source setup.hmac correct setup.joint setup.dh _

end BeaconcryptCore.Computational.RegistrationNativeProviderStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderStartup.family_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderStartup.family_distance
