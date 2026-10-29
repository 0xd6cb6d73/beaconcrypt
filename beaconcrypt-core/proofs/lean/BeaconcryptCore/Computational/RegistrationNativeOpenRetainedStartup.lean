-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenRetained
import BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup

/-! The open retained client runs the literal generated public startup and full original raw/secrecy compiler. Only KEM operations remain in the external opaque-pool interface; all startup hashing and subsequent ordinary World work share the returned World/cache. Neither selected secret is supplied to this executable frontend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenRetainedStartup
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def coins : QueryImpl unifSpec (OracleComp (RegistrationNativeOpenRetained.Spec KemSK)) :=
  RegistrationNativeOpenRetained.baseLift ∘ₛ RegistrationNativePublicRetained.coins

noncomputable def start (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) :
    OracleComp (RegistrationNativeOpenRetained.Spec KemSK)
      (Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State n) :=
  simulateQ coins ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run
    PqxdhRecordLiftWorld.initial)

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Bool := do
  let initialized ← start (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity
  match initialized.1 with
  | none => pure false
  | some started =>
      RegistrationNativeOpenRetained.client setup wire route (RegistrationNativeMldsa.owned source started.credential)
        ((decision ∘ Prod.fst) <$>
          RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
            selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
            (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend)
        { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 }

end BeaconcryptCore.Computational.RegistrationNativeOpenRetainedStartup
