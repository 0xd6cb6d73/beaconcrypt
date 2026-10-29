-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource

/-! The complete actual generated native profile is the value component of the lazy joint-use report source. This source identity includes native startup failures, mandatory authentication, raw wire/ledger commands, reached World state and every local signing attempt; the monitor adds only public history and origin observations. Routing this unbounded lazy source into the finite multi-user primitive requires a separate creation bound or verified budget stop. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportProfile
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Ordinary report instrumentation preserves the exact original full native profile event distribution. -/
theorem native_value (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (count : Nat) :
    Prod.fst <$> PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit
        identityIndex serverKeyId bounds mode adversary event) =
      RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit
        identityIndex serverKeyId bounds mode adversary (fun result => event (RegistrationNativeIdentityMainProfile.ledgerOnly result)) := by
  have projected := congrArg (fun distribution => Prod.fst <$> distribution)
    (RegistrationNativeIdentityReportSource.run_source setup.joint count
      (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit
        identityIndex serverKeyId bounds mode adversary event))
  simp only [Functor.map_map, Prod.map_def, id_eq] at projected
  change _ = (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
    (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit
      identityIndex serverKeyId bounds mode adversary event)).run' PqxdhDynamicIdentityPool.initialState at projected
  rw [RegistrationNativeIdentityMainProfile.client_source] at projected
  exact projected

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportProfile.native_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportProfile.native_value
