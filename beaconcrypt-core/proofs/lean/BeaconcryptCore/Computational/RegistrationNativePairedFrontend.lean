-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedBeacon
import BeaconcryptCore.Computational.RegistrationNativePairedServer
import BeaconcryptCore.Computational.RegistrationNativePairedOther

/-! The complete original native frontend preserves the paired-slot monitor through both actual material roles and every installation-free command. This is an open-program fact for all callback replies and complete original native ledgers, with no private source or lifecycle premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePairedTrace (Safe)
open RegistrationNativePublicFrontend (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem mapped {Next : Type}
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (observe : Value → Next)
    (safe : Safe work) : Safe (observe <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact RegistrationNativePairedTrace.bind_safe work _ safe (fun value => RegistrationNativePairedTrace.pure_safe (observe value))

/-- Every actual typed native command preserves a clean paired monitor under arbitrary source replies. -/
theorem query (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    Safe ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before) := by
  by_cases quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5
  · exact RegistrationNativePairedSafe.free _ (fun role =>
      RegistrationNativePairedOther.other_free role setup checks wire sign selectedOwner selectedAccept publicPrekey query quiet before)
  · cases query with
    | inl coin => exact (quiet (by simp [RegistrationNativeRawAdapter.kind])).elim
    | inr command => cases command with
      | build handle application =>
          exact RegistrationNativePairedServer.frontend_build setup checks wire source sign selectedOwner selectedAccept publicPrekey handle application before
      | finish index packet =>
          simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon, StateT.run]
          exact mapped _ _ (RegistrationNativePairedBeacon.owners setup source index packet before.beacons before.environment)
      | _ => exact (quiet (by simp [RegistrationNativeRawAdapter.kind])).elim

/-- Adaptive typed continuations retain the same paired observer through their complete mutable frontend state. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State source) :
    Safe ((simulateQ (RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact RegistrationNativePairedTrace.pure_safe _
  | query_bind request next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact RegistrationNativePairedTrace.bind_safe _ _
        (query setup checks wire sign selectedOwner selectedAccept publicPrekey request before) (fun reached => ih reached.1 reached.2)

/-- The literal complete original raw/secrecy ledger is covered by the same paired monitor without a full-game correspondence assumption. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    Safe (RegistrationNativePublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before) :=
  program setup checks wire sign selectedOwner selectedAccept publicPrekey _ before
end BeaconcryptCore.Computational.RegistrationNativePairedFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedFrontend.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedFrontend.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedFrontend.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedFrontend.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedFrontend.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedFrontend.run
