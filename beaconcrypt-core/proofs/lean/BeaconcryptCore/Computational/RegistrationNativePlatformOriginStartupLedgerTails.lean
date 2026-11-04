-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails
/-! The actual effectful constructor, shared pin hash and complete original native ledger have one reserve-tail source tree, including startup rejection and dynamic writer failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupLedgerTails
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformOriginSourceTails (HasTails)
variable {n : Nat} {I KemSK Platform Failure Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
variable (env : RegistrationNativeHiddenStartup.Started source → RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : RegistrationNativeHiddenStartup.Started source → Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : RegistrationNativeHiddenStartup.Started source → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (initial : RegistrationNativeHiddenStartup.Started source → Platform)
noncomputable def world : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome Platform Value) := do
  let born ← RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity
  match born with
  | none=>pure none
  | some born=>RegistrationNativePlatformGatedNativeEntropy.program (env born) (reserve born) setup.source.crypto codec serverKeyId bounds mode (work born) born.created (initial born)

/-- Constructor refusal and every complete native continuation retain their literal reserve tails beneath the original full ledger, at the same warm source cursor and control. -/
theorem tails (route : RawCtxServerRouting.SenderDecoder) :
    HasTails (RegistrationNativeEntropyPort.State Platform) Failure
      (RegistrationNativeRecordOriginProgram.program codec route
        (world setup source ensureInit identityIndex serverKeyId identity env reserve codec bounds mode work initial)) := by
  have complete : HasTails (RegistrationNativeEntropyPort.State Platform) Failure
      (RegistrationNativePlatformOriginStartupTails.compile codec route
        (world setup source ensureInit identityIndex serverKeyId identity env reserve codec bounds mode work initial)
          CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl) := by
    unfold world
    apply RegistrationNativePlatformOriginStartupTails.bind
    · exact RegistrationNativePlatformOriginStartupTails.start setup source ensureInit identityIndex serverKeyId identity codec route _ _
    · intro born shell control
      cases born with
      | none=>simp only [RegistrationNativePlatformOriginStartupTails.compile,simulateQ_pure,StateT.run_pure];trivial
      | some born=>exact RegistrationNativePlatformOriginLedgerTails.complete (env born) (reserve born) setup.source.crypto codec route serverKeyId bounds mode (work born) born.created (initial born) shell control
  have mapped := RegistrationNativePlatformOriginSourceTails.map
    (fun result=>(RegistrationNativeRecordPackage.encode result.1.1,result.2)) _ complete
  simpa only [RegistrationNativeRecordOriginProgram.program,RegistrationNativeRecordPackage.client,
    PqxdhRecordLiftProtocol.schedule,CborRecordWorldClient.client,RegistrationNativePlatformOriginStartupTails.compile,
    simulateQ_map,StateT.run_map,Functor.map_map] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupLedgerTails

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupLedgerTails.tails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupLedgerTails.tails
