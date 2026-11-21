-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open RegistrationNativePlatformOriginJournalProgram (Front Calls Client)
variable {n : Nat} {I KemSK Platform Failure Reader Response Value View : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (env : RegistrationNativeHiddenStartup.Started source → RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : RegistrationNativeHiddenStartup.Started source → Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : RegistrationNativeHiddenStartup.Started source → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (initial : RegistrationNativeHiddenStartup.Started source → Platform)
    (observe : RegistrationNativeHiddenStartup.Started source → Front n Platform → View)
local notation "compile" => RegistrationNativePlatformOriginStartupTails.compile codec route
local notation "world" => RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId identity env reserve codec bounds mode work initial


local notation "counted" => RegistrationNativePlatformOriginSendCallbackBudget.Sending
local notation "stop" => RegistrationNativePlatformOriginCallbackFreeStop.stop
local notation "markedResume" => RegistrationNativePlatformOriginCallbackFreeStop.markedResume

def compiled (born : RegistrationNativeHiddenStartup.Started source) :=
  PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode (work born))

noncomputable def program (index : Nat) :=
  RegistrationNativePlatformOriginExtendedProgram.program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds initial observe
    (fun born=>stop counted (compiled source mode work born) index >>=markedResume) Prod.snd

/-- The concrete selected-public-callback certificate erases to the exact original genuine-startup/full-ledger source tree. -/
theorem erase (index : Nat) :
    (fun result=>result.1.1) <$> program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index =
      RegistrationNativeRecordOriginProgram.program codec route world := by
  apply RegistrationNativePlatformOriginExtendedProgram.erase
  intro born
  exact RegistrationNativePlatformOriginCallbackFreeStop.client_erase counted (compiled source mode work born) index

/-- Every concrete selected ordinal keeps the actual reserve-tail syntax in all startup and callback failure branches. -/
theorem tails (index : Nat) :
    RegistrationNativePlatformOriginSourceTails.HasTails (RegistrationNativeEntropyPort.State Platform) Failure
      (program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index) :=
  RegistrationNativePlatformOriginExtendedProgram.tails setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds initial observe _ Prod.snd

/-- The concrete public ordinal extension inherits original source-derived one-use sealing freshness. -/
theorem fresh (index : Nat) :
    (PqxdhRecordLiftProtocolHistory.annotated
      (program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index) []).AllQueriesSatisfy PqxdhRecordLiftProtocolHistory.Fresh := by
  apply RegistrationNativePlatformOriginExtendedProgram.fresh
  intro born
  exact RegistrationNativePlatformOriginCallbackFreeStop.client_erase counted (compiled source mode work born) index
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram.erase


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram.tails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram.tails


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram.fresh
