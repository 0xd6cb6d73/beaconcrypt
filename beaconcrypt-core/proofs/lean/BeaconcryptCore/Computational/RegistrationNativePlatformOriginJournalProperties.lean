-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProperties
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open RegistrationNativePlatformOriginJournalProgram (Front Calls Client program pack)
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


/-- The actual initialized journal retains every literal post-seal reserve tail, including failed startup and public writes. -/
theorem tails : RegistrationNativePlatformOriginSourceTails.HasTails (RegistrationNativeEntropyPort.State Platform) Failure
    (program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe) := by
  unfold program
  apply RegistrationNativePlatformOriginSourceTails.bind
  · exact RegistrationNativePlatformOriginStartupTails.start setup source ensureInit identityIndex serverKeyId identity codec route _ _
  · rintro ⟨⟨_ | born,shell⟩,control⟩
    · trivial
    · simpa only [bind_pure_comp] using RegistrationNativePlatformOriginSourceTails.map (pack born.created) _
        (RegistrationNativePlatformOriginObservedTails.program
          (RegistrationNativeEntropyPort.environment (env born))
          (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto codec route serverKeyId bounds
          (observe born) (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode (work born)))
          ((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]))

/-- The pure journal inherits the actual source's one-use seal syntax, without an erasure premise. -/
theorem fresh :
    (PqxdhRecordLiftProtocolHistory.annotated
      (program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe) []).AllQueriesSatisfy PqxdhRecordLiftProtocolHistory.Fresh :=
  RegistrationNativePlatformOriginInstrumentedBounds.fresh codec route world _ Prod.fst
    (RegistrationNativePlatformOriginJournalProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProperties

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProperties.tails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProperties.tails


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProperties.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProperties.fresh
