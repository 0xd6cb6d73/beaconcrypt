-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds
/-! A computable projected macro journal is a pure return extension of the genuine initialized original source tree. The actual platform, shell, control and all failed callbacks remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProgram
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open RegistrationNativeStageTrace (Call)
open RegistrationNativePlatformOriginFreeFullTrace (frontend)
variable {n : Nat} {I KemSK Platform Failure Reader Response Value View : Type} {base : OracleSpec I}
abbrev Front (n : Nat) (Platform : Type) := RegistrationNativePlatformOriginFreeFullTrace.State n (RegistrationNativeEntropyPort.State Platform)
abbrev Calls (View : Type) := List (Call PqxdhDeploymentInterface.FullSpec View)
abbrev Client (n : Nat) (Platform Value : Type) := PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra Platform) Value

def plain (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (result : Value × Front n Platform) : Client n Platform Value :=
  (RegistrationNativeRecordPackage.encode (some (PqxdhRegistrationJointServerBirth.encode created,
    (result.1,RegistrationNativeEntropyRestore.ledger result.2.1),result.2.2.1.1.2)),result.2.2.2)

def pack (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (result : Value × (Front n Platform × Calls View)) : Client n Platform Value × Calls View :=
  (plain created (result.1,result.2.1),result.2.2)

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

noncomputable def program : OracleComp (ServiceSpec n) (Client n Platform Value × Calls View) := do
  let started ← compile (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
    CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl
  match started.1.1 with
  | none => pure ((none,started.2),[])
  | some born =>
    let result ← (simulateQ (RegistrationNativeObservedStageTrace.handler (observe born)
      (frontend (RegistrationNativeEntropyPort.environment (env born)) (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born))
        setup.source.crypto codec route serverKeyId bounds))
      (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode (work born)))).run
      ((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),started.1.2),started.2)),[])
    pure (pack born.created result)

private theorem suffix_source (born : RegistrationNativeHiddenStartup.Started source)
    (shell : CborRecordWorldClient.Shell) (control : Control n) :
    plain born.created <$>
      (simulateQ (frontend (RegistrationNativeEntropyPort.environment (env born))
        (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto codec route serverKeyId bounds)
        (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode (work born)))).run
        (PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)) =
      (fun result=>(RegistrationNativeRecordPackage.encode result.1.1,result.2)) <$>
        compile (RegistrationNativePlatformGatedNativeEntropy.program (env born) (reserve born) setup.source.crypto codec
          serverKeyId bounds mode (work born) born.created (initial born)) shell control := by
  rw [RegistrationNativePlatformOriginFreeFullTrace.frontend_source,
    ←RegistrationNativePlatformGatedNativeEntropy.program_transport (env born) (reserve born) setup.source.crypto codec
      serverKeyId bounds mode (work born) born.created (initial born)]
  simp only [RegistrationNativePlatformGatedEntropyWorld.program,RegistrationNativePlatformOriginStartupTails.compile,
    RegistrationNativePlatformOriginNativeTails.source,PqxdhDeploymentSecrecy.wrap,simulateQ_map,StateT.run_map,Functor.map_map,
    plain,RegistrationNativeEntropyProgram.outcome,RegistrationNativeEntropyExecution.result,Option.map_some,
    RegistrationNativePlatformOriginFreeFullTrace.fullJoin,RegistrationNativePlatformOriginFreeFullTrace.join]

/-- Erasing only the computable macro journal restores the exact genuine initialized original source tree. -/
theorem erase :
    Prod.fst <$> program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe =
      RegistrationNativeRecordOriginProgram.program codec route world := by
  have sourceForm : RegistrationNativeRecordOriginProgram.program codec route world =
      (fun result=>(RegistrationNativeRecordPackage.encode result.1.1,result.2)) <$>
        compile world CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl := by
    simp only [RegistrationNativeRecordOriginProgram.program,RegistrationNativeRecordPackage.client,
      PqxdhRecordLiftProtocol.schedule,CborRecordWorldClient.client,RegistrationNativePlatformOriginStartupTails.compile,
      simulateQ_map,StateT.run_map,Functor.map_map]
  rw [sourceForm]
  unfold program RegistrationNativePlatformOriginStartupLedgerTails.world
  simp only [RegistrationNativePlatformOriginStartupTails.compile,simulateQ_bind,StateT.run_bind,map_bind]
  apply bind_congr
  rintro ⟨⟨_ | born,shell⟩,control⟩
  · simp only [simulateQ_pure,StateT.run_pure,map_pure,RegistrationNativeRecordPackage.encode,Option.map_none]
  · simp only [bind_pure_comp,Functor.map_map]
    have erased := congrArg (Functor.map (plain born.created))
      (RegistrationNativePlatformOriginFreeFullTrace.erase (RegistrationNativeEntropyPort.environment (env born))
        (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto codec route serverKeyId bounds
        (observe born) (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode (work born)))
        ((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]))
    simp only [Functor.map_map] at erased
    change (plain born.created ∘ Prod.map id Prod.fst) <$> _ = _
    rw [show (plain born.created ∘ Prod.map id Prod.fst) = (fun a => plain born.created (Prod.map id Prod.fst a)) from rfl, erased]
    exact suffix_source (setup:=setup) (source:=source) (serverKeyId:=serverKeyId) (env:=env) (reserve:=reserve) (codec:=codec) (route:=route) (bounds:=bounds) (mode:=mode) (work:=work) (initial:=initial) born shell control
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProgram


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProgram.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProgram.erase
