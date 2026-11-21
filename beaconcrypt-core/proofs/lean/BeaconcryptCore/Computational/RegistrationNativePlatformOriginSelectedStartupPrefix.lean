-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourceStop
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedStartupPrefix
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

open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginOrdinalPath (Prefix)
local notation "compile" => RegistrationNativePlatformOriginStartupTails.compile codec route
local notation "counted" => RegistrationNativePlatformOriginSendCallbackBudget.Sending
local notation "markedResume" => RegistrationNativePlatformOriginCallbackFreeStop.markedResume
local notation "stop" => RegistrationNativePlatformOriginCallbackFreeStop.stop
local notation "front(" born ")" => RegistrationNativeObservedStageTrace.handler (observe born)
  (RegistrationNativePlatformOriginFreeFullTrace.frontend (RegistrationNativeEntropyPort.environment (env born))
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto codec route serverKeyId bounds)

abbrev Certificate := Option (RegistrationNativePlatformOriginCallbackFreeStop.PublicCall PqxdhDeploymentInterface.FullSpec)

def pack (born : RegistrationNativeHiddenStartup.Started source)
    (result : (Certificate × Value) × (Front n Platform × Calls View)) :=
  ((RegistrationNativePlatformOriginJournalProgram.plain born.created (result.1.2,result.2.1),some result.1),result.2.2)

/-- A literal supported initialized callback scan reaches its own marked public continuation inside the complete original certificate/journal program. -/
theorem pending (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (initialPrivate : CtxPrivate n) (born : RegistrationNativeHiddenStartup.Started source)
    (shell : CborRecordWorldClient.Shell) (control : Control n) (privateBefore : CtxPrivate n)
    (started : (((some born,shell),control),privateBefore)∈support
      ((simulateQ service (compile (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl)).run initialPrivate))
    (index : Nat)
    (cut : RegistrationNativePlatformOriginCallbackCut.Cut PqxdhDeploymentInterface.FullSpec
      ((Front n Platform × Calls View) × CtxPrivate n) Value)
    (selected : Sum.inr cut∈support (RegistrationNativePlatformOriginCallbackCut.scan counted
      (QueryImpl.Stateful.link (front(born)) service)
      (RegistrationNativePlatformOriginSelectedProgram.compiled source mode work born) index
      (((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]),privateBefore))) :
    ∃past cuts,Prefix service
      (RegistrationNativePlatformOriginSelectedProgram.program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index)
      initialPrivate []
      (pack source born <$> (simulateQ (front(born)) (markedResume (.pending cut.query cut.next))).run cut.state.1)
      cut.state.2 past cuts := by
  have actual := started
  rw [←PqxdhRecordFactsOriginOrdinalTrace.track_drop service _ initialPrivate []] at actual
  simp only [support_map] at actual
  obtain ⟨tracked,called,equal⟩ :=actual
  rcases tracked with ⟨startupCuts,⟨startupValue,startupPrivate⟩⟩
  cases equal
  have path := PqxdhRecordFactsOriginOrdinalPath.support_path service _ initialPrivate [] _ called
  obtain ⟨startupPast,completed⟩ := PqxdhRecordFactsOriginOrdinalFinalPrefix.path_prefix service path
  let nextStartup : ((Option (RegistrationNativeHiddenStartup.Started source) × CborRecordWorldClient.Shell) × Control n) →
      OracleComp (ServiceSpec n) ((Client n Platform Value × Option (Certificate × Value)) × Calls View) := fun current =>
    match current.1.1 with
    | none=>pure (((none,current.2),none),[])
    | some chosen=>pack source chosen <$>
      (simulateQ (front(chosen)) (stop counted (RegistrationNativePlatformOriginSelectedProgram.compiled source mode work chosen) index >>=markedResume)).run
        ((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial chosen),current.1.2),current.2)),[])
  have first := RegistrationNativePlatformOriginPathBind.prefix_bind service nextStartup completed
  simp only [pure_bind] at first
  obtain ⟨past,bodyCuts,bodyPrefix⟩ := RegistrationNativePlatformOriginCallbackSourceStop.reached (front(born)) service counted
    (RegistrationNativePlatformOriginSelectedProgram.compiled source mode work born) index
    (((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]),privateBefore) startupPast cut selected
  have body := RegistrationNativePlatformOriginPathBind.prefix_bind service (fun result=>pure (pack source born result)) bodyPrefix
  simp only [bind_pure_comp] at body
  have joined := PqxdhRecordFactsOriginOrdinalPath.prefix_trans service first body
  refine ⟨past,startupCuts.map (RegistrationNativePlatformOriginPathBind.bindCut nextStartup) ++
    bodyCuts.map (RegistrationNativePlatformOriginPathBind.bindCut (fun result=>pure (pack source born result))),?_⟩
  have original : RegistrationNativePlatformOriginSelectedProgram.program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe index =
      compile (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl >>=nextStartup := by
    unfold RegistrationNativePlatformOriginSelectedProgram.program RegistrationNativePlatformOriginExtendedProgram.program
    apply bind_congr
    rintro ⟨⟨_ | chosen,chosenShell⟩,chosenControl⟩
    · rfl
    · dsimp only [nextStartup]
      rw [bind_pure_comp]
      rfl
  rw [←original] at joined
  exact joined

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedStartupPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedStartupPrefix.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSelectedStartupPrefix.pending
