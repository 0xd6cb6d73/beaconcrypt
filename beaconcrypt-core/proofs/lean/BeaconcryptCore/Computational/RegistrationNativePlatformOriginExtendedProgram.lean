-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginJournalProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupMarker
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginInstrumentedBounds
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open RegistrationNativeStageTrace (Call)
open RegistrationNativePlatformOriginFreeFullTrace (frontend)
variable {n : Nat} {I KemSK Platform Failure Reader Response Value View Extra : Type} {base : OracleSpec I}
open RegistrationNativePlatformOriginJournalProgram (Front Calls Client plain)
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


variable (extended : RegistrationNativeHiddenStartup.Started source → OracleComp PqxdhDeploymentInterface.FullSpec Extra)
    (project : Extra → Value)

/-- A pure return extension of the actual old full-client tree retains its own artifact and complete original journal. -/
noncomputable def program : OracleComp (ServiceSpec n) ((Client n Platform Value × Option Extra) × Calls View) := do
  let started←compile (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
    CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl
  match started.1.1 with
  | none=>pure (((none,started.2),none),[])
  | some born=>
    let result←(simulateQ (RegistrationNativeObservedStageTrace.handler (observe born)
      (frontend (RegistrationNativeEntropyPort.environment (env born)) (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born))
        setup.source.crypto codec route serverKeyId bounds)) (extended born)).run
          ((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),started.1.2),started.2)),[])
    pure ((plain born.created (project result.1,result.2.1),some result.1),result.2.2)

/-- The extension is carried only in the returned artifact; erasing it restores the exact initialized original journal, with every actual call and state unchanged. -/
theorem journal_source
    (erasure : ∀born,project <$>extended born=PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode (work born))) :
    (fun result=>(result.1.1,result.2)) <$>
      program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds initial observe extended project =
        RegistrationNativePlatformOriginJournalProgram.program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe := by
  unfold program RegistrationNativePlatformOriginJournalProgram.program
  rw [map_bind]
  apply bind_congr
  rintro ⟨⟨_ | born,shell⟩,control⟩
  · simp only [map_pure]
  · simp only [bind_pure_comp,Functor.map_map]
    have mapped:=congrArg (fun tree=>(simulateQ (RegistrationNativeObservedStageTrace.handler (observe born)
      (frontend (RegistrationNativeEntropyPort.environment (env born)) (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born))
        setup.source.crypto codec route serverKeyId bounds)) tree).run
        ((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[])) (erasure born)
    simp only [simulateQ_map,StateT.run_map] at mapped
    rw [←mapped,Functor.map_map]
    rfl

/-- Forgetting only the public return certificate and journal gives the exact genuine initialized source tree; no private backend state is part of the certificate. -/
theorem erase
    (erasure : ∀born,project <$>extended born=PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode (work born))) :
    (fun result=>result.1.1) <$>
      program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds initial observe extended project =
      RegistrationNativeRecordOriginProgram.program codec route world := by
  have first:=congrArg (Functor.map Prod.fst)
    (journal_source setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe extended project erasure)
  have second:=RegistrationNativePlatformOriginJournalProgram.erase setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe
  simpa only [Functor.map_map] using first.trans second
/-- Every actual extended callback program retains the genuine reserve-tail syntax, without an extension-erasure premise. -/
theorem tails : RegistrationNativePlatformOriginSourceTails.HasTails (RegistrationNativeEntropyPort.State Platform) Failure
    (program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds initial observe extended project) := by
  unfold program
  apply RegistrationNativePlatformOriginSourceTails.bind
  · exact RegistrationNativePlatformOriginStartupTails.start setup source ensureInit identityIndex serverKeyId identity codec route _ _
  · rintro ⟨⟨_ | born,shell⟩,control⟩
    · trivial
    · simpa only [bind_pure_comp] using RegistrationNativePlatformOriginSourceTails.map
        (fun result=>((plain born.created (project result.1,result.2.1),some result.1),result.2.2)) _
        (RegistrationNativePlatformOriginObservedTails.program
          (RegistrationNativeEntropyPort.environment (env born))
          (RegistrationNativePlatformGatedNativeEntropy.reserveLift (reserve born)) setup.source.crypto codec route serverKeyId bounds
          (observe born) (extended born)
          ((PqxdhDeploymentSecrecy.Ledger.empty,((([],initial born),shell),control)),[]))

/-- The statically proved pure client projection supplies one-use sealing freshness for the actual extended initialized tree. -/
theorem fresh
    (erasure : ∀born,project <$>extended born=PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode (work born))) :
    (PqxdhRecordLiftProtocolHistory.annotated
      (program setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds initial observe extended project) []).AllQueriesSatisfy PqxdhRecordLiftProtocolHistory.Fresh :=
  RegistrationNativePlatformOriginInstrumentedBounds.fresh codec route world _ (fun result=>result.1.1)
    (erase setup source ensureInit identityIndex serverKeyId identity env reserve codec route bounds mode work initial observe extended project erasure)

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram.journal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram.journal_source


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram.erase


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram.tails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram.tails


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginExtendedProgram.fresh
