-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedReceive
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy
import BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (Spec FullSpec Entry Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {I KemSK Reader Response E Failure A : Type} {base : OracleSpec I}
variable (modes : Label n →KeyMode) (replace : Pqxdh.Bytes →Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat →StateT E ProbComp (core.result.Result Unit Failure))
local notation "Runtime" => CborRawRecordFlat.NativeState n E
local notation "Whole" => PqxdhDeploymentSecrecy.Ledger×Runtime
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "native" => RegistrationNativePlatformGatedRecordFlat.native service env reserve codec route
variable (serverKeyId : U64) (bounds : FreshBounds)
local notation "full" => RegistrationNativePlatformGatedRecordFlat.full service env reserve setup.source.crypto codec route serverKeyId bounds

private theorem native_program_step (work : OracleComp Spec A) (before : Runtime)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) (result : A × Runtime)
    (supported : result∈support ((simulateQ native work).run before)) :
    PqxdhRecordLiftProtocolHistory.Step before.1.2 result.2.1.2 := by
  rw [RegistrationNativePlatformGatedRecordFlat.native_program,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact PqxdhRecordLiftProtocolHistory.interpreted_schedule service codec.frameRead route _ before.1.2 safe before.2 inner called

private theorem native_path {before after : Runtime} {calls : List (Call Spec Runtime)}
    (path : Path native before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) :
    PqxdhRecordLiftProtocolHistory.Step before.1.2 after.1.2 := by
  induction path with
  | nil state => exact PqxdhRecordLiftProtocolHistory.step_refl _ safe
  | cons call called rest last following ih =>
    have step := native_program_step modes replace setup codec route env reserve (Spec.query call.query) call.before safe
      (call.reply,call.after) (by simpa only [simulateQ_spec_query,Executed] using called)
    exact PqxdhRecordFactsOriginControl.step_trans _ _ _ step (ih step.1)

private theorem full_step (query : FullSpec.Domain) (before : Whole)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2) (result : FullSpec.Range query × Whole)
    (supported : result∈support ((full query).run before)) :
    PqxdhRecordLiftProtocolHistory.Step before.2.1.2 result.2.2.1.2 := by
  change result∈support ((fun actual => (actual.1.1,(actual.1.2,actual.2))) <$>
    (simulateQ native ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run before.1)).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact native_program_step modes replace setup codec route env reserve _ before.2 safe inner called

private theorem full_path {before after : Whole} {calls : List (Call FullSpec Whole)}
    (path : Path full before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2) :
    PqxdhRecordLiftProtocolHistory.Step before.2.1.2 after.2.1.2 := by
  induction path with
  | nil state => exact PqxdhRecordLiftProtocolHistory.step_refl _ safe
  | cons call called rest last following ih =>
    have step := full_step modes replace setup codec route env reserve serverKeyId bounds call.query call.before safe
      (call.reply,call.after) called
    exact PqxdhRecordFactsOriginControl.step_trans _ _ _ step (ih step.1)

private theorem full_record (query : FullSpec.Domain) (before : Whole) (result : FullSpec.Range query × Whole)
    (supported : result∈support ((full query).run before)) :
    result.2.1.transcript=before.1.transcript++[⟨query,result.1⟩] := by
  change result∈support ((fun actual => (actual.1.1,(actual.1.2,actual.2))) <$>
    (simulateQ native ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run before.1)).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  have projected : inner.1∈support ((simulateQ native
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run before.1)).run' before.2) := by
    rw [StateT.run'_eq,support_map]
    exact ⟨inner,called,rfl⟩
  have free := support_simulateQ_run'_subset native _ before.2 projected
  exact PqxdhDeploymentCausalCoverage.ledger_records setup.source.crypto codec serverKeyId bounds query before.1 inner.1 free

private theorem transcript {before after : Whole} {calls : List (Call FullSpec Whole)}
    (path : Path full before calls after) :
    after.1.transcript=before.1.transcript++calls.map (fun call => (⟨call.query,call.reply⟩ : Entry)) := by
  induction path with
  | nil state => exact (List.append_nil _).symm
  | cons call called rest last following ih =>
    have recorded := full_record modes replace setup codec route env reserve serverKeyId bounds call.query call.before (call.reply,call.after) called
    rw [ih,recorded,List.map_cons,List.append_assoc]
    rfl


/-- The named erased full callback run has one genuine journal, with every accepted reply attributed to that callback's own before-state. -/
theorem program (work : OracleComp FullSpec A) (before : Runtime)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) (result : A×Whole)
    (supported : result∈support ((simulateQ full work).run (PqxdhDeploymentSecrecy.Ledger.empty,before))) :
    ∃calls,Path full (PqxdhDeploymentSecrecy.Ledger.empty,before) calls result.2 ∧
      result.2.1.transcript=calls.map (fun call=>(⟨call.query,call.reply⟩:Entry)) ∧
      ∀call∈calls,∀receiver raw opened,
        (⟨call.query,call.reply⟩:Entry).received=some (receiver,raw,core.option.Option.Some opened) →
        ∃leading trailing,calls=leading++call::trailing ∧Path full (PqxdhDeploymentSecrecy.Ledger.empty,before) leading call.before ∧
          ∃handle,PqxdhRecordLiftIdeal.receivingHandle route receiver raw=some handle ∧
            PqxdhRecordFactsOriginAccepted.Accepted codec call.before.2.1.2 call.before.2.2 handle raw opened := by
  rw [←RegistrationNativeStageTrace.erase full work ((PqxdhDeploymentSecrecy.Ledger.empty,before),[]),support_map] at supported
  obtain ⟨traced,reached,same⟩:=supported
  have actual:=RegistrationNativeStageTrace.path full work (PqxdhDeploymentSecrecy.Ledger.empty,before) traced reached
  cases same
  refine ⟨traced.2.2,actual,?_,?_⟩
  · change traced.2.1.1.transcript=_
    simpa only [PqxdhDeploymentSecrecy.Ledger.empty,List.nil_append] using
      transcript modes replace setup codec route env reserve serverKeyId bounds actual
  · intro call member receiver raw opened received
    obtain ⟨leading,trailing,split,earlier,called,_later⟩:=actual.member call member
    refine ⟨leading,trailing,split,earlier,?_⟩
    exact RegistrationNativePlatformOriginErasedReceive.full_received_before modes replace setup codec route env reserve serverKeyId bounds
      call.query call.before (full_path modes replace setup codec route env reserve serverKeyId bounds earlier safe).1
      (call.reply,call.after) called receiver raw opened received


private def packed (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (result : A×Whole) :=
  (((some (PqxdhRegistrationJointServerBirth.encode created,(result.1,result.2.1),result.2.2.1.1.1),
      result.2.2.1.1.2),result.2.2.1.2),result.2.2.2)

private theorem world_source (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) A)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    (simulateQ service (RegistrationNativePlatformOriginStartupTails.compile codec route
      (RegistrationNativePlatformGatedEntropyWorld.program env reserve setup.source.crypto codec serverKeyId bounds mode work created initial)
      shell control)).run secret=
    packed created <$> (simulateQ full (PqxdhDeploymentInterface.asModeO mode work)).run
      (PqxdhDeploymentSecrecy.Ledger.empty,(((initial,shell),control),secret)) := by
  have represented:=RegistrationNativePlatformGatedRecordFlat.native_program service env reserve codec route
    (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode work))
    initial shell control secret
  rw [PqxdhDeploymentSecrecy.wrap,OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT] at represented
  have mapped:=congrArg (Functor.map (fun result : (A×PqxdhDeploymentSecrecy.Ledger)×Runtime=>
    (((some (PqxdhRegistrationJointServerBirth.encode created,result.1,result.2.1.1.1),
      result.2.1.1.2),result.2.1.2),result.2.2))) represented
  simp only [RegistrationNativePlatformGatedEntropyWorld.program,RegistrationNativePlatformOriginStartupTails.compile,
    simulateQ_map,StateT.run_map,Functor.map_map,RegistrationNativePlatformGatedRecordFlat.full,
    RegistrationNativePlatformGatedRecordFlat.join,CborRawRecordOriginFlatten.interpret] at mapped ⊢
  exact mapped.symm


abbrev TransportRuntime (n : Nat) (E : Type) :=
  PqxdhDeploymentSecrecy.Ledger×CborRawRecordFlat.NativeState n (RegistrationNativeEntropyPort.State E)

def restored (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (result : A×TransportRuntime n E) :
    (((RegistrationNativeEntropyRun.Outcome E A×CborRecordWorldClient.Shell)×PqxdhRecordLiftProtocol.Control n)×CtxPrivate n) :=
  (((some (PqxdhRegistrationJointServerBirth.encode created,
      ((result.1,RegistrationNativeEntropyRestore.ledger result.2.1),result.2.2.1.1.1.2)),
      result.2.2.1.1.2),result.2.2.1.2),result.2.2.2)

/-- The literal current native program closes through the named erased service with only its proved native ledger restoration and product association. -/
theorem source
    (nativeEnv : RegistrationNativeEntropyInterface.Environment n E)
    (nativeReserve : Nat →StateT E ProbComp (core.result.Result Unit Failure))
    (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    (simulateQ service (RegistrationNativePlatformOriginStartupTails.compile codec route
      (RegistrationNativePlatformGatedNativeEntropy.program nativeEnv nativeReserve setup.source.crypto codec serverKeyId bounds mode work created initial)
      shell control)).run secret=
    restored created <$> (simulateQ (RegistrationNativePlatformGatedRecordFlat.full service
      (RegistrationNativeEntropyPort.environment nativeEnv) (RegistrationNativePlatformGatedNativeEntropy.reserveLift nativeReserve)
      setup.source.crypto codec route serverKeyId bounds)
      (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work))).run
        (PqxdhDeploymentSecrecy.Ledger.empty,(((([],initial),shell),control),secret)) := by
  rw [←RegistrationNativePlatformGatedNativeEntropy.program_transport nativeEnv nativeReserve setup.source.crypto codec serverKeyId bounds mode work created initial]
  have same:=world_source modes replace setup codec route
    (RegistrationNativeEntropyPort.environment nativeEnv) (RegistrationNativePlatformGatedNativeEntropy.reserveLift nativeReserve)
    serverKeyId bounds mode (RegistrationNativeEntropyCompile.compile mode work) created ([],initial) shell control secret
  have mapped:=congrArg (Functor.map (Prod.map (Prod.map (Prod.map RegistrationNativeEntropyProgram.outcome id) id) id)) same
  simp only [RegistrationNativePlatformOriginStartupTails.compile,simulateQ_map,StateT.run_map,Functor.map_map] at mapped ⊢
  exact mapped


/-- Every accepted raw callback in the actual erased native World program has its matching source seal at the same earlier warm prefix; the original restored ledger and raw callback chronology are retained exactly. -/
theorem initialized_stages
    (nativeEnv : RegistrationNativeEntropyInterface.Environment n E)
    (nativeReserve : Nat →StateT E ProbComp (core.result.Result Unit Failure))
    (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : PqxdhRecordLiftProtocolHistory.Safe control) (secret : CtxPrivate n)
    (result : (((RegistrationNativeEntropyRun.Outcome E A×CborRecordWorldClient.Shell)×PqxdhRecordLiftProtocol.Control n)×CtxPrivate n))
    (supported : result∈support ((simulateQ service (RegistrationNativePlatformOriginStartupTails.compile codec route
      (RegistrationNativePlatformGatedNativeEntropy.program nativeEnv nativeReserve setup.source.crypto codec serverKeyId bounds mode work created initial)
      shell control)).run secret)) :
    let implementation:=RegistrationNativePlatformGatedRecordFlat.full service
      (RegistrationNativeEntropyPort.environment nativeEnv) (RegistrationNativePlatformGatedNativeEntropy.reserveLift nativeReserve)
      setup.source.crypto codec route serverKeyId bounds
    let startState:TransportRuntime n E:=(PqxdhDeploymentSecrecy.Ledger.empty,(((([],initial),shell),control),secret))
    ∀born∈result.1.1.1,∃final:TransportRuntime n E,∃calls:List (Call FullSpec (TransportRuntime n E)),
      Path implementation startState calls final ∧final.2.1.2=result.1.2 ∧final.2.2=result.2 ∧
      RegistrationNativeEntropyTrace.strip (calls.map (fun call=>(⟨call.query,call.reply⟩:Entry)))=born.2.1.2.ledger.transcript ∧
      ∀call∈calls,∀receiver raw opened,
        (⟨call.query,call.reply⟩:Entry).received=some (receiver,raw,core.option.Option.Some opened) →
        ∃leading trailing,calls=leading++call::trailing ∧Path implementation startState leading call.before ∧
          ∃handle,PqxdhRecordLiftIdeal.receivingHandle route receiver raw=some handle ∧
            PqxdhRecordFactsOriginAccepted.Accepted codec call.before.2.1.2 call.before.2.2 handle raw opened := by
  rw [source modes replace setup codec route serverKeyId bounds nativeEnv nativeReserve mode work created initial shell control secret,support_map] at supported
  obtain ⟨old,called,rfl⟩:=supported
  obtain ⟨calls,actual,transcript,stages⟩:=program modes replace setup codec route
    (RegistrationNativeEntropyPort.environment nativeEnv) (RegistrationNativePlatformGatedNativeEntropy.reserveLift nativeReserve)
    serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work))
    (((([],initial),shell),control),secret) safe old called
  dsimp only
  intro born member
  have selected : born=(PqxdhRegistrationJointServerBirth.encode created,
      ((old.1,RegistrationNativeEntropyRestore.ledger old.2.1),old.2.2.1.1.1.2)) := by
    symm
    simpa only [restored,Option.mem_some_iff] using member
  subst born
  refine ⟨old.2,calls,actual,rfl,rfl,?_,stages⟩
  rw [RegistrationNativeEntropyRestore.ledger_transcript,transcript]


/-- Any supplied same-run erased full path preserves actual control safety and forward handle provenance. -/
theorem path_step {before after : Whole} {calls : List (Call FullSpec Whole)}
    (path : Path full before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2) :
    PqxdhRecordLiftProtocolHistory.Step before.2.1.2 after.2.1.2 :=
  full_path modes replace setup codec route env reserve serverKeyId bounds path safe

/-- The ledger of any supplied erased full path is exactly its initial ledger followed by that same complete callback journal. -/
theorem path_transcript {before after : Whole} {calls : List (Call FullSpec Whole)}
    (path : Path full before calls after) :
    after.1.transcript=before.1.transcript++calls.map (fun call=>(⟨call.query,call.reply⟩:Entry)) :=
  transcript modes replace setup codec route env reserve serverKeyId bounds path

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.initialized_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.initialized_stages

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.path_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.path_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.path_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized.path_transcript
