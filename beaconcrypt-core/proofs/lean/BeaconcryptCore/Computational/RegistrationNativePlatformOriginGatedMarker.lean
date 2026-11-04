-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry
import BeaconcryptCore.Computational.PqxdhDeploymentTargetRange
/-! Actual cursor-filtered native and full-ledger callbacks retain the sticky selected replay marker. The per-receive source body is reused directly, while current reserve and failed full callbacks remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode handleSlot)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (Spec Entry Handle)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginMarkerEntry (EntryFact entry_mono)
variable {n : Nat} {I KemSK Reader Response E Failure X : Type} {base : OracleSpec I}
variable (target : Label n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
local notation "service" => PqxdhRecordFactsOriginMarkerNative.service target modes replace setup codec
local notation "native" => RegistrationNativePlatformGatedRecordFlat.native service env reserve codec route
local notation "State" => RegistrationNativePlatformGatedRecordFlat.State n E (CtxPrivate n × Bool)

/-- Literal cursor and reserve execution preserve the actual forward control relation. -/
private theorem step (query : Spec.Domain) (before : State) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × State) (supported : result∈support ((native query).run before)) :
    PqxdhRecordLiftProtocolHistory.Step before.1.2 result.2.1.2 := by
  change result∈support (RegistrationNativePlatformGatedRecordFlat.join <$>
    (simulateQ service
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler ((RegistrationNativePlatformGatedRecordInterface.native env reserve query).run before.1.1.1)).run before.1.1.2)).run before.1.2)).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact PqxdhRecordLiftProtocolHistory.interpreted_schedule service codec.frameRead route _ before.1.2 safe before.2 inner called

/-- The actual public reserve and cursor cannot change a handle's caller-known classification. -/
private theorem known (handle : Handle) (query : Spec.Domain) (before : State)
    (prior : PqxdhRecordLiftFlat.KnownAt before.1.2 handle)
    (result : Spec.Range query × State) (supported : result∈support ((native query).run before)) :
    PqxdhRecordLiftFlat.KnownAt result.2.1.2 handle := by
  change result∈support (RegistrationNativePlatformGatedRecordFlat.join <$>
    (simulateQ service
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler ((RegistrationNativePlatformGatedRecordInterface.native env reserve query).run before.1.1.1)).run before.1.1.2)).run before.1.2)).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    (fun current => PqxdhRecordLiftFlat.KnownAt current handle)
    (PqxdhRecordLiftFlat.handler_known codec.frameRead route handle) _ before.1.2 prior inner.1
    (PqxdhRecordLiftFlat.support_run_fst service _ before.2 inner called)

/-- Every adaptive service continuation retains its already-raised selected replay marker, including all actual reserve outcomes. -/
private theorem sticky (query : Spec.Domain) (before : State) (raised : before.2.2=true)
    (result : Spec.Range query × State) (supported : result∈support ((native query).run before)) :
    result.2.2.2=true := by
  change result∈support (RegistrationNativePlatformGatedRecordFlat.join <$>
    (simulateQ service
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler ((RegistrationNativePlatformGatedRecordInterface.native env reserve query).run before.1.1.1)).run before.1.1.2)).run before.1.2)).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact PqxdhRecordFactsOriginMarkerNative.service_sticky target modes replace setup codec _ before.2 raised inner called

/-- Successful raw receives in the current gated callback raise their own literal marker; nonreceive replies satisfy the same statement vacuously. -/
private theorem before (query : Spec.Domain) (before : State) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × State) (supported : result∈support ((native query).run before)) :
    EntryFact target route before.1.2 result.2.2.2 ⟨.inl query,result.1⟩ := by
  intro receiver raw opened handle received routed
  have nonsending : PqxdhRecordFactsOriginPublicationNative.NonSending query := by
    rcases query with coin | command
    · trivial
    · cases command <;> simp_all only [PqxdhRecordFactsOriginPublicationNative.NonSending,Entry.received,reduceCtorEq]
  rw [RegistrationNativePlatformGatedRecordOriginStage.native_nonSend service codec route env reserve query nonsending] at supported
  have projected : (result.1,CborRawRecordOriginService.project result.2)∈support
      ((CborRawRecordOriginService.original service env codec route query).run (CborRawRecordOriginService.project before)) := by
    rw [←CborRawRecordOriginService.nonrecord_project service env codec route query before ?_,support_map]
    · exact ⟨result,supported,rfl⟩
    · rcases query with coin | command
      · simp [PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
      · cases command <;> simp_all [PqxdhRecordFactsOriginPublicationNative.NonSending,PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
  exact PqxdhRecordFactsOriginMarkerEntry.native_before target modes replace setup codec route env query
    (CborRawRecordOriginService.project before) safe (result.1,CborRawRecordOriginService.project result.2) projected
    receiver raw opened handle received routed

/-- Current gated native replies carry the same received-entry fact at their final full control and sticky flag. -/
theorem final (query : Spec.Domain) (before : State) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × State) (supported : result∈support ((native query).run before)) :
    EntryFact target route result.2.1.2 result.2.2.2 ⟨.inl query,result.1⟩ :=
  entry_mono target route before.1.2 result.2.1.2 result.2.2.2 result.2.2.2
    (step target modes replace setup codec route env reserve query before safe result supported)
    (fun handle prior => known target modes replace setup codec route env reserve handle query before prior result supported)
    id _ (RegistrationNativePlatformOriginGatedMarker.before target modes replace setup codec route env reserve query before safe result supported)

private theorem program_step (work : OracleComp Spec X) (before : State)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) (result : X × State)
    (supported : result∈support ((simulateQ native work).run before)) :
    PqxdhRecordLiftProtocolHistory.Step before.1.2 result.2.1.2 := by
  apply PqxdhRecordLiftFlat.support_keep_oracle native
    (fun current => PqxdhRecordLiftProtocolHistory.Step before.1.2 current.1.2) _ work before
    (PqxdhRecordLiftProtocolHistory.step_refl _ safe) result supported
  intro query current prior output called
  exact PqxdhRecordFactsOriginControl.step_trans _ _ _ prior
    (step target modes replace setup codec route env reserve query current prior.1 output called)

private theorem program_known (work : OracleComp Spec X) (before : State) (handle : Handle)
    (prior : PqxdhRecordLiftFlat.KnownAt before.1.2 handle) (result : X × State)
    (supported : result∈support ((simulateQ native work).run before)) :
    PqxdhRecordLiftFlat.KnownAt result.2.1.2 handle :=
  PqxdhRecordLiftFlat.support_keep_oracle native (fun current => PqxdhRecordLiftFlat.KnownAt current.1.2 handle)
    (fun query current active => known target modes replace setup codec route env reserve handle query current active)
    work before prior result supported

private theorem program_sticky (work : OracleComp Spec X) (before : State) (raised : before.2.2=true)
    (result : X × State) (supported : result∈support ((simulateQ native work).run before)) : result.2.2.2=true :=
  PqxdhRecordLiftFlat.support_keep_oracle native (fun current => current.2.2=true)
    (fun query current active => sticky target modes replace setup codec route env reserve query current active)
    work before raised result supported

noncomputable def fullImpl (serverKid : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) :
    QueryImpl PqxdhDeploymentInterface.FullSpec (StateT (PqxdhDeploymentSecrecy.Ledger × State) ProbComp) :=
  ((native).mapStateTBase (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds)).flattenStateT

/-- Exact full-query execution retains the literal ledger, native state, and analysis flag. -/
private theorem full_run (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (state : State) :
    (fullImpl target modes replace setup codec route env reserve serverKid bounds query).run (ledger, state) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (native)
        ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state := rfl

/-- Every actual ledger step appends its literal query/reply and gives the exact final selected received-entry fact. -/
private theorem ledger_record (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : State) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : (PqxdhDeploymentInterface.FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × State)
    (supported : result ∈ support ((simulateQ (native)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run before)) :
    result.1.2.transcript = ledger.transcript ++ [⟨query, result.1.1⟩] ∧
      EntryFact target route result.2.1.2 result.2.2.2 ⟨query, result.1.1⟩ := by
  refine ⟨PqxdhDeploymentTargetRange.ledger_step setup.source.crypto codec serverKid bounds query ledger result.1
    (PqxdhRecordLiftFlat.support_run_fst _ _ _ result supported), ?_⟩
  rcases query with forwarded | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact final target modes replace setup codec route env reserve forwarded before safe inner reached
  · exact PqxdhRecordFactsOriginMarkerEntry.secrecy_entry target route result.2.1.2 result.2.2.2 secrecy result.1.1

/-- Every recorded accepted entry retains its current handle provenance and same-execution selected marker; the source control is safe. -/
def Invariant (target : Label n) (route : RawCtxServerRouting.SenderDecoder)
    (state : PqxdhDeploymentSecrecy.Ledger × State) : Prop :=
  PqxdhRecordLiftProtocolHistory.Safe state.2.1.2 ∧ ∀ entry ∈ state.1.transcript, EntryFact target route state.2.1.2 state.2.2.2 entry

/-- A complete full query preserves all earlier received-entry facts and appends its literal new entry. -/
theorem full_invariant (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × State) (good : Invariant target route before)
    (result : PqxdhDeploymentInterface.FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × State))
    (supported : result ∈ support ((fullImpl target modes replace setup codec route env reserve serverKid bounds query).run before)) :
    Invariant target route result.2 := by
  rw [full_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have progress := program_step target modes replace setup codec route env reserve _ before.2 good.1 inner reached
  have recorded := ledger_record target modes replace setup codec route env reserve serverKid bounds query before.1 before.2 good.1 inner reached
  refine ⟨progress.1, ?_⟩
  intro entry member
  rw [recorded.1, List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · exact entry_mono target route before.2.1.2 inner.2.1.2 before.2.2.2 inner.2.2.2 progress
      (fun handle known => program_known target modes replace setup codec route env reserve _ before.2 handle known inner reached)
      (fun bad => program_sticky target modes replace setup codec route env reserve _ before.2 bad inner reached)
      entry (good.2 entry prior)
  · exact recorded.2

/-- Every adaptive full continuation preserves selected received-entry facts through all permitted commands. -/
theorem full_program_invariant (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (client : OracleComp PqxdhDeploymentInterface.FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × State) (good : Invariant target route before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × State))
    (supported : result ∈ support ((simulateQ (fullImpl target modes replace setup codec route env reserve serverKid bounds) client).run before)) :
    Invariant target route result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (fullImpl target modes replace setup codec route env reserve serverKid bounds) (Invariant target route)
    (fun query state present => full_invariant target modes replace setup codec route env reserve serverKid bounds query state present)
    client before good result supported

/-- The actual empty initial transcript needs only source control safety; no record-origin or marker assumption is supplied. -/
private theorem empty_invariant (target : Label n) (route : RawCtxServerRouting.SenderDecoder)
    (state : State) (safe : PqxdhRecordLiftProtocolHistory.Safe state.1.2) :
    Invariant target route (PqxdhDeploymentSecrecy.Ledger.empty, state) :=
  ⟨safe, by simp [PqxdhDeploymentSecrecy.Ledger.empty]⟩


/-- Any accepted raw record in the same current complete ledger raises the marker for its actual physical label. The original source failures and public reserve poststates are retained. -/
theorem received (serverKid : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp PqxdhDeploymentInterface.FullSpec X) (before : State)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × State))
    (supported : result∈support ((simulateQ (fullImpl target modes replace setup codec route env reserve serverKid bounds) work).run
      (PqxdhDeploymentSecrecy.Ledger.empty,before)))
    (entry : Entry) (member : entry∈result.2.1.transcript)
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted) (handle : Handle)
    (accepted : entry.received=some (receiver,raw,.Some opened))
    (routed : PqxdhRecordLiftIdeal.receivingHandle route receiver raw=some handle)
    (slot : handleSlot result.2.2.1.2 handle=some target.slot)
    (direction : target.direction = !PqxdhRecordFactsOriginHandles.handleDirection handle)
    (position : target.position+1=opened.sequence.val) : result.2.2.2.2=true := by
  have invariant := full_program_invariant target modes replace setup codec route env reserve serverKid bounds work
    (PqxdhDeploymentSecrecy.Ledger.empty,before) (empty_invariant target route before safe) result supported
  exact (invariant.2 entry member receiver raw opened handle accepted routed).2 slot direction position
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker.final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker.final

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker.full_invariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker.full_program_invariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker.received' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGatedMarker.received
