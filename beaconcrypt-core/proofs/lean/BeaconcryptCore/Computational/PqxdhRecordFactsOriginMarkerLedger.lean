-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry
import BeaconcryptCore.Computational.PqxdhDeploymentTargetRange

/-! The complete adaptive secrecy ledger retains every selected receive marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (KnownAt support_keep_oracle support_run_fst)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle FullSpec FreshBounds)
open PqxdhRecordFactsOriginMarkerNative PqxdhRecordFactsOriginMarkerEntry
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The actual secrecy ledger over the marked native source compiler. -/
noncomputable def fullImpl (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (PqxdhDeploymentSecrecy.Ledger × State n E) ProbComp) :=
  ((nativeImpl target modes replace setup codec route env).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds)).flattenStateT

/-- Exact full-query execution retains the literal ledger, native state, and analysis flag. -/
theorem full_run (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (state : State n E) :
    (fullImpl target modes replace setup codec route env serverKid bounds query).run (ledger, state) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (nativeImpl target modes replace setup codec route env)
        ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state := rfl

/-- Every actual ledger step appends its literal query/reply and gives the exact final selected received-entry fact. -/
theorem ledger_record (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : State n E) (safe : Safe before.1.2)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × State n E)
    (supported : result ∈ support ((simulateQ (nativeImpl target modes replace setup codec route env)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run before)) :
    result.1.2.transcript = ledger.transcript ++ [⟨query, result.1.1⟩] ∧
      EntryFact target route result.2.1.2 result.2.2.2 ⟨query, result.1.1⟩ := by
  refine ⟨PqxdhDeploymentTargetRange.ledger_step setup.source.crypto codec serverKid bounds query ledger result.1
    (support_run_fst _ _ _ result supported), ?_⟩
  rcases query with forwarded | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact native_final target modes replace setup codec route env forwarded before safe inner reached
  · exact secrecy_entry target route result.2.1.2 result.2.2.2 secrecy result.1.1

/-- Every recorded accepted entry retains its current handle provenance and same-execution selected marker; the source control is safe. -/
def Invariant (target : Label n) (route : RawCtxServerRouting.SenderDecoder)
    (state : PqxdhDeploymentSecrecy.Ledger × State n E) : Prop :=
  Safe state.2.1.2 ∧ ∀ entry ∈ state.1.transcript, EntryFact target route state.2.1.2 state.2.2.2 entry

/-- A complete full query preserves all earlier received-entry facts and appends its literal new entry. -/
theorem full_invariant (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × State n E) (good : Invariant target route before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × State n E))
    (supported : result ∈ support ((fullImpl target modes replace setup codec route env serverKid bounds query).run before)) :
    Invariant target route result.2 := by
  rw [full_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have progress := program_step target modes replace setup codec route env _ before.2 good.1 inner reached
  have recorded := ledger_record target modes replace setup codec route env serverKid bounds query before.1 before.2 good.1 inner reached
  refine ⟨progress.1, ?_⟩
  intro entry member
  rw [recorded.1, List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · exact entry_mono target route before.2.1.2 inner.2.1.2 before.2.2.2 inner.2.2.2 progress
      (fun handle known => program_known target modes replace setup codec route env _ before.2 handle known inner reached)
      (fun bad => program_sticky target modes replace setup codec route env _ before.2 bad inner reached)
      entry (good.2 entry prior)
  · exact recorded.2

/-- Every adaptive full continuation preserves selected received-entry facts through all permitted commands. -/
theorem full_program_invariant (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × State n E) (good : Invariant target route before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × State n E))
    (supported : result ∈ support ((simulateQ (fullImpl target modes replace setup codec route env serverKid bounds) client).run before)) :
    Invariant target route result.2 :=
  support_keep_oracle (fullImpl target modes replace setup codec route env serverKid bounds) (Invariant target route)
    (fun query state present => full_invariant target modes replace setup codec route env serverKid bounds query state present)
    client before good result supported

/-- The actual empty initial transcript needs only source control safety; no record-origin or marker assumption is supplied. -/
theorem empty_invariant (target : Label n) (route : RawCtxServerRouting.SenderDecoder)
    (state : State n E) (safe : Safe state.1.2) :
    Invariant target route (PqxdhDeploymentSecrecy.Ledger.empty, state) :=
  ⟨safe, by simp [PqxdhDeploymentSecrecy.Ledger.empty]⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.full_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.full_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.ledger_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.ledger_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.full_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.full_program_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.empty_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger.empty_invariant
