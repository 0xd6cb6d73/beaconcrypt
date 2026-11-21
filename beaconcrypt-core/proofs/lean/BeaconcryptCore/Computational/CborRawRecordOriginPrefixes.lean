-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginHistory
import BeaconcryptCore.Computational.PqxdhDeploymentTargetRange
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes

/-! Every receive in the actual raw cursor ledger keeps its exact pre-event transcript and original failed-writer distinction. Prefix witnesses survive later forwarded and refused commands without changing their earlier public entries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginPrefixes
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (support_keep_oracle support_run_fst)
open CborRawRecordFlat (NativeState nativeImpl fullImpl fullImpl_run)
open CborRawRecordOriginProgress
open PqxdhRecordFactsOriginPublicationHistory (History)
open PqxdhRecordFactsOriginPublicationTemporal (ReceivedBefore receivedBefore_mono)
open PqxdhRecordFactsOriginPublicationPrefixes (Prefixes split_snoc)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Spec FullSpec Entry FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

theorem full_receivedBefore (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (history : History codec before.2.1.2 before.2.2 before.1.transcript)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    ReceivedBefore codec route result.2.2.1.2 result.2.2.2 before.1.transcript ⟨query, result.1⟩ := by
  rcases query with forwarded | secrecy
  · rw [fullImpl_run, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at reached
    obtain ⟨nativeResult, nativeReached, rfl⟩ := reached
    exact native_receivedBefore modes ideal replace setup codec route readback env forwarded before.2 safe
      before.1.transcript history nativeResult nativeReached
  · cases secrecy <;> simp [ReceivedBefore, Entry.received]


/-- The actual original secrecy ledger appends its literal query and reply after every private subprogram, including refused sends. -/
theorem full_record_trace (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    result.2.1.transcript = before.1.transcript ++ [⟨query, result.1⟩] := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhDeploymentTargetRange.ledger_step setup.source.crypto codec serverKid bounds query before.1 inner.1
    (support_run_fst _ _ _ inner reached)

/-- Complete current history and every actual earlier receive prefix. -/
def Invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  CborRawRecordOriginHistory.Invariant codec state ∧
    Prefixes codec route state.2.1.2 state.2.2 state.1.transcript

/-- Actual full-ledger execution retains every literal earlier receive prefix. -/
theorem full_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Invariant codec route result.2 := by
  have progress := full_step modes replace setup codec route env serverKid bounds query before good.1.1 result supported
  have grows := full_grows modes ideal replace setup codec route env serverKid bounds query before result supported
  have recorded := full_record_trace modes replace setup codec route env serverKid bounds query before result supported
  refine ⟨CborRawRecordOriginHistory.full_invariant modes ideal replace setup codec route readback
    env serverKid bounds query before good.1 result supported, ?_⟩
  intro earlier event later split
  rw [recorded] at split
  rcases split_snoc before.1.transcript ⟨query, result.1⟩ earlier event later split with ⟨tail, old⟩ | ⟨rfl, rfl, rfl⟩
  · exact receivedBefore_mono codec route before.2.1.2 result.2.2.1.2 before.2.2 result.2.2.2 progress
      (fun handle known => full_known modes replace setup codec route env serverKid bounds query before handle known result supported)
      grows.seals earlier event (good.2 earlier event tail old)
  · exact full_receivedBefore modes ideal replace setup codec route readback env serverKid bounds query
      before good.1.1 good.1.2 result supported


/-- Actual full-ledger execution retains every literal earlier receive prefix. -/
theorem full_program_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) client).run before)) :
    Invariant codec route result.2 :=
  support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds) (Invariant codec route)
    (fun query state valid => full_invariant modes ideal replace setup codec route readback env serverKid bounds query state valid)
    client before good result supported


end BeaconcryptCore.Computational.CborRawRecordOriginPrefixes

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPrefixes.full_receivedBefore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPrefixes.full_receivedBefore
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPrefixes.full_record_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPrefixes.full_record_trace
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPrefixes.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPrefixes.full_invariant
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPrefixes.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPrefixes.full_program_invariant
