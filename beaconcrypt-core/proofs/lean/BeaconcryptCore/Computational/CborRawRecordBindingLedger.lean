-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordBindingControl

/-! The actual raw-CBOR ledger derives all accepted, published and known-key cache witnesses from its literal callbacks. Empty initialized ledgers need only reached Protocol safety; no record-origin or binding conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawRecordBindingLedger
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocolHistory (Safe)
open PqxdhRecordLiftFlat (support_keep_oracle)
open PqxdhRecordFactsOriginNative (EntryFacts)
open PqxdhRecordFactsBindingNative (KnownEntryFacts)
open PqxdhDeploymentInterface (Spec FullSpec Entry Handle Secrecy FreshBounds)
open CborRawRecordFlat (NativeState nativeImpl fullImpl fullImpl_run)
open PqxdhRecordFactsOriginLedger (secrecyHandle)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

def Fact (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) (entry : Entry) : Prop :=
  EntryFacts codec route control secret entry ∧ KnownEntryFacts codec route control secret entry

private theorem secrecy_fact (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (query : Secrecy) (reply : Option RawCtxSourceSend.Encrypted)
    (good : ∀ encrypted, reply = some encrypted →
      PqxdhRecordFactsOriginPublished.Published codec control secret (secrecyHandle query) encrypted ∧
      (PqxdhRecordLiftFlat.KnownAt control (secrecyHandle query) →
        PqxdhRecordFactsBindingKnown.SharedRecord codec secret encrypted.ciphertext)) :
    Fact codec route control secret ⟨.inr query, reply⟩ :=
  ⟨PqxdhRecordFactsOriginLedger.secrecy_entryFacts codec route control secret query reply
      (fun encrypted returned => (good encrypted returned).1),
    PqxdhRecordFactsBindingKnownLedger.secrecy_knownEntryFacts codec route control secret query reply
      (fun encrypted returned => (good encrypted returned).2)⟩

private theorem send_fact (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec) (env : Environment n E)
    (handle : Handle) (plaintext : Pqxdh.Bytes) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    PqxdhRecordFactsOriginPublished.Published codec result.2.1.2 result.2.2 handle encrypted ∧
      (PqxdhRecordLiftFlat.KnownAt result.2.1.2 handle →
        PqxdhRecordFactsBindingKnown.SharedRecord codec result.2.2 encrypted.ciphertext) := by
  have reached := CborRawRecordBindingReceipt.send_supported modes replace setup codec route env handle plaintext before result supported encrypted returned
  exact ⟨PqxdhRecordFactsOriginNative.native_send_published modes ideal replace setup codec route readback env handle plaintext
      (CborRawRecordFlat.project before) safe _ reached encrypted returned,
    PqxdhRecordFactsBindingNative.native_send_shared modes ideal replace setup codec route readback env handle plaintext
      (CborRawRecordFlat.project before) safe _ reached encrypted returned⟩

/-- Every actual ledger command appends its literal reply with exact final-state record evidence. -/
theorem ledger_record (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : NativeState n E) (safe : Safe before.1.2)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run before)) :
    result.1.2.transcript = ledger.transcript ++ [⟨query, result.1.1⟩] ∧
      Fact codec route result.2.1.2 result.2.2 ⟨query, result.1.1⟩ := by
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact ⟨rfl, CborRawRecordBindingReceipt.native_final modes ideal replace setup codec route readback env forwarded before safe inner reached⟩
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    split at supported
    · split at supported
      · simp only [simulateQ_bind, simulateQ_pure] at supported
        change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
        simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
        obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
        obtain rfl := (mem_support_pure_iff _ _).mp finished
        refine ⟨rfl, secrecy_fact codec route sent.2.1.2 sent.2.2 (.test handle left right) sent.1 ?_⟩
        exact send_fact modes ideal replace setup codec route readback env handle
          (if drawn.1 then right else left) drawn.2
          (CborRawRecordBindingControl.native_program modes ideal replace setup codec route env _ before safe drawn drawReached).step.1 sent sendReached
      · split at supported
        · simp only [simulateQ_bind, simulateQ_pure] at supported
          change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
          simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
          obtain ⟨sent, sendReached, finished⟩ := supported
          obtain rfl := (mem_support_pure_iff _ _).mp finished
          exact ⟨rfl, secrecy_fact codec route sent.2.1.2 sent.2.2 (.test handle left right) sent.1
            (send_fact modes ideal replace setup codec route readback env handle _ before safe sent sendReached)⟩
        · obtain rfl := (mem_support_pure_iff _ _).mp supported
          simp [PqxdhDeploymentSecrecy.Ledger.record, Fact, EntryFacts, KnownEntryFacts, Entry.published, Entry.received]
    · obtain rfl := (mem_support_pure_iff _ _).mp supported
      simp [PqxdhDeploymentSecrecy.Ledger.record, Fact, EntryFacts, KnownEntryFacts, Entry.published, Entry.received]
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    split at supported
    · simp only [simulateQ_bind, simulateQ_pure] at supported
      change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
      obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
      obtain rfl := (mem_support_pure_iff _ _).mp finished
      exact ⟨rfl, secrecy_fact codec route sent.2.1.2 sent.2.2 (.fresh handle length) sent.1
        (send_fact modes ideal replace setup codec route readback env handle drawn.1 drawn.2
          (CborRawRecordBindingControl.native_program modes ideal replace setup codec route env _ before safe drawn drawReached).step.1 sent sendReached)⟩
    · obtain rfl := (mem_support_pure_iff _ _).mp supported
      simp [PqxdhDeploymentSecrecy.Ledger.record, Fact, EntryFacts, KnownEntryFacts, Entry.published, Entry.received]

/-- The flattened full query appends its actual reply and satisfies exact final-state record evidence. -/
theorem full_record (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    result.2.1.transcript = before.1.transcript ++ [⟨query, result.1⟩] ∧
      Fact codec route result.2.2.1.2 result.2.2.2 ⟨query, result.1⟩ := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ledger_record modes ideal replace setup codec route readback env serverKid bounds query
    before.1 before.2 safe inner reached

/-- Every retained transcript entry has both actual endpoint classification and known-key cache evidence. -/
def Invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  Safe state.2.1.2 ∧ ∀ entry ∈ state.1.transcript, Fact codec route state.2.1.2 state.2.2 entry

/-- One actual full callback extends its own original ledger and retains all earlier witnesses. -/
theorem full_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Invariant codec route result.2 := by
  have progress := CborRawRecordBindingControl.full_advance modes ideal replace setup codec route env serverKid bounds query before good.1 result supported
  have recorded := full_record modes ideal replace setup codec route readback env serverKid bounds query before good.1 result supported
  refine ⟨progress.step.1, ?_⟩
  intro entry member
  rw [recorded.1, List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · exact ⟨PqxdhRecordFactsOriginNative.entryFacts_mono codec route before.2.1.2 result.2.2.1.2 before.2.2 result.2.2.2
      progress.step progress.known progress.grows.seals entry (good.2 entry prior).1,
      PqxdhRecordFactsBindingNative.knownEntryFacts_mono codec route before.2.1.2 result.2.2.1.2 before.2.2 result.2.2.2
      progress.step progress.cache entry (good.2 entry prior).1 (good.2 entry prior).2⟩
  · exact recorded.2

/-- Every adaptive full continuation retains the derived actual transcript witnesses from its reached initialized cache. -/
theorem full_program (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (work : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) work).run before)) :
    Invariant codec route result.2 :=
  support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds) (Invariant codec route)
    (fun query current previous => full_invariant modes ideal replace setup codec route readback env serverKid bounds query current previous)
    work before good result supported

/-- Initial record witnesses are empty; only actual control safety is required. -/
theorem empty_invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (before : NativeState n E) (safe : Safe before.1.2) :
    Invariant codec route (PqxdhDeploymentSecrecy.Ledger.empty, before) :=
  ⟨safe, by simp [PqxdhDeploymentSecrecy.Ledger.empty]⟩

/-- The four exact source-ledger obligations follow from the derived transcript facts. -/
theorem evidence (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E)
    (good : Invariant codec route before) :
    PqxdhRecordFactsBindingLedger.LedgerEvidence codec route before.2.1.2 before.2.2 before.1.transcript := by
  refine ⟨?_, fun entry member => (good.2 entry member).1.1,
    fun entry member => (good.2 entry member).2.2,
    fun entry member => (good.2 entry member).2.1⟩
  intro entry member receiver raw opened handle returned routed
  obtain ⟨actual, actualRoute, accepted⟩ := (good.2 entry member).1.2 receiver raw opened returned
  exact (Option.some.inj (actualRoute.symm.trans routed)) ▸ accepted

end BeaconcryptCore.Computational.CborRawRecordBindingLedger

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingLedger.ledger_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingLedger.ledger_record

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingLedger.full_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingLedger.full_record

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingLedger.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingLedger.full_invariant

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingLedger.full_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingLedger.full_program

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingLedger.empty_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingLedger.empty_invariant

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingLedger.evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingLedger.evidence
