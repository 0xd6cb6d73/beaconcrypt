-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative

/-! Actual secrecy-ledger record observations and their adaptive persistence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginControl
open PqxdhRecordFactsOriginPublished PqxdhRecordFactsOriginAccepted
open PqxdhRecordFactsOriginNative PqxdhRecordFactsOriginMonotone
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Receiver Spec FullSpec Entry Secrecy FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The literal handle selected by a secrecy command. -/
def secrecyHandle : Secrecy → Handle
  | .test handle _ _ => handle
  | .fresh handle _ => handle

/-- A secrecy entry records the optional ciphertext actually returned by its send. -/
theorem secrecy_entryFacts (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (query : Secrecy) (reply : Option RawCtxSourceSend.Encrypted)
    (good : ∀ encrypted, reply = some encrypted → Published codec control secret (secrecyHandle query) encrypted) :
    EntryFacts codec route control secret ⟨.inr query, reply⟩ := by
  cases query <;> cases reply <;> simp_all [EntryFacts, Entry.published, Entry.received, secrecyHandle]

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
      EntryFacts codec route result.2.1.2 result.2.2 ⟨query, result.1.1⟩ := by
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact ⟨rfl, native_entryFacts modes ideal replace setup codec route readback env forwarded before safe inner reached⟩
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    split at supported
    · split at supported
      · simp only [simulateQ_bind, simulateQ_pure] at supported
        change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
        simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
        obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
        obtain rfl := (mem_support_pure_iff _ _).mp finished
        refine ⟨rfl, secrecy_entryFacts codec route sent.2.1.2 sent.2.2 (.test handle left right) sent.1 ?_⟩
        exact native_send_published modes ideal replace setup codec route readback env handle
          (if drawn.1 then right else left) drawn.2
          (native_program_step modes replace setup codec route env _ before safe drawn drawReached).1 sent sendReached
      · split at supported
        · simp only [simulateQ_bind, simulateQ_pure] at supported
          change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
          simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
          obtain ⟨sent, sendReached, finished⟩ := supported
          obtain rfl := (mem_support_pure_iff _ _).mp finished
          exact ⟨rfl, secrecy_entryFacts codec route sent.2.1.2 sent.2.2 (.test handle left right) sent.1
            (native_send_published modes ideal replace setup codec route readback env handle _ before safe sent sendReached)⟩
        · obtain rfl := (mem_support_pure_iff _ _).mp supported
          simp [PqxdhDeploymentSecrecy.Ledger.record, EntryFacts, Entry.published, Entry.received]
    · obtain rfl := (mem_support_pure_iff _ _).mp supported
      simp [PqxdhDeploymentSecrecy.Ledger.record, EntryFacts, Entry.published, Entry.received]
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    split at supported
    · simp only [simulateQ_bind, simulateQ_pure] at supported
      change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
      obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
      obtain rfl := (mem_support_pure_iff _ _).mp finished
      exact ⟨rfl, secrecy_entryFacts codec route sent.2.1.2 sent.2.2 (.fresh handle length) sent.1
        (native_send_published modes ideal replace setup codec route readback env handle drawn.1 drawn.2
          (native_program_step modes replace setup codec route env _ before safe drawn drawReached).1 sent sendReached)⟩
    · obtain rfl := (mem_support_pure_iff _ _).mp supported
      simp [PqxdhDeploymentSecrecy.Ledger.record, EntryFacts, Entry.published, Entry.received]

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
      EntryFacts codec route result.2.2.1.2 result.2.2.2 ⟨query, result.1⟩ := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ledger_record modes ideal replace setup codec route readback env serverKid bounds query
    before.1 before.2 safe inner reached

/-- Every recorded observation has its exact current source witness, and the actual control is safe. -/
def Invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  Safe state.2.1.2 ∧ ∀ entry ∈ state.1.transcript, EntryFacts codec route state.2.1.2 state.2.2 entry

/-- One complete full query preserves every prior record witness and adds its literal new observation. -/
theorem full_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Invariant codec route result.2 := by
  have progress := full_step modes replace setup codec route env serverKid bounds query before good.1 result supported
  have grows := full_grows modes ideal replace setup codec route env serverKid bounds query before result supported
  have recorded := full_record modes ideal replace setup codec route readback env serverKid bounds query before good.1 result supported
  refine ⟨progress.1, ?_⟩
  intro entry member
  rw [recorded.1, List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · exact entryFacts_mono codec route before.2.1.2 result.2.2.1.2 before.2.2 result.2.2.2 progress
      (fun handle known => full_known modes replace setup codec route env serverKid bounds query before handle known result supported)
      grows.seals entry (good.2 entry prior)
  · exact recorded.2

/-- Every adaptive full continuation preserves all prior accepted and published record witnesses. -/
theorem full_program_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) client).run before)) :
    Invariant codec route result.2 :=
  support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds)
    (Invariant codec route)
    (fun query state invariant => full_invariant modes ideal replace setup codec route readback env serverKid bounds query state invariant)
    client before good result supported

/-- An empty analysis ledger has no assumed record origin; only the derived source control safety is needed. -/
theorem empty_invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (state : NativeState n E) (safe : Safe state.1.2) :
    Invariant codec route (PqxdhDeploymentSecrecy.Ledger.empty, state) :=
  ⟨safe, by simp [PqxdhDeploymentSecrecy.Ledger.empty]⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.secrecy_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.secrecy_entryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.ledger_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.ledger_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.full_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.full_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.full_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.full_program_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.empty_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger.empty_invariant

