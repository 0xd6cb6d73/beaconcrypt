-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingNative
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingLedger
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal

/-! Exact initialized adaptive ledger evidence for caller-known and hidden records. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsBindingKnown PqxdhRecordFactsBindingEvidence PqxdhRecordFactsBindingNative
open PqxdhRecordFactsOriginNative PqxdhRecordFactsOriginControl PqxdhRecordFactsOriginGlobal
open PqxdhRecordFactsOriginLedger (secrecyHandle)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Receiver Spec FullSpec Entry Secrecy FreshBounds Mode ModeSpec asModeO)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- A secrecy entry retains shared-cache evidence for its actual successful caller-known send. -/
theorem secrecy_knownEntryFacts (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (query : Secrecy) (reply : Option RawCtxSourceSend.Encrypted)
    (good : ∀ encrypted, reply = some encrypted → KnownAt control (secrecyHandle query) →
      SharedRecord codec secret encrypted.ciphertext) :
    KnownEntryFacts codec route control secret ⟨.inr query, reply⟩ := by
  cases query <;> cases reply <;> simp_all [KnownEntryFacts, Entry.published, Entry.received, secrecyHandle]

/-- Every actual ledger command appends its literal reply with final caller-known commitment evidence. -/
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
      KnownEntryFacts codec route result.2.1.2 result.2.2 ⟨query, result.1.1⟩ := by
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact ⟨rfl, native_knownEntryFacts modes ideal replace setup codec route readback env forwarded before safe inner reached⟩
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    split at supported
    · split at supported
      · simp only [simulateQ_bind, simulateQ_pure] at supported
        change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
        simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
        obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
        obtain rfl := (mem_support_pure_iff _ _).mp finished
        exact ⟨rfl, secrecy_knownEntryFacts codec route sent.2.1.2 sent.2.2 (.test handle left right) sent.1
          (native_send_shared modes ideal replace setup codec route readback env handle
            (if drawn.1 then right else left) drawn.2
            (native_program_step modes replace setup codec route env _ before safe drawn drawReached).1 sent sendReached)⟩
      · split at supported
        · simp only [simulateQ_bind, simulateQ_pure] at supported
          change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
          simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
          obtain ⟨sent, sendReached, finished⟩ := supported
          obtain rfl := (mem_support_pure_iff _ _).mp finished
          exact ⟨rfl, secrecy_knownEntryFacts codec route sent.2.1.2 sent.2.2 (.test handle left right) sent.1
            (native_send_shared modes ideal replace setup codec route readback env handle _ before safe sent sendReached)⟩
        · obtain rfl := (mem_support_pure_iff _ _).mp supported
          simp [PqxdhDeploymentSecrecy.Ledger.record, KnownEntryFacts, Entry.published, Entry.received]
    · obtain rfl := (mem_support_pure_iff _ _).mp supported
      simp [PqxdhDeploymentSecrecy.Ledger.record, KnownEntryFacts, Entry.published, Entry.received]
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    split at supported
    · simp only [simulateQ_bind, simulateQ_pure] at supported
      change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
      obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
      obtain rfl := (mem_support_pure_iff _ _).mp finished
      exact ⟨rfl, secrecy_knownEntryFacts codec route sent.2.1.2 sent.2.2 (.fresh handle length) sent.1
        (native_send_shared modes ideal replace setup codec route readback env handle drawn.1 drawn.2
          (native_program_step modes replace setup codec route env _ before safe drawn drawReached).1 sent sendReached)⟩
    · obtain rfl := (mem_support_pure_iff _ _).mp supported
      simp [PqxdhDeploymentSecrecy.Ledger.record, KnownEntryFacts, Entry.published, Entry.received]

/-- Every flattened full query appends the actual reply with exact final caller-known evidence. -/
theorem full_record (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    result.2.1.transcript = before.1.transcript ++ [⟨query, result.1⟩] ∧
      KnownEntryFacts codec route result.2.2.1.2 result.2.2.2 ⟨query, result.1⟩ := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ledger_record modes ideal replace setup codec route readback env serverKid bounds query before.1 before.2 safe inner reached

/-- The actual ledger has source-derived endpoint classification and every caller-known cache witness. -/
def Invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  PqxdhRecordFactsOriginLedger.Invariant codec route state ∧
    ∀ entry ∈ state.1.transcript, KnownEntryFacts codec route state.2.1.2 state.2.2 entry

/-- One complete actual query preserves prior witnesses and appends its literal record observation. -/
theorem full_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Invariant codec route result.2 := by
  refine ⟨PqxdhRecordFactsOriginLedger.full_invariant modes ideal replace setup codec route readback
    env serverKid bounds query before good.1 result supported, ?_⟩
  intro entry member
  have recorded := full_record modes ideal replace setup codec route readback env serverKid bounds query before good.1.1 result supported
  rw [recorded.1, List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · exact knownEntryFacts_mono codec route before.2.1.2 result.2.2.1.2 before.2.2 result.2.2.2
      (full_step modes replace setup codec route env serverKid bounds query before good.1.1 result supported)
      (full_cache_grows modes replace setup codec route env serverKid bounds query before result supported)
      entry (good.1.2 entry prior) (good.2 entry prior)
  · exact recorded.2

/-- Every adaptive full continuation retains the source classification and all known-record commitment witnesses. -/
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

/-- An empty analysis ledger starts without any assumed record witness. -/
theorem empty_invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (state : NativeState n E) (safe : Safe state.1.2) :
    Invariant codec route (PqxdhDeploymentSecrecy.Ledger.empty, state) :=
  ⟨PqxdhRecordFactsOriginLedger.empty_invariant codec route state safe,
    by simp [PqxdhDeploymentSecrecy.Ledger.empty]⟩

/-- The initialized complete source run derives shared-cache evidence for every caller-known transcript record. -/
theorem ctxRun_knownEntryFacts (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript,
      KnownEntryFacts codec route result.1.2 result.2 entry := by
  rw [ctxRun_flat, mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  cases bornEq : born.1.1 with
  | none =>
    simp only [bornEq] at continued
    obtain rfl := (mem_support_pure_iff _ _).mp continued
    simp
  | some initial =>
    rcases initial with ⟨created, initial⟩
    simp only [bornEq, mem_support_bind_iff] at continued
    obtain ⟨installed, installSupported, continued⟩ := continued
    rw [support_map] at continued
    obtain ⟨final, finalSupported, rfl⟩ := continued
    have complete := full_program_invariant modes ideal replace setup codec route readback
      env serverKid bounds (asModeO mode adversary) _
      (empty_invariant codec route _ (install_safe modes replace setup codec route created born.1.2
        (startup_safe modes replace setup codec route env born bornSupported) born.2 installed installSupported)) final finalSupported
    simpa using complete.2

/-- The public view retains the initialized source run's caller-known record witnesses. -/
theorem ctxView_knownEntryFacts (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ (ctxView result).result, ∀ entry ∈ value.2.1.transcript,
      KnownEntryFacts codec route result.1.2 result.2 entry := by
  intro value member
  change value ∈ result.1.1.map _ at member
  rw [Option.mem_def, Option.map_eq_some_iff] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  exact ctxRun_knownEntryFacts modes ideal replace setup codec route readback env serverKid bounds mode adversary
    result supported original originalMember

/-- The actual initialized adaptive source run discharges all four internal binding-ledger obligations. -/
theorem ctxView_ledgerEvidence (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ (ctxView result).result,
      PqxdhRecordFactsBindingLedger.LedgerEvidence codec route result.1.2 result.2 value.2.1.transcript := by
  intro value member
  have facts := ctxView_entryFacts modes ideal replace setup codec route readback env serverKid bounds mode adversary result supported value member
  have shared := ctxView_knownEntryFacts modes ideal replace setup codec route readback env serverKid bounds mode adversary result supported value member
  refine ⟨?_, (fun entry member => (facts entry member).1),
    (fun entry member => (shared entry member).2),
    (fun entry member => (shared entry member).1)⟩
  intro entry entryMember receiver raw opened handle returned routed
  obtain ⟨actualHandle, actualRoute, accepted⟩ := (facts entry entryMember).2 receiver raw opened returned
  exact (Option.some.inj (actualRoute.symm.trans routed)) ▸ accepted

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.secrecy_knownEntryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.secrecy_knownEntryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.ledger_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.ledger_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.full_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.full_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.full_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.full_program_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.empty_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.empty_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.ctxRun_knownEntryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.ctxRun_knownEntryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.ctxView_knownEntryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.ctxView_knownEntryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.ctxView_ledgerEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger.ctxView_ledgerEvidence
