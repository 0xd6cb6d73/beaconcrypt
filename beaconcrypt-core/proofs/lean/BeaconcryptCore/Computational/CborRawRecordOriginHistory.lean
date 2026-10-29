-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginProgress

/-! The original secrecy ledger retains raw temporal publication history below its actual private draws and native CBOR send refusals. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginHistory
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (support_keep_oracle support_run_fst)
open CborRawRecordFlat (NativeState nativeImpl fullImpl fullImpl_run)
open PqxdhRecordFactsOriginPublicationHistory (History history_publications_eq)
open PqxdhRecordFactsOriginPublicationWrapper (history_append)
open CborRawRecordOriginProgress
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Spec FullSpec Entry FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Literal uniform draws preserve every actual hidden sealing dictionary and its publication witness. -/
theorem coin_history (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (coin : Nat) (before : NativeState n E) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Fin (coin + 1) × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inl coin)).run before)) :
    History codec result.2.1.2 result.2.2 transcript := by
  have projected : (result.1, CborRawRecordOriginService.project result.2) ∈ support
      ((CborRawRecordOriginService.original (ctxInterpreter modes replace setup codec) env codec route (.inl coin)).run
        (CborRawRecordOriginService.project before)) := by
    rw [← CborRawRecordOriginService.nonrecord_project _ env codec route (.inl coin) before
      (by simp [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]), support_map]
    exact ⟨result, supported, rfl⟩
  exact PqxdhRecordFactsOriginPublicationWrapper.coin_history modes replace setup codec route env coin
    (CborRawRecordOriginService.project before) transcript history _ projected

/-- The complete actual raw ledger retains this current-transcript publication witness. -/
theorem drawBit_history (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (before : NativeState n E) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Bool × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      PqxdhDeploymentSecrecy.drawBit).run before)) :
    History codec result.2.1.2 result.2.2 transcript := by
  simp only [PqxdhDeploymentSecrecy.drawBit, PqxdhDeploymentSecrecy.coin, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact coin_history modes replace setup codec route env 1 before transcript history inner reached


/-- The complete actual raw ledger retains this current-transcript publication witness. -/
theorem uniformBytes_history (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (length : Nat) (before : NativeState n E) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Pqxdh.Bytes × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.uniformBytes length)).run before)) :
    History codec result.2.1.2 result.2.2 transcript := by
  induction length generalizing before result with
  | zero =>
    simp only [PqxdhDeploymentSecrecy.uniformBytes, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact history
  | succ length ih =>
    simp only [PqxdhDeploymentSecrecy.uniformBytes, PqxdhDeploymentSecrecy.coin,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff] at supported
    obtain ⟨drawn, drawReached, rest, restReached, finished⟩ := supported
    obtain rfl := (mem_support_pure_iff _ _).mp finished
    exact ih drawn.2 (coin_history modes replace setup codec route env 255 before transcript history drawn drawReached)
      rest restReached


/-- The complete actual raw ledger retains this current-transcript publication witness. -/
theorem send_history (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (handle : Handle) (plaintext : Pqxdh.Bytes) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before)) (event : Entry)
    (published : event.published = result.1.map (fun encrypted => (handle, encrypted))) :
    History codec result.2.1.2 result.2.2 (transcript ++ [event]) := by
  cases handle with
  | peer keyId =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    have actual := native_history modes ideal replace setup codec route readback env (.inr (.serverSend keyId plaintext))
      before safe transcript history result supported
    apply history_publications_eq codec result.2.1.2 result.2.2 _ _ _ actual
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, published]
    cases result.1 <;> rfl
  | owner owner =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    have actual := native_history modes ideal replace setup codec route readback env (.inr (.beaconSend owner plaintext))
      before safe transcript history result supported
    apply history_publications_eq codec result.2.1.2 result.2.2 _ _ _ actual
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, published]
    cases result.1 <;> rfl


/-- The complete actual raw ledger retains this current-transcript publication witness. -/
theorem ledger_history (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : NativeState n E) (safe : Safe before.1.2)
    (history : History codec before.1.2 before.2 ledger.transcript)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run before)) :
    History codec result.2.1.2 result.2.2 result.1.2.transcript := by
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact native_history modes ideal replace setup codec route readback env forwarded before safe
      ledger.transcript history inner reached
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    split at supported
    · split at supported
      · simp only [simulateQ_bind, simulateQ_pure] at supported
        change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
        simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
        obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
        obtain rfl := (mem_support_pure_iff _ _).mp finished
        apply send_history modes ideal replace setup codec route readback env handle _ drawn.2
          (native_program_step modes replace setup codec route env _ before safe drawn drawReached).1
          ledger.transcript (drawBit_history modes replace setup codec route env before ledger.transcript history drawn drawReached)
          sent sendReached ⟨.inr (.test handle left right), sent.1⟩
        cases sent.1 <;> rfl
      · split at supported
        · simp only [simulateQ_bind, simulateQ_pure] at supported
          change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
          simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
          obtain ⟨sent, sendReached, finished⟩ := supported
          obtain rfl := (mem_support_pure_iff _ _).mp finished
          apply send_history modes ideal replace setup codec route readback env handle _ before safe
            ledger.transcript history sent sendReached ⟨.inr (.test handle left right), sent.1⟩
          cases sent.1 <;> rfl
        · obtain rfl := (mem_support_pure_iff _ _).mp supported
          exact history_append codec before.1.2 before.2 ledger.transcript _ history
    · obtain rfl := (mem_support_pure_iff _ _).mp supported
      exact history_append codec before.1.2 before.2 ledger.transcript _ history
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    split at supported
    · simp only [simulateQ_bind, simulateQ_pure] at supported
      change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
      obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
      obtain rfl := (mem_support_pure_iff _ _).mp finished
      apply send_history modes ideal replace setup codec route readback env handle drawn.1 drawn.2
        (native_program_step modes replace setup codec route env _ before safe drawn drawReached).1
        ledger.transcript (uniformBytes_history modes replace setup codec route env length before ledger.transcript history drawn drawReached)
        sent sendReached ⟨.inr (.fresh handle length), sent.1⟩
      cases sent.1 <;> rfl
    · obtain rfl := (mem_support_pure_iff _ _).mp supported
      exact history_append codec before.1.2 before.2 ledger.transcript _ history


/-- The complete actual raw ledger retains this current-transcript publication witness. -/
theorem full_history (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (history : History codec before.2.1.2 before.2.2 before.1.transcript)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    History codec result.2.2.1.2 result.2.2.2 result.2.1.transcript := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ledger_history modes ideal replace setup codec route readback env serverKid bounds query before.1 before.2
    safe history inner reached

/-- Source control safety and exact sealing/publication history at the current original ledger. -/
def Invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  Safe state.2.1.2 ∧ History codec state.2.1.2 state.2.2 state.1.transcript

/-- Actual full-ledger execution preserves current publication history and all private fields. -/
theorem full_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Invariant codec result.2 :=
  ⟨(full_step modes replace setup codec route env serverKid bounds query before good.1 result supported).1,
    full_history modes ideal replace setup codec route readback env serverKid bounds query before good.1 good.2 result supported⟩


/-- Actual full-ledger execution preserves current publication history and all private fields. -/
theorem full_program_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) client).run before)) :
    Invariant codec result.2 :=
  support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds) (Invariant codec)
    (fun query state valid => full_invariant modes ideal replace setup codec route readback env serverKid bounds query state valid)
    client before good result supported


end BeaconcryptCore.Computational.CborRawRecordOriginHistory

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginHistory.coin_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginHistory.coin_history
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginHistory.drawBit_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginHistory.drawBit_history
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginHistory.uniformBytes_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginHistory.uniformBytes_history
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginHistory.send_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginHistory.send_history
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginHistory.ledger_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginHistory.ledger_history
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginHistory.full_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginHistory.full_history
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginHistory.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginHistory.full_invariant
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginHistory.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginHistory.full_program_invariant
