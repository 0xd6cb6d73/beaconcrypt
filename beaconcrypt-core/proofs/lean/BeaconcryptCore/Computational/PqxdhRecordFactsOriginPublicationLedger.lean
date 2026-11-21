-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper

/-! Actual secrecy-ledger publication history through every source branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger
open PqxdhRecordLiftIdeal PqxdhRecordLiftInterface PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginPublicationHistory PqxdhRecordFactsOriginPublicationWrapper
open PqxdhRecordFactsOriginControl
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Entry Spec FullSpec FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The actual full ledger step establishes history at its actual resulting transcript, including test/fresh coins and refusals. -/
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

/-- The flattened full query preserves history at its literal final ledger. -/
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

/-- Source safety and dictionary publication evidence at the current literal ledger. -/
def Invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  Safe state.2.1.2 ∧ History codec state.2.1.2 state.2.2 state.1.transcript

/-- One actual full query preserves the current-prefix source invariant. -/
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

/-- Every adaptive full continuation preserves history relative to its literal evolving transcript. -/
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

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger.ledger_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger.ledger_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger.full_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger.full_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger.full_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger.full_program_invariant
