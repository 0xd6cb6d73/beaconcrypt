-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy
/-! A successful inner native send is the publication of its same literal full-ledger callback. This is reply bookkeeping for the actual test/fresh program, with arbitrary private/native state and failed branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPublication
open PqxdhDeploymentInterface (Spec FullSpec Entry Handle FreshBounds)
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativeStageTrace (Call)
variable {S V Reader Response : Type}

def Good (outer : Entry) (calls : List (Call Spec S)) : Prop :=
  ∀call∈calls,∀pair,(⟨.inl call.query,call.reply⟩ : Entry).published=some pair → outer.published=some pair

private theorem empty (outer : Entry) : Good (S := S) outer [] := by intro call member;cases member

private theorem append (outer : Entry) (calls : List (Call Spec S)) (good : Good outer calls)
    (call : Call Spec S)
    (same : ∀pair,(⟨.inl call.query,call.reply⟩ : Entry).published=some pair → outer.published=some pair) :
    Good outer (calls++[call]) := by
  intro chosen member pair published
  rcases List.mem_append.mp member with prior | current
  · exact good chosen prior pair published
  · simp only [List.mem_singleton] at current
    subst chosen
    exact same pair published

variable (implementation : QueryImpl Spec (StateT S ProbComp))
local notation "logged" => RegistrationNativeStageTrace.handler implementation

private theorem query_good (outer : Entry) (query : Spec.Domain) (before : S × List (Call Spec S))
    (good : Good outer before.2) (result : Spec.Range query × (S × List (Call Spec S)))
    (supported : result ∈ support ((logged query).run before))
    (same : ∀pair,(⟨.inl query,result.1⟩ : Entry).published=some pair → outer.published=some pair) : Good outer result.2.2 := by
  simp only [RegistrationNativeStageTrace.handler,StateT.run,support_map] at supported
  obtain ⟨actual,_called,rfl⟩ := supported
  exact append outer before.2 good _ same

private theorem coin_good (outer : Entry) (amount : Nat) (before : S × List (Call Spec S))
    (good : Good outer before.2) (result : Fin (amount+1) × (S × List (Call Spec S)))
    (supported : result ∈ support ((logged (.inl amount)).run before)) : Good outer result.2.2 := by
  exact query_good implementation outer (.inl amount) before good result supported (by intro pair impossible;cases impossible)

private theorem bit_good (outer : Entry) (before : S × List (Call Spec S)) (good : Good outer before.2)
    (result : Bool × (S × List (Call Spec S)))
    (supported : result ∈ support ((simulateQ logged PqxdhDeploymentSecrecy.drawBit).run before)) : Good outer result.2.2 := by
  simp only [PqxdhDeploymentSecrecy.drawBit,PqxdhDeploymentSecrecy.coin,simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at supported
  obtain ⟨actual,called,rfl⟩ := supported
  exact coin_good implementation outer 1 before good actual called

private theorem bytes_good (outer : Entry) (length : Nat) (before : S × List (Call Spec S)) (good : Good outer before.2)
    (result : Pqxdh.Bytes × (S × List (Call Spec S)))
    (supported : result ∈ support ((simulateQ logged (PqxdhDeploymentSecrecy.uniformBytes length)).run before)) : Good outer result.2.2 := by
  induction length generalizing before result with
  | zero =>
      simp only [PqxdhDeploymentSecrecy.uniformBytes,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      subst result
      exact good
  | succ length ih =>
      simp only [PqxdhDeploymentSecrecy.uniformBytes,PqxdhDeploymentSecrecy.coin,simulateQ_bind,simulateQ_spec_query,simulateQ_pure,
        StateT.run_bind,StateT.run_pure,mem_support_bind_iff] at supported
      obtain ⟨drawn,called,rest,continued,finished⟩ := supported
      obtain rfl := (mem_support_pure_iff _ _).mp finished
      exact ih drawn.2 (coin_good implementation outer 255 before good drawn called) rest continued

private theorem send_good (outer : Entry) (handle : Handle) (plaintext : Pqxdh.Bytes)
    (before : S × List (Call Spec S)) (good : Good outer before.2)
    (result : Option RawCtxSourceSend.Encrypted × (S × List (Call Spec S)))
    (supported : result ∈ support ((simulateQ logged (PqxdhDeploymentSecrecy.send handle plaintext)).run before))
    (same : outer.published=result.1.map (fun encrypted => (handle,encrypted))) : Good outer result.2.2 := by
  cases handle with
  | peer keyId =>
      simp only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] at supported
      apply query_good implementation outer (.inr (.serverSend keyId plaintext)) before good result supported
      intro pair published
      rw [same]
      cases found : result.1 <;> simpa only [Entry.published,found,Option.map_none,Option.map_some] using published
  | owner owner =>
      simp only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] at supported
      apply query_good implementation outer (.inr (.beaconSend owner plaintext)) before good result supported
      intro pair published
      rw [same]
      cases found : result.1 <;> simpa only [Entry.published,found,Option.map_none,Option.map_some] using published

/-- Every successful native send journaled inside the actual full callback is its same outer publication, including experiment-chosen test and fresh messages. -/
theorem full (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64) (bounds : FreshBounds)
    (query : FullSpec.Domain) (ledger : PqxdhDeploymentSecrecy.Ledger) (before : S)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × (S × List (Call Spec S)))
    (supported : result ∈ support ((simulateQ logged ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKeyId bounds query).run ledger)).run (before,[]))) :
    Good (⟨query,result.1.1⟩ : Entry) result.2.2 := by
  rcases query with forwarded | (⟨handle,left,right⟩ | ⟨handle,length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward,simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at supported
    obtain ⟨actual,called,rfl⟩ := supported
    exact query_good implementation _ forwarded (before,[]) (empty _) actual called (by intro pair found;exact found)
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl,StateT.run] at supported
    split at supported
    · split at supported
      · simp only [simulateQ_bind,simulateQ_pure] at supported
        change result ∈ support ((_ : StateT (S × List (Call Spec S)) ProbComp _).run (before,[])) at supported
        simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff] at supported
        obtain ⟨drawn,called,sent,continued,finished⟩ := supported
        obtain rfl := (mem_support_pure_iff _ _).mp finished
        apply send_good implementation _ handle _ drawn.2 (bit_good implementation _ (before,[]) (empty _) drawn called) sent continued
        cases sent.1 <;> rfl
      · split at supported
        · simp only [simulateQ_bind,simulateQ_pure] at supported
          change result ∈ support ((_ : StateT (S × List (Call Spec S)) ProbComp _).run (before,[])) at supported
          simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff] at supported
          obtain ⟨sent,called,finished⟩ := supported
          obtain rfl := (mem_support_pure_iff _ _).mp finished
          apply send_good implementation _ handle _ (before,[]) (empty _) sent called
          cases sent.1 <;> rfl
        · simp only [simulateQ_pure] at supported
          change result ∈ support ((_ : StateT (S × List (Call Spec S)) ProbComp _).run (before,[])) at supported
          simp only [StateT.run_pure,mem_support_pure_iff] at supported
          subst result
          exact empty _
    · simp only [simulateQ_pure] at supported
      change result ∈ support ((_ : StateT (S × List (Call Spec S)) ProbComp _).run (before,[])) at supported
      simp only [StateT.run_pure,mem_support_pure_iff] at supported
      subst result
      exact empty _
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl,StateT.run] at supported
    split at supported
    · simp only [simulateQ_bind,simulateQ_pure] at supported
      change result ∈ support ((_ : StateT (S × List (Call Spec S)) ProbComp _).run (before,[])) at supported
      simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff] at supported
      obtain ⟨drawn,called,sent,continued,finished⟩ := supported
      obtain rfl := (mem_support_pure_iff _ _).mp finished
      apply send_good implementation _ handle _ drawn.2 (bytes_good implementation _ length (before,[]) (empty _) drawn called) sent continued
      cases sent.1 <;> rfl
    · simp only [simulateQ_pure] at supported
      change result ∈ support ((_ : StateT (S × List (Call Spec S)) ProbComp _).run (before,[])) at supported
      simp only [StateT.run_pure,mem_support_pure_iff] at supported
      subst result
      exact empty _

section Actual
open PqxdhRecordLiftIdeal (KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK E Failure : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
local notation "runtime" => CborRawRecordFlat.NativeState n E
local notation "impl" => RegistrationNativePlatformGatedRecordFreshCoupling.nativeImpl modes replace setup codec route env reserve
include ideal readback in
/-- A new hidden seal in an actual full callback has its same source acquisition and actual public send reply. Any successful inner publication is necessarily this outer ledger entry's publication. -/
theorem acquired (serverKeyId : U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : runtime)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × runtime))
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route env reserve serverKeyId bounds query).run (ledger,before)))
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal) (absent : entry ∉ (before.2.keys label).1.successfulSeals)
    (present : entry ∈ (result.2.2.2.keys label).1.successfulSeals) :
    ∃ (call : Call Spec runtime), ∃ leading trailing,
      RegistrationNativeStageTrace.Path impl before leading call.before ∧ RegistrationNativeStageTrace.Executed impl call ∧
      RegistrationNativeStageTrace.Path impl call.after trailing result.2.2 ∧ PqxdhRecordLiftProtocolHistory.Safe call.before.1.2 ∧
      entry ∉ (call.before.2.keys label).1.successfulSeals ∧ entry ∈ (call.after.2.keys label).1.successfulSeals ∧
      (∀pair,(⟨.inl call.query,call.reply⟩ : Entry).published=some pair → (⟨query,result.1⟩ : Entry).published=some pair) ∧
      ∃ original,original ∈ support ((CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route call.query).run call.before) ∧
        (call.reply,call.after) ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold (ctxInterpreter modes replace setup codec) codec route
          (RegistrationNativePlatformGatedRecordInterface.post reserve call.query original.1)).run original.2) ∧
        PqxdhRecordFactsOriginPublicationNative.CreatedAt codec call.before.1.2 ⟨.inl call.query,original.1⟩ label entry := by
  change result ∈ support ((fun actual => (actual.1.1,(actual.1.2,actual.2))) <$>
    (simulateQ impl ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run ledger)).run before) at supported
  rw [←RegistrationNativeStageTrace.erase impl _ (before,[]),Functor.map_map,support_map] at supported
  obtain ⟨journal,called,rfl⟩ := supported
  have actual := RegistrationNativeStageTrace.path impl _ before journal called
  have publication := full impl setup.source.crypto codec serverKeyId bounds query ledger before journal called
  obtain ⟨call,leading,trailing,split,prior,middle,suffix,safeBefore,notYet,inserted,original,sourceCalled,gated,created⟩ :=
    RegistrationNativePlatformOriginNativeAttribution.path_entry modes ideal replace setup codec route readback env reserve
      actual safe label entry absent present
  have member : call ∈ journal.2.2 := by rw [split];simp
  exact ⟨call,leading,trailing,prior,middle,suffix,safeBefore,notYet,inserted,
    publication call member,original,sourceCalled,gated,created⟩
end Actual
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPublication.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPublication.full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPublication.acquired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPublication.acquired
