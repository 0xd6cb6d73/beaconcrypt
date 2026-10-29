-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginService
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal

/-! Concrete same-execution marker and receive-metadata receipts for every actual raw cursor command. Send refusals preserve the full source state and cannot create a receive receipt; successful receives use the exact original Protocol callback and private marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginReceipt
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (KnownAt support_keep_oracle support_run_fst)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Spec FullSpec Entry FreshBounds)
open PqxdhRecordFactsOriginMarkerNative (service)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

abbrev State (n : Nat) (E : Type) := CborRawRecordOriginService.State n E (CtxPrivate n × Bool)

noncomputable abbrev nativeImpl (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) := CborRawRecordOriginService.native (service target modes replace setup codec) env codec route

/-- Actual guarded calls preserve safe forward control independently of all service replies. -/
theorem native_step (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E) (safe : Safe before.1.2)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    Step before.1.2 result.2.1.2 :=
  CborRawRecordOriginService.native_step (service target modes replace setup codec) env codec route query before safe result supported

/-- The actual cursor retains every installed caller-known handle. -/
theorem native_known (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (handle : Handle) (query : Spec.Domain) (before : State n E)
    (known : KnownAt before.1.2 handle) (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    KnownAt result.2.1.2 handle :=
  CborRawRecordOriginService.native_known (service target modes replace setup codec) env codec route handle query before known result supported

/-- Every raw guarded call preserves a selected marker already raised on this execution. -/
theorem native_sticky (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E) (bad : before.2.2 = true)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    result.2.2.2 = true := by
  rw [CborRawRecordOriginService.source_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordFactsOriginMarkerNative.service_sticky target modes replace setup codec _ before.2 bad inner reached

/-- Adaptive native continuations preserve the actual marker. -/
theorem program_sticky (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : State n E) (bad : before.2.2 = true)
    (result : X × State n E)
    (supported : result ∈ support ((simulateQ (nativeImpl target modes replace setup codec route env) client).run before)) :
    result.2.2.2 = true :=
  support_keep_oracle (nativeImpl target modes replace setup codec route env) (fun current => current.2.2 = true)
    (fun query state raised => native_sticky target modes replace setup codec route env query state raised)
    client before bad result supported


/-- Adaptive native continuations preserve safe forward control. -/
theorem program_step (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : State n E) (safe : Safe before.1.2)
    (result : X × State n E)
    (supported : result ∈ support ((simulateQ (nativeImpl target modes replace setup codec route env) client).run before)) :
    Step before.1.2 result.2.1.2 := by
  apply support_keep_oracle (nativeImpl target modes replace setup codec route env)
    (fun current => Step before.1.2 current.1.2) _ client before
    (PqxdhRecordLiftProtocolHistory.step_refl before.1.2 safe) result supported
  exact fun query state progress next reached => PqxdhRecordFactsOriginControl.step_trans _ _ _ progress
    (native_step target modes replace setup codec route env query state progress.1 next reached)


/-- Adaptive native continuations preserve known handles. -/
theorem program_known (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : State n E)
    (handle : Handle) (known : KnownAt before.1.2 handle) (result : X × State n E)
    (supported : result ∈ support ((simulateQ (nativeImpl target modes replace setup codec route env) client).run before)) :
    KnownAt result.2.1.2 handle :=
  support_keep_oracle (nativeImpl target modes replace setup codec route env) (fun current => KnownAt current.1.2 handle)
    (fun query state present => native_known target modes replace setup codec route env handle query state present)
    client before known result supported

/-- Both receipts refer to the same actual final control and sticky flag. -/
def Receipt (target : Label n) (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (flag : Bool) (entry : Entry) : Prop :=
  PqxdhRecordFactsOriginMarkerEntry.EntryFact target route control flag entry ∧
    PqxdhRecordFactsOriginMetadataNative.EntryFact read route control entry

/-- Every literal guarded native reply supplies both complete same-execution receive receipts. -/
theorem native_final (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E) (safe : Safe before.1.2)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    Receipt target codec.frameRead route result.2.1.2 result.2.2.2 ⟨.inl query, result.1⟩ := by
  by_cases free : ¬PqxdhRecordLiftBudget.NativeRecord .send query
  · have projected : (result.1, CborRawRecordOriginService.project result.2) ∈ support
        ((PqxdhRecordFactsOriginMarkerNative.nativeImpl target modes replace setup codec route env query).run
          (CborRawRecordOriginService.project before)) := by
      change (result.1, CborRawRecordOriginService.project result.2) ∈ support
        ((CborRawRecordOriginService.original (service target modes replace setup codec) env codec route query).run
          (CborRawRecordOriginService.project before))
      rw [← CborRawRecordOriginService.nonrecord_project (service target modes replace setup codec) env codec route query before free,
        support_map]
      exact ⟨result, supported, rfl⟩
    exact ⟨PqxdhRecordFactsOriginMarkerEntry.native_final target modes replace setup codec route env query
        (CborRawRecordOriginService.project before) safe _ projected,
      PqxdhRecordFactsOriginMetadataNative.native_final target modes replace setup codec route env query
        (CborRawRecordOriginService.project before) _ projected⟩
  · rcases query with coin | command
    · exact False.elim (free (by simp [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]))
    · cases command <;> simp_all [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind,
        Receipt, PqxdhRecordFactsOriginMarkerEntry.EntryFact, PqxdhRecordFactsOriginMetadataNative.EntryFact,
        Entry.received, reduceCtorEq, implies_true, and_self]

/-- The two receipts persist through actual forward control, known handles and the same sticky marker. -/
theorem receipt_mono (target : Label n) (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (before after : PqxdhRecordLiftProtocol.Control n) (first last : Bool) (progress : Step before after)
    (known : ∀ handle, KnownAt before handle → KnownAt after handle)
    (sticky : first = true → last = true) (entry : Entry) (good : Receipt target read route before first entry) :
    Receipt target read route after last entry :=
  ⟨PqxdhRecordFactsOriginMarkerEntry.entry_mono target route before after first last progress known sticky entry good.1,
    PqxdhRecordFactsOriginMetadataNative.entry_mono read route before after known entry good.2⟩

/-- Secrecy sends contain no receive event regardless of admitted secret draws or missing ciphertext replies. -/
theorem secrecy_receipt (target : Label n) (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (flag : Bool)
    (query : PqxdhDeploymentInterface.Secrecy) (reply : Option RawCtxSourceSend.Encrypted) :
    Receipt target read route control flag ⟨.inr query, reply⟩ :=
  ⟨PqxdhRecordFactsOriginMarkerEntry.secrecy_entry target route control flag query reply,
    PqxdhRecordFactsOriginMetadataNative.secrecy_entry read route control query reply⟩

end BeaconcryptCore.Computational.CborRawRecordOriginReceipt

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.native_step
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.native_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.native_known
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.native_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.native_sticky
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.program_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.program_sticky
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.program_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.program_step
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.program_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.program_known
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.native_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.native_final
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.receipt_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.receipt_mono
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceipt.secrecy_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceipt.secrecy_receipt
