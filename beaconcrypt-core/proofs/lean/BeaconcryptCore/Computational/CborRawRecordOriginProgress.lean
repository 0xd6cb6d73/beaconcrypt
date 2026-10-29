-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginService
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal

/-! Concrete raw cursor progress and temporal publication history. A refusal retains complete source state; every forwarded outcome keeps the original fallible writer's dictionary/publication relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginProgress
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (KnownAt support_keep_oracle support_run_fst)
open CborRawRecordFlat (NativeState nativeImpl fullImpl nativeImpl_known fullImpl_run)
open PqxdhRecordFactsOriginMonotone (Grows program_grows)
open PqxdhRecordFactsOriginControl (step_trans)
open PqxdhRecordFactsOriginPublicationHistory (History)
open PqxdhRecordFactsOriginPublicationTemporal (ReceivedBefore)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Spec FullSpec Entry FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every actual raw native call follows safe forward control, including pre-callback refusals. -/
theorem native_step (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    Step before.1.2 result.2.1.2 :=
  CborRawRecordOriginService.native_step (ctxInterpreter modes replace setup codec) env codec route query before safe result supported

/-- The complete raw callback preserves all prior attempted-frame and sealing witnesses. -/
theorem native_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    Grows before.2 result.2.2 := by
  change result ∈ support ((CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route query).run before) at supported
  rw [CborRawRecordOriginService.source_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact program_grows modes ideal replace setup codec _ before.2 inner reached

/-- Actual raw cursor execution retains this source invariant through the complete original continuation. -/
theorem native_program_step (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : NativeState n E) (safe : Safe before.1.2)
    (result : X × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env) client).run before)) :
    Step before.1.2 result.2.1.2 := by
  apply support_keep_oracle (nativeImpl modes replace setup codec route env)
    (fun state => Step before.1.2 state.1.2) _ client before
    (PqxdhRecordLiftProtocolHistory.step_refl before.1.2 safe) result supported
  exact fun query state progress next reached => step_trans _ _ _ progress
    (native_step modes replace setup codec route env query state progress.1 next reached)


/-- Actual raw cursor execution retains this source invariant through the complete original continuation. -/
theorem native_program_known (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : NativeState n E)
    (handle : Handle) (known : KnownAt before.1.2 handle) (result : X × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env) client).run before)) :
    KnownAt result.2.1.2 handle :=
  support_keep_oracle (nativeImpl modes replace setup codec route env)
    (fun state => KnownAt state.1.2 handle)
    (fun query state present => nativeImpl_known modes replace setup codec route env handle query state present)
    client before known result supported


/-- Actual raw cursor execution retains this source invariant through the complete original continuation. -/
theorem native_program_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (program : OracleComp PqxdhDeploymentInterface.Spec X)
    (before : CborRawRecordFlat.NativeState n E) (result : X × CborRawRecordFlat.NativeState n E)
    (supported : result ∈ support ((simulateQ (CborRawRecordFlat.nativeImpl modes replace setup codec route env) program).run before)) :
    Grows before.2 result.2.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (CborRawRecordFlat.nativeImpl modes replace setup codec route env)
    (fun state => Grows before.2 state.2)
    (fun query state previous output reached => Grows.trans before.2 state.2 output.2.2 previous
      (native_grows modes ideal replace setup codec route env query state output reached))
    program before (Grows.refl before.2) result supported


/-- Actual raw cursor execution retains this source invariant through the complete original continuation. -/
theorem full_step (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Step before.2.1.2 result.2.2.1.2 := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_program_step modes replace setup codec route env _ before.2 safe inner reached


/-- Actual raw cursor execution retains this source invariant through the complete original continuation. -/
theorem full_known (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E)
    (handle : Handle) (known : KnownAt before.2.1.2 handle)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    KnownAt result.2.2.1.2 handle := by
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_program_known modes replace setup codec route env _ before.2 handle known inner reached


/-- Actual raw cursor execution retains this source invariant through the complete original continuation. -/
theorem full_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × CborRawRecordFlat.NativeState n E)
    (result : PqxdhDeploymentInterface.FullSpec.Range query ×
      (PqxdhDeploymentSecrecy.Ledger × CborRawRecordFlat.NativeState n E))
    (supported : result ∈ support ((CborRawRecordFlat.fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Grows before.2.2 result.2.2.2 := by
  rw [CborRawRecordFlat.fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_program_grows modes ideal replace setup codec route env _ before.2 inner reached

/-- Every actual raw call keeps complete dictionary history against its literal public entry and fallible writer. -/
theorem native_history (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (transcript : List Entry) (history : History codec before.1.2 before.2 transcript)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    History codec result.2.1.2 result.2.2 (transcript ++ [⟨.inl query, result.1⟩]) := by
  rcases CborRawRecordOriginService.support_or_stutter (ctxInterpreter modes replace setup codec)
    env codec route query before result supported with forwarded | refused
  · exact PqxdhRecordFactsOriginPublicationHistory.native_history modes ideal replace setup codec route readback env query
      (CborRawRecordOriginService.project before) safe transcript history
      (result.1, CborRawRecordOriginService.project result.2) forwarded
  · have control : result.2.1.2 = before.1.2 := congrArg (fun state => state.1.2) refused
    have secret : result.2.2 = before.2 :=
      congrArg (fun state : (E × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n => state.2) refused
    rw [control, secret]
    exact PqxdhRecordFactsOriginPublicationWrapper.history_append codec before.1.2 before.2 transcript _ history

/-- Actual successful raw receives retain their literal earlier transcript; oversized send refusals contain no receive event. -/
theorem native_receivedBefore (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (transcript : List Entry) (history : History codec before.1.2 before.2 transcript)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    ReceivedBefore codec route result.2.1.2 result.2.2 transcript ⟨.inl query, result.1⟩ := by
  by_cases free : ¬PqxdhRecordLiftBudget.NativeRecord .send query
  · have forwarded : (result.1, CborRawRecordOriginService.project result.2) ∈ support
        ((CborRawRecordOriginService.original (ctxInterpreter modes replace setup codec) env codec route query).run
          (CborRawRecordOriginService.project before)) := by
      rw [← CborRawRecordOriginService.nonrecord_project _ env codec route query before free, support_map]
      exact ⟨result, supported, rfl⟩
    exact PqxdhRecordFactsOriginPublicationTemporal.native_receivedBefore modes ideal replace setup codec route readback env query
      (CborRawRecordOriginService.project before) safe transcript history
      (result.1, CborRawRecordOriginService.project result.2) forwarded
  · rcases query with coin | command
    · exact False.elim (free (by simp [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]))
    · cases command <;> simp_all [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind,
        ReceivedBefore, Entry.received, reduceCtorEq, implies_true]

end BeaconcryptCore.Computational.CborRawRecordOriginProgress

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_step
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_grows
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_program_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_program_step
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_program_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_program_known
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_program_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_program_grows
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.full_step
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.full_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.full_known
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.full_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.full_grows
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_history
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_receivedBefore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProgress.native_receivedBefore
