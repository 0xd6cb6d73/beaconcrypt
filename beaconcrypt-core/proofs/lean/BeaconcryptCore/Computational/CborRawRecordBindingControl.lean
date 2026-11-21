-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordBindingReceipt

/-! Every actual cursor-filtered callback advances safe Protocol control while retaining installed known handles, published frames, successful seal witnesses and the one shared hash cache. This structural receipt includes refused sends and arbitrary reached warm initial states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawRecordBindingControl
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftFlat (KnownAt support_keep_oracle)
open PqxdhRecordFactsOriginMonotone (Grows)
open PqxdhDeploymentInterface (Spec FullSpec Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open CborRawRecordFlat (NativeState nativeImpl fullImpl)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {base : OracleSpec ι}

structure Advance (before after : NativeState n E) : Prop where
  step : Step before.1.2 after.1.2
  known : ∀ handle, KnownAt before.1.2 handle → KnownAt after.1.2 handle
  grows : Grows before.2 after.2
  cache : before.2.base.primitive.2 ≤ after.2.base.primitive.2

private theorem advance_refl (before : NativeState n E) (safe : Safe before.1.2) : Advance before before :=
  ⟨PqxdhRecordLiftProtocolHistory.step_refl _ safe, fun _ member => member, Grows.refl _, le_rfl⟩

private theorem advance_trans (before middle after : NativeState n E)
    (left : Advance before middle) (right : Advance middle after) : Advance before after :=
  ⟨PqxdhRecordFactsOriginControl.step_trans _ _ _ left.step right.step,
    fun handle member => right.known handle (left.known handle member), Grows.trans _ _ _ left.grows right.grows,
    left.cache.trans right.cache⟩

/-- The complete actual callback preserves all source witnesses jointly, without dropping cursor refusals or shared-cache work. -/
theorem native_advance (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    Advance before result.2 := by
  refine ⟨CborRawRecordOriginService.native_step (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec)
      env codec route query before safe result supported,
    fun handle known => CborRawRecordFlat.nativeImpl_known modes replace setup codec route env handle query before known result supported, ?_, ?_⟩
  · rw [CborRawRecordFlat.nativeImpl_run, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact PqxdhRecordFactsOriginMonotone.program_grows modes ideal replace setup codec _ before.2 inner reached
  · rw [CborRawRecordFlat.nativeImpl_run, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact PqxdhRecordFactsBindingEvidence.program_cache_grows modes replace setup codec _ before.2 inner reached

/-- Every adaptive raw continuation preserves the same joint receipt from its literal reached state. -/
theorem native_program (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (work : OracleComp Spec X) (before : NativeState n E) (safe : Safe before.1.2)
    (result : X × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env) work).run before)) :
    Advance before result.2 := by
  apply support_keep_oracle (nativeImpl modes replace setup codec route env) (Advance before) _ work before
    (advance_refl before safe) result supported
  exact fun query current previous output reached => advance_trans _ _ _ previous
    (native_advance modes ideal replace setup codec route env query current previous.step.1 output reached)

/-- Full secrecy commands retain their own original coins and then the same actual cursor-filtered record receipts. -/
theorem full_advance (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Advance before.2 result.2.2 := by
  rcases before with ⟨ledger, before⟩
  rw [CborRawRecordFlat.fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_program modes ideal replace setup codec route env _ before safe inner reached

end BeaconcryptCore.Computational.CborRawRecordBindingControl
/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingControl.native_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingControl.native_advance

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingControl.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingControl.native_program

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingControl.full_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingControl.full_advance
