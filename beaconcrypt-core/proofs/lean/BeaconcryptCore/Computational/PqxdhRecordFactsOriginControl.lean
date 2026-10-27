-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat

/-! Control and handle persistence for actual native commands and adaptive continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat PqxdhRecordFactsOriginHandles
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Spec FullSpec FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every actual native query follows the source control's safety and forward transition relation. -/
theorem native_step (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    Step before.1.2 result.2.1.2 := by
  rw [nativeImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordLiftProtocolHistory.interpreted_schedule (ctxInterpreter modes replace setup codec)
    codec.frameRead route ((native env query).run before.1.1) before.1.2 safe before.2 inner reached

/-- Source control transitions compose without identifying any private cryptographic state. -/
theorem step_trans (first middle last : PqxdhRecordLiftProtocol.Control n)
    (left : Step first middle) (right : Step middle last) : Step first last :=
  ⟨right.1, PqxdhRecordLiftWorldProvenance.forward_trans _ _ _ left.2 right.2⟩

/-- Every adaptive native continuation retains source safety and forward handle provenance. -/
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

/-- A caller-known handle remains caller-known through every adaptive native continuation. -/
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

/-- The complete secrecy-ledger command preserves source control safety and forward provenance. -/
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

/-- Secrecy commands cannot turn an already caller-known handle into a hidden one. -/
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

/-- Arbitrary adaptive full commands preserve the source control relation, including experiment-generated sends. -/
theorem full_program_step (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) client).run before)) :
    Step before.2.1.2 result.2.2.1.2 := by
  apply support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds)
    (fun state => Step before.2.1.2 state.2.1.2) _ client before
    (PqxdhRecordLiftProtocolHistory.step_refl before.2.1.2 safe) result supported
  exact fun query state progress next reached => step_trans _ _ _ progress
    (full_step modes replace setup codec route env serverKid bounds query state progress.1 next reached)

/-- A caller-known handle remains caller-known through every adaptive full continuation. -/
theorem full_program_known (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E)
    (handle : Handle) (known : KnownAt before.2.1.2 handle)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) client).run before)) :
    KnownAt result.2.2.1.2 handle :=
  support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds)
    (fun state => KnownAt state.2.1.2 handle)
    (fun query state present => full_known modes replace setup codec route env serverKid bounds query state handle present)
    client before known result supported

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.native_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.step_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.step_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.native_program_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.native_program_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.native_program_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.native_program_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.full_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.full_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.full_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.full_program_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.full_program_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.full_program_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginControl.full_program_known

