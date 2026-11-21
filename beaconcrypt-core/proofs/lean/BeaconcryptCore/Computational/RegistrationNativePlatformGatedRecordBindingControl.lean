-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordBindingLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftFlat (KnownAt support_keep_oracle)
open PqxdhRecordFactsOriginMonotone (Grows)
open PqxdhDeploymentInterface (Spec FullSpec Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open CborRawRecordFlat (NativeState)
open CborRawRecordBindingControl (Advance)
open RegistrationNativePlatformGatedRecordFlat (fold native full)
variable {n : Nat} {I KemSK Reader Response E X Failure : Type} {base : OracleSpec I}

/-- Every actual open World continuation keeps all source witnesses and the reached shared cache, including public post-send work. -/
theorem fold_advance (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) X) (before : NativeState n E) (safe : Safe before.1.2)
    (result : X × NativeState n E)
    (supported : result ∈ support ((fold (ctxInterpreter modes replace setup codec) codec route work).run before)) :
    Advance before result.2 := by
  unfold fold at supported
  change result ∈ support (RegistrationNativePlatformGatedRecordFlat.join <$>
    CborRawRecordOriginFlatten.interpret (ctxInterpreter modes replace setup codec) codec route
      (work.run before.1.1.1) before.1.1.2 before.1.2 before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  refine ⟨PqxdhRecordLiftProtocolHistory.interpreted_schedule (ctxInterpreter modes replace setup codec)
      codec.frameRead route _ before.1.2 safe before.2 inner reached, ?_, ?_, ?_⟩
  · intro handle known
    exact support_keep_oracle (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      (fun control => KnownAt control handle) (PqxdhRecordLiftFlat.handler_known codec.frameRead route handle)
      _ before.1.2 known inner.1 (PqxdhRecordLiftFlat.support_run_fst _ _ _ inner reached)
  · exact PqxdhRecordFactsOriginMonotone.program_grows modes ideal replace setup codec _ before.2 inner reached
  · exact PqxdhRecordFactsBindingEvidence.program_cache_grows modes replace setup codec _ before.2 inner reached

/-- The gated native callback retains its original safe control and every prior record witness. -/
theorem native_advance (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((native (ctxInterpreter modes replace setup codec) env reserve codec route query).run before)) :
    Advance before result.2 :=
  fold_advance modes ideal replace setup codec route _ before safe result supported

/-- Every adaptive gated continuation preserves the same joint witness receipt from its literal reached state. -/
theorem native_program (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (work : OracleComp Spec X) (before : NativeState n E) (safe : Safe before.1.2)
    (result : X × NativeState n E)
    (supported : result ∈ support ((simulateQ (native (ctxInterpreter modes replace setup codec) env reserve codec route) work).run before)) :
    Advance before result.2 := by
  apply support_keep_oracle (native (ctxInterpreter modes replace setup codec) env reserve codec route)
    (Advance before) _ work before
    (⟨PqxdhRecordLiftProtocolHistory.step_refl _ safe, fun _ member => member, Grows.refl _, le_rfl⟩) result supported
  intro query current previous output reached
  have next := native_advance modes ideal replace setup codec route env reserve query current previous.step.1 output reached
  exact ⟨PqxdhRecordFactsOriginControl.step_trans _ _ _ previous.step next.step,
    fun handle member => next.known handle (previous.known handle member),
    Grows.trans _ _ _ previous.grows next.grows, previous.cache.trans next.cache⟩

/-- Full test/fresh commands keep their original coins and actual post-send failures below their ledger update. -/
theorem full_advance (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : Safe before.2.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((full (ctxInterpreter modes replace setup codec) env reserve setup.source.crypto codec route serverKid bounds query).run before)) :
    Advance before.2 result.2.2 := by
  rw [RegistrationNativePlatformGatedRecordSemantics.full_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_program modes ideal replace setup codec route env reserve _ before.2 safe inner reached

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl.fold_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl.fold_advance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl.native_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl.native_advance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl.full_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl.full_advance
