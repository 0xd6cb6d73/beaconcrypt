-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingControl
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingReceipt
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocolHistory (Safe)
open PqxdhDeploymentInterface (Spec Entry)
open PqxdhServerAuthExperiment (Setup Codec)
open CborRawRecordFlat (NativeState)
open CborRawRecordBindingLedger (Fact)
open RegistrationNativePlatformGatedRecordFlat (fold native)
open RegistrationNativePlatformGatedRecordInterface (post)
attribute [local irreducible] ctxInterpreter
variable {n : Nat} {I KemSK Reader Response E Failure : Type} {base : OracleSpec I}

/-- Every gated native reply has its literal same-final-state accepted/published and known-key record witnesses. -/
theorem native_final (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec) (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((native (ctxInterpreter modes replace setup codec) env reserve codec route query).run before)) :
    Fact codec route result.2.1.2 result.2.2 ⟨.inl query, result.1⟩ := by
  rw [RegistrationNativePlatformGatedRecordFlat.native_split, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨original, called, gated⟩ := supported
  have prior := CborRawRecordBindingReceipt.native_final modes ideal replace setup codec route readback env query before safe original called
  have originalProgress := CborRawRecordBindingControl.native_advance modes ideal replace setup codec route env query before safe original called
  have progress := RegistrationNativePlatformGatedRecordBindingControl.fold_advance modes ideal replace setup codec route
    (post reserve query original.1) original.2 originalProgress.step.1 result gated
  have retained : Fact codec route result.2.1.2 result.2.2 ⟨.inl query, original.1⟩ :=
    ⟨PqxdhRecordFactsOriginNative.entryFacts_mono codec route _ _ _ _ progress.step progress.known progress.grows.seals _ prior.1,
      PqxdhRecordFactsBindingNative.knownEntryFacts_mono codec route _ _ _ _ progress.step progress.cache _ prior.1 prior.2⟩
  rcases query with coin | command
  · have same := RegistrationNativePlatformGatedRecordPost.pure_reply (ctxInterpreter modes replace setup codec) codec route original.1 original.2 result gated
    simpa only [same] using retained
  · cases command
    case serverSend keyId plaintext =>
      rcases RegistrationNativePlatformGatedRecordPost.send_reply (ctxInterpreter modes replace setup codec) codec route reserve
          (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) original.1 original.2 result gated with same | refused
      · simpa only [same] using retained
      · simp [CborRawRecordBindingLedger.Fact, PqxdhRecordFactsOriginNative.EntryFacts, PqxdhRecordFactsBindingNative.KnownEntryFacts,
          Entry.published, Entry.received, refused]
    case beaconSend owner plaintext =>
      rcases RegistrationNativePlatformGatedRecordPost.send_reply (ctxInterpreter modes replace setup codec) codec route reserve
          (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) original.1 original.2 result gated with same | refused
      · simpa only [same] using retained
      · simp [CborRawRecordBindingLedger.Fact, PqxdhRecordFactsOriginNative.EntryFacts, PqxdhRecordFactsBindingNative.KnownEntryFacts,
          Entry.published, Entry.received, refused]
    all_goals
      have same := RegistrationNativePlatformGatedRecordPost.pure_reply (ctxInterpreter modes replace setup codec) codec route original.1 original.2 result gated
      simpa only [same] using retained

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingReceipt.native_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingReceipt.native_final
