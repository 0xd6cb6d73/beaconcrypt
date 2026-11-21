-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateReply
/-! Actual new dictionary entries retain the temporal distinction between a failed source encoder, an actual withheld public send and an original outer-ledger publication. No blanket publication-history premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginMacroOutcome
open PqxdhRecordLiftIdeal (KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (Spec FullSpec Entry FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {I KemSK Reader Response E Failure : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
local notation "Runtime" => CborRawRecordFlat.NativeState n E
local notation "impl" => RegistrationNativePlatformGatedRecordFreshCoupling.nativeImpl modes replace setup codec route env reserve
include ideal readback in
/-- A hidden seal newly retained by the literal full callback has its exact native send/frame witness and one of its actual three publication outcomes. Failed reservations are kept separately from codec failure. -/
theorem full (serverKeyId : U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : Runtime)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × Runtime))
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route env reserve serverKeyId bounds query).run (ledger,before)))
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal) (absent : entry ∉ (before.2.keys label).1.successfulSeals)
    (present : entry ∈ (result.2.2.2.keys label).1.successfulSeals) :
    ∃ (call : Call Spec Runtime), ∃ leading trailing sender frame,
      Path impl before leading call.before ∧ Executed impl call ∧ Path impl call.after trailing result.2.2 ∧
      PqxdhRecordLiftProtocolHistory.Safe call.before.1.2 ∧
      entry ∉ (call.before.2.keys label).1.successfulSeals ∧ entry ∈ (call.after.2.keys label).1.successfulSeals ∧
      PqxdhRecordFactsOriginHandles.OwnsLabel call.before.1.2 label sender ∧
      PqxdhRecordFactsOriginReplay.Matches frame entry ∧
      (codec.frameWrite frame=none ∨ (⟨.inl call.query,call.reply⟩ : Entry).published=none ∨
        ∃ encrypted,(⟨query,result.1⟩ : Entry).published=some (sender,encrypted) ∧ codec.frameRead encrypted.ciphertext=some frame) := by
  obtain ⟨call,leading,trailing,prior,called,suffix,safeBefore,notYet,inserted,publication,original,sourceCalled,gated,sender,frame,owned,matched,outcome⟩ :=
    RegistrationNativePlatformOriginLedgerPublication.acquired modes ideal replace setup codec route readback env reserve
      serverKeyId bounds query ledger before safe result supported label entry absent present
  refine ⟨call,leading,trailing,sender,frame,prior,called,suffix,safeBefore,notYet,inserted,owned,matched,?_⟩
  rcases outcome with failed | ⟨encrypted,published,decoded⟩
  · exact Or.inl failed
  · have gate := RegistrationNativePlatformOriginGateReply.post_subset (ctxInterpreter modes replace setup codec) codec route reserve
      call.query original.1 original.2 (call.reply,call.after) gated
    rcases gate with withheld | same
    · exact Or.inr (Or.inl withheld)
    · exact Or.inr (Or.inr ⟨encrypted,publication _ (same.trans published),decoded⟩)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginMacroOutcome

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginMacroOutcome.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginMacroOutcome.full
