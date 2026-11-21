-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback
/-! The same acquired native send with absent public reply has that exact absent output at its actual reserve gate, retaining the reached platform, cursor, control and private states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginRefusedReply
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (ServiceSpec)
open RegistrationNativePlatformOriginSendAcquisition (Receipt SendResult)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
variable {n : Nat} {Platform Failure : Type}

/-- A missing original native send reply is the same literal missing gate output, with its actual reached platform and private states. -/
theorem gate
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (beforeP : Platform) (tag : PqxdhDeploymentInterface.FrameTag)
    (after : Option RawCtxSourceSend.Encrypted → Platform → SendResult n Platform)
    (advancedShell : CborRecordWorldClient.Shell) (advancedControl : PqxdhRecordLiftProtocol.Control n)
    (form : ∀output reachedP,after output reachedP=(((output,reachedP),advancedShell),advancedControl))
    (reply : Option RawCtxSourceSend.Encrypted) (before : CtxPrivate n) (result : SendResult n Platform × CtxPrivate n)
    (supported : result∈support ((simulateQ service (continued reserve (fun output state=>pure (after output state)) beforeP tag reply)).run before))
    (refused : result.1.1.1.1=none) :
    ∃ reached : (Option RawCtxSourceSend.Encrypted × Platform) × CtxPrivate n,
      reached∈support ((simulateQ service
        (RegistrationNativePlatformOriginResumedCallback.prefixWork reserve beforeP tag reply)).run before) ∧
      reached.1.1=none ∧ result=((((none,reached.1.2),advancedShell),advancedControl),reached.2) := by
  have ast : continued (n := n) reserve (fun output state=>pure (after output state)) beforeP tag reply=
      (RegistrationNativePlatformOriginResumedCallback.prefixWork reserve beforeP tag reply >>= fun gated=>pure (after gated.1 gated.2)) := by
    simp only [continued,RegistrationNativePlatformOriginResumedCallback.prefixWork,bind_assoc]
  rw [ast,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨reached,called,returned⟩ := supported
  simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at returned
  have outputEq := congrArg (fun current=>current.1.1.1.1) returned
  rw [form] at outputEq
  have missing : reached.1.1=none := outputEq.symm.trans refused
  refine ⟨reached,called,missing,?_⟩
  rw [form,missing] at returned
  exact returned

/-- The same acquired hidden send receipt exposes the actual public refusal prefix, rather than replacing it by a codec failure. -/
theorem acquired
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (beforeP : Platform)
    (work : OracleComp (ServiceSpec n) (SendResult n Platform)) (before : CtxPrivate n)
    (result : SendResult n Platform × CtxPrivate n) (label : PqxdhRecordLiftWorldCompiler.Label n) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (receipt : Receipt service reserve beforeP work before result label entry)
    (advancedShell : CborRecordWorldClient.Shell) (advancedControl : PqxdhRecordLiftProtocol.Control n)
    (form : ∀output reachedP,receipt.after output reachedP=(((output,reachedP),advancedShell),advancedControl))
    (refused : result.1.1.1.1=none) :
    ∃ reached : (Option RawCtxSourceSend.Encrypted × Platform) × CtxPrivate n,
      reached∈support ((simulateQ service
        (RegistrationNativePlatformOriginResumedCallback.prefixWork reserve beforeP receipt.tag receipt.sealed.1)).run receipt.sealed.2) ∧
      reached.1.1=none ∧ result=((((none,reached.1.2),advancedShell),advancedControl),reached.2) :=
  gate service reserve beforeP receipt.tag receipt.after advancedShell advancedControl form receipt.sealed.1 receipt.sealed.2 result receipt.tailCalled refused
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginRefusedReply

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginRefusedReply.gate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginRefusedReply.gate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginRefusedReply.acquired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginRefusedReply.acquired
