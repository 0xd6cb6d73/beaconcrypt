-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess
/-! Literal hidden send source after its public admission cut: the advanced kernel is fixed before sealing, and the actual optional ciphertext is used only as the returned value. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendSource
open PqxdhRecordLiftInterface (Slot)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label LabeledKernel Owner)
open PqxdhRecordLiftChainState (advance)
variable {n : Nat}

/-- The actual source advances the kernel before the single seal request, then publishes only its fixed role tag. Every ciphertext option, including failure, leaves that same advanced control. -/
theorem owner (tag : PqxdhDeploymentInterface.FrameTag) (sender : U64) (decode : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (owner : Owner n) (slot : Slot n) (kernel : LabeledKernel n)
    (hidden : owner.kernel=.hidden slot kernel) (nonempty : plaintext.isEmpty=false)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (requested : RawCtxChainSend.normalBegin kernel ⟨plaintext,owner.expectedSender,sender,owner.associatedData⟩=.requested pending) :
    PqxdhRecordLiftProtocol.ownerRun tag sender decode (.inl plaintext) owner =
      (do
        let _ ← ((ServiceSpec n).query (.lookup pending.request) : OracleComp (ServiceSpec n) _)
        let ready := RawCtxChainSend.ready pending (advance pending.request 1,pending.request)
        let reply ← ((ServiceSpec n).query (.sealing ready) : OracleComp (ServiceSpec n) _)
        let _ ← ((ServiceSpec n).query (.publish tag) : OracleComp (ServiceSpec n) _)
        pure (reply,{owner with kernel:=.hidden slot ready.advanced})) := by
  simp only [PqxdhRecordLiftProtocol.ownerRun,PqxdhRecordLiftProtocol.ownerStep,PqxdhRecordLiftProtocol.ownerSend,
    nonempty,Bool.false_eq_true,ite_false,hidden,PqxdhRecordLiftProtocol.kernelSend,
    PqxdhRecordLiftOpaqueDrivers.admittedSend,requested,PqxdhRecordLiftOpaqueDrivers.sendProgram,
    simulateQ_bind,simulateQ_spec_query,simulateQ_pure,PqxdhRecordLiftProtocol.localLift,
    bind_assoc,pure_bind]
  rfl

/-- At a selected seal the real owner helper, fixed publication tag and actual charged reserve have exactly the stopped source continuation used by the digest-guess bound. All original owner/P effects survive on the refused branch. -/
theorem owner_stopped {Platform Failure X : Type}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (future : Owner n → Platform → OracleComp (ServiceSpec n) X) (before : Platform)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : U64) (decode : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (owner : Owner n) (slot : Slot n) (kernel : LabeledKernel n)
    (hidden : owner.kernel=.hidden slot kernel) (nonempty : plaintext.isEmpty=false)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (requested : RawCtxChainSend.normalBegin kernel ⟨plaintext,owner.expectedSender,sender,owner.associatedData⟩=.requested pending) :
    (do
      let sent ← PqxdhRecordLiftProtocol.ownerRun tag sender decode (.inl plaintext) owner
      let gated ← simulateQ RegistrationNativePlatformOriginGateSource.coins
        ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) sent.1).run before)
      if gated.1.isNone then (fun value => some (value,gated.2)) <$> future sent.2 gated.2 else pure none) =
    (do
      let _ ← ((ServiceSpec n).query (.lookup pending.request) : OracleComp (ServiceSpec n) _)
      let ready := RawCtxChainSend.ready pending (advance pending.request 1,pending.request)
      let reply ← ((ServiceSpec n).query (.sealing ready) : OracleComp (ServiceSpec n) _)
      RegistrationNativePlatformOriginReserveSourceGuess.tail reserve
        (fun platform => future {owner with kernel:=.hidden slot ready.advanced} platform) before tag reply) := by
  rw [RegistrationNativePlatformOriginSendSource.owner tag sender decode plaintext owner slot kernel hidden nonempty pending requested]
  simp only [bind_assoc,pure_bind,RegistrationNativePlatformOriginReserveSourceGuess.tail]

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendSource.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendSource.owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendSource.owner_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendSource.owner_stopped
