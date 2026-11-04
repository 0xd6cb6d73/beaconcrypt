-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess
/-! The concrete canonical source frame writer exposes the fixed public seal size to reservation, independently of the fresh commitment bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordFactsOriginSelectedSeal (hiddenResult)
variable {n : Nat}

def amount (pending : PqxdhRecordLiftProtocol.Sealing n) (body : Pqxdh.Bytes) : Nat :=
  CborSizing.frameLen pending.sequence.val pending.context.senderId.val (body.length+80)

/-- Concrete successful frame serialization has a digest-independent public length, with all codec admission failures retained. -/
theorem concrete (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length=16) (state : CtxPrivate n)
    (digest : CtxDigest) (value : RawCtxSourceSend.Encrypted)
    (encoded : (hiddenResult RegistrationNativePlatformConcreteSource.wire.frameWrite pending input body tag width digest state).1=some value) :
    value.ciphertext.length=amount pending body := by
  let frame : RawCtxReceive.DecodedFrame := ⟨pending.sequence,pending.context.senderId,(⟨body,tag,width,digest⟩ : CtxRomRecord).encode⟩
  have payload : frame.payload.length=body.length+80 := by
    simp only [frame,CtxRomRecord.encode,CtxRomRecord.toRecordCipher,Pqxdh.RecordCipher.encode,
      List.length_append,width,ctxDigest_toList_length]
  change (BeaconcryptCore.Refinement.FrameCodecContracts.nativeWrite frame).map
    (fun ciphertext => (⟨ciphertext,pending.context.targetId,pending.sequence⟩ : RawCtxSourceSend.Encrypted))=some value at encoded
  rw [Option.map_eq_some_iff] at encoded
  obtain ⟨bytes,written,rfl⟩ := encoded
  unfold BeaconcryptCore.Refinement.FrameCodecContracts.nativeWrite at written
  split at written
  · rename_i admitted
    have same := Option.some.inj written
    subst bytes
    have sized := CborTransport.render_length frame admitted.1
    simpa only [amount,payload,frame] using sized
  · cases written

variable {I KemSK X Platform Failure : Type} {base : OracleSpec I}
local instance (T : Type) : MeasurableSpace T := ⊤
local instance (T : Type) : DiscreteMeasurableSpace T := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (CtxDigest × Option ((X × CtxPrivate n) × Platform)) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × Option ((X × CtxPrivate n) × Platform)) := ⟨fun _ => trivial⟩
local notation "codec" => RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire

/-- The real canonical source frame size discharges the public gate's only size hypothesis in the original unconditional commitment-guess experiment. -/
theorem guess_bound (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length=16) (state : CtxPrivate n)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (client : Platform → OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X) (before : Platform)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (guess : (X × CtxPrivate n) × Platform → Option CtxDigest) :
    𝒟[RegistrationNativePlatformOriginReserveGuess.experiment modes setup codec replace pending input body tag width state reserve client before]
      {result | result.2.bind guess=some result.1} ≤ 2 * ((2^512 : Nat) : ENNReal)⁻¹ := by
  exact RegistrationNativePlatformOriginReserveGuess.guess_bound modes setup codec replace pending input body tag width state reserve client before
    (amount pending body) (concrete pending input body tag width state) noSeal guess

/-- Any finite receive family after the actual concrete post-seal reserve refusal is charged at the unchanged coefficient two, with complete platform poststate and no arbitrary writer law. -/
theorem guesses_bound (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length=16) (state : CtxPrivate n)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (client : Platform → OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X) (before : Platform)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (attempts : Nat) (guess : Fin attempts → (X × CtxPrivate n) × Platform → Option CtxDigest) :
    𝒟[RegistrationNativePlatformOriginReserveGuess.experiment modes setup codec replace pending input body tag width state reserve client before]
      {result | ∃ index,result.2.bind (guess index)=some result.1} ≤ 2 * attempts * ((2^512 : Nat) : ENNReal)⁻¹ := by
  exact RegistrationNativePlatformOriginReserveGuess.guesses_bound modes setup codec replace pending input body tag width state reserve client before
    (amount pending body) (concrete pending input body tag width state) noSeal attempts guess

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth.concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth.concrete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth.guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth.guess_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth.guesses_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth.guesses_bound
