-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope
import BeaconcryptCore.Computational.TransportSizingBridge
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission
/-! The literal SDK checked sequence increment and protected-frame length test coincide with the current inclusive native send gate. No successful-send or primitive/controller premise is supplied. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate
open BeaconcryptCore.Computational

theorem increment (sequence : U64) :
    ∃reply,core.num.U64.checked_add sequence 1#u64=.ok reply ∧
      match reply with
      | .None => ¬sequence.val<UScalar.max .U64
      | .Some next => next.val=sequence.val+1 ∧sequence.val<UScalar.max .U64 := by
  have overflow := UScalar.overflowing_add_eq sequence 1#u64
  by_cases bounded : sequence.val+1≤UScalar.max .U64
  · have incremented := (ite_eq_right (Nat.not_lt.mpr bounded) ▸ overflow)
    refine ⟨.Some (UScalar.overflowing_add sequence 1#u64).1,?_,?_,by omega⟩
    · simp [core.num.U64.checked_add,core.num.U64.overflowing_add,
        rust_primitives.arithmetic.overflowing_add_u64]
      dsimp! only
      simp [incremented.2]
    · simpa using incremented.1
  · have incremented := (ite_eq_left (Nat.lt_of_not_ge bounded) ▸ overflow)
    refine ⟨.None,?_,by omega⟩
    simp [core.num.U64.checked_add,core.num.U64.overflowing_add,
      rust_primitives.arithmetic.overflowing_add_u64]
    dsimp! only
    simp [incremented.2]

theorem frame_length (bytes : Slice U8) (sequence sender : U64) :
    ∃reply,beaconcrypt_public_ordinary.wire.frame_len bytes.len sequence sender=.ok reply ∧
      Transport.absLength reply=Transport.messageCap
        (CborSizing.frameLen sequence.val sender.val (bytes.val.length+80)) := by
  obtain ⟨reply,run,size⟩ := TransportSizingBridge.protected_frame_len_exact bytes.len sequence sender
  refine ⟨reply,run,?_⟩
  simpa only [Slice.len_val,Slice.length] using size

private theorem empty (bytes : Slice U8) :
    core.slice.Slice.is_empty bytes=.ok bytes.val.isEmpty := by
  change RustM.ok (decide (bytes.len=0#usize))=_
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.isEmpty_iff_length_eq_zero]
  constructor
  · intro zero
    have length := congrArg UScalar.val zero
    simpa [Slice.len_val,Slice.length] using length
  · intro zero
    apply UScalar.eq_of_val_eq
    simpa [Slice.len_val,Slice.length] using zero

private theorem cap_presence (reply : core.option.Option Usize) (total : Nat)
    (represented : Transport.absLength reply=Transport.messageCap total) :
    reply.isSome=decide (total≤CborSizing.maxMessageSize) := by
  change reply.isSome=decide (total≤33554432)
  by_cases fits : total≤33554432
  · cases reply with
    | none => simp [Transport.absLength,Transport.messageCap,fits] at represented
    | some value => simp only [Option.isSome_some, fits,decide_true]
  · cases reply with
    | none => simp only [Option.isSome_none,fits,decide_false]
    | some value => simp [Transport.absLength,Transport.messageCap,fits] at represented

theorem prepare (bytes : Slice U8) (target sender : U64) (ad : Array U8 151#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    AdapterPublicOrdinaryEnvelope.prepareSend bytes target sender ad kernel=.ok
      (if bytes.val.isEmpty then .None else
       if kernel.refined.control.send_sequence.val<UScalar.max .U64 then
         if CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val sender.val then
           .Some (⟨bytes,.None,ad,target,sender,.Frame⟩ : record_effects.SealFrameContext)
         else .None
       else .None) := by
  obtain ⟨next,incrementRun,incremented⟩ := increment kernel.refined.control.send_sequence
  cases next with
  | none =>
      simp only [UScalar.max_UScalarTy_U64_eq] at incremented
      simp [AdapterPublicOrdinaryEnvelope.prepareSend,empty,incrementRun,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,incremented]
  | some next =>
      rcases incremented with ⟨nextValue,within⟩
      simp only [UScalar.max_UScalarTy_U64_eq] at within
      obtain ⟨sized,lengthRun,represented⟩ := frame_length bytes next sender
      have admitted := cap_presence sized _ represented
      have fits : sized.isSome=CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val sender.val := by
        simpa only [CborRecordWorldClient.nextFits,nextValue] using admitted
      cases sized with
      | none =>
          have refused : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val sender.val=false := fits.symm
          simp [AdapterPublicOrdinaryEnvelope.prepareSend,empty,incrementRun,
            show core.slice.Slice.len bytes=.ok bytes.len from rfl,lengthRun,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,within,refused]
      | some size =>
          have accepted : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val sender.val=true := fits.symm
          simp [AdapterPublicOrdinaryEnvelope.prepareSend,empty,incrementRun,
            show core.slice.Slice.len bytes=.ok bytes.len from rfl,lengthRun,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,within,accepted,
            record_effects.SealFrameContext.new]
          split_ifs <;> rfl

end BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate.increment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate.increment
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate.frame_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate.frame_length
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate.prepare
