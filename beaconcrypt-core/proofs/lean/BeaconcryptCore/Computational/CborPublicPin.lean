-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborSplitCompiler
import BeaconcryptCore.Computational.CborLogPins

/-! Finish normalization reads only the numeric pin from the existing public creation log. The checked log-pin invariant supplies the active case, and the original inactive-finish theorem makes every other selected proof tag irrelevant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborPublicPin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open CborAdmissionCompiler (Local Good merge)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

def pin (memory : Local) (index : Nat) : Std.U64 :=
  (CborLogPins.pins memory.copies.log index).getD 0#u64

/-- Public creation records select the same meaningful finish pin as the native owner. Missing, fresh, aborted and established owners reject independently of the tag. -/
theorem finish_tag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native)
    (index : Nat) (raw : Pqxdh.Bytes) :
    (PqxdhDeploymentNative.handler setup codec checks route seed
      (.inr (.finish index (CborTaggedCodec.tag (pin memory index) raw)))).run (merge memory native) =
      (PqxdhDeploymentNative.handler setup codec checks route seed
        (.inr (.finish index (CborTaggedCodec.tag
          (CborProductionBoundary.normalizationSender (.inr (.finish index raw)) (merge memory native)) raw)))).run
        (merge memory native) := by
  rcases CborLogPins.selection setup codec memory.copies native good.nativeGood index raw with selected | inactive
  · change CborProductionBoundary.normalizationSender (.inr (.finish index raw)) (merge memory native) =
      pin memory index at selected
    rw [selected]
  · rw [CborInactiveFinish.deployment_inactive setup codec checks route seed index _
      (merge memory native) inactive,
      CborInactiveFinish.deployment_inactive setup codec checks route seed index _
        (merge memory native) inactive]

end BeaconcryptCore.Computational.CborPublicPin

/-- info: 'BeaconcryptCore.Computational.CborPublicPin.finish_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborPublicPin.finish_tag
