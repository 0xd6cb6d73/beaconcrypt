-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborTaggedCodec
import BeaconcryptCore.Computational.CborResponseRepresentation
import BeaconcryptCore.Computational.PqxdhRegistrationSchedule
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.CborTaggedBuild

/-! The actual native registration finish commutes with the total public response tag. These equalities preserve the optional reply and every shared cache, owner and deployment counter. The final theorem uses each selected owner's current public Server pin; it does not assume a single pin for all owners or restrict creation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborTaggedFinish
open PqxdhServerAuthExperiment PqxdhRegistrationSchedule PqxdhServerAuthNative
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem preparation_calls (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (sender : Std.U64) (raw : Pqxdh.Bytes) :
    CborResponseRepresentation.PreparationCalls (Prod.mk sender)
      ((callbacks setup (CborRegistrationCodec.normalize wire sender) ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ
        PqxdhBeaconPhase2Publication.preLift)
      ((callbacks setup (CborTaggedCodec.codec wire) ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ
        PqxdhBeaconPhase2Publication.preLift) raw (CborTaggedCodec.tag sender raw) := by
  constructor
  all_goals simp only [QueryImpl.compose, PqxdhBeaconPhase2Publication.preLift,
    simulateQ_spec_query, PqxdhBeaconPhase2Publication.nativeAdapter, callbacks, preparation]
  all_goals try (intros; trivial)
  rw [CborTaggedCodec.read_tagged, ← nativeCoins_map]
  rfl

theorem tail_calls (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (sender : Std.U64) :
    CborResponseRepresentation.TailCalls (Prod.mk sender)
      ((callbacks setup (CborRegistrationCodec.normalize wire sender) ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ
        PqxdhBeaconPhase2Publication.tailLift)
      ((callbacks setup (CborTaggedCodec.codec wire) ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ
        PqxdhBeaconPhase2Publication.tailLift) := by
  constructor
  all_goals simp only [QueryImpl.compose, PqxdhBeaconPhase2Publication.tailLift,
    PqxdhBeaconPhase2Publication.nativeAdapter, PqxdhBeaconPhase2Publication.nativeTailAdapter,
    simulateQ_spec_query, ← QueryImpl.simulateQ_compose]
  all_goals try simp only [PqxdhBeaconPhase2Publication.nativeTailLift, simulateQ_spec_query, callbacks,
    sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot, beaconNative,
    CborTaggedCodec.application_tagged]
  all_goals try (intros; trivial)

theorem native_owner (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (sender : Std.U64) (raw : Pqxdh.Bytes) (owner : Owner KemSK) :
    simulateQ (callbacks setup (CborTaggedCodec.codec wire))
      (PqxdhBeaconPhase2Publication.nativeOwner (CborTaggedCodec.codec wire).frameRead
        (CborTaggedCodec.tag sender raw) owner) =
    simulateQ (callbacks setup (CborRegistrationCodec.normalize wire sender))
      (PqxdhBeaconPhase2Publication.nativeOwner (CborRegistrationCodec.normalize wire sender).frameRead raw owner) := by
  exact CborResponseRepresentation.native_owner (Prod.mk sender) _ _ raw
    (CborTaggedCodec.tag sender raw) (preparation_calls setup wire sender raw)
    (tail_calls setup wire sender) wire.frameRead owner

/-- Public response tagging preserves the optional finish reply and the complete scheduler state. -/
theorem finish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (sender : Std.U64) (index : Nat) (raw : Pqxdh.Bytes) :
    PqxdhRegistrationSchedule.finish setup (CborTaggedCodec.codec wire)
      index (CborTaggedCodec.tag sender raw) =
    PqxdhRegistrationSchedule.finish setup (CborRegistrationCodec.normalize wire sender) index raw := by
  unfold PqxdhRegistrationSchedule.finish
  simp_rw [native_owner]

theorem deployment_finish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (seed : PqxdhJointIdentity.IdentitySeed) (sender : Std.U64) (index : Nat) (raw : Pqxdh.Bytes) :
    PqxdhDeploymentNative.handler setup (CborTaggedCodec.codec wire) checks route seed
      (.inr (.finish index (CborTaggedCodec.tag sender raw))) =
    PqxdhDeploymentNative.handler setup (CborRegistrationCodec.normalize wire sender) checks route seed
      (.inr (.finish index raw)) := by
  simp only [PqxdhDeploymentNative.handler, PqxdhRegistrationSchedule.handler, finish]

theorem reader_finish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    {Message Root : Type} (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (sender : Std.U64) (index : Nat) (raw : Pqxdh.Bytes) :
    PqxdhRegistrationSchedule.finish setup
      (PqxdhBoundaryRecordPrelude.withReader (CborRegistrationCodec.normalize wire sender) reader) index raw =
    PqxdhRegistrationSchedule.finish setup
      (CborRegistrationCodec.normalize (PqxdhBoundaryRecordPrelude.withReader wire reader) sender) index raw := by
  rfl

/-- The normalized filtered CBOR finish is exactly the fixed-codec finish after adding the selected owner's public pin. -/
theorem production_finish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    (CborProductionBoundary.normalizedHandler setup wire parse checks seed (.inr (.finish index raw))).run state =
    (PqxdhDeploymentNative.handler setup
      (CborTaggedCodec.codec (PqxdhBoundaryRecordPrelude.withReader
        (CborProductionBoundary.wireCodec wire parse) (CborProductionBoundary.nativeReader parse)))
      checks (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed
      (.inr (.finish index (CborTaggedCodec.tag
        (CborProductionBoundary.normalizationSender (.inr (.finish index raw)) state) raw)))).run state := by
  have native := congrArg (fun selected : Codec Reader Response =>
      (PqxdhDeploymentNative.handler setup selected checks
        (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed
        (.inr (.finish index raw))).run state)
    (CborTaggedBuild.reader_codec (CborProductionBoundary.wireCodec wire parse)
      (CborProductionBoundary.nativeReader parse) (funext (CborProductionBoundary.decode_native parse))
      (CborProductionBoundary.normalizationSender (.inr (.finish index raw)) state))
  have base := CborTaggedBuild.base_at setup wire parse checks seed (.inr (.finish index raw)) state
  have tagged := congrArg (fun work : StateT (PqxdhDeploymentNative.State KemSK) ProbComp
      (Option Pqxdh.Bytes) => work.run state)
    (deployment_finish setup
      (PqxdhBoundaryRecordPrelude.withReader (CborProductionBoundary.wireCodec wire parse)
        (CborProductionBoundary.nativeReader parse)) checks
      (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed
      (CborProductionBoundary.normalizationSender (.inr (.finish index raw)) state) index raw).symm
  exact (CborCommandFilter.admitted_run CborProductionBoundary.allowed CborProductionBoundary.reject
    (CborProductionBoundary.normalizedBaseHandler setup wire parse checks seed)
    (.inr (.finish index raw)) state rfl).trans (base.trans (native.trans tagged))

end BeaconcryptCore.Computational.CborTaggedFinish

/-- info: 'BeaconcryptCore.Computational.CborTaggedFinish.preparation_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedFinish.preparation_calls
/-- info: 'BeaconcryptCore.Computational.CborTaggedFinish.tail_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedFinish.tail_calls
/-- info: 'BeaconcryptCore.Computational.CborTaggedFinish.native_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedFinish.native_owner
/-- info: 'BeaconcryptCore.Computational.CborTaggedFinish.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedFinish.finish
/-- info: 'BeaconcryptCore.Computational.CborTaggedFinish.deployment_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedFinish.deployment_finish
/-- info: 'BeaconcryptCore.Computational.CborTaggedFinish.reader_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedFinish.reader_finish
/-- info: 'BeaconcryptCore.Computational.CborTaggedFinish.production_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedFinish.production_finish
