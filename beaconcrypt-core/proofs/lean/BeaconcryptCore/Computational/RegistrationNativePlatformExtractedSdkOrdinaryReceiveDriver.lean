-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver
import BeaconcryptCore.Computational.RegistrationNativeExtractedReceive
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open PqxdhServerAuthExperiment (Setup Codec)
variable {Platform I KemSK Reader Response : Type} {base : OracleSpec I}
abbrev Primitive := PqxdhRecordLiftWorld.Primitive
abbrev State := RegistrationNativePlatformExtractedSdkOrdinaryDriver.State
abbrev M (Platform : Type) := RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform

noncomputable def replies (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 357#usize) :
    QueryImpl AdapterRecordRequestMonad.Spec (StateT Primitive ProbComp) :=
  AdapterRecordNativeRepresentation.typed (RegistrationNativeExtractedReceive.primitives setup codec) ∘ₛ
    AdapterRecordStatefulReceive.native erased

noncomputable def primitive (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 357#usize) (effect : record_effects.RecordReceiveEffect) :
    StateT Primitive ProbComp (RustM AdapterRecordStatefulReceive.Result) :=
  simulateQ (replies setup codec erased)
    (AdapterRecordStatefulReceive.drive (RecordEffectsReceiveRank.rank effect + 2) effect).run

noncomputable def receivedPrimitive (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 357#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (sequence : U64) (payload : Slice U8) (ad : Array U8 281#usize) (sender : U64) :
    StateT Primitive ProbComp (RustM AdapterRecordStatefulReceive.Result) :=
  simulateQ (replies setup codec erased)
    (AdapterRecordStatefulReceive.receive kernel sequence payload ad sender).run

def liftPrimitive {A : Type} (work : StateT Primitive ProbComp A) : M Platform A := fun before =>
  StateT.lift ((fun result => (result.1,(result.2,before.2))) <$> work.run before.1)

noncomputable def effect (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 357#usize) (pending : record_effects.RecordReceiveEffect) :
    M Platform (RustM AdapterRecordStatefulReceive.Result) :=
  liftPrimitive (primitive setup codec erased pending)

noncomputable def received (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 357#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (sequence : U64) (payload : Slice U8) (ad : Array U8 281#usize) (sender : U64) :
    M Platform (RustM AdapterRecordStatefulReceive.Result) :=
  liftPrimitive (receivedPrimitive setup codec erased kernel sequence payload ad sender)


theorem lift_run {A : Type} (work : StateT Primitive ProbComp A)
    (before : State) (previous : Platform) :
    ((liftPrimitive work).run before).run previous =
      (fun result => ((result.1,(result.2,before.2)),previous)) <$> work.run before.1 := by
  change (do
    let result ← (fun result : A ×Primitive => (result.1,(result.2,before.2))) <$> work.run before.1
    pure (result,previous)) = _
  rw [bind_map_left,bind_pure_comp]

theorem lift_map {A B : Type} (change : A → B) (work : StateT Primitive ProbComp A) :
    liftPrimitive (Platform := Platform) (change <$> work) = change <$> liftPrimitive work := by
  funext before previous
  change ((liftPrimitive (Platform := Platform) (change <$> work)).run before).run previous =
    ((change <$> liftPrimitive work).run before).run previous
  simp only [StateT.run_map,lift_run,Functor.map_map]

theorem received_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 357#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (sequence : U64) (payload : Slice U8) (ad : Array U8 281#usize) (sender : U64) :
    (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      receivedPrimitive setup codec erased kernel sequence payload ad sender =
    simulateQ (RegistrationNativeExtractedReceive.primitives setup codec)
      (RecordEffectsReceiveProgram.receive erased kernel sequence payload ad sender) := by
  funext before
  change ((fun result => AdapterRecordReceive.decodeResult <$> result) <$>
    receivedPrimitive setup codec erased kernel sequence payload ad sender).run before =
      (simulateQ (RegistrationNativeExtractedReceive.primitives setup codec)
        (RecordEffectsReceiveProgram.receive erased kernel sequence payload ad sender)).run before
  rw [StateT.run_map]
  simpa only [receivedPrimitive,replies,AdapterRecordNativeRepresentation.receive,
    AdapterRecordStatefulReceive.interpret, QueryImpl.simulateQ_compose,simulateQ_map,StateT.run_map] using
    AdapterRecordNativeRepresentation.receive_native (RegistrationNativeExtractedReceive.primitives setup codec)
      (RegistrationNativeExtractedReceive.functional setup codec length) erased kernel sequence payload ad sender before



def receiveReply (reply : core.option.Option beaconcrypt.shared.Decrypted) : Option RawCtxWholeOwner.Decrypted :=
  _root_.Option.map (fun opened => ⟨TranscriptAuthParts.absSlice opened.plaintext,opened.key_id,opened.seq⟩) reply

theorem received_projection (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (reply : core.option.Option beaconcrypt.shared.Decrypted) :
    AdapterRecordReceive.decodeResult <$> (.ok (kernel,reply) : RustM AdapterRecordStatefulReceive.Result) =
      .ok (kernel,receiveReply reply) := by
  cases reply <;> rfl

noncomputable def model (setup : Setup base KemSK) (codec : Codec Reader Response)
    (raw : Pqxdh.Bytes) (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : U64)
    (payload : Slice U8) (ad : Array U8 281#usize) (sender : U64) :
    StateT Primitive ProbComp RecordEffectsReceiveProgram.Result :=
  let frame : RawCtxReceive.DecodedFrame := ⟨sequence,sender,RawCtxNativeFramePrelude.sliceBytes payload⟩
  simulateQ (RegistrationNativeExtractedReceive.primitives setup codec)
    (simulateQ RawCtxSourceOpen.nativeAdapter
      (if RawCtxReceive.ValidFrame sender (PqxdhRefinement.absBytes ad) frame then
        simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel sequence
            ⟨raw,frame,PqxdhRefinement.absBytes ad⟩)
      else pure (kernel,none)))

theorem received_model (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 357#usize) (raw : Pqxdh.Bytes)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : U64)
    (payload : Slice U8) (ad : Array U8 281#usize) (sender : U64) :
    (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      receivedPrimitive setup codec erased kernel sequence payload ad sender =
        .ok <$> model setup codec raw kernel sequence payload ad sender := by
  rw [received_native setup codec length erased kernel sequence payload ad sender]
  have source := RecordEffectsReceiveBridge.decoded_native_model erased kernel sender raw
    (⟨sequence,sender,RawCtxNativeFramePrelude.sliceBytes payload⟩ : RawCtxReceive.DecodedFrame)
    (PqxdhRefinement.absBytes ad) payload ad rfl rfl
  simp only [RecordEffectsReceiveProgram.decoded,ite_true] at source
  rw [source,simulateQ_map]
  rfl


theorem received_model_lift (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 357#usize) (raw : Pqxdh.Bytes)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : U64)
    (payload : Slice U8) (ad : Array U8 281#usize) (sender : U64) :
    (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      received (Platform := Platform) setup codec erased kernel sequence payload ad sender =
        .ok <$> liftPrimitive (model setup codec raw kernel sequence payload ad sender) := by
  change (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
    liftPrimitive (receivedPrimitive setup codec erased kernel sequence payload ad sender) = _
  rw [← lift_map,received_model setup codec length erased raw kernel sequence payload ad sender,lift_map]


theorem received_normal (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 357#usize) (raw : Pqxdh.Bytes)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : U64)
    (payload : Slice U8) (ad : Array U8 281#usize) (sender : U64)
    (before after : Primitive) (reply : RustM AdapterRecordStatefulReceive.Result)
    (supported : (reply,after) ∈ support
      ((receivedPrimitive setup codec erased kernel sequence payload ad sender).run before)) :
    ∃ value,reply = .ok value := by
  let project := fun result : RustM AdapterRecordStatefulReceive.Result => AdapterRecordReceive.decodeResult <$> result
  have equality := congrArg (fun work => work.run before)
    (received_model setup codec length erased raw kernel sequence payload ad sender)
  have closed : (fun result => (project result.1,result.2)) <$>
      (receivedPrimitive setup codec erased kernel sequence payload ad sender).run before =
    (fun result => (.ok result.1,result.2)) <$>
      (model setup codec raw kernel sequence payload ad sender).run before := by
    simpa only [StateT.run_map] using equality
  have possible : (project reply,after) ∈ support
      ((fun result => (.ok result.1,result.2)) <$>
        (model setup codec raw kernel sequence payload ad sender).run before) := by
    rw [← closed,support_map]
    exact ⟨(reply,after),supported,rfl⟩
  rw [support_map] at possible
  obtain ⟨reached,_supported,same⟩ := possible
  have normal := (congrArg Prod.fst same).symm
  cases reply with
  | ok value => exact ⟨value,rfl⟩
  | fail error =>
      change RustM.fail error = .ok reached.1 at normal
      cases normal
  | div =>
      change RustM.div = .ok reached.1 at normal
      cases normal

theorem begin_effect (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 357#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (sequence : U64) (payload : Slice U8) (ad : Array U8 281#usize) (sender : U64) :
    received (Platform := Platform) setup codec erased kernel sequence payload ad sender =
      (do
        let pending ← (AdapterRecordRequestMonad.liftRust
          (record_effects.begin_record_receive kernel sequence payload ad sender) : RustT (M Platform) _)
        (⟨effect setup codec erased pending⟩ : RustT (M Platform) AdapterRecordStatefulReceive.Result)).run := by
  obtain ⟨pending,admitted⟩ := BeaconcryptCore.PanicFreedom.RecordEffects.begin_record_receive_total
    kernel sequence payload ad sender
  simp only [RustT.run_bind,RustT.run_liftRust,admitted,pure_bind]
  unfold received receivedPrimitive effect primitive
  simp only [AdapterRecordStatefulReceive.receive,AdapterRecordRequestMonad.Program.run_bind,
    AdapterRecordRequestMonad.Program.run_lift,admitted,pure_bind]

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.begin_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.begin_effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_model

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_model_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_model_lift
