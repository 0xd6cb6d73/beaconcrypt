-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters
import BeaconcryptCore.Computational.PqxdhDeploymentNative

/-! The actual source frame-writer log is retained beside arbitrary primitive state. KDF and coordinate lookup framing leaves this log unchanged; sealing retains the original writer effects, including failed publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters
open PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable PqxdhRecordLiftChainCompiler
variable {Slot PrimitiveState Result : Type}
abbrev Frames := List PqxdhDeploymentNative.Frame
abbrev Native (PrimitiveState : Type) :=
  QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState ProbComp)

/-- Pair reassociation changes no reply, primitive state or actual writer frame. -/
def swapResult (result : (Result × Frames) × PrimitiveState) : Result × (PrimitiveState × Frames) :=
  (result.1.1, (result.2, result.1.2))

/-- Execute the literal native frame logger under the original interpreter, retaining all state effects. -/
noncomputable def loggedNative (native : Native PrimitiveState) : Native (PrimitiveState × Frames) :=
  fun query state => swapResult <$>
    (simulateQ native ((PqxdhDeploymentNative.frameLog query).run state.2)).run state.1

/-- The complete adaptive program has exactly the original native frame log and full primitive poststate. -/
theorem program_logged (native : Native PrimitiveState) (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (primitive : PrimitiveState) (frames : Frames) :
    (simulateQ (loggedNative native) work).run (primitive, frames) =
      swapResult <$> (simulateQ native ((simulateQ PqxdhDeploymentNative.frameLog work).run frames)).run primitive := by
  induction work using OracleComp.inductionOn generalizing primitive frames with
  | pure result => simp only [simulateQ_pure, StateT.run_pure, map_pure, swapResult]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      change ((swapResult <$> (simulateQ native ((PqxdhDeploymentNative.frameLog query).run frames)).run primitive) >>=
        fun result => (simulateQ (loggedNative native) (next result.1)).run result.2) = _
      rw [bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply.1.1 reply.2 reply.1.2

/-- Empty initial writer log is exactly the native experiment's existing per-command logging operation. -/
theorem program_native_logged (native : Native PrimitiveState)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (primitive : PrimitiveState) :
    (simulateQ (loggedNative native) work).run (primitive, []) =
      swapResult <$> (simulateQ native (PqxdhDeploymentNative.logged work)).run primitive :=
  program_logged native work primitive []

/-- A native KDF query has no frame-writer side effect and keeps its actual response and primitive poststate. -/
theorem logged_kdf (native : Native PrimitiveState) (request : SymmetricRatchetKdfRequest)
    (primitive : PrimitiveState) (frames : Frames) :
    (loggedNative native (.inl request)).run (primitive, frames) =
      (fun reply => (reply.1, (reply.2, frames))) <$> (native (.inl request)).run primitive := by
  change swapResult <$> (simulateQ native
    ((PqxdhDeploymentNative.frameLog (.inl request)).run frames)).run primitive = _
  simp only [PqxdhDeploymentNative.frameLog, StateT.run_lift, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, Functor.map_map, swapResult]

/-- A real writer query records its exact source frame even when the writer returns failure. -/
theorem logged_writer (native : Native PrimitiveState) (frame : PqxdhDeploymentNative.Frame)
    (primitive : PrimitiveState) (frames : Frames) :
    (loggedNative native (.inr (.inr (.inr (.inr frame))))).run (primitive, frames) =
      (fun reply => (reply.1, (reply.2, frames ++ [frame]))) <$>
        (native (.inr (.inr (.inr (.inr frame))))).run primitive := by
  change swapResult <$> (simulateQ native ((fun reply => (reply, frames ++ [frame])) <$>
    RawCtxMixedOwner.NativeSpec.query (.inr (.inr (.inr (.inr frame)))))).run primitive = _
  rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl

/-- Lift only the KDF state by carrying the unrelated existing writer log unchanged. -/
noncomputable def liftKdf (kdf : Kdf PrimitiveState) : Kdf (PrimitiveState × Frames) :=
  fun request state => (fun reply => (reply.1, (reply.2, state.2))) <$> (kdf request).run state.1

/-- Coordinate lookups retain their entire source table and primitive effects while leaving the writer log alone. -/
noncomputable def liftLookup (lookup : Lookup Slot PrimitiveState) : Lookup Slot (PrimitiveState × Frames) :=
  fun coordinate state => (fun reply => (reply.1, (reply.2.1, (reply.2.2, state.2.2)))) <$>
    (lookup coordinate).run (state.1, state.2.1)

/-- Existing lookup validity and complete table persistence transport to the source state with its writer log. -/
theorem liftLookup_preserves (valid : Table Slot → Prop) (lookup : Lookup Slot PrimitiveState)
    (preserves : LookupPreserves valid lookup) : LookupPreserves valid (liftLookup lookup) := by
  intro coordinate state good available result supported
  simp only [liftLookup, StateT.run, support_map] at supported
  obtain ⟨reply, supported, rfl⟩ := supported
  exact preserves coordinate (state.1, state.2.1) good available reply supported

/-- Full lookup realization preserves the same native KDF response and state while framing the writer log. -/
theorem liftLookup_realized (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (kdf : Kdf PrimitiveState)
    (realized : LookupRealized seeds valid lookup kdf) :
    LookupRealized seeds valid (liftLookup lookup) (liftKdf kdf) := by
  intro coordinate state good available
  have framed := congrArg (fun computation =>
    (fun reply => (reply.1, (reply.2, state.2.2))) <$> computation)
      (realized coordinate (state.1, state.2.1) good available)
  simpa only [liftLookup, liftKdf, StateT.run, Functor.map_map] using framed

/-- Ordinary native functional response correctness is unchanged by the unrelated writer log. -/
theorem liftKdf_real (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (kdf : Kdf PrimitiveState) (correct : KdfReal source kdf) : KdfReal source (liftKdf kdf) := by
  intro request state result supported
  simp only [liftKdf, StateT.run, support_map] at supported
  obtain ⟨reply, supported, rfl⟩ := supported
  exact correct request state.1 reply supported

/-- The actual real table callback commutes with adding the untouched writer log, on repeats as well as first calls. -/
theorem realLookup_lift [DecidableEq Slot] (seeds : Seeds Slot) (kdf : Kdf PrimitiveState) :
    realLookup seeds (liftKdf kdf) = liftLookup (realLookup seeds kdf) := by
  funext coordinate state
  simp only [realLookup, liftLookup, liftKdf, StateT.run, bind_map_left, map_bind, map_pure]

/-- The original mixed receive inclusion supplies the precise native source adapter required by the local bridge. -/
noncomputable def receiveNative (native : Native PrimitiveState) :
    PqxdhRecordLiftNativeAdapters.ReceiveNative PrimitiveState := native ∘ₛ RawCtxMixedOwner.receiveAdapter

/-- The original mixed send inclusion retains native sealing, hash and frame-writer effects. -/
noncomputable def sendNative (native : Native PrimitiveState) :
    PqxdhRecordLiftNativeAdapters.SendNative PrimitiveState := native ∘ₛ RawCtxMixedOwner.sendAdapter

/-- Receive's mixed inclusion forwards exactly the original typed KDF request. -/
theorem receiveNative_kdf (native : Native PrimitiveState) (request : SymmetricRatchetKdfRequest) :
    receiveNative native (.inl request) = native (.inl request) := by
  simp only [receiveNative, RawCtxMixedOwner.receiveAdapter, QueryImpl.compose,
    RawCtxSourceOpen.nativeAdapter, liftM, simulateQ_spec_query, RawCtxMixedOwner.receiveLift]

/-- Send's mixed inclusion forwards the same original typed KDF request. -/
theorem sendNative_kdf (native : Native PrimitiveState) (request : SymmetricRatchetKdfRequest) :
    sendNative native (.inl request) = native (.inl request) := by
  simp only [sendNative, RawCtxMixedOwner.sendAdapter, QueryImpl.compose,
    RawCtxSourceSeal.nativeAdapter, liftM, simulateQ_spec_query, RawCtxMixedOwner.sendLift]

/-- The actual logged receive KDF is precisely the original source KDF lifted with its untouched writer log. -/
theorem receiveKdf_logged (native : Native PrimitiveState) :
    PqxdhRecordLiftNativeAdapters.receiveKdf (receiveNative (loggedNative native)) =
      liftKdf (PqxdhRecordLiftNativeAdapters.receiveKdf (receiveNative native)) := by
  funext request state
  change (PqxdhRecordLiftRealTable.fromResponse <$> receiveNative (loggedNative native) (.inl request)).run
    (state.1, state.2) = (fun reply => (reply.1, (reply.2, state.2))) <$>
      (PqxdhRecordLiftRealTable.fromResponse <$> receiveNative native (.inl request)).run state.1
  rw [receiveNative_kdf, receiveNative_kdf, StateT.run_map, logged_kdf, StateT.run_map]
  simp only [Functor.map_map]
  rfl

/-- The actual logged send KDF has the same untouched-log lifting; this claim does not apply to sealing. -/
theorem sendKdf_logged (native : Native PrimitiveState) :
    PqxdhRecordLiftNativeAdapters.sendKdf (sendNative (loggedNative native)) =
      liftKdf (PqxdhRecordLiftNativeAdapters.sendKdf (sendNative native)) := by
  funext request state
  change (PqxdhRecordLiftRealTable.fromResponse <$> sendNative (loggedNative native) (.inl request)).run
    (state.1, state.2) = (fun reply => (reply.1, (reply.2, state.2))) <$>
      (PqxdhRecordLiftRealTable.fromResponse <$> sendNative native (.inl request)).run state.1
  rw [sendNative_kdf, sendNative_kdf, StateT.run_map, logged_kdf, StateT.run_map]
  simp only [Functor.map_map]
  rfl

/-- Complete mixed receive-adapter work retains the original native per-command frame log and all primitive effects. -/
theorem receive_program_logged (native : Native PrimitiveState)
    (work : OracleComp RawCtxWholeOwner.PrimitiveSpec Result) (primitive : PrimitiveState) :
    (simulateQ (receiveNative (loggedNative native)) work).run (primitive, []) =
      swapResult <$> (simulateQ native
        (PqxdhDeploymentNative.logged (simulateQ RawCtxMixedOwner.receiveAdapter work))).run primitive := by
  change (simulateQ (loggedNative native ∘ₛ RawCtxMixedOwner.receiveAdapter) work).run (primitive, []) = _
  rw [QueryImpl.simulateQ_compose]
  exact program_native_logged native (simulateQ RawCtxMixedOwner.receiveAdapter work) primitive

/-- Complete mixed send-adapter work retains all actual writer frames, including a frame whose writer returned failure. -/
theorem send_program_logged (native : Native PrimitiveState)
    (work : OracleComp RawCtxSourceSend.PrimitiveSpec Result) (primitive : PrimitiveState) :
    (simulateQ (sendNative (loggedNative native)) work).run (primitive, []) =
      swapResult <$> (simulateQ native
        (PqxdhDeploymentNative.logged (simulateQ RawCtxMixedOwner.sendAdapter work))).run primitive := by
  change (simulateQ (loggedNative native ∘ₛ RawCtxMixedOwner.sendAdapter) work).run (primitive, []) = _
  rw [QueryImpl.simulateQ_compose]
  exact program_native_logged native (simulateQ RawCtxMixedOwner.sendAdapter work) primitive

/-- The local real receive at the actual command boundary equals the original source work with its native frame log. -/
theorem real_receive_logged [DecidableEq Slot] (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (native : Native PrimitiveState)
    (correct : KdfReal source (PqxdhRecordLiftNativeAdapters.receiveKdf (receiveNative native)))
    (entry : LabeledKernel Slot) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (table : Table Slot) (primitive : PrimitiveState) (good : RealValid source seeds table)
    (refs : KernelReferences table entry) :
    (PqxdhRecordLiftNativeAdapters.concreteResult ∘ eraseResult seeds) <$>
      ((receive seeds
        (liftLookup (realLookup seeds (PqxdhRecordLiftNativeAdapters.receiveKdf (receiveNative native))))
        (PqxdhRecordLiftNativeAdapters.receiveOpen (receiveNative (loggedNative native)))
        (RawCtxChainReceive.normalBegin entry target context)).run (table, (primitive, []))) =
      swapResult <$> (simulateQ native (PqxdhDeploymentNative.logged
        (simulateQ RawCtxMixedOwner.receiveAdapter (simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.receive ⟨eraseKernel seeds table entry⟩ target context))))).run primitive := by
  have liftedCorrect : KdfReal source
      (PqxdhRecordLiftNativeAdapters.receiveKdf (receiveNative (loggedNative native))) := by
    rw [receiveKdf_logged]
    exact liftKdf_real source _ correct
  have joined := PqxdhRecordLiftNativeAdapters.real_receive_adapter source seeds
    (receiveNative (loggedNative native)) liftedCorrect entry target context (table, (primitive, [])) good refs
  rw [receiveKdf_logged, realLookup_lift] at joined
  exact joined.trans (receive_program_logged native
    (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive ⟨eraseKernel seeds table entry⟩ target context)) primitive)

/-- The local real send at the actual command boundary retains exactly the original produced-frame log, including writer failure. -/
theorem real_send_logged [DecidableEq Slot] (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (native : Native PrimitiveState)
    (correct : KdfReal source (PqxdhRecordLiftNativeAdapters.sendKdf (sendNative native)))
    (entry : LabeledKernel Slot) (context : RawCtxSourceSend.SealContext)
    (table : Table Slot) (primitive : PrimitiveState) (good : RealValid source seeds table)
    (refs : KernelReferences table entry) :
    (PqxdhRecordLiftNativeAdapters.concreteResult ∘ eraseSendResult seeds) <$>
      ((send seeds
        (liftLookup (realLookup seeds (PqxdhRecordLiftNativeAdapters.sendKdf (sendNative native))))
        (PqxdhRecordLiftNativeAdapters.sendSeal (sendNative (loggedNative native)))
        (RawCtxChainSend.normalBegin entry context)).run (table, (primitive, []))) =
      swapResult <$> (simulateQ native (PqxdhDeploymentNative.logged
        (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter
          (RawCtxSourceSend.send ⟨eraseKernel seeds table entry⟩ context))))).run primitive := by
  have liftedCorrect : KdfReal source
      (PqxdhRecordLiftNativeAdapters.sendKdf (sendNative (loggedNative native))) := by
    rw [sendKdf_logged]
    exact liftKdf_real source _ correct
  have joined := PqxdhRecordLiftNativeAdapters.real_send_adapter source seeds
    (sendNative (loggedNative native)) liftedCorrect entry context (table, (primitive, [])) good refs
  rw [sendKdf_logged, realLookup_lift] at joined
  exact joined.trans (send_program_logged native
    (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send ⟨eraseKernel seeds table entry⟩ context)) primitive)

end BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.program_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.program_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.program_native_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.program_native_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.logged_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.logged_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.logged_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.logged_writer

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.liftLookup_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.liftLookup_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.liftLookup_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.liftLookup_realized

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.liftKdf_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.liftKdf_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.realLookup_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.realLookup_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.receiveNative_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.receiveNative_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.sendNative_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.sendNative_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.receiveKdf_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.receiveKdf_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.sendKdf_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.sendKdf_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.receive_program_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.receive_program_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.send_program_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.send_program_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.real_receive_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.real_receive_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.real_send_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters.real_send_logged
