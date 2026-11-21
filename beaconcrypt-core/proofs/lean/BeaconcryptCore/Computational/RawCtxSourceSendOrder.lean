import BeaconcryptCore.Computational.RawCtxSendLineageCollision

/-!
The original no-install LIVE family preserves a sending counter's chronological lower bound. The local facts come from actual source admission, receive publication and send advancement, including failed sealing/writing. This scope deliberately excludes later registration or replacement of a kernel at the same public route: the global caller must retain its cryptographic installation origin and classify other-origin meetings separately.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceSendOrder
open PqxdhJointKdfGame PqxdhSecretInputKdf RawCtxSourceFamilyPath
variable {A M P I D K Result : Type} {S B : Nat}

/-- Every actual source send preserves the old counter or advances it exactly once; an optional writer failure does not undo advancement. -/
theorem send_counter {Context Output State ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (RawCtxSourceSend.SendSpec Context Output) (StateT State (OracleComp base)))
    (entry : ConcreteRatchetKernel) (context : Context) (state : State)
    (result : (ConcreteRatchetKernel × Option Output) × State)
    (supported : result ∈ support ((simulateQ impl (RawCtxSourceSend.send entry context)).run state)) :
    entry.refined.control.send_sequence.val ≤ result.1.1.refined.control.send_sequence.val := by
  by_cases exhausted : entry.refined.control.send_sequence = core.num.U64.MAX
  · rw [RawCtxSourceSend.send_exhausted entry context exhausted] at supported
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact le_refl _
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, advanced, _⟩ :=
      RawCtxSourceSend.send_nonexhausted_support impl entry context state exhausted result supported
    omega

/-- The literal refined native receive callback retains the original sending counter under every raw outcome. -/
theorem receive_call (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (entry : Kernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : State A)
    (result : (Kernel × core.option.Option RawCtxWholeOwner.Decrypted) × State A)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls
      (RawCtxSourceSendPath.native source writer stage)).receive entry target context).run state)) :
    result.1.1.control.send_sequence = entry.control.send_sequence := by
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) ∈ support
      ((simulateQ (RawCtxSourcePathCalls.receiveImpl source writer stage)
        (RawCtxOwnerOracle.receive ⟨entry⟩ target context)).run state) := by
    rw [RawCtxSourcePathCalls.receiveImpl, RawCtxGenericNativeCalls.receive_realized, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  exact (RawCtxReceiveSendFields.receive_fields _ state ⟨entry⟩ target context _ original).2

/-- The literal refined native send callback is monotone even if the native optional ciphertext is absent. -/
theorem send_call (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (entry : Kernel) (context : RawCtxSourceSend.SealContext) (state : State A)
    (result : (Kernel × Option RawCtxSourceSend.Encrypted) × State A)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls
      (RawCtxSourceSendPath.native source writer stage)).send entry context).run state)) :
    entry.control.send_sequence.val ≤ result.1.1.control.send_sequence.val := by
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) ∈ support
      ((simulateQ (RawCtxSourceSendPath.sendImpl source writer stage)
        (RawCtxSourceSend.send ⟨entry⟩ context)).run state) := by
    rw [RawCtxSourceSendPath.sendImpl, RawCtxGenericNativeCalls.send_realized, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  exact send_counter _ ⟨entry⟩ context state _ original

private theorem rules (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage floor : Nat) :
    RawCtxFamilyStateInvariant.Rules
      (RawCtxGenericNativeCalls.calls (RawCtxSourceSendPath.native (A := A) source writer stage))
      (fun _ _ => True) (fun kernel _ => floor ≤ kernel.control.send_sequence.val) where
  refl := fun _ => trivial
  trans := fun _ _ _ _ _ => trivial
  mono := fun _ _ _ _ valid => valid
  receive := fun entry target context state result supported =>
    ⟨trivial, fun valid => by simpa only [receive_call source writer stage entry target context state result supported] using valid⟩
  send := fun entry context state result supported =>
    ⟨trivial, fun valid => valid.trans (send_call source writer stage entry context state result supported)⟩

/-- The complete original generic LIVE schedule retains a selected sender's chronological lower bound, with every callback law discharged from native execution. -/
theorem schedule (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage floor : Nat)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (entry : LiveState M P I D K S B)
    (state : State A) (result : (Result × LiveState M P I D K S B) × State A)
    (supported : result ∈ support (((simulateQ (RawCtxSourceFamilyPath.impl source writer stage sender route decode) client).run entry).run state))
    (initial : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected entry.1 = some kernel →
      floor ≤ kernel.control.send_sequence.val) :
    ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected result.1.2.1 = some kernel →
      floor ≤ kernel.control.send_sequence.val := by
  exact (RawCtxFamilyStateInvariant.schedule _ _ _ (rules source writer stage floor)
    _ (fun _ _ _ _ => trivial) _ (fun _ _ _ _ => trivial) sender route decode client entry state result supported selected).2 initial

/-- The literal native no-install family retains every established selected send-counter lower bound under its actual complete shared-state execution. -/
theorem source_lower (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage floor : Nat)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : State A)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B
      sender route decode client entry state.1 state.2))
    (initial : ∀ kernel, RawCtxProtocolReveals.selectedKernel selected entry.1 = some kernel →
      floor ≤ kernel.refined.control.send_sequence.val) :
    ∀ kernel, RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some kernel →
      floor ≤ kernel.refined.control.send_sequence.val := by
  rw [RawCtxPendingSelectiveFamily.source_program, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  have reached' : original ∈ support (((simulateQ (RawCtxSourceFamilyPath.impl source writer stage sender route decode) client).run
      (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1, entry.2)).run state) := by
    simpa only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingSelectiveFamily.program,
      RawCtxPendingFamilyNative.program_interpretation, RawCtxSourceFamilyPath.impl, RawCtxSourceSendPath.native] using reached
  have before : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected
      (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1) = some kernel →
      floor ≤ kernel.control.send_sequence.val := by
    intro kernel found
    have actual : RawCtxProtocolReveals.selectedKernel selected entry.1 = some (ConcreteRatchetKernel.mk kernel) := by
      rw [← RawCtxGenericRoleFamily.roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk (fun _ => rfl) entry.1,
        RawCtxGenericRoleFamily.native_selected, found]
      rfl
    exact initial ⟨kernel⟩ actual
  have preserved := schedule source writer stage floor selected sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1, entry.2) state original reached' before
  intro kernel found
  change RawCtxProtocolReveals.selectedKernel selected
    (RawCtxGenericRoleFamily.nativeRoles ConcreteRatchetKernel.mk original.1.2.1) = some kernel at found
  rw [RawCtxGenericRoleFamily.native_selected] at found
  obtain ⟨old, present, rfl⟩ := Option.map_eq_some_iff.mp found
  exact preserved old present

/-- Two reached kernels of the same installed owner are ordered by the actual original LIVE schedule, not by an assumed counter invariant. -/
theorem source_mono (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : State A)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B
      sender route decode client entry state.1 state.2))
    (before after : ConcreteRatchetKernel)
    (installed : RawCtxProtocolReveals.selectedKernel selected entry.1 = some before)
    (retained : RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some after) :
    before.refined.control.send_sequence.val ≤ after.refined.control.send_sequence.val := by
  apply source_lower source writer stage before.refined.control.send_sequence.val selected sender route decode
    client entry state result supported _ after retained
  intro kernel found
  cases Option.some.inj (installed.symm.trans found)
  exact le_refl _

/-- An actual admitted send followed by arbitrary original no-install LIVE work can return to its old send input only through a real directional cache cycle. Strict chronological order, path provenance and the final complete cache are all derived from those same executions. -/
theorem source_cycle (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (first : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (initialState : State A) (initialPath : RawCtxSourceSendPath.Path root first initialState.2.1)
    (active : first.refined.control.send_sequence ≠ core.num.U64.MAX)
    (sent : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × State A)
    (sentActual : sent ∈ support ((simulateQ (RawCtxSourceSendPath.sendImpl source writer stage)
      (RawCtxSourceSend.send first context)).run initialState))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B)
    (installed : RawCtxProtocolReveals.selectedKernel selected entry.1 = some sent.1.1)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B
      sender route decode client entry sent.2.1 sent.2.2))
    (later : ConcreteRatchetKernel)
    (retained : RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some later)
    (same : first.refined.send_chain = later.refined.send_chain) :
    RawCtxSendLineageCollision.Cycle result.2.2.1 root later.refined.control.send_sequence.val := by
  have sentPath := RawCtxSourceSendPath.send_path source writer stage root first context initialState initialPath sent sentActual
  have initial : NativeGood root selected entry.1 sent.2 := by
    intro kernel found
    cases Option.some.inj (installed.symm.trans found)
    exact sentPath.2
  have finalPath := RawCtxSourceFamilyPath.source source writer stage root selected sender route decode
    client entry sent.2 initial result supported
  have monotone := source_mono source writer stage selected sender route decode client entry sent.2 result supported
    sent.1.1 later installed retained
  obtain ⟨_, _, _, _, _, _, _, _, _, _, advanced, _⟩ :=
    RawCtxSourceSend.send_nonexhausted_support (RawCtxSourceSendPath.sendImpl source writer stage)
      first context initialState active sent sentActual
  exact RawCtxSendLineageCollision.same_direction_cycle result.2.2.1 root first later
    (RawCtxSourceSendPath.path_extends root first sent.2.2.1 result.2.2.1
      (RawCtxSourceSendPath.path_extends root first initialState.2.1 sent.2.2.1 initialPath sentPath.1) finalPath.1)
    (finalPath.2 later retained) (by omega) same

end BeaconcryptCore.Computational.RawCtxSourceSendOrder

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendOrder.send_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendOrder.send_counter

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendOrder.receive_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendOrder.receive_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendOrder.send_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendOrder.send_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendOrder.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendOrder.schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendOrder.source_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendOrder.source_lower

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendOrder.source_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendOrder.source_mono

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendOrder.source_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendOrder.source_cycle
