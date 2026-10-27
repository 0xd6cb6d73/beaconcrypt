import BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath
import BeaconcryptCore.Computational.RawCtxNativeCounterOrder

/-!
The actual fixed retained private interpreter preserves initialized directional reachability throughout the original no-install LIVE schedule. Combining this source invariant with actual chronological counter order supplies the cycle event for repeated sending inputs in that same execution. No source distribution is replaced and no collision probability is assumed.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxRetainedNativeCycles
open PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxPendingOwnerQueries
variable {AD PT CT A M P I D K Result : Type} {S B : Nat}

/-- The concrete retained native receive preserves the actual initialized directional origins through all optional outcomes. -/
theorem receive_valid (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (entry : Kernel RatchetChain)
    (valid : RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin ⟨entry⟩)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) (state : RawCtxSharedPrimitive.SharedState A)
    (result : (Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls
      (RawCtxFunctionalFamily.native source writer prior)).receive entry target context).run state)) :
    RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin ⟨result.1.1⟩ := by
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) ∈ support
      ((simulateQ ((RawCtxFunctionalFamily.native source writer prior ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive ⟨entry⟩ target context)).run state) := by
    rw [RawCtxGenericNativeCalls.receive_realized, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  exact RawCtxFunctionalPositions.receive cr (RawCtxFunctionalFamily.execute prior) sendOrigin receiveOrigin
    ⟨entry⟩ valid target context (RawCtxFunctionalFamily.opening source writer prior) state
    ((⟨result.1.1⟩, result.1.2), result.2)
    (by simpa only [RawCtxFunctionalFamily.receive_handler] using original)

/-- The concrete retained native send preserves the same initialized directional origins, including exhausted and failed-writer branches. -/
theorem send_valid (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (entry : Kernel RatchetChain)
    (valid : RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin ⟨entry⟩)
    (context : RawCtxSourceSend.SealContext) (state : RawCtxSharedPrimitive.SharedState A)
    (result : (Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls
      (RawCtxFunctionalFamily.native source writer prior)).send entry context).run state)) :
    RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin ⟨result.1.1⟩ := by
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) ∈ support
      ((simulateQ ((RawCtxFunctionalFamily.native source writer prior ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send ⟨entry⟩ context)).run state) := by
    rw [RawCtxGenericNativeCalls.send_realized, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  exact RawCtxFunctionalPositions.send cr (RawCtxFunctionalFamily.execute prior) sendOrigin receiveOrigin
    ⟨entry⟩ valid context (RawCtxFunctionalFamily.sealing source writer prior) state
    ((⟨result.1.1⟩, result.1.2), result.2)
    (by simpa only [RawCtxFunctionalFamily.send_handler] using original)

private theorem rules (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain) :
    RawCtxFamilyStateInvariant.Rules
      (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native (A := A) source writer prior))
      (fun _ _ => True)
      (fun kernel _ => RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
        sendOrigin receiveOrigin ⟨kernel⟩) where
  refl := fun _ => trivial
  trans := fun _ _ _ _ _ => trivial
  mono := fun _ _ _ _ valid => valid
  receive := fun entry target context state result supported =>
    ⟨trivial, fun valid => receive_valid source writer prior cr sendOrigin receiveOrigin
      entry valid target context state result supported⟩
  send := fun entry context state result supported =>
    ⟨trivial, fun valid => send_valid source writer prior cr sendOrigin receiveOrigin
      entry valid context state result supported⟩

/-- The original complete retained-native LIVE schedule preserves the selected owner's initialized origins; all other owners and backend effects remain unrestricted. -/
theorem schedule_reachable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxGenericFamilyLive.State (Kernel RatchetChain) M P I D K S B)
    (state : RawCtxSharedPrimitive.SharedState A)
    (result : (Result × RawCtxGenericFamilyLive.State (Kernel RatchetChain) M P I D K S B) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support (((simulateQ (RawCtxGenericFamilyLive.impl
      (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native source writer prior))
      (RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift)
      (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
      sender route decode) client).run entry).run state))
    (initial : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected entry.1 = some kernel →
      RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin ⟨kernel⟩) :
    ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected result.1.2.1 = some kernel →
      RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin ⟨kernel⟩ := by
  exact (RawCtxFamilyStateInvariant.schedule _ _ _ (rules source writer prior cr sendOrigin receiveOrigin)
    _ (fun _ _ _ _ => trivial) _ (fun _ _ _ _ => trivial)
    sender route decode client entry state result supported selected).2 initial

/-- Actual source kernel lookups preserve initialized origins in the complete native execution, using source-derived callbacks rather than an abstract path-preservation premise. -/
theorem source_reachable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : RawCtxSharedPrimitive.SharedState A)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((simulateQ (RawCtxFunctionalFamily.backend source writer prior)
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run entry)).run state))
    (initial : ∀ kernel, RawCtxProtocolReveals.selectedKernel selected entry.1 = some kernel →
      RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin kernel) :
    ∀ kernel, RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some kernel →
      RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin kernel := by
  rw [RawCtxGenericFamilyNative.actual, StateT.run_map, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  have before : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected
      (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1) = some kernel →
      RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin ⟨kernel⟩ := by
    intro kernel found
    have actual : RawCtxProtocolReveals.selectedKernel selected entry.1 = some (ConcreteRatchetKernel.mk kernel) := by
      rw [← RawCtxGenericRoleFamily.roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk (fun _ => rfl) entry.1,
        RawCtxGenericRoleFamily.native_selected, found]
      rfl
    exact initial ⟨kernel⟩ actual
  have preserved := schedule_reachable source writer prior cr sendOrigin receiveOrigin selected sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1, entry.2) state original reached before
  intro kernel found
  change RawCtxProtocolReveals.selectedKernel selected
    (RawCtxGenericRoleFamily.nativeRoles ConcreteRatchetKernel.mk original.1.2.1) = some kernel at found
  rw [RawCtxGenericRoleFamily.native_selected] at found
  obtain ⟨old, present, rfl⟩ := Option.map_eq_some_iff.mp found
  exact preserved old present

/-- A repeated sending input after an actual admitted send and its complete retained-native LIVE suffix exposes a cycle in that same private view. Path preservation and strict counter order are both derived from those source executions. -/
theorem source_cycle (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (first : ConcreteRatchetKernel)
    (valid : RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin first)
    (context : RawCtxSourceSend.SealContext) (state : RawCtxSharedPrimitive.SharedState A)
    (active : first.refined.control.send_sequence ≠ core.num.U64.MAX)
    (sent : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × RawCtxSharedPrimitive.SharedState A)
    (sentActual : sent ∈ support ((simulateQ
      ((RawCtxFunctionalFamily.native source writer prior ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send first context)).run state))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B)
    (installed : RawCtxProtocolReveals.selectedKernel selected entry.1 = some sent.1.1)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((simulateQ (RawCtxFunctionalFamily.backend source writer prior)
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run entry)).run sent.2))
    (later : ConcreteRatchetKernel)
    (retained : RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some later)
    (same : first.refined.send_chain = later.refined.send_chain) :
    RawCtxSendLineageCollision.Cycle (RawCtxRetainedFunctionalPath.table prior)
      (RawCtxSelectedQueryTrace.rootVector sendOrigin) later.refined.control.send_sequence.val := by
  have sentValid := RawCtxFunctionalPositions.send cr (RawCtxFunctionalFamily.execute prior)
    sendOrigin receiveOrigin first valid context (RawCtxFunctionalFamily.sealing source writer prior) state sent
    (by simpa only [RawCtxFunctionalFamily.send_handler] using sentActual)
  have initial : ∀ kernel, RawCtxProtocolReveals.selectedKernel selected entry.1 = some kernel →
      RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin kernel := by
    intro kernel found
    cases Option.some.inj (installed.symm.trans found)
    exact sentValid
  have finalValid := source_reachable source writer prior cr sendOrigin receiveOrigin selected
    sender route decode client entry sent.2 result supported initial later retained
  have ordered := RawCtxNativeCounterOrder.after_send_strict (RawCtxFunctionalFamily.backend source writer prior)
    first context state active sent sentActual selected sender route decode client entry installed result supported later retained
  exact RawCtxSendLineageCollision.same_direction_cycle (RawCtxRetainedFunctionalPath.table prior) _ first later
    (RawCtxRetainedFunctionalPath.reachable_path prior cr sendOrigin receiveOrigin first valid)
    (RawCtxRetainedFunctionalPath.reachable_path prior cr sendOrigin receiveOrigin later finalValid) ordered same

/-- Equal reached sending inputs at two source owners expose a meeting in their actual retained paths, including equal roots explicitly. Both path premises are propagated through the same complete source execution. -/
theorem source_meeting (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (leftSend leftReceive rightSend rightReceive : RatchetChain)
    (leftOwner rightOwner : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : RawCtxSharedPrimitive.SharedState A)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((simulateQ (RawCtxFunctionalFamily.backend source writer prior)
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run entry)).run state))
    (leftInitial : ∀ kernel, RawCtxProtocolReveals.selectedKernel leftOwner entry.1 = some kernel →
      RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) leftSend leftReceive kernel)
    (rightInitial : ∀ kernel, RawCtxProtocolReveals.selectedKernel rightOwner entry.1 = some kernel →
      RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) rightSend rightReceive kernel)
    (first second : ConcreteRatchetKernel)
    (leftFound : RawCtxProtocolReveals.selectedKernel leftOwner result.1.2.1 = some first)
    (rightFound : RawCtxProtocolReveals.selectedKernel rightOwner result.1.2.1 = some second)
    (same : first.refined.send_chain = second.refined.send_chain) :
    ∃ left right, left.length = first.refined.control.send_sequence.val ∧
      right.length = second.refined.control.send_sequence.val ∧
      RawCtxSendPathMeeting.Meeting (RawCtxRetainedFunctionalPath.table prior)
        (RawCtxSelectedQueryTrace.rootVector leftSend) (RawCtxSelectedQueryTrace.rootVector rightSend) left right := by
  exact RawCtxSendPathMeeting.paths_meeting (RawCtxRetainedFunctionalPath.table prior) _ _ first second
    (RawCtxRetainedFunctionalPath.reachable_path prior cr leftSend leftReceive first
      (source_reachable source writer prior cr leftSend leftReceive leftOwner
        sender route decode client entry state result supported leftInitial first leftFound))
    (RawCtxRetainedFunctionalPath.reachable_path prior cr rightSend rightReceive second
      (source_reachable source writer prior cr rightSend rightReceive rightOwner
        sender route decode client entry state result supported rightInitial second rightFound)) same

end BeaconcryptCore.Computational.RawCtxRetainedNativeCycles

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.receive_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.receive_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.send_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.send_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.schedule_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.schedule_reachable

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.source_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.source_reachable

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.source_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.source_cycle

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.source_meeting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedNativeCycles.source_meeting
