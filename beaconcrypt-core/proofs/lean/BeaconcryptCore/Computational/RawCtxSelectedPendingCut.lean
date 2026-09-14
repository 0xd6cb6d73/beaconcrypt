import BeaconcryptCore.Computational.RawCtxSelectedParentSource

/-!
The selected predecessor entry is constructed from the original pending source KDF request and its full76 reply. Every old chain is retained as known before this new draw; the stopped send or receive continuation uses only its material projection and a hidden next-chain marker. The exact original callback is included before all remaining receive skips/opening or the advanced send/seal tail. Full state, optional failure, prior lookup values and equal-byte aliases are preserved.

These equations describe the same source driver under the explicitly retained lookup. Its fixed-source specialization is supplied by the preceding response laws. They do not prove that this pending request is reached at a fresh table miss, that its response is uniform, or that prior/live ancestor knowledge is absent. Neither a target-dependent rebase nor byte distinctness is used to construct the stop. Full76 sampling and local lookup/KDF/conversion work are separate from these literal program equations; no work bound is inferred from evaluated distribution equality. All pending fields are private protocol context, not an adversary API. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedPendingCut
open RawCtxSelectedChain RawCtxChainInterpretation RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

def receivePending {Value Context : Type}
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain Value Context) :
    RawCtxChainReceive.Kdf Slot Slot Value Context :=
  { entry := mapChains Slot.known Slot.known pending.entry
    context := pending.context
    target := pending.target
    working_control := pending.working_control
    staged_slots := pending.staged_slots
    first_slot := pending.first_slot
    skipped := pending.skipped
    remaining := pending.remaining
    request := .known pending.request }

/-- All original pending chains remain known before the selected draw; no comparison with that future draw constructs the stopped context. -/
theorem receive_pending {Value Context : Type} (target : RatchetChain)
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain Value Context) :
    RawCtxChainReceive.nativeKdf (interpret target) (interpret target) (receivePending pending) =
      RawCtxChainReceive.nativeKdf id id pending := rfl

def sendPending {Value Context : Type}
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain Value Context) :
    RawCtxChainSend.Kdf Slot Slot Value Context :=
  { entry := mapChains Slot.known Slot.known pending.entry
    context := pending.context
    committed_control := pending.committed_control
    logical := pending.logical
    sequence := pending.sequence
    request := .known pending.request }

/-- Source send likewise retains its original complete pending state without inspecting the future chain coordinate. -/
theorem send_pending {Value Context : Type} (target : RatchetChain)
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain Value Context) :
    RawCtxChainSend.nativeKdf (interpret target) (interpret target) (sendPending pending) =
      RawCtxChainSend.nativeKdf id id pending := rfl

def requestAddress (chain : RatchetChain) : JointKdfAddress :=
  RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain)

noncomputable def receiveStop {Context : Type}
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial Context)
    (value : Material) : RawCtxChainReceive.Effect Slot Slot RatchetMaterial Context :=
  RawCtxChainReceive.normalResume (receivePending pending) (.hidden, RawCtxFreshChainCut.concreteMaterial value)

/-- The original pending receive and its exact request address produce the stopped continuation from material alone, before every remaining skip/open effect. -/
theorem receive_cut {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (output : FullOutput) :
    simulateQ (RawCtxSelectedParentSource.nativeReceive (Auxiliary := Auxiliary) source writer prior
      (fromOutput (requestAddress pending.request) output) (nextChain output))
      (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.normalResume
        (RawCtxChainReceive.nativeKdf id id pending)
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)))) =
      (fun result => (mapChains (interpret (RawCtxFreshChainCut.concreteChain (nextChain output)))
        (interpret (RawCtxFreshChainCut.concreteChain (nextChain output))) result.1, result.2)) <$>
      simulateQ (RawCtxSelectedParentSource.labelReceive source writer prior
        (fromOutput (requestAddress pending.request) output)
        (RawCtxSelectedParentSource.response prior (fromOutput (requestAddress pending.request) output)
          (nextChain output) (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain (nextChain output)))))
        (RawCtxChainReceive.program (receiveStop pending (material output))) := by
  simpa only [receive_pending, realize_fromOutput, receiveStop,
    show (fromOutput (requestAddress pending.request) output).material = material output from rfl] using
    RawCtxSelectedParentSource.receive_cut source writer prior
      (fromOutput (requestAddress pending.request) output) (nextChain output) (receivePending pending)

def sendStop {Context : Type}
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial Context)
    (value : Material) : RawCtxChainSend.Seal Slot Slot RatchetMaterial Context :=
  RawCtxChainSend.ready (sendPending pending) (.hidden, RawCtxFreshChainCut.concreteMaterial value)

/-- The original send request supplies the entry address, while its complete advanced sealing continuation is constructed without the new chain coordinate. -/
theorem send_cut {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (output : FullOutput) (challenge : RatchetKdfResponse) :
    (do
      let ready := RawCtxSourceSend.resumeSend
        (RawCtxInterpretedSend.nativeKdf (RawCtxChainSend.nativeKdf id id pending))
        (RawCtxKdfRequestTable.fullResponse output)
      let sealed ← RawCtxSourceChainHandles.sendNative (Auxiliary := Auxiliary) source writer (.inr ready)
      pure (ready.advanced, sealed)) =
      (fun result => (nativeKernel (RawCtxFreshChainCut.concreteChain (nextChain output)) result.1, result.2)) <$>
      (do
        let ready := sendStop pending (material output)
        let sealed ← RawCtxSelectedParentSource.labelSend source writer prior
          (fromOutput (requestAddress pending.request) output) challenge (.inr ready)
        pure (ready.advanced, sealed)) := by
  have equality := RawCtxSelectedParentSource.send_cut (Auxiliary := Auxiliary) source writer prior
    (fromOutput (requestAddress pending.request) output) (nextChain output) challenge (sendPending pending)
  rw [realize_fromOutput] at equality
  exact equality

/-- The selected response belongs to the original requested address, with the same prior lookup retained everywhere else. -/
theorem response_requested (prior : Prior) (request : RatchetChain) (output : FullOutput) :
    RawCtxSelectedParentSource.response prior (fromOutput (requestAddress request) output)
      (nextChain output) (RawCtxChainSend.nativeRequest request) =
      RawCtxKdfRequestTable.fullResponse output := by
  rw [RawCtxSelectedParentSource.response, lookup, if_pos (show
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest request) =
      (fromOutput (requestAddress request) output).address from rfl), realize_fromOutput]

/-- The selected callback is the next actual pending receive request, followed by its entire remaining source driver. -/
theorem receive_requested {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (output : FullOutput) :
    simulateQ (RawCtxSelectedParentSource.nativeReceive (Auxiliary := Auxiliary) source writer prior
      (fromOutput (requestAddress pending.request) output) (nextChain output))
      (RawCtxInterpretedReceive.program (.kdfRequested
        (RawCtxChainReceive.nativeKdf id id pending))) =
      (fun result => (mapChains (interpret (RawCtxFreshChainCut.concreteChain (nextChain output)))
        (interpret (RawCtxFreshChainCut.concreteChain (nextChain output))) result.1, result.2)) <$>
      simulateQ (RawCtxSelectedParentSource.labelReceive source writer prior
        (fromOutput (requestAddress pending.request) output)
        (RawCtxSelectedParentSource.response prior (fromOutput (requestAddress pending.request) output)
          (nextChain output) (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain (nextChain output)))))
        (RawCtxChainReceive.program (receiveStop pending (material output))) := by
  simp only [RawCtxInterpretedReceive.program, simulateQ_bind, simulateQ_spec_query,
    RawCtxSelectedParentSource.nativeReceive, RawCtxChainReceive.nativeKdf,
    id_eq, response_requested, pure_bind]
  exact receive_cut source writer prior pending output

/-- The actual send KDF query at the original request address precedes the same advanced sealing tail. -/
theorem send_requested {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (output : FullOutput) (challenge : RatchetKdfResponse) :
    (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$>
    simulateQ (RawCtxSelectedParentSource.nativeSend (Auxiliary := Auxiliary) source writer prior
      (fromOutput (requestAddress pending.request) output) (nextChain output))
      (RawCtxInterpretedSend.program (.requested (RawCtxChainSend.nativeKdf id id pending))) =
      (fun result => (nativeKernel (RawCtxFreshChainCut.concreteChain (nextChain output)) result.1, result.2)) <$>
      (do
        let ready := sendStop pending (material output)
        let sealed ← RawCtxSelectedParentSource.labelSend source writer prior
          (fromOutput (requestAddress pending.request) output) challenge (.inr ready)
        pure (ready.advanced, sealed)) := by
  simp only [RawCtxInterpretedSend.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    RawCtxSelectedParentSource.nativeSend, RawCtxChainSend.nativeKdf,
    id_eq, response_requested, pure_bind]
  have equality := send_cut (Auxiliary := Auxiliary) source writer prior pending output challenge
  rw [RawCtxInterpretedSend.ready_native] at equality
  simpa only [map_bind, map_pure, RawCtxInterpretedSend.nativeSeal,
    RawCtxChainSend.nativeKdf, id_eq, OracleSpec.Range, RawCtxSourceSend.SendSpec,
    OracleSpec.add_def, Sum.elim_inr, OracleSpec.ofFn] using equality

end BeaconcryptCore.Computational.RawCtxSelectedPendingCut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingCut.receive_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingCut.receive_pending

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingCut.send_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingCut.send_pending

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingCut.receive_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingCut.receive_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingCut.send_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingCut.send_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingCut.response_requested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingCut.response_requested

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingCut.receive_requested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingCut.receive_requested

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingCut.send_requested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingCut.send_requested
