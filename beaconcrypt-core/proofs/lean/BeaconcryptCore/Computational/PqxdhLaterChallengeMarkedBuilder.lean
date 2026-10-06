-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedAddress

/-! The literal first Builder supplies the state of the exact annotated later-challenge execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhInitialReceiptConstruction PqxdhInitialPendingPost PqxdhRetainedOccurrenceInterpreter
open PqxdhLaterChallengePaths PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response A N Selection AD PT CT : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (A := A) (N := N) (S := S) (B := B)
local notation "Source" => SourceState A N M P I D K Response S B
local notation "Built" => ((RustM (Option PqxdhServerRegistrationPublication.Response) ×
  Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf RatchetChain))) × Front RatchetChain M P I D K S B) × InitialState A N
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The complete native callback interpreter for this literal pre-normalization source packet. -/
noncomputable def callbacks (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (start : Start) :=
  PqxdhInitialOccurrencePaths.handler (S := S) (B := B) source writer prior start.1.selectedMessage zeroRoot
    (PqxdhInitialSampledParent.response start)
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.pre start.1.other query))
    (fun reply => ambient (PqxdhInitialSourcePreparedSecrecy.application start.1.other reply))
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.selector start.1.other query))
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.aux start.1.other query))

/-- The first Builder executes before the challenge wrapper, including its actual optional result and all writer effects. -/
noncomputable def builder (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (sender : M → Std.U64) (start : Start) : ProbComp Built :=
  (simulateQ (callbacks source writer prior start)
    ((PqxdhInitialBuilderReceipt.build source
      (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialSampledParent.response start))
      sender start.1.index start.1.metadata {start.1.ready with root := zeroRoot}).run start.1.before)).run
        (reassociate (start.1.shared, (start.1.privateState, start.1.cache)))

/-- Literal source occurrence bookkeeping after the actual Builder; no existing owner or state field is reconstructed from a desired target event. -/
noncomputable def afterBuilder (start : Start) (built : Built) : Source :=
  (((built.1.2, PqxdhInitialOriginPost.afterBuilder PqxdhInitialSourcePublication.empty built.1.2 start.1.index true built.1.1.1),
    PqxdhInitialInstallOccurrence.built (PqxdhInitialInstallOccurrence.begin PqxdhInitialInstallOccurrence.empty)
      0 {start.1.ready with root := zeroRoot} start.1.index built.1.2 built.1.1.1 built.1.1.2), built.2)

/-- Execute the original first Builder and entire source Post, with one private request marker added and every returned state retained. -/
noncomputable def run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (start : Start) (target : RootOutput)
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (bit : Bool) (selection : Selection) :
    ProbComp (Bool × PqxdhLaterChallengeSourceMonitor.State Source) := do
  let built ← builder source writer prior sender start
  (simulateQ (PqxdhLaterChallengeMarkedTrace.annotated
    (PqxdhLaterChallengeAddress.sampleHandler source writer prior sender route decode start)
    (PqxdhLaterChallengeMarkedAddress.Selected target start.1.selected) start.1.selected number bit)
    (adversary selection built.1.1.1)).run ((PqxdhRecordConfidentialityChallenge.initial, afterBuilder start built), none)

/-- Remove only the private marker and close the unchanged source challenge output; all native and occurrence state is returned. -/
noncomputable def forget (number : Std.U64) (result : Bool × PqxdhLaterChallengeSourceMonitor.State Source) :=
  ((PqxdhRecordConfidentialityChallenge.output number (result.1, result.2.1.1), result.2.1.2.1), result.2.1.2.2)

/-- The complete annotated distribution erases exactly to the literal first-Builder/source-Post sequence. No outcome, refusal, source state or callback history is discarded. -/
theorem source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (start : Start) (target : RootOutput)
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (bit : Bool) (selection : Selection) :
    forget number <$> run source writer prior sender route decode start target adversary number bit selection =
      (simulateQ (callbacks source writer prior start)
        ((PqxdhInitialInstallOccurrence.sequence source
          (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialSampledParent.response start))
          (PqxdhInitialSelectedOrigin.mark source start.1.selectedMessage) true sender route decode start.1.index start.1.metadata
          {start.1.ready with root := zeroRoot} (PqxdhRecordConfidentialityChallenge.post adversary start.1.selected number bit selection)).run
            ((start.1.before, PqxdhInitialSourcePublication.empty), PqxdhInitialInstallOccurrence.empty))).run
              (reassociate (start.1.shared, (start.1.privateState, start.1.cache))) := by
  simp only [run, builder, PqxdhInitialInstallOccurrence.sequence, StateT.run, simulateQ_bind, map_bind]
  change _ = StateT.run _ _
  rw [StateT.run_bind]
  apply bind_congr
  intro built
  have erased := congrArg (fun work => (fun result =>
      ((PqxdhRecordConfidentialityChallenge.output number result.1, result.2.1), result.2.2)) <$> work)
    (PqxdhLaterChallengeMarkedTrace.program_nested
      (PqxdhLaterChallengeAddress.sampleHandler source writer prior sender route decode start)
      (PqxdhLaterChallengeMarkedAddress.Selected target start.1.selected) start.1.selected number bit
      (adversary selection built.1.1.1) ((PqxdhRecordConfidentialityChallenge.initial, afterBuilder start built), none))
  simp only [Functor.map_map] at erased
  simp only [StateT.run] at erased
  unfold forget
  rw [erased]
  have flattened := PqxdhLaterChallengePaths.source_program source writer prior start.1.selectedMessage zeroRoot
    (PqxdhInitialSampledParent.response start)
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.pre start.1.other query))
    (fun reply => ambient (PqxdhInitialSourcePreparedSecrecy.application start.1.other reply))
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.selector start.1.other query))
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.aux start.1.other query)) sender route decode
    ((simulateQ (PqxdhRecordConfidentialityChallenge.handler start.1.selected number bit)
      (adversary selection built.1.1.1)).run PqxdhRecordConfidentialityChallenge.initial) (afterBuilder start built)
  simp only [StateT.run] at flattened
  rw [PqxdhLaterChallengeAddress.sampleHandler, flattened]
  simp only [PqxdhRecordConfidentialityChallenge.post, simulateQ_map, Functor.map_map, callbacks, afterBuilder]
  change _ = (simulateQ (callbacks source writer prior start) (StateT.run _ (afterBuilder start built).1)).run built.2
  rw [StateT.run_map, simulateQ_map, StateT.run_map]
  rfl

/-- The actual first Builder discharges the source-path and prior-publication premises. Every true target event with the original marked publication has a true final designation on this same full annotated sequence. -/
theorem marked (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (sampled : Sum.inr pending ∈ support (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (position : number.val = depth + 2) (bit : Bool) (selection : Selection)
    (result : Bool × PqxdhLaterChallengeSourceMonitor.State Source)
    (supported : result ∈ support (run source writer
      (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) sender route decode start
      (nextChain parent) adversary number bit selection))
    (accepted : PqxdhRecordConfidentialityChallenge.Target number result.2.1.1)
    (published : ((start.1.selected, number), true) ∈ result.2.1.2.1.1.2.published) :
    result.2.2 = some true := by
  simp only [run, mem_support_bind_iff] at supported
  obtain ⟨built, builtSupported, rest⟩ := supported
  apply PqxdhLaterChallengeMarkedAddress.sampled_marker source writer sender route decode cr depth start pending sampled
    parent output safe number position bit (adversary selection built.1.1.1)
    PqxdhRecordConfidentialityChallenge.initial (afterBuilder start built) _ rfl _ result rest accepted published
  · refine ⟨?_, ?_⟩
    · exact PqxdhRetainedSelectedOrigins.builder_selected source writer
        (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) start.1.selectedMessage zeroRoot
        (PqxdhInitialSampledParent.response start) _ _ _ _ _ _ true sender start.1.index start.1.metadata
        {start.1.ready with root := zeroRoot} start.1.before
        (reassociate (start.1.shared, (start.1.privateState, start.1.cache)))
        PqxdhInitialSourcePublication.empty PqxdhInitialInstallOccurrence.empty
        (fun _ impossible => nomatch impossible) built builtSupported
    · exact PqxdhInitialOccurrencePaths.builder_holds source writer
        (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) start.1.selectedMessage zeroRoot
        (PqxdhInitialSampledParent.response start) _ _ _ _ cr (PqxdhInitialSampledParent.response start) sender
        start.1.index start.1.metadata {start.1.ready with root := zeroRoot} start.1.before
        (reassociate (start.1.shared, (start.1.privateState, start.1.cache))) built builtSupported
  · exact PqxdhLaterChallengePaths.builder_absent source writer
      (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) start.1.selectedMessage zeroRoot
      (PqxdhInitialSampledParent.response start) _ _ _ _ sender (PqxdhInitialSampledParent.response start) true
      start.1.index start.1.metadata {start.1.ready with root := zeroRoot} start.1.before
      (reassociate (start.1.shared, (start.1.privateState, start.1.cache))) built builtSupported start.1.selected number (by omega)

/-- The original challenge-output and marked-publication test; the private designation is not part of this event. -/
noncomputable def event (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (result : Bool × PqxdhLaterChallengeSourceMonitor.State Source) : Bool := by
  classical
  exact PqxdhRecordConfidentialityChallenge.output number (result.1, result.2.1.1) &&
    decide (((owner, number), true) ∈ result.2.1.2.1.1.2.published)

/-- The actual original true event forces the marker without a caller-supplied target or source-validity premise. -/
theorem event_marked (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (sampled : Sum.inr pending ∈ support (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (position : number.val = depth + 2) (bit : Bool) (selection : Selection)
    (result : Bool × PqxdhLaterChallengeSourceMonitor.State Source)
    (supported : result ∈ support (run source writer
      (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) sender route decode start
      (nextChain parent) adversary number bit selection))
    (accepted : event start.1.selected number result = true) :
    result.2.2 = some true := by
  classical
  simp only [event, PqxdhRecordConfidentialityChallenge.output, Bool.and_eq_true, decide_eq_true_eq] at accepted
  apply marked source writer sender route decode cr depth start pending sampled parent output safe
    adversary number position bit selection result supported
  · exact accepted.1.2
  · exact accepted.2

/-- Adding the designation test leaves the original event probability unchanged, even with any further predicate of the complete native result and poststate. This removes only the marker-false branch under the explicit same-input alias exclusion. -/
theorem event_filter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (sampled : Sum.inr pending ∈ support (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (position : number.val = depth + 2) (bit : Bool) (selection : Selection)
    (fresh : Bool × Source → Bool) :
    𝒟[(fun result => event start.1.selected number result && fresh (result.1, result.2.1.2)) <$>
      run source writer (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output)
        sender route decode start (nextChain parent) adversary number bit selection] {true} =
    𝒟[(fun result => event start.1.selected number result && fresh (result.1, result.2.1.2) &&
        @decide (result.2.2 = some true) (Classical.propDecidable _)) <$>
      run source writer (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output)
        sender route decode start (nextChain parent) adversary number bit selection] {true} := by
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  apply OracleComp.probEvent_congr' _ rfl
  intro result supported
  simp only [Function.comp_def, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun accepted => ⟨accepted, event_marked source writer sender route decode cr depth start pending sampled
    parent output safe adversary number position bit selection result supported accepted.1⟩, And.left⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder.source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder.marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder.marked

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder.event_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder.event_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder.event_filter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedBuilder.event_filter
