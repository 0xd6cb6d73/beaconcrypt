-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedTrace
import BeaconcryptCore.Computational.PqxdhLaterChallengeAddress

/-! The original marked publication fixes the private designation on its actual native source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedAddress
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhCorrelatedExpand PqxdhOrderedChainHybrids
open PqxdhLaterChallengePaths PqxdhFirstRecordConfidentiality
open PqxdhLaterChallengeMarkedTrace
variable {ι M P I D K X Response A N Result AD PT CT : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (A := A) (N := N) (S := S) (B := B)
local notation "Source" => SourceState A N M P I D K Response S B
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- Read the literal send-chain address from the original native role lookup. This predicate does not alter the source interpreter. -/
def Selected (target : RootOutput) (owner : RawCtxProtocolReveals.Owner S B) (before : Source) : Prop :=
  ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.1.roles.1 = some kernel →
    RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target

/-- The same sampled parent and actual annotated target-publication path force a true final designation. Initial operational validity and absence of a previous publication remain explicit for the subsequent literal Builder join. No independently chosen trace supplies the conclusion. -/
theorem sampled_marker (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (sampled : Sum.inr pending ∈ support (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (number : Std.U64) (position : number.val = depth + 2) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result)
    (current : PqxdhRecordConfidentialityChallenge.State) (ambient : Source)
    (initial : Valid cr (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output)
      (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialSampledParent.response start))
      (PqxdhInitialRootAudit.kernel (zeroRoot, PqxdhInitialSampledParent.response start)).refined ambient)
    (unused : current.pair = none)
    (absent : ((start.1.selected, number), true) ∉ ambient.1.1.2.published)
    (result : Result × PqxdhLaterChallengeSourceMonitor.State Source)
    (supported : result ∈ support ((simulateQ (annotated
      (PqxdhLaterChallengeAddress.sampleHandler source writer
        (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) sender route decode start)
      (Selected (nextChain parent) start.1.selected) start.1.selected number bit) client).run ((current, ambient), none)))
    (accepted : PqxdhRecordConfidentialityChallenge.Target number result.2.1.1)
    (published : ((start.1.selected, number), true) ∈ result.2.1.2.1.1.2.published) :
    result.2.2 = some true := by
  obtain ⟨left, right, next, atRequest, reached, after, record, traced, unchosen, length, clear, sent, tail, sequence, designation⟩ :=
    origin _ _ start.1.selected number bit client (current, ambient) result supported unused accepted
  have sourceTail := PqxdhRecordConfidentialityTrace.run_trace _ start.1.selected number bit (next (some record)) _ after _
    (original_supported _ _ start.1.selected number bit (next (some record)) _ result tail)
  have facts := PqxdhLaterChallengeOrigin.request_facts source writer
    (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) start.1.selectedMessage zeroRoot
    (PqxdhInitialSampledParent.response start) _ _ _ _ sender route decode cr _ start.1.selected number bit
    client left right next current atRequest ambient reached after record _ initial
    (Reaches.source _ _ _ _ _ traced) unchosen clear sent sourceTail sequence accepted absent published
  obtain ⟨valid, marked, kernel, found, counter⟩ := facts
  have address := PqxdhLaterSendAddress.marked_address source writer sender route decode cr depth start pending sampled
    parent output safe reached.1.1.1 reached.1.1.2 reached.1.2 valid.1 valid.2 marked kernel found (by omega)
  have selected : Selected (nextChain parent) start.1.selected reached := by
    intro chosen lookup
    have same : kernel = chosen := Option.some.inj (found.symm.trans lookup)
    exact same ▸ address
  simpa only [selected, decide_true] using designation

end BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedAddress

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedAddress.sampled_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkedAddress.sampled_marker
