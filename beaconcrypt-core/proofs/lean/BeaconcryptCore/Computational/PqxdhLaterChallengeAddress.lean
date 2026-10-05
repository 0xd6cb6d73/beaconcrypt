import BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin

/-! The actual sampled parent cut and original challenge trace identify the selected directional send input at request time. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeAddress
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhCorrelatedExpand PqxdhOrderedChainHybrids
open PqxdhInitialNativeRetained PqxdhPreparedPendingReplay PqxdhRetainedOccurrenceInterpreter
open PqxdhRecordConfidentialityChallenge PqxdhRecordConfidentialityTrace PqxdhLaterChallengePaths
open PqxdhFirstRecordConfidentiality (AdvSpec)
variable {ι M P I D K X Response A N Selection AD PT CT : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (A := A) (N := N) (S := S) (B := B)
local notation "Evidence" => PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B
local notation "Final" => PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B × RetainedState A N RootOracle.QueryCache
local notation "Source" => SourceState A N M P I D K Response S B
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The exact concrete callback interpreter for the sampled source, with only tuple association changed. -/
noncomputable def sampleHandler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (start : Start) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B) (StateT Source ProbComp) :=
  sourceHandler source writer prior start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start)
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.pre start.1.other query))
    (fun reply => ambient (PqxdhInitialSourcePreparedSecrecy.application start.1.other reply))
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.selector start.1.other query))
    (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.aux start.1.other query)) sender route decode

/-- A literal reached challenge and full source suffix, with the pre-send kernel at the selected input. This is an execution witness, not a probability or independence assertion. -/
def AtChallenge (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (start : Start) (child : RootOutput)
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (bit : Bool) (selection : Selection) (result : Final) : Prop :=
  let impl := sampleHandler source writer prior sender route decode start
  ∃ (evidence : Evidence) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (ambient : Source) (final current : State) (left right : Pqxdh.Bytes)
    (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Bool)
    (reached after : Source) (record : RawCtxSourceSend.Encrypted) (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain),
    Reaches impl start.1.selected number bit (adversary selection reply) initial ambient
      ((AdvSpec extra S B).query (.inr (left, right)) >>= next) current reached ∧
    current.pair = none ∧ left.length = right.length ∧ current.otherTarget = false ∧
    (some record, after) ∈ support ((simulateQ impl (send start.1.selected (if bit then right else left))).run reached) ∧
    Trace impl start.1.selected number bit (next (some record))
      { current with pair := some (left, right), reply := some (some record) } after
      ((true, final), ((result.1.2, evidence), reassociate result.2)) ∧
    record.sequence = number ∧ Target number final ∧
    reached.1.1.2.installed start.1.selected = some true ∧
    RawCtxGenericRoleFamily.selectedKernel start.1.selected reached.1.1.1.roles.1 = some kernel ∧
    number.val = kernel.control.send_sequence.val + 1 ∧
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest kernel.send_chain) =
      RawCtxSelectedParentPrivatePatch.targetAddress child

/-- The actual annotated sampled execution supplies the request-time selected input, using the same sampled cursor and retained table throughout. -/
theorem sampled_request (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (sampled : Sum.inr pending ∈ support (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (position : number.val = depth + 2) (bit : Bool) (selection : Selection)
    (challenge : start.1.post = post adversary start.1.selected number bit selection)
    (result : Final) (evidence : Evidence)
    (supported : ((result.1.1, (result.1.2, evidence)), result.2) ∈ support
      ((simulateQ (retained source writer (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output)
        (sampleExternal source start)) (PqxdhPreparedOccurrencePaths.sampleAnnotated source sender route decode start)).run
          (start.1.shared, (start.1.privateState, start.1.cache))))
    (accepted : result.1.1 = true)
    (published : ((start.1.selected, number), true) ∈ result.1.2.2.published) :
    AtChallenge source writer (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output)
      sender route decode start (nextChain parent) adversary number bit selection result := by
  have actual := Set.mem_image_of_mem (Prod.map id (reassociate (A := A) (N := N))) supported
  rw [← support_map] at actual
  rw [PqxdhRetainedOccurrenceInterpreter.source_program source writer
    (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) start.1.selectedMessage zeroRoot
      (PqxdhInitialSampledParent.response start) (PqxdhInitialSourcePreparedSecrecy.pre start.1.other)
      (PqxdhInitialSourcePreparedSecrecy.application start.1.other) (PqxdhInitialSourcePreparedSecrecy.selector start.1.other)
      (PqxdhInitialSourcePreparedSecrecy.aux start.1.other)] at actual
  simp only [PqxdhPreparedOccurrencePaths.sampleAnnotated, sampleExecution, PqxdhInitialSourceExperiment.execution,
    PqxdhInitialSampledParent.marker, challenge] at actual
  obtain ⟨reply, initialState, final, left, right, next, current, reached, after, record, traced, unused, length, clear,
    sent, tail, sequence, target, valid, marked, kernel, found, counter⟩ :=
    PqxdhLaterChallengeOrigin.sequence_request source writer
      (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) start.1.selectedMessage zeroRoot
      (PqxdhInitialSampledParent.response start)
      (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.pre start.1.other query))
      (fun reply => ambient (PqxdhInitialSourcePreparedSecrecy.application start.1.other reply))
      (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.selector start.1.other query))
      (fun query => ambient (PqxdhInitialSourcePreparedSecrecy.aux start.1.other query))
      sender route decode cr (PqxdhInitialSampledParent.response start) true start.1.index start.1.metadata
      {start.1.ready with root := zeroRoot} adversary start.1.selected number bit selection start.1.before
      (reassociate (start.1.shared, (start.1.privateState, start.1.cache))) _ actual accepted (by omega) published
  refine ⟨evidence, reply, initialState, final, current, left, right, next, reached, after, record, kernel,
    traced, unused, length, clear, sent, tail, sequence, target, marked, found, counter, ?_⟩
  exact PqxdhLaterSendAddress.marked_address source writer sender route decode cr depth start pending sampled
    parent output safe reached.1.1.1 reached.1.1.2 reached.1.2 valid.1 valid.2 marked kernel found (by omega)

/-- The actual saved pending completion supplies the complete annotated execution and therefore the literal challenge request, with no caller-supplied request marker, counter or path. -/
theorem pending_request (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (sampled : Sum.inr pending ∈ support (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (position : number.val = depth + 2) (bit : Bool) (selection : Selection)
    (challenge : start.1.post = post adversary start.1.selected number bit selection)
    (result : Final)
    (completed : result ∈ support ((simulateQ
      (retained source writer (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) (sampleExternal source start))
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker source start) sender route decode pending.1
        (PqxdhInitialParentBuilderContext.reply sender route decode pending.1.original parent))).run (project pending.2.1)))
    (accepted : result.1.1 = true)
    (published : ((start.1.selected, number), true) ∈ result.1.2.2.published) :
    AtChallenge source writer (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output)
      sender route decode start (nextChain parent) adversary number bit selection result := by
  obtain ⟨evidence, annotated, _⟩ := PqxdhLaterPatchedOccurrence.sample_one_paths source writer sender route decode
    cr depth start pending sampled parent output safe result completed
  exact sampled_request source writer sender route decode cr depth start pending sampled parent output safe
    adversary number position bit selection challenge result evidence annotated accepted published

local notation "MaterialContext" => PqxdhErasedParentMaterial.MaterialContext (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)

/-- The full material sampler and saved completion expose the actual pre-normalization source draw and its literal challenge request. The same bounded input-alias event remains explicit; no reachability is asserted for a reconstructed normalized start. -/
theorem material_request (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (depth : Nat)
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (context : MaterialContext)
    (sampled : context ∈ support (PqxdhErasedParentMaterial.prepare source writer sender route decode depth prior))
    (start : Start) (pending : Pending) (shape : context.1.1.1 = .inr (start, .inr pending))
    (safe : PqxdhLaterInputAlias.collision context = false) (output : FullOutput)
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (number : Std.U64) (position : number.val = depth + 2) (bit : Bool) (selection : Selection)
    (challenge : start.1.post = post adversary start.1.selected number bit selection)
    (result : Final)
    (completed : result ∈ support ((simulateQ
      (retained source writer
        (PqxdhLaterPatchedOccurrence.patchedPrior source pending (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2) output)
        (sampleExternal source start))
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker source start) sender route decode pending.1
        (PqxdhInitialParentBuilderContext.reply sender route decode pending.1.original
          (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2)))).run (project pending.2.1)))
    (accepted : result.1.1 = true)
    (published : ((start.1.selected, number), true) ∈ result.1.2.2.published) :
    ∃ actualStart : Start,
      PqxdhErasedParentSample.forgetStart actualStart = start ∧
      Sum.inr actualStart.1 ∈ support prior ∧
      AtChallenge source writer
        (PqxdhLaterPatchedOccurrence.patchedPrior source pending (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2) output)
        sender route decode actualStart context.1.2 adversary number bit selection result := by
  simp only [PqxdhErasedParentMaterial.prepare, mem_support_bind_iff, mem_support_pure_iff] at sampled
  obtain ⟨packet, sampled, parent, _, nonce, _, chain, _, rfl⟩ := sampled
  simp only [RawCtxSelectedParentEntry.realize_fromOutput] at completed ⊢
  simp only [PqxdhErasedParentSample.sample, mem_support_bind_iff] at sampled
  obtain ⟨common | input, priorReached, block, _, sampled⟩ := sampled
  all_goals simp only [mem_support_bind_iff, mem_support_pure_iff] at sampled
  · simp only [sampled, PqxdhErasedParentSample.normalize, reduceCtorEq] at shape
  · obtain ⟨common | reachedPending, reached, rfl⟩ := sampled
    · cases shape
    · simp only [PqxdhErasedParentSample.normalize, Sum.inr.injEq, Prod.mk.injEq] at shape
      rcases shape with ⟨rfl, rfl⟩
      exact ⟨(input, block), rfl, priorReached, pending_request source writer sender route decode cr depth
        (input, block) reachedPending reached parent output (of_decide_eq_false safe) adversary number position bit
        selection challenge result completed accepted published⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeAddress

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeAddress.sampled_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeAddress.sampled_request
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeAddress.pending_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeAddress.pending_request
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeAddress.material_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeAddress.material_request
