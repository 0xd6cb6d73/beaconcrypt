import BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy
import BeaconcryptCore.Computational.PqxdhInitialHalfInitializer
import BeaconcryptCore.Computational.PqxdhInitialSourceSampled
import BeaconcryptCore.Computational.PqxdhInitialSourceReal
import BeaconcryptCore.Computational.PqxdhInitialSourceRandom

/-!
The first directional-chain reduction starts at the original source input before the Server's first send. The selected owner chooses the hidden initial half, the opposite half remains in the comparison context, and every repeated initializer reconstructs the same original64-byte response. This module instantiates the complete private observer with those literal callbacks and full original state.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceHalf
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
open PqxdhInitialSourceInitialSecrecy (Input Context)
open RawCtxInitialSentinelSampler RawCtxSelectedParentEntry RawCtxSelectedParentTable
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

noncomputable def second (selected : RawCtxProtocolReveals.Owner S B) : Bool :=
  match selected with
  | .server _ _ => false
  | .beacon _ => true

def zeroRoot : RootOutput := List.Vector.replicate 32 0

noncomputable def execution (input : Input extra M P I D K X Response A N S B) (other : RootOutput) :
    PqxdhInitialHalfProgram.Execution extra M P I D K Bool Bool S B :=
  ⟨labelInitial (second input.selected) false other, input.index, input.metadata,
    { input.ready with root := zeroRoot }, input.post, PqxdhInitialPostContext.knownFront input.before,
    PqxdhInitialSourcePublication.empty, true⟩

noncomputable def view (source : FixedHkdfSha512NoSaltSource) :
    PqxdhInitialHalfSecrecy.View (Input extra M P I D K X Response A N S B) extra M P I D K X Response
      PqxdhPhase2DecapsulationRouting.Shared A N RootOracle.QueryCache S B where
  execution := fun context => execution context.1 context.2.material.1
  prior := fun _ => productionStream source.crypto
  pre := fun input query => input.other (.inl query)
  application := fun input reply => input.other (.inr (.inl reply))
  initializer := fun context => PqxdhInitialHalfInitializer.initial source context.1.selectedMessage zeroRoot
    (second context.1.selected) context.2.material.1
  selector := fun input query => input.other (.inr (.inr (.inr (.inl query))))
  aux := fun input query => input.other (.inr (.inr (.inr (.inr query))))
  ambient := fun input => ((input.shared, input.privateState), input.cache)
  priorCandidates := fun _ => []
  disclosed := Input.disclosed
  ancestors := Input.ancestors
  selected := Input.selected
  number := Input.number

noncomputable def mark (source : FixedHkdfSha512NoSaltSource)
    (input : Input extra M P I D K X Response A N S B) :=
  PqxdhInitialSelectedOrigin.mark source input.selectedMessage

/-- The original external interface is reconstructed exactly, including repeated selected initializer calls and all original ambient state. -/
theorem external (source : FixedHkdfSha512NoSaltSource)
    (input : Input extra M P I D K X Response A N S B) (other target : RootOutput) (padding : NonceOutput) :
    PqxdhInitialNativeAudit.external ((view source).pre input) ((view source).application input)
      (PqxdhInitialHalfRetained.nativeInitial target ((view source).initializer (input, RawCtxInitialSentinel.entry other padding)))
      ((view source).selector input) ((view source).aux input) =
    PqxdhInitialOriginFinishPath.withInitial source input.selectedMessage zeroRoot
      (RawCtxSelectedInitialConstructor.response64 (join (second input.selected) other target)) input.other := by
  funext query
  rcases query with query | (reply | (secrets | (query | query)))
  all_goals try rfl
  change Prod.snd <$> (Prod.map id (Option.map (RawCtxSelectedParentCalls.nativeKernel target)) <$>
      PqxdhInitialHalfInitializer.initial source input.selectedMessage zeroRoot (second input.selected) other secrets) = _
  rw [PqxdhInitialHalfInitializer.initial_native]
  rfl

/-- The first builder uses exactly the original supplied Server constructor under the full native chain interpretation. -/
theorem first (input : Input extra M P I D K X Response A N S B) (other target : RootOutput) :
    RawCtxSelectedParentCalls.nativeKernel target <$> (execution input other).first =
      ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false
        (RawCtxSelectedInitialConstructor.response64 (join (second input.selected) other target)) := by
  rw [PqxdhInitialSelectedBuilder.kernel_response]
  simp only [execution, Functor.map_map]
  rfl

/-- The actual selected owner sends on the hidden half of the same supplied initial64 response. -/
theorem root (source : FixedHkdfSha512NoSaltSource) (selected : RawCtxProtocolReveals.Owner S B)
    (other target : RootOutput) :
    PqxdhInitialSourceExperiment.root source zeroRoot
      (RawCtxSelectedInitialConstructor.response64 (join (second selected) other target)) selected = target := by
  cases selected with
  | server index peer =>
      have created := PqxdhInitialSourceExperiment.server_created source
        (RawCtxSelectedInitialConstructor.response64 (join false other target))
      rw [PqxdhInitialSelectedBuilder.kernel_response] at created
      simp [labelInitial, Bool.false_eq_true, RawCtxSelectedInitialConstructor.initial,
        RawCtxSelectedInitialConstructor.sendSlot, RawCtxSelectedInitialConstructor.receiveSlot,
        RefinedRatchet.new, RefinedRatchet.from_counters, control.RatchetState.from_counters, control.SequenceCache.empty, empty_material_slots] at created
      simp only [PqxdhInitialSourceExperiment.root, PqxdhInitialOriginPostPath.rootFor, second]
      change ok _ = ok _ at created
      have same := RustM.ok.inj created
      rw [← same]
      exact RawCtxSelectedQueryTrace.rootVector_concrete target
  | beacon index =>
      have created := PqxdhInitialSelectedBuilder.kernel_response true true other target
      have native : PqxdhInitialReplyErasure.kernelOf true
          (RawCtxSelectedInitialConstructor.response64 (join true other target)) =
          ok (PqxdhInitialRootAudit.kernel (zeroRoot,
            RawCtxSelectedInitialConstructor.response64 (join true other target))) := by
        exact PqxdhBeaconPhase2Publication.normalInitial_exact _ _
      rw [native] at created
      simp [labelInitial, RawCtxSelectedInitialSecond.initialSecond, Bool.not_true,
        RawCtxSelectedInitialConstructor.initial, RawCtxSelectedInitialConstructor.sendSlot,
        RawCtxSelectedInitialConstructor.receiveSlot, Bool.false_eq_true,
        RefinedRatchet.new, RefinedRatchet.from_counters, control.RatchetState.from_counters, control.SequenceCache.empty, empty_material_slots] at created
      simp only [PqxdhInitialSourceExperiment.root, PqxdhInitialOriginPostPath.rootFor, second,
        PqxdhInitialOriginFinishPath.sendRoot]
      change ok _ = ok _ at created
      have same := RustM.ok.inj created
      rw [same]
      exact RawCtxSelectedQueryTrace.rootVector_concrete target

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

noncomputable def retained (input : Input extra M P I D K X Response A N S B)
    (other target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  (fun result => PqxdhInitialHalfRetained.decision
    (RawCtxSelectedParentPrivatePatch.privatePatch (productionStream source.crypto) target output) target
    (input.number.val - 1) input.ancestors input.disclosed input.selected input.number result.1) <$>
    (simulateQ (PqxdhInitialNativeRetained.retained source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch (productionStream source.crypto) target output)
      (PqxdhInitialOriginFinishPath.withInitial source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 (join (second input.selected) other target)) input.other))
      (PqxdhInitialNativeCarried.original source (mark source input) sender route decode
        (PqxdhInitialSourceExperiment.execution
          (RawCtxSelectedInitialConstructor.response64 (join (second input.selected) other target))
          input.index input.metadata { input.ready with root := zeroRoot } input.post input.before))).run
      (input.shared, (input.privateState, input.cache))

/-- The original retained source publication and byte-freshness event is the complete native initial-half observer. This is an exact program equality, preserving all initializer, first-send and later adaptive effects. -/
theorem retained_native (input : Input extra M P I D K X Response A N S B)
    (other target : RootOutput) (padding : NonceOutput) (output : FullOutput) :
    retained source writer sender route decode input other target output =
      PqxdhInitialHalfSecrecy.native source writer (mark source) sender route decode (view source)
        (.inr input, RawCtxInitialSentinel.entry other padding) target output := by
  have equality := PqxdhInitialHalfRetained.decision_compiled source writer (productionStream source.crypto)
    other target padding ((view source).pre input) ((view source).application input)
    ((view source).initializer (input, RawCtxInitialSentinel.entry other padding))
    ((view source).selector input) ((view source).aux input) (mark source input) sender route decode
    (execution input other) output (input.number.val - 1) (input.shared, (input.privateState, input.cache)) []
    input.ancestors input.disclosed input.selected input.number
  rw [external source input other target padding, first input other target] at equality
  simp only [execution, PqxdhInitialParentPost.known_front] at equality
  exact equality

/-- The actual stage-zero source event is obtained by supplying the selected input's unchanged real full76 response to the same private observer. -/
theorem real_native (input : Input extra M P I D K X Response A N S B)
    (other target : RootOutput) (padding : NonceOutput) :
    PqxdhInitialSourceInitialSecrecy.sourceGame source writer sender route decode input zeroRoot
      (RawCtxSelectedInitialConstructor.response64 (join (second input.selected) other target)) 0 =
    PqxdhInitialHalfSecrecy.native source writer (mark source) sender route decode (view source)
      (.inr input, RawCtxInitialSentinel.entry other padding) target
      (productionStream source.crypto (RawCtxSelectedParentPrivatePatch.targetAddress target)) := by
  rw [← retained_native source writer sender route decode input other target padding]
  unfold retained PqxdhInitialSourceInitialSecrecy.sourceGame
  rw [PqxdhInitialNativeParentRealization.consistent_patch,
    PqxdhInitialSourceReal.game_source]
  unfold PqxdhInitialSourceReal.decision PqxdhInitialHalfRetained.decision
  rw [root source input.selected other target]
  rfl

/-- The actual stage-one source event draws a full76 child, preserving the same original initial64 response, publication gate and byte-level freshness observation. -/
theorem random_native (input : Input extra M P I D K X Response A N S B)
    (positive : 0 < input.number.val) (other target : RootOutput) (padding : NonceOutput) :
    𝒟[PqxdhInitialSourceInitialSecrecy.sourceGame source writer sender route decode input zeroRoot
      (RawCtxSelectedInitialConstructor.response64 (join (second input.selected) other target)) 1] =
    𝒟[($ᵗ FullOutput) >>= fun output =>
      PqxdhInitialHalfSecrecy.native source writer (mark source) sender route decode (view source)
        (.inr input, RawCtxInitialSentinel.entry other padding) target output] := by
  unfold PqxdhInitialSourceInitialSecrecy.sourceGame
  rw [PqxdhInitialSourceRandom.game_source source writer input.selectedMessage zeroRoot _ input.other
    sender route decode input.index input.metadata _ input.post input.before input.selected
    input.shared input.privateState input.cache input.number positive]
  apply evalDist_bind_congr' ($ᵗ FullOutput)
  intro output
  rw [← retained_native source writer sender route decode input other target padding output]
  unfold PqxdhInitialSourceRandom.decision PqxdhInitialSourceRandom.randomRun
  rw [root source input.selected other target]
  rfl

end BeaconcryptCore.Computational.PqxdhInitialSourceHalf

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceHalf.external' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceHalf.external

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceHalf.first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceHalf.first

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceHalf.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceHalf.root

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceHalf.retained_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceHalf.retained_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceHalf.real_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceHalf.real_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceHalf.random_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceHalf.random_native
