import BeaconcryptCore.Computational.PqxdhInitialSourceHalf
import BeaconcryptCore.Computational.PqxdhInitialHalfObserverBudgets

/-!
The first-half source observer pays the complete original firstbuilder and post callback count, every appended private lineage check and every original external callback. The candidate bound counts the literal pre-existing disclosure list plus at most three available values per compiled callback. The source initializer costs at most32 uniform byte queries. No whole-observer cost, final event or input-recovery probability is supplied as a premise.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfResources
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialHalfObserverBudgets PqxdhInitialHalfProgram
open PqxdhInitialSourceInitialSecrecy (Input)
open PqxdhInitialSourceHalf RawCtxSelectedParentEntry
variable {ι M P I D K X Response Shared Result Origin A N : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Every private lineage check contributes exactly its finite depth-plus-one reservation and invokes no external source callback. -/
theorem checker_total (depth : Nat) :
    (checker (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) depth).IsTotalQueryBound
      (depth + 1) :=
  PqxdhBeaconPhase2Bounds.simulate_total checkerCompiler _ (depth + 1)
    (RawCtxFiniteLineageCheck.queries RawCtxFiniteLineageCheck.labelKey depth .hidden)
    (fun _ => ⟨by change 0 < 1; decide, fun _ => True.intro⟩)

/-- The source-derived original seven-plus67-per-request allowance and the concrete audit compiler derive the full first-hop callback cap. -/
theorem program_total (source : FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : Execution extra M P I D K Result Origin S B) (depth qPost : Nat)
    (bounded : ∀ reply, (execution.post reply).IsTotalQueryBound qPost) :
    (program (X := X) (Response := Response) source mark sender route decode execution depth).IsTotalQueryBound (2 * (7 + qPost * 67) + (depth + 1)) := by
  unfold program baseProgram
  apply isTotalQueryBound_bind
    (PqxdhInitialHalfObserverCompiler.program_bound _ _
      (PqxdhInitialOriginPost.sequence_total source execution.first mark execution.origin sender route decode
        execution.index execution.metadata execution.ready execution.post qPost bounded (execution.before, execution.trace)))
  intro result
  rw [bind_pure_comp]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr (checker_total depth)

def callbackCap (qPost qCheck : Nat) : Nat := 2 * (7 + qPost * 67) + qCheck

def costs (qPre qApplication qSelector qAux : Nat) : Costs :=
  ⟨qPre, qApplication, 32, qSelector, qAux⟩

def uniformCap (qPost qCheck qPre qApplication qSelector qAux : Nat) : Nat :=
  callbackCap qPost qCheck * (costs qPre qApplication qSelector qAux).cap

def candidateCap (qPost qCheck qKnown : Nat) : Nat := qKnown + 3 * callbackCap qPost qCheck

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (input : Input extra M P I D K X Response A N S B)
  (qPost qCheck qKnown qPre qApplication qSelector qAux : Nat)
  (postBound : ∀ reply, (input.post reply).IsTotalQueryBound qPost)
  (checkBound : input.number.val - 1 + 1 ≤ qCheck)
  (knownBound : (RawCtxFamilyFreshnessProxy.knownInputs input.disclosed input.before.roles.2).length ≤ qKnown)
  (preBound : ∀ query state cache, (input.other (.inl query) state cache).IsTotalQueryBound qPre)
  (applicationBound : ∀ query state cache, (input.other (.inr (.inl query)) state cache).IsTotalQueryBound qApplication)
  (selectorBound : ∀ query state cache, (input.other (.inr (.inr (.inr (.inl query)))) state cache).IsTotalQueryBound qSelector)
  (auxBound : ∀ query state cache, (input.other (.inr (.inr (.inr (.inr query)))) state cache).IsTotalQueryBound qAux)

include preBound applicationBound selectorBound auxBound in
/-- The concrete source callbacks supply the ordinary observer's resource certificate; repeated initializer calls retain their exact32-byte root-cache bill. -/
theorem callbacks (entry : Entry) : ExternalUniform (costs qPre qApplication qSelector qAux)
    ((view source).pre input) ((view source).application input) ((view source).initializer (input, entry))
    ((view source).selector input) ((view source).aux input) := by
  refine ⟨preBound, applicationBound, ?_, selectorBound, auxBound⟩
  exact PqxdhInitialHalfInitializer.initial_uniform source input.selectedMessage zeroRoot (second input.selected) entry.material.1

include postBound checkBound knownBound preBound applicationBound selectorBound auxBound in
/-- The literal complete ordinary first-half observer has the derived uniform-byte and candidate bills from the actual source input. -/
theorem one_bounds (entry : Entry) (output : FullOutput) :
    let work := PqxdhInitialHalfSecrecy.observed source writer (mark source) sender route decode (view source) (.inr input, entry) output
    work.IsTotalQueryBound (uniformCap qPost qCheck qPre qApplication qSelector qAux) ∧
      ∀ result ∈ support work, (PqxdhInitialHalfSecrecy.candidates result).length ≤ candidateCap qPost qCheck qKnown := by
  have fullBound := (program_total (X := X) (Response := Response) source (mark source input) sender route decode (PqxdhInitialSourceHalf.execution input entry.material.1)
    (input.number.val - 1) qPost postBound).mono (Nat.add_le_add_left checkBound _)
  have callbackBound := callbacks source input qPre qApplication qSelector qAux preBound applicationBound selectorBound auxBound entry
  have uniform := complete_uniform source writer (productionStream source.crypto) entry output
    ((view source).pre input) ((view source).application input) ((view source).initializer (input, entry))
    ((view source).selector input) ((view source).aux input) (costs qPre qApplication qSelector qAux) callbackBound
    RawCtxSelectedLiveRead.labelRead _ (callbackCap qPost qCheck) fullBound
    (initial input.disclosed (PqxdhInitialSourceHalf.execution input entry.material.1) ((input.shared, input.privateState), input.cache) [])
  constructor
  · exact (isQueryBound_map_iff _ _ _ _ _).mpr uniform
  · intro result supported
    simp only [PqxdhInitialHalfSecrecy.observed, support_map] at supported
    obtain ⟨result, supported, rfl⟩ := supported
    have count := trace_length
      (PqxdhInitialHalfObserver.handler source writer (productionStream source.crypto) entry output
        ((view source).pre input) ((view source).application input) ((view source).initializer (input, entry))
        ((view source).selector input) ((view source).aux input) RawCtxSelectedLiveRead.labelRead)
      _ (callbackCap qPost qCheck) fullBound
      (initial input.disclosed (PqxdhInitialSourceHalf.execution input entry.material.1) ((input.shared, input.privateState), input.cache) [])
      result supported
    apply count.trans
    exact Nat.add_le_add_right (by simpa only [initial, PqxdhInitialSourceHalf.execution,
      PqxdhInitialPostContext.knownFront, RawCtxGenericFamilyLive.mapState, List.length_append, List.length_nil, Nat.add_zero] using knownBound) _

end BeaconcryptCore.Computational.PqxdhInitialHalfResources

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfResources.checker_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfResources.checker_total

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfResources.program_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfResources.program_total

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfResources.callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfResources.callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfResources.one_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfResources.one_bounds
