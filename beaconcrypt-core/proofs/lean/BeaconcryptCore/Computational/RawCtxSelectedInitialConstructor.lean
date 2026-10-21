import BeaconcryptCore.Computational.RawCtxSelectedInitialSampler

/-!
The actual64-byte source initializer installs two oppositely oriented chains and no initialization nonce. Its private first32-hidden constructor retains the other32 bytes, zero counters, empty cache slots and complete RustM result. A full76 analysis response enters only through its exact shared64-byte prefix; no source call or nonce draw is added. The complete uniform64 law will preserve arbitrary continuations and both role orientations without exposing the first32 coordinate through the retained constructor.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor
open RawCtxSelectedChain RawCtxChainInterpretation RawCtxSelectedInitialEntry
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialRatchetComplementarity PqxdhRefinement

/-- The original source consumes exactly this64-byte response wrapper. -/
def response64 (output : HmacBlock) : pqxdh.concrete.InitialRatchetKdfResponse :=
  ⟨⟨output.toList.map BeaconcryptCore.Refinement.ProtocolComposition.concreteByte, by simp⟩⟩

def from64 (request : RawCtxInitializedKdfFamily.InitialRequest) (output : HmacBlock) : RustM ConcreteRatchetKernel :=
  pqxdh.concrete.resume_initial_ratchet_kdf
    (if request.1 then beaconPending request.2 else serverPending request.2) (response64 output)

def sendSlot (beacon : Bool) (other : RootOutput) : Slot :=
  if beacon then .known (RawCtxFreshChainCut.concreteChain other) else .hidden

def receiveSlot (beacon : Bool) (other : RootOutput) : Slot :=
  if beacon then .hidden else .known (RawCtxFreshChainCut.concreteChain other)

def initial (beacon : Bool) (other : RootOutput) : RustM Kernel :=
  RefinedRatchet.new RatchetMaterial (sendSlot beacon other) (receiveSlot beacon other)

/-- Both32-byte halves are exactly the original consumed response bytes. -/
theorem halves64 (target other : RootOutput) :
    ChainBytesRefines (RawCtxFreshChainCut.concreteChain target) (firstHalf (response64 (target ++ other)).bytes) ∧
    ChainBytesRefines (RawCtxFreshChainCut.concreteChain other) (secondHalf (response64 (target ++ other)).bytes) := by
  simp [ChainBytesRefines, firstHalf, secondHalf, response64, RawCtxFreshChainCut.concreteChain,
    PqxdhRefinement.absBytes, List.map_map, Function.comp_def]
  change target.toList = (target.toList ++ other.toList).take 32 ∧
    other.toList = (target.toList ++ other.toList).drop 32
  simp

/-- The original zero-counter/empty-slot constructor commutes with the private chain map and preserves its entire RustM result. -/
theorem new_map (target : RatchetChain) (send receive : Slot) :
    ConcreteRatchetKernel.new (interpret target send) (interpret target receive) =
      nativeKernel target <$> RefinedRatchet.new RatchetMaterial send receive := by
  simp only [ConcreteRatchetKernel.new, ConcreteRatchetKernel.from_counters, RefinedRatchet.new,
    RefinedRatchet.from_counters, map_bind, bind_assoc]
  congr 1

/-- The exact extracted split chooses opposite directions from the same64-byte output for Beacon and Server. -/
theorem split64 (request : RawCtxInitializedKdfFamily.InitialRequest) (target other : RootOutput) :
    pqxdh.split_initial_ratchet_kdf_output (response64 (target ++ other)).bytes
      (if request.1 then (beaconPending request.2).initialization else (serverPending request.2).initialization) =
    ok ⟨interpret (RawCtxFreshChainCut.concreteChain target) (sendSlot request.1 other),
      interpret (RawCtxFreshChainCut.concreteChain target) (receiveSlot request.1 other)⟩ := by
  rcases request with ⟨role, root⟩
  cases role with
  | false =>
    obtain ⟨left, right, split, hleft, hright⟩ := splitInitialServer_exact (response64 (target ++ other)).bytes
    simpa only [chain_eq_of_refines hleft (halves64 target other).1,
      chain_eq_of_refines hright (halves64 target other).2,
      sendSlot, receiveSlot, Bool.false_eq_true, ite_false, serverPending, interpret] using split
  | true =>
    obtain ⟨left, right, split, hleft, hright⟩ := splitInitialBeacon_exact (response64 (target ++ other)).bytes
    simpa only [chain_eq_of_refines hleft (halves64 target other).2,
      chain_eq_of_refines hright (halves64 target other).1,
      sendSlot, receiveSlot, ite_true, beaconPending, interpret] using split

/-- The actual64-byte initializer is exactly the first32-hidden zero-state constructor, with no source nonce. -/
theorem from64_initial (request : RawCtxInitializedKdfFamily.InitialRequest) (target other : RootOutput) :
    from64 request (target ++ other) =
      nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initial request.1 other := by
  have split := split64 request target other
  rcases request with ⟨role, root⟩
  cases role <;> simp only [from64, Bool.false_eq_true, ite_false, ite_true,
    pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition] at split ⊢
  all_goals rw [split, bind_tc_ok, new_map]
  all_goals rfl

/-- A full76 analysis response contributes exactly its shared64-byte prefix to the original initializer. -/
theorem full_prefix (request : RawCtxInitializedKdfFamily.InitialRequest) (output : FullOutput) :
    from64 request (initialPrefix output) = RawCtxInitializedKdfFamily.initialProject request output := by
  rfl

/-- The retained full76 entry initializes only the selected first32 and other directional32, irrespective of its analysis nonce. -/
theorem full_initial (request : RawCtxInitializedKdfFamily.InitialRequest) (entry : Entry) (target : RootOutput) :
    RawCtxInitializedKdfFamily.initialProject request (realize entry target) =
      nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initial request.1 entry.otherChain := by
  rw [← full_prefix, initial_prefix, from64_initial]

/-- The actual fixed-source64 initializer supplies exactly this complete hidden-first constructor in either role. -/
theorem source_initial (source : FixedHkdfSha512NoSaltSource) (request : RawCtxInitializedKdfFamily.InitialRequest) :
    RawCtxInitializedKdfFamily.initialReply source request =
      nativeKernel (RawCtxFreshChainCut.concreteChain (JointKdfProjection.first32.project
        (productionStream source.crypto (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)))) <$>
      initial request.1 (fromOutput (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)
        (productionStream source.crypto (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩))).otherChain := by
  rw [← RawCtxInitializedKdfFamily.initial_projection]
  simpa only [realize_fromOutput] using full_initial request
    (fromOutput (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)
      (productionStream source.crypto (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)))
    (JointKdfProjection.first32.project
      (productionStream source.crypto (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)))

/-- The same pair of chain values has opposite source orientation in the two roles; no independent second draw is introduced. -/
theorem opposite_roles (other : RootOutput) :
    sendSlot false other = receiveSlot true other ∧ sendSlot true other = receiveSlot false other := by
  exact ⟨rfl, rfl⟩

/-- The two initial halves reconstruct every byte of the exact original64-byte response. -/
theorem split_reconstruct (output : HmacBlock) :
    PqxdhSecretInputKdf.first32 output ++ RawCtxSelectedInitialSampler.initialOther output = output := by
  exact (vectorSplitEquiv 32 32).symm_apply_apply output

/-- The complete64-byte draw supplies both directional chains before the same full continuation, preserving all prior context. -/
theorem uniform_native {Context Result : Type} (sample : ProbComp Context)
    (request : Context → RawCtxInitializedKdfFamily.InitialRequest)
    (observe : Context → HmacBlock → RustM ConcreteRatchetKernel → ProbComp Result) :
    EvalDistEq
      (do let context ← sample
          let output ← $ᵗ HmacBlock
          observe context output (from64 (request context) output))
      (do let context ← sample
          let other ← $ᵗ RootOutput
          let target ← $ᵗ RootOutput
          observe context (target ++ other)
            (nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initial (request context).1 other)) := by
  refine EvalDistEq.bind_right sample (fun context => ?_)
  simpa only [split_reconstruct, from64_initial] using
    RawCtxSelectedInitialSampler.initial_observed (fun other target =>
      observe context (target ++ other) (from64 (request context) (target ++ other)))

set_option maxRecDepth 2048 in
/-- The literal initial64 execution charges its complete prior sampler,64-byte draw and original initializer continuation. -/
theorem uniform_native_bound {Context Result : Type} (sample : ProbComp Context)
    (request : Context → RawCtxInitializedKdfFamily.InitialRequest)
    (observe : Context → HmacBlock → RustM ConcreteRatchetKernel → ProbComp Result)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output kernel, (observe context output kernel).IsTotalQueryBound qObserve) :
    (do let context ← sample
        let output ← $ᵗ HmacBlock
        observe context output (from64 (request context) output)).IsTotalQueryBound (qSample + (64 + qObserve)) := by
  exact isTotalQueryBound_bind sampleBound fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
      fun output => observeBound context output _

/-- After the same initial64 split, the concrete private constructor can run before drawing only its omitted first32 coordinate. -/
theorem delayed_initial {Context Result : Type} (sample : ProbComp Context)
    (role : Context → Bool) (observe : Context → RustM Kernel → ProbComp Result) :
    EvalDistEq
      (do let context ← sample
          let output ← $ᵗ HmacBlock
          let result ← observe context (initial (role context) (RawCtxSelectedInitialSampler.initialOther output))
          pure (PqxdhSecretInputKdf.first32 output, result))
      (do let context ← sample
          let other ← $ᵗ RootOutput
          let result ← observe context (initial (role context) other)
          let target ← $ᵗ RootOutput
          pure (target, result)) := by
  exact RawCtxSelectedInitialSampler.initial_delayed_eq sample
    (fun context other => observe context (initial (role context) other))

end BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.halves64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.halves64

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.new_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.new_map

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.split64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.split64

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.from64_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.from64_initial

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.full_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.full_prefix

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.full_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.full_initial

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.source_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.source_initial

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.opposite_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.opposite_roles

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.split_reconstruct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.split_reconstruct

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.uniform_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.uniform_native

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.uniform_native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.uniform_native_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.delayed_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor.delayed_initial
