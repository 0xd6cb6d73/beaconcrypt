import BeaconcryptCore.Computational.RawCtxSelectedChain

/-!
The actual decoder retains all76 bytes as key32, next-chain32 and nonce12. Original send and receive resumption can install the next chain as a private unavailable marker while preserving all prior control, staged materials and context. These source laws retain malformed continuation branches and the original full result.

The distribution statements apply to the same explicitly sampled full76 reply. They prove its material and next-chain partition through arbitrary full continuations, with no independent-input premise. The stopped constructor cannot read the chain coordinate. Delaying that coordinate retains the full prior context, material and continued result and does not condition on successful completion. A reached native cut still must be proved to have this earlier hybrid distribution, and permitted prior live disclosures must remain in its exposure event. No fixed-source output uniformity, arbitrary-state freshness, random public HKDF, or global security claim follows. Snapshot, persistence and restoration services are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFreshChainCut
open RawCtxSelectedChain RawCtxChainInterpretation
open PqxdhFullSecretInputKdf PqxdhSecretInputKdf PqxdhOrderedChainHybrids
open BeaconcryptCore.Refinement.RepresentationBridge BeaconcryptCore.Refinement.ProtocolComposition PqxdhRefinement

def concreteChain (value : RootOutput) : RatchetChain :=
  ⟨⟨value.toList.map concreteByte, by simp⟩⟩

def concreteMaterial (value : Material) : RatchetMaterial :=
  ⟨⟨⟨value.1.toList.map concreteByte, by simp⟩⟩,
    ⟨⟨value.2.toList.map concreteByte, by simp⟩⟩⟩

/-- The actual source decoder exposes exactly the same key32/chain32/nonce12 partition for every full reply. -/
theorem decoded_parts (output : FullOutput) :
    RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output) =
      (concreteChain (nextChain output), concreteMaterial (material output)) := by
  have parts := interpretedStep_bytes (fun _ => RawCtxKdfRequestTable.fullResponse output) unusedChain
  refine Prod.ext (absChain_injective ?_) (absMaterial_injective ?_)
  · simpa [RawCtxInterpretedReceive.decodeResponse, interpretedStep, interpretedResponse,
      RawCtxKdfRequestTable.fullResponse, absChain, concreteChain, nextChain,
      PqxdhJointKdf.second32, PqxdhJointKdf.streamBytes, List.Vector.toList, Function.comp_def,
      PqxdhJointKdfGame.JointKdfProjection.project, absBytes, List.map_map] using parts.1
  · simpa [RawCtxInterpretedReceive.decodeResponse, interpretedStep, interpretedResponse,
      RawCtxKdfRequestTable.fullResponse, absMaterial, concreteMaterial, material,
      PqxdhJointKdf.first32, PqxdhJointKdf.final12, PqxdhJointKdf.streamBytes,
      List.Vector.toList, Function.comp_def, PqxdhJointKdfGame.JointKdfProjection.project,
      absBytes, List.map_map] using parts.2

/-- After this same full reply, the source receive resumes with its new chain hidden and every original staged material/control field retained. -/
theorem receive_resume {Context : Type}
    (pending : RawCtxChainReceive.Kdf Slot Slot RatchetMaterial Context) (output : FullOutput) :
    RawCtxInterpretedReceive.normalResume
      (RawCtxChainReceive.nativeKdf (interpret (concreteChain (nextChain output)))
        (interpret (concreteChain (nextChain output))) pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)) =
      RawCtxChainReceive.nativeEffect (interpret (concreteChain (nextChain output)))
        (interpret (concreteChain (nextChain output)))
        (RawCtxChainReceive.normalResume pending (.hidden, concreteMaterial (material output))) := by
  rw [decoded_parts]
  exact RawCtxChainReceive.normalResume_native (interpret (concreteChain (nextChain output)))
    (interpret (concreteChain (nextChain output))) pending (.hidden, concreteMaterial (material output))

/-- The same reply advances source send with a hidden next chain before the actual optional seal. -/
theorem send_resume {Context : Type}
    (pending : RawCtxChainSend.Kdf Slot Slot RatchetMaterial Context) (output : FullOutput) :
    RawCtxInterpretedSend.resume
      (RawCtxChainSend.nativeKdf (interpret (concreteChain (nextChain output)))
        (interpret (concreteChain (nextChain output))) pending)
      (ok (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))) =
      RawCtxChainSend.nativeSeal (interpret (concreteChain (nextChain output)))
        (interpret (concreteChain (nextChain output))) <$>
        RawCtxChainSend.resume pending (ok (.hidden, concreteMaterial (material output))) := by
  rw [decoded_parts]
  simpa only [RawCtxMaterialInterpretation.rust_map_ok, interpret] using RawCtxChainSend.native_resume
    (interpret (concreteChain (nextChain output))) (interpret (concreteChain (nextChain output)))
    pending (ok (.hidden, concreteMaterial (material output)))

/-- The actual uniform full reply supplies a private stopped context and the next secret input; the context constructor cannot inspect its chain coordinate. -/
noncomputable def sampledCut {Context Stopped : Type} (sample : ProbComp Context)
    (stop : Context → RatchetMaterial → Stopped) : ProbComp (Stopped × Pqxdh.Bytes) := do
  let context ← sample
  let output ← $ᵗ FullOutput
  pure (stop context (concreteMaterial (material output)), (nextChain output).toList)

/-- This is the same sampler after partitioning its one full reply, with all prior source context retained. -/
noncomputable def partitionedCut {Context Stopped : Type} (sample : ProbComp Context)
    (stop : Context → RatchetMaterial → Stopped) : ProbComp (Stopped × Pqxdh.Bytes) := do
  let context ← sample
  let value ← $ᵗ Material
  let chain ← $ᵗ RootOutput
  pure (stop context (concreteMaterial value), chain.toList)

/-- Exact full-context equality derives the input distribution from the actual response partition, rather than imposing an independent-input hypothesis. -/
theorem sampledCut_partition {Context Stopped : Type} (sample : ProbComp Context)
    (stop : Context → RatchetMaterial → Stopped) :
    EvalDistEq (sampledCut sample stop) (partitionedCut sample stop) := by
  exact EvalDistEq.bind_right sample (fun context =>
    fullOutput_observed (fun value chain => pure (stop context (concreteMaterial value), chain.toList)))

/-- Typed form used by the concrete selected-chain source game. -/
noncomputable def typedCut {Context Stopped : Type} (sample : ProbComp Context)
    (stop : Context → RatchetMaterial → Stopped) : ProbComp (Stopped × RootOutput) := do
  let context ← sample
  let output ← $ᵗ FullOutput
  pure (stop context (concreteMaterial (material output)), nextChain output)

/-- The typed target is the same source input bytes, not a new secret draw. -/
theorem typedCut_bytes {Context Stopped : Type} (sample : ProbComp Context)
    (stop : Context → RatchetMaterial → Stopped) :
    (fun pair => (pair.1, pair.2.toList)) <$> typedCut sample stop = sampledCut sample stop := by
  simp only [typedCut, sampledCut, map_bind, map_pure]

/-- Retain the target only in analysis while a target-free continuation executes on the actual stopped context. -/
noncomputable def observedCut {Context Stopped Result : Type} (sample : ProbComp Context)
    (stop : Context → RatchetMaterial → Stopped) (observe : Stopped → ProbComp Result) :
    ProbComp (RootOutput × Result) := do
  let (context, target) ← typedCut sample stop
  let result ← observe context
  pure (target, result)

/-- Draw-order form for measuring all adaptive known-value candidates without revealing the selected input. -/
noncomputable def delayedCut {Context Stopped Result : Type} (sample : ProbComp Context)
    (stop : Context → RatchetMaterial → Stopped) (observe : Stopped → ProbComp Result) :
    ProbComp (RootOutput × Result) := do
  let context ← sample
  let value ← $ᵗ Material
  let result ← observe (stop context (concreteMaterial value))
  let target ← $ᵗ RootOutput
  pure (target, result)

/-- The complete original prior state, material and continued result survive delaying only the independent second32 coordinate. -/
theorem observedCut_delayed {Context Stopped Result : Type} (sample : ProbComp Context)
    (stop : Context → RatchetMaterial → Stopped) (observe : Stopped → ProbComp Result) :
    EvalDistEq (observedCut sample stop observe) (delayedCut sample stop observe) := by
  simp only [observedCut, typedCut, delayedCut, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right sample (fun context => ?_)
  refine (fullOutput_observed (fun value target => do
    let result ← observe (stop context (concreteMaterial value)); pure (target, result))).trans ?_
  exact EvalDistEq.bind_right ($ᵗ Material) (fun value =>
    evalSPMF_sample_comm ($ᵗ RootOutput) (observe (stop context (concreteMaterial value)))
      (fun target result => pure (target, result)))

end BeaconcryptCore.Computational.RawCtxFreshChainCut

/-- info: 'BeaconcryptCore.Computational.RawCtxFreshChainCut.decoded_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFreshChainCut.decoded_parts

/-- info: 'BeaconcryptCore.Computational.RawCtxFreshChainCut.receive_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFreshChainCut.receive_resume

/-- info: 'BeaconcryptCore.Computational.RawCtxFreshChainCut.send_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFreshChainCut.send_resume

/-- info: 'BeaconcryptCore.Computational.RawCtxFreshChainCut.sampledCut_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFreshChainCut.sampledCut_partition

/-- info: 'BeaconcryptCore.Computational.RawCtxFreshChainCut.typedCut_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFreshChainCut.typedCut_bytes

/-- info: 'BeaconcryptCore.Computational.RawCtxFreshChainCut.observedCut_delayed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFreshChainCut.observedCut_delayed
