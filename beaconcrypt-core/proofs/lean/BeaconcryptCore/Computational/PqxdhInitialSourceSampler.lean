import BeaconcryptCore.Computational.PqxdhInitialSentinelSource
import BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds

/-!
The actual uniform64 initializer and its complete current Server first-send continuation are compared with one full76 analysis draw. Both orientations retain the opposite directional half, the exact original response and every builder poststate field. The comparison's extra12 bytes never enter a source initializer or source cache; the two literal draw costs are stated separately. The target remains private to this mathematical source interpretation, not an executable reduction input.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceSampler
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxInitialSentinelSampler
variable {M P I D K A Context Result : Type} {S B : Nat}

structure Input (M P I D K A : Type) (S B : Nat) where
  index : Fin S
  metadata : P
  ready : PqxdhPrivateAcceptedRoot.Ready
  state : PqxdhRegistrationProtocolState.State M P I D K A S B
  second : Bool

abbrev Built (M P I D K A : Type) (S B : Nat) :=
  RustM (Option PqxdhServerRegistrationPublication.Response) × PqxdhRegistrationProtocolState.State M P I D K A S B

noncomputable def sourceBuilder (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (input : Input M P I D K A S B) (output : HmacBlock) : ProbComp (Built M P I D K A S B) :=
  simulateQ (PqxdhInitialReplyErasure.supplied (RawCtxSelectedInitialConstructor.response64 output))
    ((PqxdhInitialServiceBuilder.protocolBuild source writer aux sender input.index input.metadata input.ready).run input.state)

noncomputable def selectedBuilder (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (input : Input M P I D K A S B) (other target : RootOutput) (extra : NonceOutput) :
    ProbComp (Built M P I D K A S B) :=
  Prod.map id (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
    (PqxdhInitialGenericProtocolBuilder.build source
      (RawCtxSelectedParentCalls.labelCalls source writer (PqxdhJointKdf.productionStream source.crypto)
        (RawCtxInitialSentinel.entry other extra)
        (RawCtxSelectedParentCalls.childResponse (PqxdhJointKdf.productionStream source.crypto) (RawCtxInitialSentinel.entry other extra) target))
      aux (labelInitial input.second false other) sender input.index input.metadata
      (PqxdhInitialBuilderCut.eraseRoot input.ready)).run
        (PqxdhInitialGenericProtocol.fromNative PqxdhInitialSelectedBuilder.knownKernel input.state)

/-- The actual source64 response and entire first-send result agree with the private selected-half interpretation for any analysis-only extra bytes. -/
theorem source_halves (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (input : Input M P I D K A S B) (other target : RootOutput) (extra : NonceOutput) :
    sourceBuilder source writer aux sender input (join input.second other target) =
      selectedBuilder source writer aux sender input other target extra :=
  PqxdhInitialSentinelSource.supplied_source source writer input.second other target extra aux sender input.index input.metadata input.ready input.state

/-- The whole evaluated continuation, including the original64 response and all private/public builder poststate, preserves one shared directional draw under either adaptively selected orientation. -/
theorem full_continuation (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : ProbComp Context) (input : Context → Input M P I D K A S B)
    (aux : Context → QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (next : Context → HmacBlock → Built M P I D K A S B → ProbComp Result) :
    𝒮[(do let context ← prior
          let output ← $ᵗ HmacBlock
          let result ← sourceBuilder source writer (aux context) sender (input context) output
          next context output result)] =
      𝒮[(do let context ← prior
            let output ← $ᵗ FullOutput
            let result ← selectedBuilder source writer (aux context) sender (input context)
              (PqxdhOrderedChainHybrids.material output).1 (PqxdhOrderedChainHybrids.nextChain output)
              (PqxdhOrderedChainHybrids.material output).2
            next context (join (input context).second (PqxdhOrderedChainHybrids.material output).1
              (PqxdhOrderedChainHybrids.nextChain output)) result)] := by
  apply evalSPMF_bind_congr' prior
  intro context
  have halves := initial_observed (input context).second
    (fun other target => do
      let result ← sourceBuilder source writer (aux context) sender (input context) (join (input context).second other target)
      next context (join (input context).second other target) result)
  simp only [join_parts] at halves
  refine halves.trans (evalSPMF_bind_congr' ($ᵗ FullOutput) (fun output => ?_))
  rw [source_halves source writer (aux context) sender (input context) _ _ (PqxdhOrderedChainHybrids.material output).2]

/-- The literal actual source builder pays its derived one-commitment plus five-auxiliary-call bill for every supplied64 response. -/
theorem source_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (qAux : Nat) (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (sender : M → Std.U64) (input : Input M P I D K A S B) (output : HmacBlock) :
    (sourceBuilder source writer aux sender input output).IsTotalQueryBound (64 + 5 * qAux) := by
  unfold sourceBuilder
  rw [PqxdhInitialSuppliedBuilder.protocol_supplied]
  exact PqxdhInitialBuilderQueryBounds.protocol_uniform source writer _ aux qAux auxBound sender input.index input.metadata _ input.state

/-- The selected mathematical builder has the same literal primitive program by the proved typed-source equality; this bound does not use an evaluated distribution equation. -/
theorem selected_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (qAux : Nat) (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (sender : M → Std.U64) (input : Input M P I D K A S B) (other target : RootOutput) (extra : NonceOutput) :
    (selectedBuilder source writer aux sender input other target extra).IsTotalQueryBound (64 + 5 * qAux) := by
  rw [← source_halves]
  exact source_uniform source writer aux qAux auxBound sender input _

set_option maxRecDepth 2048 in
/-- The two literal source/comparison programs pay64 versus76 sampler bytes, all actual builder work and the complete outside continuation separately. -/
theorem execution_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : ProbComp Context) (input : Context → Input M P I D K A S B)
    (aux : Context → QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (next : Context → HmacBlock → Built M P I D K A S B → ProbComp Result)
    (qPrior qAux qNext : Nat) (priorBound : prior.IsTotalQueryBound qPrior)
    (auxBound : ∀ context query primitive, (((aux context) query).run primitive).IsTotalQueryBound qAux)
    (nextBound : ∀ context output state, (next context output state).IsTotalQueryBound qNext) :
    (do let context ← prior
        let output ← $ᵗ HmacBlock
        let result ← sourceBuilder source writer (aux context) sender (input context) output
        next context output result).IsTotalQueryBound (qPrior + (64 + ((64 + 5 * qAux) + qNext))) ∧
      (do let context ← prior
          let output ← $ᵗ FullOutput
          let result ← selectedBuilder source writer (aux context) sender (input context)
            (PqxdhOrderedChainHybrids.material output).1 (PqxdhOrderedChainHybrids.nextChain output)
            (PqxdhOrderedChainHybrids.material output).2
          next context (join (input context).second (PqxdhOrderedChainHybrids.material output).1
            (PqxdhOrderedChainHybrids.nextChain output)) result).IsTotalQueryBound
        (qPrior + (76 + ((64 + 5 * qAux) + qNext))) := by
  constructor
  · exact isTotalQueryBound_bind priorBound (fun context =>
      isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) (fun output =>
        isTotalQueryBound_bind (source_uniform source writer (aux context) qAux (auxBound context) sender (input context) output)
          (fun state => nextBound context output state)))
  · exact isTotalQueryBound_bind priorBound (fun context =>
      isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) (fun output =>
        isTotalQueryBound_bind (selected_uniform source writer (aux context) qAux (auxBound context) sender (input context)
          (PqxdhOrderedChainHybrids.material output).1 (PqxdhOrderedChainHybrids.nextChain output)
          (PqxdhOrderedChainHybrids.material output).2) (fun state => nextBound context _ state)))

end BeaconcryptCore.Computational.PqxdhInitialSourceSampler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSampler.source_halves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSampler.source_halves

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSampler.full_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSampler.full_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSampler.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSampler.source_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSampler.selected_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSampler.selected_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSampler.execution_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSampler.execution_queries
