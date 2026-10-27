import BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder
import BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder
import BeaconcryptCore.Computational.RawCtxInitialSentinelSampler

/-!
A single supplied64-byte initializer response enters the actual current Server builder after its original admission callbacks and before its first ciphertext. Either selected directional half is represented by a hidden label; the opposite half remains known, and the original zero-state constructor is retained. No source initializer nonce or independent second directional draw is added.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialGenericProtocol PqxdhInitialGenericProtocolBuilder RawCtxInitialSentinelSampler
variable {M P I D K A : Type} {S B : Nat}

/-- The actual typed64 reply gives the exact nonce-free selected-half constructor for either role and either direction. -/
theorem kernel_response (role second : Bool) (other target : RootOutput) :
    PqxdhInitialReplyErasure.kernelOf role
      (RawCtxSelectedInitialConstructor.response64 (join second other target)) =
      RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) <$>
        labelInitial second role other := by
  exact constructor (role, ⟨List.replicate 32 0#u8, by simp⟩) second other target

/-- The original initializer service is consumed at its actual source location, and its complete first-send builder result equals the hidden-half builder under the native full-state interpretation. -/
theorem supplied_build (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (second : Bool) (other target : RootOutput)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : State RawCtxSelectedChain.Kernel M P I D K A S B) :
    simulateQ (PqxdhInitialReplyErasure.supplied (RawCtxSelectedInitialConstructor.response64 (join second other target)))
      ((PqxdhInitialPrivateBuilder.protocolBuild source writer (retainedKdf prior entry target)
        aux sender index metadata ready).run
        (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state)) =
      Prod.map id (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (build source (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)) aux (labelInitial second false other)
          sender index metadata (PqxdhInitialBuilderCut.eraseRoot ready)).run state := by
  rw [PqxdhInitialPrivateBuilder.protocol_supplied, kernel_response, selected_build]

/-- The current labelled root/initializer service preserves its full private root cache and complete first-send result when the selected initial half is represented before the send. -/
theorem labelled_build (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (second : Bool) (other target : RootOutput)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (selected : PqxdhCorrelatedExtractFamily.Message) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : State RawCtxSelectedChain.Kernel M P I D K A S B)
    (cache : PqxdhCorrelatedExpand.RootOracle.QueryCache) :
    (simulateQ (PqxdhInitialRootLabelService.labelledFull source (QueryImpl.ofLift unifSpec ProbComp) selected
      (RawCtxSelectedInitialConstructor.response64 (join second other target)))
      (PqxdhInitialPrivateBuilder.build source writer (retainedKdf prior entry target) aux sender index metadata selected ready
        (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state))).run cache =
      (fun result => (Prod.map id (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) result, cache)) <$>
        (build source (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)) aux (labelInitial second false other)
          sender index metadata (PqxdhInitialBuilderCut.eraseRoot ready)).run state := by
  rw [PqxdhInitialPrivateBuilder.build_response, kernel_response, selected_build, Functor.map_map]

def knownKernel (kernel : ConcreteRatchetKernel) : RawCtxSelectedChain.Kernel :=
  RawCtxChainInterpretation.mapChains RawCtxSelectedChain.Slot.known RawCtxSelectedChain.Slot.known kernel.refined

/-- Retaining every preexisting native chain as known reconstructs the original entire kernel for every later selected half. -/
theorem known_kernel (target : RootOutput) (kernel : ConcreteRatchetKernel) :
    RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) (knownKernel kernel) = kernel := by
  simp only [RawCtxSelectedChain.nativeKernel, knownKernel, RawCtxChainInterpretation.mapChains,
    RawCtxSelectedChain.interpret]

/-- The complete pre-initializer state can be represented before the fresh half is sampled, without target-dependent rebasing or loss of any preexisting role or history. -/
theorem known_state (target : RootOutput) (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))
      (fromNative knownKernel state) = state :=
  roundtrip knownKernel _ (known_kernel target) state

/-- The actual original pre-initializer source state enters the selected-half builder through a target-independent representation, before its original first send. -/
theorem supplied_known (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (second : Bool) (other target : RootOutput)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    simulateQ (PqxdhInitialReplyErasure.supplied (RawCtxSelectedInitialConstructor.response64 (join second other target)))
      ((PqxdhInitialPrivateBuilder.protocolBuild source writer (retainedKdf prior entry target)
        aux sender index metadata ready).run state) =
      Prod.map id (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (build source (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)) aux (labelInitial second false other)
          sender index metadata (PqxdhInitialBuilderCut.eraseRoot ready)).run (fromNative knownKernel state) := by
  simpa only [known_state] using supplied_build source writer prior entry second other target aux sender index metadata ready
    (fromNative knownKernel state)

end BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.kernel_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.kernel_response

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.supplied_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.supplied_build

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.labelled_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.labelled_build

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.known_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.known_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.known_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.known_state

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.supplied_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder.supplied_known
