import BeaconcryptCore.Computational.PqxdhInitialGenericBuilder
import BeaconcryptCore.Computational.PqxdhInitialGenericProtocol
import BeaconcryptCore.Computational.PqxdhInitialPrivateKdf

/-!
The complete current protocol builder carries a private kernel representation before its first send. Actual registration consumption, current peer selection, admission, publication, every other role, reveal history and shared primitive state are retained. The concrete retained-table specialization discharges the native send equation; its private target is confined to the interpretation, not an executable label kernel.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder
open PqxdhJointKdfGame PqxdhInitialGenericProtocol
variable {Kernel M P I D K A : Type} {S B : Nat}

noncomputable def build (source : FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (initial : RustM Kernel) (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (State Kernel M P I D K A S B) ProbComp (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun state =>
  let current := consume index ready state
  let input := selected senderId index current
  reinstall index current <$>
    (PqxdhInitialGenericBuilder.readyBuild source calls aux initial
      ⟨input.server.identity, input.identityKeyId⟩ ready metadata input).run current.primitive

/-- The complete original private-KDF builder is obtained by interpreting only the private kernel representation, including all failure and publication branches. -/
theorem build_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (interpret : Kernel → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sendRealized : ∀ entry context,
      simulateQ ((RawCtxMixedShared.sharedImpl source.crypto writer kdf ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (initial : RustM Kernel) (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : State Kernel M P I D K A S B) :
    (PqxdhInitialPrivateKdf.build source writer kdf (interpret <$> initial) aux senderId index metadata ready).run
      (native interpret state) =
      Prod.map id (native interpret) <$> (build source calls aux initial senderId index metadata ready).run state := by
  unfold PqxdhInitialPrivateKdf.build build
  simp only [StateT.run, ← consume_native, ← selected_native interpret senderId index metadata]
  change PqxdhRegistrationProtocolState.reinstall index (native interpret (consume index ready state)) <$>
    (simulateQ (PqxdhInitialGenericPublication.nativeImpl (RawCtxMixedShared.sharedImpl source.crypto writer kdf) aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhInitialBuilderCut.readyBuild source (interpret <$> initial)
          ⟨(selected senderId index (consume index ready state)).server.identity,
            (selected senderId index (consume index ready state)).identityKeyId⟩ ready metadata
          (PqxdhInitialGenericPublication.native interpret (selected senderId index (consume index ready state)))))).run
      (consume index ready state).primitive = _
  rw [PqxdhInitialGenericBuilder.ready_native source interpret calls _ aux sendRealized]
  simp only [StateT.run_map, Functor.map_map]
  simp only [← reinstall_native]
  rfl

noncomputable def retainedKdf (prior : RawCtxSelectedParentTable.Prior)
    (entry : RawCtxSelectedParentEntry.Entry) (target : PqxdhSecretInputKdf.RootOutput) :
    QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  fun request => pure (RawCtxSelectedParentSource.response prior entry target request)

/-- The retained private response handler is exactly the same original complete shared primitive backend; only private record derivation responses change. -/
theorem retained_backend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput) :
    RawCtxSelectedParentNativeBackend.backend (Auxiliary := A) source writer prior entry target =
      RawCtxMixedShared.sharedImpl source.crypto writer (retainedKdf prior entry target) := by
  funext query
  rcases query with request | (sealing | (opening | (bytes | frame)))
  all_goals simp [RawCtxSelectedParentNativeBackend.backend, RawCtxSourceMaterialLabels.nativeImpl,
    RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, QueryImpl.compose,
    OracleSpec.query]
  all_goals rfl

/-- The concrete retained-table execution discharges the complete current protocol builder equation without a supplied send-compatibility premise. -/
theorem selected_build (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (initial : RustM RawCtxSelectedChain.Kernel) (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : State RawCtxSelectedChain.Kernel M P I D K A S B) :
    (PqxdhInitialPrivateKdf.build source writer (retainedKdf prior entry target)
      (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initial)
      aux senderId index metadata ready).run
      (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state) =
      Prod.map id (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (build source (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)) aux initial senderId index metadata ready).run state := by
  apply build_native
  intro kernel context
  rw [← retained_backend]
  exact PqxdhInitialGenericPublication.selected_send source writer prior entry target kernel context

/-- After a typed initializer is supplied, the complete generic current builder has no dependency on the Ready root, including consumed-state updates and publication. -/
theorem root_unused (source : FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (initial : RustM Kernel) (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput) :
    build (I := I) (D := D) (K := K) (B := B) source calls aux initial senderId index metadata {ready with root := root} =
      build source calls aux initial senderId index metadata ready := rfl

end BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder.build_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder.build_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder.retained_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder.retained_backend

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder.selected_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder.selected_build

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder.root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder.root_unused
