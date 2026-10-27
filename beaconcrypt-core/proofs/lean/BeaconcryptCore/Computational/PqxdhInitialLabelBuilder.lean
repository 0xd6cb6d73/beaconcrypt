import BeaconcryptCore.Computational.PqxdhInitialLabelPost
import BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder

/-!
The actual Server registration builder uses a selected root-family label at its original initializer position. Its executable Ready context is root-erased before any callback. Identity checks, reservation, first-send work, publication and full consumed-registration state keep their original order. The supplied response is interpreted only at the one private initializer callback; it does not replace public HKDF or move source effects across gates.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialLabelBuilder
open PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialRootLabelService PqxdhInitialReplyErasure
variable {Result M P I D K A : Type} {S B : Nat}

def compiler (selected : Message) : QueryImpl PqxdhInitialServiceBuilder.RunSpec (OracleComp PqxdhInitialLabelCompiler.Spec)
  | .inl query => PqxdhInitialLabelCompiler.Spec.query (.inl query)
  | .inr _ => PqxdhInitialLabelCompiler.Spec.query (.inr (.family selected))

set_option backward.isDefEq.respectTransparency false in
/-- Interpreting the selected-coordinate compiler supplies the same response at every actual builder initializer request and preserves its complete ordinary computation and root cache. -/
theorem response_program (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (response : PqxdhInitialRootLabelService.Response)
    (work : OracleComp PqxdhInitialServiceBuilder.RunSpec Result) (cache : RootOracle.QueryCache) :
    (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (simulateQ (compiler selected) work)).run cache =
      (fun result => (result, cache)) <$> simulateQ (supplied response) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, compiler, StateT.run_bind]
          change (do let answer ← (unifSpec.query query : ProbComp _)
                     (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
                       (simulateQ (compiler selected) (next answer))).run cache) = _
          simp only [ih, map_bind]
          rfl
      | inr request =>
          simp only [simulateQ_bind, simulateQ_spec_query, compiler, StateT.run_bind,
            labelledFull, QueryImpl.add_apply_inr, pure_bind, supplied]
          rw [PqxdhInitialRootLabelService.selected_reply fixed selected response cache, pure_bind]
          exact ih response

noncomputable def build (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :=
  simulateQ (compiler selected)
    ((PqxdhInitialServiceBuilder.protocolBuild fixed writer aux sender index metadata
      (PqxdhInitialBuilderCut.eraseRoot ready)).run state)

/-- Changing only the supplied Ready root cannot change any executable compiled builder operation or continuation. -/
theorem root_unused (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    build fixed writer aux sender index metadata selected { ready with root := root } state =
      build fixed writer aux sender index metadata selected ready state := rfl

/-- The actual root-erased compiled Server builder consumes the supplied response after its original checks and preserves first-send work and the complete protocol/shared result and root cache. -/
theorem build_response (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : PqxdhRegistrationProtocolState.State M P I D K A S B)
    (response : PqxdhInitialRootLabelService.Response) (cache : RootOracle.QueryCache) :
    (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (build fixed writer aux sender index metadata selected ready state)).run cache =
      (fun result => (result, cache)) <$>
        (PqxdhInitialBuilderCut.protocolBuild fixed writer (kernelOf false response) aux sender index metadata
          (PqxdhInitialBuilderCut.eraseRoot ready)).run state := by
  rw [build, response_program, PqxdhInitialSuppliedBuilder.protocol_supplied]
  rfl

/-- The response-only Server kernel at a real initializer reply is exactly the original fixed-source initializer, despite the erased Ready root. -/
theorem kernel_source (fixed : FixedHkdfSha512NoSaltSource) (root : PqxdhSecretInputKdf.RootOutput) :
    kernelOf false (realInitial fixed root) = PqxdhRootTableInitialization.initialKernelRun fixed false root := by
  simp only [PqxdhRootTableInitialization.initialKernelRun,
    BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeServer_eq]
  exact kernel_root_unused false (List.Vector.replicate 32 0) root (realInitial fixed root)

/-- At the actual real initializer reply, the root-erased executable builder has the exact original full registration build result, preserving the complete root cache. -/
theorem build_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : PqxdhRegistrationProtocolState.State M P I D K A S B)
    (cache : RootOracle.QueryCache) :
    (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected (realInitial fixed ready.root))
      (build fixed writer aux sender index metadata selected ready state)).run cache =
      (fun result => (result, cache)) <$>
        (PqxdhRegistrationProtocolState.build fixed writer aux sender index metadata ready).run state := by
  rw [build_response, kernel_source, PqxdhInitialBuilderCut.protocol_erased_source]

end BeaconcryptCore.Computational.PqxdhInitialLabelBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.response_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.response_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.build_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.build_response

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.kernel_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.kernel_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelBuilder.build_source
