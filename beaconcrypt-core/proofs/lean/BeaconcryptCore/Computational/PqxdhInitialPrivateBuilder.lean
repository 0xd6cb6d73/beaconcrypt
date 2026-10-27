import BeaconcryptCore.Computational.PqxdhInitialPrivateKdf
import BeaconcryptCore.Computational.PqxdhInitialLabelBuilder

/-!
The original initializer service keeps its identity/reservation gates and entire first-send continuation while exposing the same private KDF interpreter used by later records. At the default fixed KDF this is exactly the current labelled Server builder. Supplying a64-byte response retains the handler before first sealing and preserves every source state field.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder
open PqxdhServerRegistrationPublication PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialResponseService PqxdhInitialReplyErasure
open PqxdhInitialRootLabelService PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpand
open PqxdhInitialServiceBuilder (BuilderSpec RunSpec readyBuild)
variable {M P I D K A Result : Type} {S B : Nat}

noncomputable def tailImpl (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    QueryImpl BuilderSpec (StateT (RawCtxSharedPrimitive.SharedState A) (OracleComp RunSpec))
  | .inl query => fun state => simulateQ original
      ((simulateQ (PqxdhInitialPrivateKdf.registration fixed writer kdf aux) (nativeAdapter query)).run state)
  | .inr request => fun state => do
      let response ← initial request
      pure (response, state)


noncomputable def protocolBuild
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) (OracleComp RunSpec)
      (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun state =>
  let current := PqxdhRegistrationProtocolState.consume index ready state
  let selected := PqxdhRegistrationProtocolState.input senderId index metadata current
  PqxdhRegistrationProtocolState.reinstall index current <$>
    (simulateQ (tailImpl fixed writer kdf aux) (readyBuild fixed selected.binding ready metadata selected.state)).run current.primitive


/-- The default private record handler gives exactly the actual initializer-service builder, before all original first-send work. -/
theorem protocol_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    protocolBuild (I := I) (D := D) (K := K) (B := B) fixed writer (RawCtxSourceHkdf.kdfImpl fixed)
      aux senderId index metadata ready =
      PqxdhInitialServiceBuilder.protocolBuild fixed writer aux senderId index metadata ready := rfl

/-- The fixed reply interpretation preserves each original builder primitive callback, complete shared state and original random coins. -/
theorem tail_supplied (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (query : PqxdhInitialServiceBuilder.BuilderSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A) :
    simulateQ (supplied response) ((tailImpl fixed writer kdf aux query).run state) =
      (simulateQ (PqxdhInitialPrivateKdf.registration fixed writer kdf aux ∘ₛ nativeAdapter)
        (supplied response query)).run state := by
  cases query with
  | inl query =>
      rw [tailImpl, StateT.run, PqxdhInitialReplyErasure.original_program]
      simp [supplied, QueryImpl.compose, OracleSpec.query]
  | inr request =>
      simp [tailImpl, StateT.run, initial, supplied, OracleSpec.query]
      rfl


/-- The entire stateful builder tail, including every failure and public reply, uses the same response substitution and complete shared-state interpreter. -/
theorem tail_program (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (work : OracleComp PqxdhInitialServiceBuilder.BuilderSpec Result) (state : RawCtxSharedPrimitive.SharedState A) :
    simulateQ (supplied response) ((simulateQ (tailImpl fixed writer kdf aux) work).run state) =
      (simulateQ (PqxdhInitialPrivateKdf.registration fixed writer kdf aux ∘ₛ nativeAdapter)
        (simulateQ (supplied response) work)).run state := by
  rw [← QueryImpl.simulateQ_compose]
  exact simulateQ_StateT_compose (tailImpl fixed writer kdf aux) (supplied response)
    ((PqxdhInitialPrivateKdf.registration fixed writer kdf aux ∘ₛ nativeAdapter) ∘ₛ supplied response)
    (tail_supplied fixed writer response kdf aux) work state


/-- The current complete Server builder with its supplied64 reply runs from the root-erased Ready context while preserving every other field, first send and full protocol/shared poststate. -/
theorem protocol_supplied (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    simulateQ (supplied response) ((protocolBuild fixed writer kdf aux senderId index metadata ready).run state) =
      (PqxdhInitialPrivateKdf.build fixed writer kdf (kernelOf false response) aux senderId index metadata
        (PqxdhInitialBuilderCut.eraseRoot ready)).run state := by
  simp only [protocolBuild, PqxdhInitialPrivateKdf.build, StateT.run, simulateQ_map]
  have complete := tail_program fixed writer response kdf aux
    (PqxdhInitialServiceBuilder.readyBuild fixed
      (PqxdhRegistrationProtocolState.input senderId index metadata
        (PqxdhRegistrationProtocolState.consume index ready state)).binding ready metadata
      (PqxdhRegistrationProtocolState.input senderId index metadata
        (PqxdhRegistrationProtocolState.consume index ready state)).state)
    (PqxdhRegistrationProtocolState.consume index ready state).primitive
  simp only [StateT.run] at complete
  rw [complete, PqxdhInitialSuppliedBuilder.ready_supplied, QueryImpl.simulateQ_compose]
  rfl


noncomputable def build (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :=
  simulateQ (PqxdhInitialLabelBuilder.compiler selected)
    ((protocolBuild fixed writer kdf aux sender index metadata
      (PqxdhInitialBuilderCut.eraseRoot ready)).run state)

/-- Changing only the supplied Ready root cannot change any executable compiled builder operation or continuation. -/
theorem root_unused (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    build fixed writer kdf aux sender index metadata selected { ready with root := root } state =
      build fixed writer kdf aux sender index metadata selected ready state := rfl

/-- The actual root-erased compiled Server builder consumes the supplied response after its original checks and preserves first-send work and the complete protocol/shared result and root cache. -/
theorem build_response (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : PqxdhRegistrationProtocolState.State M P I D K A S B)
    (response : PqxdhInitialRootLabelService.Response) (cache : RootOracle.QueryCache) :
    (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (build fixed writer kdf aux sender index metadata selected ready state)).run cache =
      (fun result => (result, cache)) <$>
        (PqxdhInitialPrivateKdf.build fixed writer kdf (kernelOf false response) aux sender index metadata
          (PqxdhInitialBuilderCut.eraseRoot ready)).run state := by
  rw [build, PqxdhInitialLabelBuilder.response_program, protocol_supplied]
  rfl


/-- The actual labelled Server builder is the real private-handler specialization of the complete pre-first-send interface. -/
theorem build_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    build fixed writer (RawCtxSourceHkdf.kdfImpl fixed) aux sender index metadata selected ready state =
      PqxdhInitialLabelBuilder.build fixed writer aux sender index metadata selected ready state := rfl

end BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.protocol_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.protocol_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.tail_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.tail_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.tail_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.tail_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.protocol_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.protocol_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.build_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.build_response

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder.build_source
