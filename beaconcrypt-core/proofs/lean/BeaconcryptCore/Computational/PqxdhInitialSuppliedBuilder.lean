import BeaconcryptCore.Computational.PqxdhInitialReplyErasure

/-!
Supplying the actual Server initializer callback with one complete64-byte response yields the original factored builder with a root-erased Ready context. The actual identity, reservation and binding gates remain before the response callback; the complete first send, serialization, publication and reinstallation remain after it. This is a concrete source continuation law, not an assumed no-use property or a generator interchange.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder
open PqxdhServerRegistrationPublication PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialReplyErasure PqxdhInitialResponseService

/-- At the actual post-reservation callback, a fixed reply yields the full original candidate continuation with a root-free initializer result. -/
theorem candidate_supplied {Metadata PeerMetadata Consumed : Type}
    (response : pqxdh.concrete.InitialRatchetKdfResponse) (pending : pqxdh.ServerRegistrationCandidate)
    (root : RootOutput) (data : Option Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    simulateQ (supplied response) (PqxdhInitialServiceBuilder.candidate pending root data metadata state) =
      PqxdhInitialBuilderCut.candidate (kernelOf false response) pending data metadata state := by
  simp only [PqxdhInitialServiceBuilder.candidate, PqxdhInitialBuilderCut.candidate, original, OracleSpec.query,
    simulateQ_bind]
  apply bind_congr
  intro valid
  cases valid
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind]
    apply bind_congr
    intro reserved
    cases reserved
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind,
        kernel_supplied, pure_bind, PqxdhInitialReplyErasure.original_program]
      rfl

/-- The actual current allocation, consumed-registration and binding checks precede the same fixed-response candidate continuation. -/
theorem used_supplied {Metadata PeerMetadata Consumed : Type}
    (response : pqxdh.concrete.InitialRatchetKdfResponse) (pending : PqxdhRegistrationInputs.UsedInput)
    (root : RootOutput) (data : Option Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    simulateQ (supplied response) (PqxdhInitialServiceBuilder.usedBuild pending root data metadata state) =
      PqxdhInitialBuilderCut.usedBuild (kernelOf false response) pending data metadata state := by
  unfold PqxdhInitialServiceBuilder.usedBuild PqxdhInitialBuilderCut.usedBuild
  cases next : pqxdh.server_next_key_id state.control
  case ok value =>
    cases value
    case Err error => rfl
    case Ok key =>
      simp only [continueRust]
      cases prepared : PqxdhRegistrationInputs.prepare state.control pending
        ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
      case ok value =>
        cases value
        case Err error => rfl
        case Ok value => exact candidate_supplied response value root data metadata state
      all_goals rfl
  all_goals rfl

/-- The fixed initializer response leaves a complete Ready continuation containing only the dummy root and every unchanged original field. -/
theorem ready_supplied {Metadata PeerMetadata Consumed : Type}
    (fixed : FixedHkdfSha512NoSaltSource) (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    simulateQ (supplied response) (PqxdhInitialServiceBuilder.readyBuild fixed binding ready metadata state) =
      PqxdhInitialBuilderCut.readyBuild fixed (kernelOf false response) binding (PqxdhInitialBuilderCut.eraseRoot ready) metadata state := by
  exact used_supplied response _ ready.root ready.application metadata state

/-- The fixed reply interpretation preserves each original builder primitive callback, complete shared state and original random coins. -/
theorem tail_supplied {A : Type} (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (query : PqxdhInitialServiceBuilder.BuilderSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A) :
    simulateQ (supplied response) ((PqxdhInitialServiceBuilder.tailImpl fixed writer aux query).run state) =
      (simulateQ (PqxdhRegistrationProtocolState.registrationImpl fixed writer aux ∘ₛ nativeAdapter)
        (supplied response query)).run state := by
  cases query with
  | inl query =>
      rw [PqxdhInitialServiceBuilder.tailImpl, StateT.run, PqxdhInitialReplyErasure.original_program]
      simp [supplied, QueryImpl.compose, OracleSpec.query]
  | inr request =>
      simp [PqxdhInitialServiceBuilder.tailImpl, StateT.run, initial, supplied, OracleSpec.query]
      rfl

/-- The entire stateful builder tail, including every failure and public reply, uses the same response substitution and complete shared-state interpreter. -/
theorem tail_program {A Result : Type} (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (work : OracleComp PqxdhInitialServiceBuilder.BuilderSpec Result) (state : RawCtxSharedPrimitive.SharedState A) :
    simulateQ (supplied response) ((simulateQ (PqxdhInitialServiceBuilder.tailImpl fixed writer aux) work).run state) =
      (simulateQ (PqxdhRegistrationProtocolState.registrationImpl fixed writer aux ∘ₛ nativeAdapter)
        (simulateQ (supplied response) work)).run state := by
  rw [← QueryImpl.simulateQ_compose]
  exact simulateQ_StateT_compose (PqxdhInitialServiceBuilder.tailImpl fixed writer aux) (supplied response)
    ((PqxdhRegistrationProtocolState.registrationImpl fixed writer aux ∘ₛ nativeAdapter) ∘ₛ supplied response)
    (tail_supplied fixed writer response aux) work state

/-- The current complete Server builder with its supplied64 reply runs from the root-erased Ready context while preserving every other field, first send and full protocol/shared poststate. -/
theorem protocol_supplied {M P I D K A : Type} {S B : Nat}
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    simulateQ (supplied response) ((PqxdhInitialServiceBuilder.protocolBuild fixed writer aux senderId index metadata ready).run state) =
      (PqxdhInitialBuilderCut.protocolBuild fixed writer (kernelOf false response) aux senderId index metadata
        (PqxdhInitialBuilderCut.eraseRoot ready)).run state := by
  simp only [PqxdhInitialServiceBuilder.protocolBuild, PqxdhInitialBuilderCut.protocolBuild, StateT.run, simulateQ_map]
  have complete := tail_program fixed writer response aux
    (PqxdhInitialServiceBuilder.readyBuild fixed
      (PqxdhRegistrationProtocolState.input senderId index metadata
        (PqxdhRegistrationProtocolState.consume index ready state)).binding ready metadata
      (PqxdhRegistrationProtocolState.input senderId index metadata
        (PqxdhRegistrationProtocolState.consume index ready state)).state)
    (PqxdhRegistrationProtocolState.consume index ready state).primitive
  simp only [StateT.run] at complete
  rw [complete, ready_supplied, QueryImpl.simulateQ_compose]
  rfl

end BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.candidate_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.candidate_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.used_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.used_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.ready_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.ready_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.tail_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.tail_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.tail_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.tail_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.protocol_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBuilder.protocol_supplied
