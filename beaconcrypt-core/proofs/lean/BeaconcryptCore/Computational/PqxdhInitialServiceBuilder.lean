import BeaconcryptCore.Computational.PqxdhInitialResponseService

/-!
The original Server builder requests its private64-byte initializer response only after the actual current-control/binding checks, identity validation and peer reservation. It then executes the original plaintext allocation, first send, erasure, serialization, publication and full reinstallation. The source specialization is proved for the complete callback program; no random sample is moved before an admission gate.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialServiceBuilder
open PqxdhServerRegistrationPublication PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialResponseService

abbrev BuilderSpec := PqxdhInitialResponseService.Spec TailSpec

noncomputable def afterInitial {Metadata PeerMetadata Consumed : Type}
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) (kernel : ConcreteRatchetKernel) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) := do
  let plaintext := data.getD registrationWitness
  if plaintext.isEmpty then pure (ok (none, state))
  else if 8 + plaintext.length ≤ Usize.max then do
    let allocated ← TailSpec.query (.inr (.reservePlaintext (8 + plaintext.length)))
    if !allocated then pure (ok (none, state)) else
      continueRust (candidate.key_id_binding) fun binding =>
        ok <$> afterInitialization candidate (absBytes binding.bytes ++ plaintext) kernel metadata state
  else pure (ok (none, state))

noncomputable def candidate {Metadata PeerMetadata Consumed : Type}
    (candidate : pqxdh.ServerRegistrationCandidate) (root : RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp BuilderSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) := do
  let valid ← original (base := TailSpec) (.inr (.checkIdentity candidate.beacon_identity_public_key))
  if !valid then pure (ok (none, state)) else do
    let reserved ← original (base := TailSpec) (.inr .reservePeer)
    if !reserved then pure (ok (none, state)) else do
      let initialized ← PqxdhInitialResponseService.kernel false root
      simulateQ original (continueRust initialized (afterInitial candidate data metadata state))

/-- The private initializer request occurs at the original post-reservation point and the actual source interpreter recovers the whole original candidate tail. -/
theorem candidate_source {Metadata PeerMetadata Consumed : Type}
    (fixed : FixedHkdfSha512NoSaltSource) (pending : pqxdh.ServerRegistrationCandidate)
    (root : RootOutput) (data : Option Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    simulateQ (source fixed) (candidate pending root data metadata state) =
      candidateTail fixed pending root data metadata state := by
  simp only [candidate, candidateTail, candidate_initialization, original, OracleSpec.query,
    simulateQ_bind]
  apply bind_congr
  intro valid
  cases valid
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, simulateQ_bind]
    apply bind_congr
    intro reserved
    cases reserved
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, simulateQ_bind,
        kernel_source, pure_bind, original_program]
      rfl

noncomputable def usedBuild {Metadata PeerMetadata Consumed : Type}
    (pending : PqxdhRegistrationInputs.UsedInput) (root : RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp BuilderSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) :=
  continueRust (pqxdh.server_next_key_id state.control) fun next =>
    match next with
    | .Err _ => pure (ok (none, state))
    | .Ok next =>
        let availability := if (state.server.peers next).isSome then
          pqxdh.KeyIdAvailability.Occupied else .Available
        continueRust (PqxdhRegistrationInputs.prepare state.control pending
          ⟨state.server.identity, state.identityKeyId⟩ availability) fun prepared =>
          match prepared with
          | .Err _ => pure (ok (none, state))
          | .Ok value => candidate value root data metadata state

/-- Rechecking the actual current Server allocation, consumed registration and binding precedes the same initializer service point. -/
theorem used_source {Metadata PeerMetadata Consumed : Type}
    (fixed : FixedHkdfSha512NoSaltSource) (pending : PqxdhRegistrationInputs.UsedInput)
    (root : RootOutput) (data : Option Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    simulateQ (source fixed) (usedBuild pending root data metadata state) =
      PqxdhRegistrationInputs.build fixed pending root data metadata state := by
  unfold usedBuild PqxdhRegistrationInputs.build
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
        case Ok value => exact candidate_source fixed value root data metadata state
      all_goals rfl
  all_goals rfl

noncomputable def readyBuild {Metadata PeerMetadata Consumed : Type}
    (fixed : FixedHkdfSha512NoSaltSource) (binding : pqxdh.ServerBinding)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :=
  usedBuild (PqxdhAcceptedRegistration.usedReady fixed.crypto binding ready) ready.root ready.application metadata state

/-- The accepted root enters only the exact requested initializer input while the original consumed registration and Ready fields stay intact. -/
theorem ready_source {Metadata PeerMetadata Consumed : Type}
    (fixed : FixedHkdfSha512NoSaltSource) (binding : pqxdh.ServerBinding)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    simulateQ (source fixed) (readyBuild fixed binding ready metadata state) =
      PqxdhAcceptedRegistration.buildReady fixed binding ready metadata state :=
  used_source fixed _ ready.root ready.application metadata state

abbrev RunSpec := PqxdhInitialResponseService.Spec unifSpec

noncomputable def tailImpl {A : Type} (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    QueryImpl BuilderSpec (StateT (RawCtxSharedPrimitive.SharedState A) (OracleComp RunSpec))
  | .inl query => fun state => simulateQ original
      ((simulateQ (PqxdhRegistrationProtocolState.registrationImpl fixed writer aux) (nativeAdapter query)).run state)
  | .inr request => fun state => do
      let response ← initial request
      pure (response, state)

/-- Every original send/allocation/publication callback retains its full primitive state and actual coins; only the new private initializer callback is separately visible. -/
theorem tail_source {A : Type} (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (query : BuilderSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A) :
    simulateQ (source fixed) ((tailImpl fixed writer aux query).run state) =
      (simulateQ (PqxdhRegistrationProtocolState.registrationImpl fixed writer aux ∘ₛ nativeAdapter)
        (source fixed query)).run state := by
  cases query with
  | inl query =>
      rw [tailImpl, StateT.run, original_program]
      simp [source, QueryImpl.compose, OracleSpec.query]
  | inr request =>
      simp [tailImpl, StateT.run, initial, source, OracleSpec.query]
      rfl

/-- The complete original builder callback program retains every result and shared poststate through initializer interpretation. -/
theorem tail_program {A Result : Type} (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (work : OracleComp BuilderSpec Result) (state : RawCtxSharedPrimitive.SharedState A) :
    simulateQ (source fixed) ((simulateQ (tailImpl fixed writer aux) work).run state) =
      (simulateQ (PqxdhRegistrationProtocolState.registrationImpl fixed writer aux ∘ₛ nativeAdapter)
        (simulateQ (source fixed) work)).run state := by
  rw [← QueryImpl.simulateQ_compose]
  exact simulateQ_StateT_compose (tailImpl fixed writer aux) (source fixed)
    ((PqxdhRegistrationProtocolState.registrationImpl fixed writer aux ∘ₛ nativeAdapter) ∘ₛ source fixed)
    (tail_source fixed writer aux) work state

noncomputable def protocolBuild {M P I D K A : Type} {S B : Nat}
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) (OracleComp RunSpec)
      (RustM (Option Response)) := fun state =>
  let current := PqxdhRegistrationProtocolState.consume index ready state
  let selected := PqxdhRegistrationProtocolState.input senderId index metadata current
  PqxdhRegistrationProtocolState.reinstall index current <$>
    (simulateQ (tailImpl fixed writer aux) (readyBuild fixed selected.binding ready metadata selected.state)).run current.primitive

/-- The current source registration builder, including consumed state, first send, serialization and selected Server reinstallation, is the real-source interpretation of this initializer service. -/
theorem protocol_source {M P I D K A : Type} {S B : Nat}
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    simulateQ (source fixed) ((protocolBuild fixed writer aux senderId index metadata ready).run state) =
      (PqxdhRegistrationProtocolState.build fixed writer aux senderId index metadata ready).run state := by
  simp only [protocolBuild, PqxdhRegistrationProtocolState.build, StateT.run, simulateQ_map]
  have complete := tail_program fixed writer aux
    (readyBuild fixed
      (PqxdhRegistrationProtocolState.input senderId index metadata
        (PqxdhRegistrationProtocolState.consume index ready state)).binding ready metadata
      (PqxdhRegistrationProtocolState.input senderId index metadata
        (PqxdhRegistrationProtocolState.consume index ready state)).state)
    (PqxdhRegistrationProtocolState.consume index ready state).primitive
  simp only [StateT.run] at complete
  rw [complete, ready_source, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.PqxdhInitialServiceBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.candidate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.candidate_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.used_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.used_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.ready_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.ready_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.tail_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.tail_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.tail_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.tail_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.protocol_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceBuilder.protocol_source
