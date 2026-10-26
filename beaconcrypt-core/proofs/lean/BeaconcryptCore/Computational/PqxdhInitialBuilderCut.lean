import BeaconcryptCore.Computational.PqxdhRegistrationProtocolState

/-!
The exact original registration builder is factored at its pure64-byte initializer result. Its current allocation/binding checks, identity validation and peer reservation still precede initialization, and plaintext allocation, first send, erasure, serialization, publication and reinstallation remain the original tail. The factored code never reads the root field. This is a source-derived continuation for an initializer hybrid, not a new protocol or an arbitrary compatibility premise.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderCut
open PqxdhServerRegistrationPublication PqxdhSecretInputKdf PqxdhJointKdfGame

noncomputable def candidate {Metadata PeerMetadata Consumed : Type}
    (initial : RustM ConcreteRatchetKernel)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) := do
  let valid ← TailSpec.query (.inr (.checkIdentity candidate.beacon_identity_public_key))
  if !valid then pure (ok (none, state)) else do
    let reserved ← TailSpec.query (.inr .reservePeer)
    if !reserved then pure (ok (none, state)) else
      continueRust initial fun kernel => do
        let plaintext := data.getD registrationWitness
        if plaintext.isEmpty then pure (ok (none, state))
        else if 8 + plaintext.length ≤ Usize.max then do
          let allocated ← TailSpec.query (.inr (.reservePlaintext (8 + plaintext.length)))
          if !allocated then pure (ok (none, state)) else
            continueRust (candidate.key_id_binding) fun binding =>
              ok <$> afterInitialization candidate (absBytes binding.bytes ++ plaintext)
                kernel metadata state
        else pure (ok (none, state))

/-- The full original candidate tail consumes exactly the supplied source initializer result in its original order. -/
theorem candidate_source {Metadata PeerMetadata Consumed : Type}
    (source : FixedHkdfSha512NoSaltSource) (pending : pqxdh.ServerRegistrationCandidate)
    (root : RootOutput) (data : Option Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    candidate (PqxdhRootTableInitialization.initialKernelRun source false root) pending data metadata state =
      candidateTail source pending root data metadata state := by
  simp only [candidate, candidateTail, candidate_initialization]

noncomputable def usedBuild {Metadata PeerMetadata Consumed : Type}
    (initial : RustM ConcreteRatchetKernel)
    (pending : PqxdhRegistrationInputs.UsedInput)
    (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) :=
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
          | .Ok candidate => PqxdhInitialBuilderCut.candidate initial candidate data metadata state

/-- Rechecks of the exact current Server control and binding precede the same source-derived initializer tail. -/
theorem used_source {Metadata PeerMetadata Consumed : Type}
    (source : FixedHkdfSha512NoSaltSource) (pending : PqxdhRegistrationInputs.UsedInput)
    (root : RootOutput) (data : Option Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    usedBuild (PqxdhRootTableInitialization.initialKernelRun source false root) pending data metadata state =
      PqxdhRegistrationInputs.build source pending root data metadata state := by
  simp only [usedBuild, PqxdhRegistrationInputs.build, candidate_source]
  rfl

noncomputable def readyBuild {Metadata PeerMetadata Consumed : Type}
    (source : FixedHkdfSha512NoSaltSource) (initial : RustM ConcreteRatchetKernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :=
  usedBuild initial (PqxdhAcceptedRegistration.usedReady source.crypto binding ready) ready.application metadata state

/-- The actual accepted-root builder uses its same consumed context and exactly one factored initializer result. -/
theorem ready_source {Metadata PeerMetadata Consumed : Type}
    (source : FixedHkdfSha512NoSaltSource) (binding : pqxdh.ServerBinding)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    readyBuild source (PqxdhRootTableInitialization.initialKernelRun source false ready.root) binding ready metadata state =
      PqxdhAcceptedRegistration.buildReady source binding ready metadata state := by
  exact used_source source _ ready.root ready.application metadata state

/-- Once the initializer result is supplied, every complete accepted builder effect is independent of the Ready root field. -/
theorem ready_root_unused {Metadata PeerMetadata Consumed : Type}
    (source : FixedHkdfSha512NoSaltSource) (initial : RustM ConcreteRatchetKernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (root : RootOutput)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    readyBuild source initial binding {ready with root := root} metadata state =
      readyBuild source initial binding ready metadata state := by
  rfl

noncomputable def protocolBuild {M P I D K A : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (initial : RustM ConcreteRatchetKernel)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) ProbComp (RustM (Option PqxdhServerRegistrationPublication.Response)) :=
  fun state =>
    let current := PqxdhRegistrationProtocolState.consume index ready state
    let selected := PqxdhRegistrationProtocolState.input senderId index metadata current
    PqxdhRegistrationProtocolState.reinstall index current <$> (simulateQ (PqxdhRegistrationProtocolState.registrationImpl source writer aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (readyBuild source initial selected.binding ready metadata selected.state))).run current.primitive

/-- Factoring initialization retains the entire real registration protocol state, first send and selected Server reinstallation. -/
theorem protocol_source {M P I D K A : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    protocolBuild (I := I) (D := D) (K := K) (B := B) source writer
      (PqxdhRootTableInitialization.initialKernelRun source false ready.root) aux senderId index metadata ready =
      PqxdhRegistrationProtocolState.build source writer aux senderId index metadata ready := by
  funext state
  simp only [protocolBuild, PqxdhRegistrationProtocolState.build, ready_source]

/-- The original complete protocol builder no longer reads Ready.root after its initializer is supplied; all other fields and shared effects remain present. -/
theorem protocol_root_unused {M P I D K A : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (initial : RustM ConcreteRatchetKernel)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) (root : RootOutput) :
    protocolBuild (I := I) (D := D) (K := K) (B := B) source writer initial aux senderId index metadata {ready with root := root} =
      protocolBuild source writer initial aux senderId index metadata ready := by
  rfl

def eraseRoot (ready : PqxdhPrivateAcceptedRoot.Ready) : PqxdhPrivateAcceptedRoot.Ready :=
  {ready with root := List.Vector.replicate 32 0}

/-- The retained initializer context contains a fixed dummy root and preserves every other Ready field. -/
theorem erased_fields (ready : PqxdhPrivateAcceptedRoot.Ready) :
    (eraseRoot ready).root = List.Vector.replicate 32 0 ∧
      (eraseRoot ready).consumed = ready.consumed ∧ (eraseRoot ready).application = ready.application ∧
      (eraseRoot ready).identity = ready.identity ∧ (eraseRoot ready).oneTime = ready.oneTime ∧
      (eraseRoot ready).ephemeral = ready.ephemeral ∧ (eraseRoot ready).ciphertext = ready.ciphertext := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual registration builder can be executed with a root-erased context and its same source initializer result before the first send. -/
theorem protocol_erased_source {M P I D K A : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    protocolBuild (I := I) (D := D) (K := K) (B := B) source writer
      (PqxdhRootTableInitialization.initialKernelRun source false ready.root) aux senderId index metadata (eraseRoot ready) =
      PqxdhRegistrationProtocolState.build source writer aux senderId index metadata ready := by
  rw [eraseRoot, protocol_root_unused, protocol_source]

end BeaconcryptCore.Computational.PqxdhInitialBuilderCut

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCut.candidate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCut.candidate_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCut.used_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCut.used_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCut.ready_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCut.ready_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCut.ready_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCut.ready_root_unused
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCut.protocol_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCut.protocol_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCut.protocol_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCut.protocol_root_unused
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCut.erased_fields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCut.erased_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCut.protocol_erased_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCut.protocol_erased_source
