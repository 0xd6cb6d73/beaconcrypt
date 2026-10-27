-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryRecordSend
import BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-! The real Server build executor over the original tail interface, retaining exact optional writer effects and existing seal logging. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild
open PqxdhRefinement RawCtxSourceSend
open PqxdhServerRegistrationPublication (TailSpec)

/-- The extracted first-send driver calls the original sealing endpoint, so its native AEAD/hash/writer effects and the existing successful-seal log remain at their original interpreter point. -/
noncomputable def executeSend (kernel : ConcreteRatchetKernel) (context : SealContext) :
    OracleComp TailSpec (RustM (ConcreteRatchetKernel × Option Encrypted)) :=
  RawCtxInterpretedOpening.bindResult (begin_send kernel context) fun start =>
    match start with
    | .SendExhausted entry _ => pure (ok (entry, none))
    | .SendKdfRequested pending =>
        RawCtxInterpretedOpening.bindResult (SendKdf.impl.request pending) fun request => do
          let response ← TailSpec.query (.inl (.inl request))
          RawCtxInterpretedOpening.bindResult (pending.resume response) fun ready =>
            RawCtxInterpretedOpening.bindResult (PqxdhBoundaryRecordSend.executeArguments ready) fun input => do
              let ciphertext ← TailSpec.query (.inl (.inr input))
              pure (ready.finish (ciphertext.map (encrypted input)))

/-- The extracted first-send execution is exactly the original tail program before interpreting any query or dropping any poststate. -/
theorem send_exact (kernel : ConcreteRatchetKernel) (context : SealContext) :
    executeSend kernel context =
      (fun result => ok result) <$> simulateQ PqxdhServerRegistrationPublication.sendLift
        (simulateQ adapter (send kernel context)) := by
  unfold executeSend
  rw [beginSend_exact, PqxdhOpenBridges.bindResult_ok]
  cases started : beginSend kernel context with
  | SendExhausted entry saved =>
    simp only [send, started, program, simulateQ_pure, map_pure]
  | SendKdfRequested pending =>
    simp only [send, started, program, adapter, PqxdhServerRegistrationPublication.sendLift,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
    simp only [PqxdhBoundaryRecordSend.executeArguments, SendKdf.impl.request, SendSeal.impl.material,
      SendSeal.impl.sequence, SendSeal.impl.context, bind_tc_ok, resumeSend_exact,
      PqxdhOpenBridges.bindResult_ok, SendSeal.finish_returns_interpreter_result,
      map_bind, bind_assoc, pure_bind, map_pure]
    rfl

open PqxdhServerRegistrationPublication
variable {Metadata PeerMetadata Consumed : Type}

/-- The actual extracted send finishes before plaintext erasure and optional outer writing; the candidate peer is installed only after a successful outer writer. -/
noncomputable def executeAfterInitialization
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) := do
  let sent ← executeSend kernel (firstContext candidate authenticated)
  RawCtxInterpretedOpening.bindResult sent fun result => do
    let _ ← TailSpec.query (.inr (.erase authenticated))
    match result.2 with
    | none => pure (ok (none, state))
    | some encrypted =>
        let serialized ← TailSpec.query (.inr (.write (responseFields candidate encrypted)))
        match serialized with
        | none => pure (ok (none, state))
        | some bytes => pure (ok (some ⟨bytes, candidate.key_id⟩,
            publish state candidate result.1 metadata))

/-- The complete tail program retains both writer outcomes and their preceding primitive effects under every interpreter. -/
theorem after_initialization_exact
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    executeAfterInitialization candidate authenticated kernel metadata state =
      (fun result => ok result) <$> afterInitialization candidate authenticated kernel metadata state := by
  simp only [executeAfterInitialization, send_exact, afterInitialization, bind_map_left,
    PqxdhOpenBridges.bindResult_ok, map_bind]
  apply bind_congr
  intro sent
  apply bind_congr
  intro erased
  cases sent.2 with
  | none => rw [map_pure]
  | some encrypted =>
    simp only [map_bind]
    apply bind_congr
    intro serialized
    cases serialized <;> rw [map_pure]

open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {KemSK Reader WireResponse ι : Type} {baseSpec : OracleSpec ι}

/-- Identity admission and peer reservation precede the real pure initializer. Empty application data is rejected only after that initializer; binding, send and both writers retain their original order. -/
noncomputable def executeCandidate (setup : Setup baseSpec KemSK)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) := do
  let valid ← TailSpec.query (.inr (.checkIdentity candidate.beacon_identity_public_key))
  if !valid then pure (ok (none, state)) else do
    let reserved ← TailSpec.query (.inr .reservePeer)
    if !reserved then pure (ok (none, state)) else
      continueRust (BeaconcryptCore.Refinement.ServerTransactionRefinement.initializeCandidate candidate
        (PqxdhRootTableInitialization.rootArray root)
        (PqxdhRootTableInitialization.initialResponse setup.source.crypto)) fun kernel => do
        let plaintext := data.getD registrationWitness
        if plaintext.isEmpty then pure (ok (none, state))
        else if 8 + plaintext.length ≤ Usize.max then do
          let allocated ← TailSpec.query (.inr (.reservePlaintext (8 + plaintext.length)))
          if !allocated then pure (ok (none, state)) else
            continueRust candidate.key_id_binding fun binding =>
              executeAfterInitialization candidate (absBytes binding.bytes ++ plaintext) kernel metadata state
        else pure (ok (none, state))

/-- The candidate executor is the original source program; the initializer remains real local work rather than an invented observable query. -/
theorem candidate_exact (setup : Setup baseSpec KemSK)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    executeCandidate setup candidate root data metadata state =
      candidateTail setup.source candidate root data metadata state := by
  simp only [executeCandidate, candidateTail, after_initialization_exact]

/-- The extracted next-ID, occupancy and candidate-preparation operations precede the candidate executor; every diagnostic or ordinary rejection retains its original branch. -/
noncomputable def executeBuild (setup : Setup baseSpec KemSK)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) :=
  continueRust (pqxdh.server_next_key_id state.control) fun next =>
    match next with
    | .Err _ => pure (ok (none, state))
    | .Ok next =>
        let availability := if (state.server.peers next).isSome then
          pqxdh.KeyIdAvailability.Occupied else .Available
        continueRust (pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩ availability) fun prepared =>
          match prepared with
          | .Err _ => pure (ok (none, state))
          | .Ok candidate => executeCandidate setup candidate root data metadata state

/-- The complete Server builder is equal before interpretation, retaining supplied root, all calls, optional writer results and returned Server state. -/
theorem build_exact (setup : Setup baseSpec KemSK)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    executeBuild setup pending root data metadata state =
      build setup.source pending root data metadata state := by
  simp only [executeBuild, build, candidate_exact]
  rfl

/-- Any complete stateful interpretation and continuation retains the original build program, including native callback transcripts, private logs and all failure poststates. -/
theorem build_complete {PrimitiveState Result κ : Type} {base : OracleSpec κ}
    (handler : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (setup : Setup baseSpec KemSK) (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) (primitive : PrimitiveState)
    (next : RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState → OracleComp base Result) :
    (simulateQ handler (executeBuild setup pending root data metadata state)).run primitive >>= next =
      (simulateQ handler (build setup.source pending root data metadata state)).run primitive >>= next := by
  rw [build_exact]

/-- The actual native sealing endpoint before its successful-result log update, exposing the real AEAD, shared hash and optional inner writer requests. -/
noncomputable def nativeSeal (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (input : SealInput) :
    StateT (RawCtxSharedPrimitive.SharedState (List SealContext)) ProbComp (Option Pqxdh.Bytes) :=
  simulateQ (fun query => PqxdhRegistrationProtocolState.registrationImpl setup.source codec.frameWrite
    (PqxdhServerAuthExperiment.tailAux codec checks) (.inl (.inr query))) (RawCtxSourceSeal.sealInput input)

/-- The original native seal callback is literally the full sealing program, before examining the optional inner writer reply. -/
theorem native_seal_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (input : SealInput) :
    PqxdhServerAuthExperiment.nativeTail (A := List SealContext) setup codec checks (.inl (.inr input)) =
      nativeSeal setup codec checks input := by
  simp only [PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, RawCtxSourceSeal.nativeAdapter,
    ← QueryImpl.simulateQ_compose]
  unfold nativeSeal
  congr 1
  funext query
  simp only [QueryImpl.compose, RawCtxSourceSeal.sealLift, simulateQ_spec_query]

/-- The original seal log appends exactly when the inner callback returns some. Inner writer failure keeps its full primitive poststate without inventing a log entry. -/
theorem seal_complete {Result : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader WireResponse) (checks : Checks) (input : SealInput)
    (state : RawCtxSharedPrimitive.SharedState (List SealContext))
    (next : Option Pqxdh.Bytes × RawCtxSharedPrimitive.SharedState (List SealContext) → ProbComp Result) :
    (PqxdhServerAuthExperiment.tailImpl setup codec checks (.inl (.inr input))).run state >>= next =
      (nativeSeal setup codec checks input).run state >>= fun result =>
        next (result.1, if result.1.isSome then (result.2.1 ++ [input.context], result.2.2) else result.2) := by
  simp only [PqxdhServerAuthExperiment.tailImpl, StateT.run_bind, native_seal_exact, bind_assoc]
  apply bind_congr
  intro result
  cases result.1 <;> simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    ite_false, ite_true, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]

/-- Inner or outer writer rejection never installs the local candidate peer. Its actual primitive poststate remains unrestricted and retained by the complete execution equality. -/
theorem after_initialization_failure {PrimitiveState κ : Type} {base : OracleSpec κ}
    (handler : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state after : State Metadata PeerMetadata Consumed) (primitive final : PrimitiveState)
    (supported : (ok (none, after), final) ∈ support ((simulateQ handler
      (executeAfterInitialization candidate authenticated kernel metadata state)).run primitive)) :
    after = state := by
  rw [after_initialization_exact, simulateQ_map, StateT.run_map] at supported
  simp only [support_map, Set.mem_image, Prod.mk.injEq, RustM.ok.injEq] at supported
  obtain ⟨⟨actual, result⟩, originalSupport, rfl, rfl⟩ := supported
  obtain ⟨sent, afterSend, afterErase, _, _, outcome⟩ := afterInitialization_support handler
    candidate authenticated kernel metadata state primitive ((none, after), _) originalSupport
  cases hs : sent.2 with
  | none =>
    simp only [hs] at outcome
    exact congrArg (fun result => result.1.2) outcome
  | some encrypted =>
    simp only [hs] at outcome
    obtain ⟨written, afterWrite, _, outcome⟩ := outcome
    cases written with
    | none => exact congrArg (fun result => result.1.2) outcome
    | some bytes =>
      have impossible := congrArg (fun result => result.1.1) outcome
      contradiction

end BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.send_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.send_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.after_initialization_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.after_initialization_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.candidate_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.candidate_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.build_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.build_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.build_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.build_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.native_seal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.native_seal_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.seal_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.seal_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.after_initialization_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild.after_initialization_failure
