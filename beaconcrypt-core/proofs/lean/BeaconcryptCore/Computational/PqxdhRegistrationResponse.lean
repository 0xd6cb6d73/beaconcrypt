-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthNative

/-! The source response publishes only after both writers succeed and advances the public checked U64 counter exactly once. Full adaptive source continuations preserve counter monotonicity and distinct successful response identifiers. Primitive/cache/log poststates remain in the original executions; failure of the outer writer does not erase prior source effects. These are operational registration-boundary statements, not a full applied-pi compiler or authentication theorem. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationResponse

/-- A successful extracted allocation exposes the predictable mathematical successor. -/
theorem next_id (state : pqxdh.ServerState) (next : U64)
    (returned : pqxdh.server_next_key_id state = ok (.Ok next)) :
    next.val = state.last_key_id.val + 1 := by
  by_cases exhausted : state.last_key_id = core.num.U64.MAX
  · simp [pqxdh.server_next_key_id, exhausted] at returned
  · obtain ⟨actual, generated, value⟩ :=
      BeaconcryptCore.Refinement.PqxdhSurface.next_server_key_id_success state exhausted
    have same := RustM.ok.inj (generated.symm.trans returned)
    cases same
    exact value

/-- The extracted successful candidate keeps current control and binds both public allocation fields to the same successor. -/
theorem prepared_counter (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (prepared : pqxdh.server_prepare_commit state pending binding availability = ok (.Ok candidate)) :
    candidate.previous_state = state ∧
      candidate.next_state.last_key_id.val = state.last_key_id.val + 1 ∧
      candidate.key_id = candidate.next_state.last_key_id := by
  simp only [pqxdh.server_prepare_commit, array_eq_abs, bind_tc_ok] at prepared
  split at prepared
  · split at prepared
    · obtain ⟨value, generated⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state
      simp only [generated, bind_tc_ok] at prepared
      cases value with
      | Err error => simp at prepared
      | Ok next =>
          have count := next_id state next generated
          cases availability <;> simp only [bind_tc_ok, Bool.false_eq_true, ite_false, ite_true] at prepared
          · obtain ⟨ad, built⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok
              binding.identity_public_key pending.beacon_identity_public_key
            simp only [built, bind_tc_ok] at prepared
            cases RustM.ok.inj prepared
            exact ⟨rfl, count, rfl⟩
          · simp at prepared
    · simp at prepared
  · simp at prepared
open PqxdhServerRegistrationPublication
variable {Metadata PeerMetadata Consumed PrimitiveState ι : Type} {base : OracleSpec ι}

/-- The exact successful writer result is the only path that publishes this candidate. -/
def Publication (candidate : pqxdh.ServerRegistrationCandidate)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (result : RustM (Option Response × State Metadata PeerMetadata Consumed)) : Prop :=
  result = ok (none, state) ∨ ∃ kernel bytes,
    result = ok (some ⟨bytes, candidate.key_id⟩, publish state candidate kernel metadata)

/-- The complete first-send tail retains ordinary failure without publication, or publishes the exact successful outer-writer response and advanced kernel. -/
theorem after_publication (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Bytes)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : PrimitiveState)
    (result : (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState)
    (supported : result ∈ support ((simulateQ impl
      (afterInitialization candidate authenticated kernel metadata state)).run primitive)) :
    Publication candidate metadata state (ok result.1) := by
  obtain ⟨sent, afterSend, afterErase, _, _, rest⟩ :=
    afterInitialization_support impl candidate authenticated kernel metadata state primitive result supported
  cases hs : sent.2 with
  | none => rw [hs] at rest; rw [rest]; exact Or.inl rfl
  | some encrypted =>
      rw [hs] at rest
      obtain ⟨written, afterWrite, _, same⟩ := rest
      rw [same]
      cases written with
      | none => exact Or.inl rfl
      | some bytes => exact Or.inr ⟨sent.1, bytes, rfl⟩

/-- Identity, allocation, nonempty payload and binding gates preserve the exact optional publication boundary. Primitive and auxiliary poststates are arbitrary supported results. -/
theorem candidate_publication (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput)
    (payload : Option Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState)
    (result : RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState)
    (supported : result ∈ support ((simulateQ impl
      (candidateTail source candidate root payload metadata state)).run primitive)) :
    Publication candidate metadata state result.1 := by
  obtain ⟨kernel, hrun, _, _, _⟩ := PqxdhRootTableInitialization.initialize_refines source
    PqxdhServerAuthExperiment.unitRatchet false root
  have hinit := (candidate_initialization source candidate root).trans hrun
  obtain ⟨binding, hbinding, _⟩ := candidate_binding candidate
  simp only [candidateTail, hinit, hbinding, continueRust, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨valid, afterIdentity⟩, _, supported⟩ := supported
  cases valid
  · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    exact Or.inl (congrArg Prod.fst supported)
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reserved, afterReserve⟩, _, supported⟩ := supported
  cases reserved
  · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    exact Or.inl (congrArg Prod.fst supported)
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at supported
  split_ifs at supported with empty fits
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact Or.inl (congrArg Prod.fst supported)
  · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨allocated, afterAllocate⟩, _, supported⟩ := supported
    cases allocated
    · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      exact Or.inl (congrArg Prod.fst supported)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map,
      support_map, Set.mem_image] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact after_publication impl candidate _ kernel metadata state afterAllocate inner reached
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact Or.inl (congrArg Prod.fst supported)

/-- Every complete source response either preserves the unpublished Server or uses its actual successful extracted candidate and writer result. -/
theorem build_publication (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (payload : Option Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState)
    (result : RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState)
    (supported : result ∈ support ((simulateQ impl (build source pending root payload metadata state)).run primitive)) :
    result.1 = ok (none, state) ∨ ∃ next candidate kernel bytes,
      pqxdh.server_next_key_id state.control = ok (.Ok next) ∧
      pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers next).isSome then .Occupied else .Available) = ok (.Ok candidate) ∧
      result.1 = ok (some ⟨bytes, candidate.key_id⟩, publish state candidate kernel metadata) := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [build, hnext, continueRust] at supported
  cases next with
  | Err error =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact Or.inl (congrArg Prod.fst supported)
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers next).isSome then .Occupied else .Available)
      simp only [hprepared] at supported
      cases prepared with
      | Err error =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          exact Or.inl (congrArg Prod.fst supported)
      | Ok candidate =>
          rcases candidate_publication impl source candidate root payload metadata state primitive result supported
            with unchanged | ⟨kernel, bytes, published⟩
          · exact Or.inl unchanged
          · exact Or.inr ⟨next, candidate, kernel, bytes, hnext, hprepared, published⟩

/-- The response's ID and published counter are exactly the old counter plus one. Failure keeps the full original Server; the interpreted private callback poststate remains unrestricted. -/
theorem build_counter (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (payload : Option Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState)
    (result : RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState)
    (supported : result ∈ support ((simulateQ impl (build source pending root payload metadata state)).run primitive)) :
    result.1 = ok (none, state) ∨ ∃ response final,
      result.1 = ok (some response, final) ∧
      final.control.last_key_id.val = state.control.last_key_id.val + 1 ∧
      response.keyId = final.control.last_key_id ∧ final.consumed = state.consumed := by
  rcases build_publication impl source pending root payload metadata state primitive result supported
    with unchanged | ⟨next, candidate, kernel, bytes, _, prepared, published⟩
  · exact Or.inl unchanged
  · obtain ⟨_, counter, assigned⟩ := prepared_counter state.control pending
      ⟨state.server.identity, state.identityKeyId⟩ _ candidate prepared
    exact Or.inr ⟨⟨bytes, candidate.key_id⟩, publish state candidate kernel metadata,
      published, counter, assigned, rfl⟩

open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhJointGapDh
variable {baseSpec : OracleSpec ι} {KemSK Reader WireResponse : Type}

/-- In the original adaptive API, only a returned response advances allocation control; failed outer serialization retains the full Server while its separate primitive/cache/log effects survive. -/
theorem build_oracle_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (index : Nat) (payload : Option Bytes) (state : GameState KemSK)
    (result : Option Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks index payload).run state)) :
    (result.1 = none ∧ result.2.server = state.server) ∨ ∃ response,
      result.1 = some response ∧
      result.2.server.control.last_key_id.val = state.server.control.last_key_id.val + 1 ∧
      response.keyId = result.2.server.control.last_key_id := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending index with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact Or.inl ⟨rfl, rfl⟩
  | some token =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨tail, lifted, supported⟩ := supported
      obtain ⟨tailMember, same⟩ := liftCoins_mem _ _ _ lifted
      simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl, rfl⟩ := supported
      rcases build_counter (tailImpl setup codec checks) setup.source token.pending token.root payload ()
        state.server ([], state.ctx) tail.1 tailMember with unchanged | ⟨response, final, written, counter, key, _⟩
      · simp [unchanged, settle]
      · simp only [written, settle]; exact Or.inr ⟨response, rfl, counter, key⟩

/-- Admission consumes its registration pair but never allocates a response identifier. -/
theorem accept_control (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (publicValue : PublicChallenge) (raw : Bytes) (state : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    result.2.server.control = state.server.control := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some input =>
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨_, _, same, _, _⟩ := client_run state.sessions (binding setup publicValue) input _ returned derived
      have control : returned.2.server.control = state.server.control := by rw [same]
      rcases returned with ⟨outcome, after⟩
      dsimp only at control
      rcases outcome with (_ | token) | error | _
      all_goals simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      all_goals subst supported
      all_goals exact control

/-- Complete Beacon receive, rejection and publication do not allocate Server response IDs. -/
theorem finish_control (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Bytes)
    (state : GameState KemSK) (result : Option Bytes × GameState KemSK)
    (supported : result ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run state)) :
    result.2.server.control = state.server.control := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hphase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [hphase, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨staged, stageRun, supported⟩ := supported
      obtain ⟨cache, extra, stagedEq, _⟩ := stage_run setup codec beaconSeed
        publicValue control state.beacon.beacon.identity oneTime kem raw state staged stageRun
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, _, rfl, rfl⟩ := supported
      rw [stagedEq]
  | _ =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- Every non-build source capability preserves allocation control, including arbitrary registrations and compromised reveals. -/
theorem quiet_control (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (query : ServerAuthSpec.Domain) (notBuild : ∀ index payload, query ≠ .inr (.build index payload))
    (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    result.2.server.control = state.server.control := by
  rcases query with coin | query
  · rw [forward_support _ _ _ supported]
  cases query with
  | accept raw => exact accept_control setup codec checks publicValue raw state result supported
  | build index payload => exact (notBuild index payload rfl).elim
  | finish raw => exact finish_control setup codec publicValue beaconSeed raw state result supported
  | hmac key message =>
      change result ∈ support ((hmacOracle key message).run state) at supported
      simp only [hmacOracle] at supported
      split_ifs at supported
      · obtain ⟨middle, first, rest⟩ := run_bind_support _ _ _ _ supported
        rw [record_run, support_pure, Set.mem_singleton_iff] at first
        subst first
        rw [forward_support _ _ _ rest]
      · rw [forward_support _ _ _ supported]
  | hash bytes =>
      obtain ⟨cache, same⟩ := hashOracle_step bytes state result supported
      rw [same]
  | reveal keyId =>
      change result ∈ support (pure _ : OracleComp PqxdhJointDhExtractRoot.RootSpec _) at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- Every step of the original scheduler either preserves or increments the same public allocation counter once. -/
theorem handler_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (query : ServerAuthSpec.Domain) (state : GameState KemSK)
    (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    result.2.server.control.last_key_id.val = state.server.control.last_key_id.val ∨
      result.2.server.control.last_key_id.val = state.server.control.last_key_id.val + 1 := by
  cases query with
  | inl coin =>
      exact Or.inl (congrArg (fun control => control.last_key_id.val)
        (quiet_control setup codec checks publicValue beaconSeed _ (by simp) state result supported))
  | inr query =>
      cases query with
      | build index payload =>
          rcases build_oracle_counter setup codec checks index payload state result supported
            with ⟨_, same⟩ | ⟨_, _, next, _⟩
          · exact Or.inl (congrArg (fun server => server.control.last_key_id.val) same)
          · exact Or.inr next
      | _ =>
          exact Or.inl (congrArg (fun control => control.last_key_id.val)
            (quiet_control setup codec checks publicValue beaconSeed _ (by simp) state result supported))

/-- All adaptive continuations preserve counter monotonicity; this does not assume success or bound the number of sessions. -/
theorem program_counter {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (program : OracleComp ServerAuthSpec α) (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run state)) :
    state.server.control.last_key_id.val ≤ result.2.server.control.last_key_id.val := by
  exact run_rel _ (fun before after => before.server.control.last_key_id.val ≤ after.server.control.last_key_id.val)
    (fun _ => le_refl _) (fun _ _ _ first second => first.trans second)
    (fun query before after reached => by
      rcases handler_counter setup codec checks publicValue beaconSeed query before after reached with same | next
      · rw [same]
      · rw [next]; omega)
    program state result supported

/-- Build attempts are charged even when the pending handle is absent or the outer writer fails. -/
def IsBuild : ServerAuthSpec.Domain → Prop
  | .inr (.build _ _) => True
  | _ => False
instance : DecidablePred IsBuild := fun query => by
  cases query with
  | inl coin => exact isFalse id
  | inr query => cases query <;> dsimp [IsBuild] <;> infer_instance

/-- An all-attempt build cap bounds the actual public counter increase without declaring any ambient source work free. -/
theorem program_counter_bound {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (program : OracleComp ServerAuthSpec α) (qBuild : Nat) (bounded : program.IsQueryBoundP IsBuild qBuild)
    (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run state)) :
    result.2.server.control.last_key_id.val ≤ state.server.control.last_key_id.val + qBuild := by
  apply run_count _ IsBuild (fun state => state.server.control.last_key_id.val) _ program qBuild bounded state result supported
  intro query before after reached
  by_cases build : IsBuild query
  · simp only [build, ite_true]
    rcases handler_counter setup codec checks publicValue beaconSeed query before after reached with same | next
    · rw [same]; omega
    · rw [next]
  · have quiet := quiet_control setup codec checks publicValue beaconSeed query
      (fun index payload equal => build (equal ▸ trivial)) before after reached
    simp only [quiet, build, ite_false, Nat.add_zero, le_refl]

/-- Any two successful responses separated by an arbitrary adaptive continuation have strictly increasing assigned IDs on the same live Server. -/
theorem ordered_response_ids {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (firstIndex lastIndex : Nat) (firstPayload lastPayload : Option Bytes) (state : GameState KemSK)
    (first : Option Response × GameState KemSK) (firstResponse : Response)
    (firstRun : first ∈ support ((buildOracle setup codec checks firstIndex firstPayload).run state))
    (firstReturned : first.1 = some firstResponse)
    (program : OracleComp ServerAuthSpec α) (middle : α × GameState KemSK)
    (continued : middle ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run first.2))
    (last : Option Response × GameState KemSK) (lastResponse : Response)
    (lastRun : last ∈ support ((buildOracle setup codec checks lastIndex lastPayload).run middle.2))
    (lastReturned : last.1 = some lastResponse) : firstResponse.keyId.val < lastResponse.keyId.val := by
  rcases build_oracle_counter setup codec checks firstIndex firstPayload state first firstRun with
    ⟨failed, _⟩ | ⟨response, returned, _, assigned⟩
  · simp only [firstReturned, Option.some_ne_none] at failed
  · cases Option.some.inj (returned.symm.trans firstReturned)
    rcases build_oracle_counter setup codec checks lastIndex lastPayload middle.2 last lastRun with
      ⟨failed, _⟩ | ⟨response, returned, counter, lastAssigned⟩
    · simp only [lastReturned, Option.some_ne_none] at failed
    · cases Option.some.inj (returned.symm.trans lastReturned)
      have monotone := program_counter setup codec checks publicValue beaconSeed program first.2 middle continued
      rw [assigned, lastAssigned, counter]
      omega

/-- The literal native build has the same failure/public-counter outcome, while its full family/cache/log poststate remains in the supported execution. -/
theorem native_build_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (seed : IdentitySeed) (scalar : ScalarBytes) (index : Nat)
    (payload : Option Bytes) (state : PqxdhServerAuthNative.NativeState KemSK)
    (result : Option Response × PqxdhServerAuthNative.NativeState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthNative.nativeBuild setup codec checks index payload).run state)) :
    (result.1 = none ∧ result.2.2.server = state.2.server) ∨ ∃ response,
      result.1 = some response ∧
      result.2.2.server.control.last_key_id.val = state.2.server.control.last_key_id.val + 1 ∧
      response.keyId = result.2.2.server.control.last_key_id := by
  apply build_oracle_counter setup codec checks index payload state.2 (result.1, result.2.2)
  apply PqxdhServerAuthNative.evaluate_support setup seed scalar _ state result
  rw [PqxdhServerAuthNative.build_native]
  exact supported

/-- Source-order constructors start at the public Server ID. Every actual adaptive execution retains the monotone counter and its all-attempt build cap, with no honest-registration or successful-publication premise. -/
theorem source_ordered_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (revealSeed : Bool) (adversary : Adversary) (qBuild : Nat)
    (bounded : ∀ input, (adversary input).IsQueryBoundP IsBuild qBuild)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthNative.sourceOrderedState setup codec checks revealSeed adversary)) :
    setup.serverKeyId.val ≤ result.2.2.1.server.control.last_key_id.val ∧
      result.2.2.1.server.control.last_key_id.val ≤ setup.serverKeyId.val + qBuild := by
  simp only [PqxdhServerAuthNative.sourceOrderedState, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, beaconSeed, _, scalar, _, keys, _, oneTime, _, published, publishedMember,
    final, finalMember, rfl⟩ := supported
  have original := PqxdhServerAuthNative.evaluate_support setup seed scalar _
    (PqxdhJointDhExtractFamily.empty, initialGameState setup (challenge setup.joint setup.dh seed scalar) published.2)
    final (by
      rw [PqxdhServerAuthNative.program_native setup codec checks seed scalar beaconSeed _ _
        (inv_initial setup codec beaconSeed (challenge setup.joint setup.dh seed scalar)
          oneTime keys.1 keys.2 published publishedMember)]
      exact finalMember)
  exact ⟨program_counter setup codec checks _ beaconSeed _ _ _ original,
    program_counter_bound setup codec checks _ beaconSeed _ qBuild (bounded _) _ _ original⟩

end BeaconcryptCore.Computational.PqxdhRegistrationResponse

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.next_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.next_id

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.prepared_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.prepared_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.after_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.after_publication

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.candidate_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.candidate_publication

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.build_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.build_publication

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.build_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.build_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.build_oracle_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.build_oracle_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.accept_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.accept_control

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.finish_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.finish_control

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.quiet_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.quiet_control

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.handler_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.handler_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.program_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.program_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.program_counter_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.program_counter_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.ordered_response_ids' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.ordered_response_ids

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.native_build_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.native_build_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationResponse.source_ordered_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationResponse.source_ordered_counter
