import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-!
The B5b negative control executes the original source admission and registration builder while privately recording its actual first-send KDF request. Its separate reveal returns a copy of the installed kernel with only the send chain replaced by that recorded input. The headline authentication handler and the actual installed kernel remain unchanged. Complete callback/program erasure and source support prove the provenance of the disclosed chain; no root-to-chain reconstruction or assumed successful publication supplies it.

The concrete adversary relays the honest Phase1, obtains one actual registration, then uses the altered reveal to recompute sequence-one material and reseal a different application payload. Its public commitment query and final delivery use the same shared cache and unchanged Beacon finish. With the existing functional control laws, accepting allocation checks, distinct nonempty bounded payloads and a nonexhausted Server identifier, the W2 winning probability is at least one minus ordinary KEM correctness error. The root-Extract and CTX/BLAKE2b random-oracle idealizations remain those of the original R1 experiment. This result tests the reveal boundary; it is not an attack on the unchanged headline protocol.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RepresentationBridge (absMaterial)
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthPresealControl
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthExperiment PqxdhServerAuthNegativeControl
open PqxdhEd25519EufCma (Ed25519PublicKey)
open PqxdhRootTableInitialization (rootArray)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

abbrev TailState := List SymmetricRatchetKdfRequest ×
  RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)

def recordKdf (query : PqxdhServerRegistrationPublication.TailSpec.Domain)
    (prior : List SymmetricRatchetKdfRequest) : List SymmetricRatchetKdfRequest :=
  match query with
  | .inl (.inl request) => prior ++ [request]
  | _ => prior

/-- The original callback executes exactly once before retaining its literal KDF request. The record is private until the altered negative-control reveal. -/
noncomputable def tail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl PqxdhServerRegistrationPublication.TailSpec (StateT TailState ProbComp) :=
  fun query state =>
    (fun result => (result.1, (recordKdf query state.1, result.2))) <$>
      (tailImpl setup codec checks query).run state.2

/-- Erasing only the added request history returns the same optional reply, source log and cache after each actual callback. -/
theorem tail_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (state : TailState) :
    Prod.map id Prod.snd <$> (tail setup codec checks query).run state =
      (tailImpl setup codec checks query).run state.2 := by
  simp only [tail, StateT.run, Functor.map_map]
  exact id_map _

/-- Every complete original tail program retains its full evaluated computation after the new request list is erased. -/
theorem program_erase {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (work : OracleComp PqxdhServerRegistrationPublication.TailSpec Result) (state : TailState) :
    Prod.map id Prod.snd <$> (simulateQ (tail setup codec checks) work).run state =
      (simulateQ (tailImpl setup codec checks) work).run state.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd (tail_erase setup codec checks) work state

/-- The observation adds no probabilistic query and removes none, for every predicate and every complete source continuation. -/
theorem program_queries {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (work : OracleComp PqxdhServerRegistrationPublication.TailSpec Result) (state : TailState)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((simulateQ (tail setup codec checks) work).run state).IsQueryBoundP predicate bound ↔
      ((simulateQ (tailImpl setup codec checks) work).run state.2).IsQueryBoundP predicate bound := by
  rw [← program_erase setup codec checks work state, isQueryBoundP_map_iff]

/-- The added history is precisely the reached KDF request; seal and auxiliary callbacks leave it unchanged even on optional rejection. -/
theorem tail_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (state : TailState)
    (result : PqxdhServerRegistrationPublication.TailSpec.Range query × TailState)
    (supported : result ∈ support ((tail setup codec checks query).run state)) :
    result.2.1 = recordKdf query state.1 := by
  simp only [tail, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨value, _, rfl⟩ := supported
  rfl

/-- The actual fixed-HKDF response is unchanged while its exact input and domain label are retained. -/
theorem tail_kdf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (request : SymmetricRatchetKdfRequest) (state : TailState) :
    (tail setup codec checks (.inl (.inl request))).run state =
      pure (RawCtxSourceHkdf.response setup.source.crypto request, (state.1 ++ [request], state.2)) := by
  change (fun result => (result.1, (state.1 ++ [request], result.2))) <$>
    (tailImpl setup codec checks (.inl (.inl request))).run state.2 = _
  rw [tailImpl_kdf_run, map_pure]

/-- The original extracted sender reaches the observed source tail through its unchanged two adapters. -/
noncomputable def sendImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl (RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT TailState ProbComp) :=
  (tail setup codec checks ∘ₛ PqxdhServerRegistrationPublication.sendLift) ∘ₛ RawCtxSourceSend.adapter

/-- Sealing, hashing and optional framing do not change the saved source KDF-request list. -/
theorem send_seal_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : SendSeal RawCtxSourceSend.SealContext) (state : TailState)
    (result : Option RawCtxSourceSend.Encrypted × TailState)
    (supported : result ∈ support ((sendImpl setup codec checks (.inr pending)).run state)) :
    result.2.1 = state.1 := by
  simp only [sendImpl, QueryImpl.apply_compose, RawCtxSourceSend.adapter, bind_pure_comp,
    PqxdhServerRegistrationPublication.sendLift, simulateQ_map, simulateQ_spec_query,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, seen, rfl⟩ := supported
  exact tail_history setup codec checks (.inl (.inr (RawCtxSourceSend.arguments pending))) state inner seen

/-- Every reached nonexhausted source send records exactly its actual old chain and production domain label, even if sealing or framing fails. -/
theorem send_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) (state : TailState)
    (notFull : kernel.refined.control.send_sequence ≠ core.num.U64.MAX)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × TailState)
    (supported : result ∈ support ((simulateQ (sendImpl setup codec checks)
      (RawCtxSourceSend.send kernel context)).run state)) :
    result.2.1 = state.1 ++ [⟨kernel.refined.send_chain.bytes, SYM_RATCHET_INFO⟩] := by
  obtain ⟨pending, response, afterKdf, _, _, input, label, kdf, sealedRun, _⟩ :=
    RawCtxSourceSend.send_nonexhausted_support (sendImpl setup codec checks)
      kernel context state notFull result supported
  simp only [sendImpl, QueryImpl.apply_compose, RawCtxSourceSend.adapter,
    PqxdhServerRegistrationPublication.sendLift, simulateQ_spec_query] at kdf
  rw [send_seal_history setup codec checks _ afterKdf (result.1.2, result.2) sealedRun,
    tail_history setup codec checks (.inl (.inl pending.request)) state (response, afterKdf) kdf]
  simp only [recordKdf, ← input, ← label]

/-- The complete post-initialization continuation retains the one reached send request through erasure, optional framing and the optional outer writer. -/
theorem after_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ConcreteRatchetKernel)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) (state : TailState)
    (notFull : kernel.refined.control.send_sequence ≠ core.num.U64.MAX)
    (result : (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) × TailState)
    (supported : result ∈ support ((simulateQ (tail setup codec checks)
      (PqxdhServerRegistrationPublication.afterInitialization candidate authenticated kernel () server)).run state)) :
    result.2.1 = state.1 ++ [⟨kernel.refined.send_chain.bytes, SYM_RATCHET_INFO⟩] := by
  obtain ⟨sent, afterSend, afterErase, hsent, herase, rest⟩ :=
    PqxdhServerRegistrationPublication.afterInitialization_support _ candidate authenticated kernel () server state result supported
  have sentHistory := send_history setup codec checks kernel
    (PqxdhServerRegistrationPublication.firstContext candidate authenticated) state notFull
    (sent, afterSend) (by simpa only [sendImpl, QueryImpl.simulateQ_compose] using hsent)
  have eraseHistory := tail_history setup codec checks (.inr (.erase authenticated)) afterSend ((), afterErase) herase
  cases hs : sent.2 with
  | none =>
      rw [hs] at rest
      rw [rest, eraseHistory, sentHistory]
      rfl
  | some encrypted =>
      rw [hs] at rest
      obtain ⟨written, afterWrite, hwritten, rfl⟩ := rest
      rw [tail_history setup codec checks (.inr (.write (PqxdhServerRegistrationPublication.responseFields candidate encrypted)))
        afterErase (written, afterWrite) hwritten, eraseHistory, sentHistory]
      rfl

/-- Successful outer publication installs the advanced kernel under the exact key ID returned to the client. -/
theorem after_peer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ConcreteRatchetKernel)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) (state : TailState)
    (result : (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) × TailState)
    (supported : result ∈ support ((simulateQ (tail setup codec checks)
      (PqxdhServerRegistrationPublication.afterInitialization candidate authenticated kernel () server)).run state))
    (response : PqxdhServerRegistrationPublication.Response) (published : result.1.1 = some response) :
    ∃ advanced, result.1.2.server.peers response.keyId =
      some ⟨candidate.beacon_identity_public_key, advanced, ()⟩ := by
  obtain ⟨sent, afterSend, afterErase, _, _, rest⟩ :=
    PqxdhServerRegistrationPublication.afterInitialization_support _ candidate authenticated kernel () server state result supported
  cases hs : sent.2 with
  | none =>
      rw [hs] at rest
      rw [rest] at published
      cases published
  | some encrypted =>
      rw [hs] at rest
      obtain ⟨written, afterWrite, _, rfl⟩ := rest
      cases written with
      | none => cases published
      | some bytes =>
          cases published
          refine ⟨sent.1, ?_⟩
          simp only [Option.isSome_some, ite_true, PqxdhServerRegistrationPublication.publish,
            Function.update_self]

/-- The unchanged stateless allocation, erasure and serialization results. -/
def auxReply (codec : Codec Reader Response) (checks : Checks) :
    (query : PqxdhServerRegistrationPublication.AuxQuery) →
      PqxdhServerRegistrationPublication.AuxSpec.Range query
  | .checkIdentity identity => checks.beaconIdentity identity
  | .reservePeer => checks.reservePeer
  | .reservePlaintext length => checks.reservePlaintext length
  | .erase _ => ()
  | .write fields => codec.write2 fields

/-- All observed auxiliary calls are the same stateless source callbacks; only the original KDF interface appends a request. -/
theorem tail_aux (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.AuxQuery) (state : TailState) :
    (tail setup codec checks (.inr query)).run state = pure (auxReply codec checks query, state) := by
  change (fun result => (result.1, (state.1, result.2))) <$>
    (tailImpl setup codec checks (.inr query)).run state.2 = _
  rw [tailImpl_aux]
  cases query <;> simp only [tailAux, StateT.run_pure, map_pure, auxReply]

/-- Every successful actual builder execution records exactly the source initializer's old send chain and installs a peer at the returned key ID. Rejected callbacks, optional writers and all original state remain in the execution. -/
theorem build_history_peer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) (state : TailState)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) × TailState)
    (supported : result ∈ support ((simulateQ (tail setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () server)).run state))
    (response : PqxdhServerRegistrationPublication.Response)
    (published : (settle server result.1).1 = some response) :
    ∃ kernel, PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel ∧
      result.2.1 = state.1 ++ [⟨kernel.refined.send_chain.bytes, SYM_RATCHET_INFO⟩] ∧
      ((settle server result.1).2.server.peers response.keyId).isSome = true := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok server.control
  simp only [PqxdhServerRegistrationPublication.build, hnext, PqxdhServerRegistrationPublication.continueRust]
    at supported
  cases next with
  | Err error =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported] at published
      cases published
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        server.control pending ⟨server.server.identity, server.identityKeyId⟩
        (if (server.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
      simp only [hprepared] at supported
      cases prepared with
      | Err error =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          rw [supported] at published
          cases published
      | Ok candidate =>
          obtain ⟨kernel, hrun, _, _, refines⟩ :=
            PqxdhRootTableInitialization.initialize_refines setup.source PqxdhServerAuthExperiment.unitRatchet false root
          have hinit : BeaconcryptCore.Refinement.ServerTransactionRefinement.initializeCandidate candidate
              (PqxdhRootTableInitialization.rootArray root)
              (PqxdhRootTableInitialization.initialResponse setup.source.crypto) = ok kernel :=
            (PqxdhServerRegistrationPublication.candidate_initialization setup.source candidate root).trans hrun
          obtain ⟨binding, hbinding, hbytes⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
          simp only [PqxdhServerRegistrationPublication.candidateTail, hinit, hbinding,
            PqxdhServerRegistrationPublication.continueRust, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, mem_support_bind_iff, tail_aux, auxReply, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, rfl, supported⟩ := supported
          cases hvalid : checks.beaconIdentity candidate.beacon_identity_public_key
          · simp only [hvalid, Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            rw [supported] at published
            cases published
          simp only [hvalid, Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, mem_support_bind_iff, tail_aux, auxReply,
            support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, rfl, supported⟩ := supported
          cases hreserved : checks.reservePeer
          · simp only [hreserved, Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            rw [supported] at published
            cases published
          simp only [hreserved, Bool.not_true, Bool.false_eq_true, ite_false] at supported
          by_cases empty : (payload.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = true
          · simp only [empty, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            rw [supported] at published
            cases published
          simp only [empty, Bool.false_eq_true, ite_false] at supported
          split_ifs at supported with fits
          · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff, tail_aux,
              auxReply, support_pure, Set.mem_singleton_iff] at supported
            obtain ⟨_, rfl, supported⟩ := supported
            cases hallocated : checks.reservePlaintext
                (8 + (payload.getD PqxdhServerRegistrationPublication.registrationWitness).length)
            · simp only [hallocated, Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at supported
              rw [supported] at published
              cases published
            simp only [hallocated, Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map,
              support_map, Set.mem_image] at supported
            obtain ⟨inner, innerSupported, rfl⟩ := supported
            rw [hbytes] at innerSupported
            have notFull : kernel.refined.control.send_sequence ≠ core.num.U64.MAX := by
              intro equal
              have values := congrArg UScalar.val equal
              simp only [refines.sendSequence] at values
              contradiction
            have history := after_history setup codec checks candidate _ kernel server state notFull inner innerSupported
            have innerPublished : inner.1.1 = some response := published
            obtain ⟨advanced, peer⟩ := after_peer setup codec checks candidate _ kernel server state inner innerSupported
              response innerPublished
            refine ⟨kernel, hrun, history, ?_⟩
            change (inner.1.2.server.peers response.keyId).isSome = true
            rw [peer]
            rfl
          · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
            rw [supported] at published
            cases published

/-- The negative control adds only the saved actual pre-seal requests. The full original experiment state is retained. -/
structure ControlState (KemSK : Type) where
  ordinary : GameState KemSK
  saved : Std.U64 → Option SymmetricRatchetKdfRequest

abbrev ControlGame (KemSK : Type) := StateT (ControlState KemSK) (OracleComp PqxdhJointDhExtractRoot.RootSpec)

/-- Every unchanged capability executes its complete original program and leaves the private saved-request map untouched. -/
def forward {Result : Type} (work : Game KemSK Result) : ControlGame KemSK Result := fun state =>
  (fun result => (result.1, { state with ordinary := result.2 })) <$> work.run state.ordinary

/-- The original publication update, with no saved-chain component. -/
def ordinaryBuilt (session : Nat) (state : GameState KemSK)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    Option PqxdhServerRegistrationPublication.Response × GameState KemSK :=
  let settled := settle state.server result.1
  (settled.1, { state with
    pending := Function.update state.pending session none
    server := settled.2
    ctx := result.2.2
    ghost := { state.ghost with seals := state.ghost.seals ++ result.2.1.map (fun context => (session, context)) } })

/-- The altered build saves only a request actually observed in this build, under its successful response's assigned key ID. -/
def builtState (session : Nat) (state : ControlState KemSK)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) × TailState) :
    Option PqxdhServerRegistrationPublication.Response × ControlState KemSK :=
  let settled := settle state.ordinary.server result.1
  let saved := match settled.1, result.2.1.head? with
    | some response, some request => Function.update state.saved response.keyId (some request)
    | _, _ => state.saved
  (settled.1, ⟨{ state.ordinary with
    pending := Function.update state.ordinary.pending session none
    server := settled.2
    ctx := result.2.2.2
    ghost := { state.ordinary.ghost with seals := state.ordinary.ghost.seals ++ result.2.2.1.map (fun context => (session, context)) } }, saved⟩)

/-- The altered builder executes the same literal extracted builder once, with the source observer. Its ordinary protocol update is unchanged. -/
noncomputable def build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) : ControlGame KemSK (Option PqxdhServerRegistrationPublication.Response) :=
  fun state => match state.ordinary.pending session with
  | none => pure (none, state)
  | some token => familyCoins (builtState session state <$> (simulateQ (tail setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () state.ordinary.server)).run
        ([], ([], state.ordinary.ctx)))

/-- Only the returned copy of the actual installed kernel is changed: the saved chain replaces its send chain. No internal installed state is rolled back. -/
def reveal (keyId : Std.U64) (state : ControlState KemSK) : Option ConcreteRatchetKernel := do
  let kernel ← revealKernel keyId state.ordinary
  match state.saved keyId with
  | none => some kernel
  | some request => some { kernel with refined := { kernel.refined with send_chain := ⟨request.input⟩ } }

/-- This separate handler changes only build's private observation and the reveal result; the headline handler is untouched. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) : QueryImpl ServerAuthSpec (ControlGame KemSK)
  | .inr (.build session payload) => build setup codec checks session payload
  | .inr (.reveal keyId) => fun state => pure (reveal keyId state, state)
  | query => forward (authHandler setup codec checks publicValue beaconSeed query)

/-- Any unchanged complete capability has exact ordinary-state erasure, for every saved map. -/
theorem forward_erase {Result : Type} (work : Game KemSK Result) (state : ControlState KemSK) :
    Prod.map id ControlState.ordinary <$> (forward work).run state = work.run state.ordinary := by
  simp only [forward, StateT.run, Functor.map_map]
  exact id_map _

/-- A successful observed source build makes the pre-seal reveal return precisely its actual old chain, while requiring an installed peer under the response key ID. -/
theorem built_reveal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (state : ControlState KemSK) (pending : pqxdh.PendingServerRegistration)
    (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) × TailState)
    (supported : result ∈ support ((simulateQ (tail setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () state.ordinary.server)).run
        ([], ([], state.ordinary.ctx))))
    (response : PqxdhServerRegistrationPublication.Response)
    (published : (settle state.ordinary.server result.1).1 = some response) :
    ∃ initial revealed, PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok initial ∧
      reveal response.keyId (builtState session state result).2 = some revealed ∧
      revealed.refined.send_chain = initial.refined.send_chain := by
  obtain ⟨initial, init, history, installed⟩ := build_history_peer setup codec checks pending root payload
    state.ordinary.server ([], ([], state.ordinary.ctx)) result supported response published
  cases hp : (settle state.ordinary.server result.1).2.server.peers response.keyId with
  | none => simp only [hp, Option.isSome_none, Bool.false_eq_true] at installed
  | some peer =>
      refine ⟨initial, { peer.kernel with refined := { peer.kernel.refined with send_chain := initial.refined.send_chain } },
        init, ?_, rfl⟩
      simp only [reveal, builtState, published, history, List.nil_append, List.head?_cons,
        Function.update_self, revealKernel, hp, Option.map_some]
      rfl

/-- Erasing the private request map from the altered build preserves the original complete build program, including both caches, pending-token disposal, optional reply and seal history. -/
theorem build_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : ControlState KemSK) :
    Prod.map id ControlState.ordinary <$> (build setup codec checks session payload).run state =
      (buildOracle setup codec checks session payload).run state.ordinary := by
  change Prod.map id ControlState.ordinary <$> build setup codec checks session payload state = _
  simp only [build, buildOracle, StateT.run_bind, StateT.run_get, pure_bind]
  cases hp : state.ordinary.pending session with
  | none => simp only [StateT.run_pure, map_pure]; rfl
  | some token =>
      simp only [liftCoins, StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_set, map_pure,
        bind_pure_comp]
      rw [← program_erase setup codec checks
        (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () state.ordinary.server)
        ([], ([], state.ordinary.ctx))]
      simp only [familyCoins, simulateQ_map, Functor.map_map]
      rfl

/-- The adversary locally recomputes sequence-one material from the revealed actual chain, uses only public transcript fields, asks the ordinary commitment oracle and delivers a freshly written Phase2 carrying its different payload. -/
noncomputable def reseal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : AuthInput) (identity : Ed25519PublicKey) (other : Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response) (kernel : ConcreteRatchetKernel) :
    OracleComp ServerAuthSpec Unit :=
  match codec.read2 response.serialized with
  | none => pure ()
  | some original =>
      match codec.ciphertext original, codec.ephemeral original with
      | some ciphertext, some ephemeral => do
          let material := chainMaterial setup.source.crypto kernel.refined.send_chain
          let ad := absBytes (PqxdhBeaconPhase2Shared.associatedData (controlOf input identity))
          let sealed := setup.source.crypto.aeadSeal (absMaterial material).1 (absMaterial material).2 ad
            (Pqxdh.LE64 response.keyId.val ++ other)
          let digest ← (ServerAuthSpec.query (.inr (.hash (Pqxdh.ctxPreimage (absMaterial material)
            ⟨ad, 1, input.serverKeyId.val⟩ sealed.2))) : OracleComp ServerAuthSpec CtxRomAuth.CtxDigest)
          match codec.frameWrite ⟨1#u64, input.serverKeyId, sealed.1 ++ sealed.2 ++ digest.toList⟩ with
          | none => pure ()
          | some frameBytes =>
              match codec.write2 ⟨response.keyId, ephemeral, PqxdhRootTableInitialization.rootArray input.server.ed25519,
                  ciphertext, frameBytes⟩ with
              | none => pure ()
              | some phase2 => do
                  let _ ← (ServerAuthSpec.query (.inr (.finish phase2)) : OracleComp ServerAuthSpec (Option Pqxdh.Bytes))
                  pure ()
      | _, _ => pure ()

/-- The public response selects the ordinary reveal handle; only a present kernel permits the attack continuation. -/
noncomputable def revealThen (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : AuthInput) (identity : Ed25519PublicKey) (other : Pqxdh.Bytes) :
    Option PqxdhServerRegistrationPublication.Response → OracleComp ServerAuthSpec Unit
  | none => pure ()
  | some response => do
      let disclosed ← (ServerAuthSpec.query (.inr (.reveal response.keyId)) :
        OracleComp ServerAuthSpec (Option ConcreteRatchetKernel))
      match disclosed with
      | none => pure ()
      | some kernel => reseal setup codec input identity other response kernel

/-- The control obtains one actual Server response, retaining its exact optional admission and publication result. -/
noncomputable def buildThen (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : AuthInput) (identity : Ed25519PublicKey) (payload other : Pqxdh.Bytes) :
    Option Nat → OracleComp ServerAuthSpec Unit
  | none => pure ()
  | some session => do
      let response ← (ServerAuthSpec.query (.inr (.build session (some payload))) :
        OracleComp ServerAuthSpec (Option PqxdhServerRegistrationPublication.Response))
      revealThen setup codec input identity other response

/-- The pre-seal control relays the target's actual Phase1 to one Server accept/build, reveals the altered installed kernel, then seals a different application payload. It draws no coins and makes no public HMAC request. -/
noncomputable def adversary (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (payload other : Pqxdh.Bytes) : Adversary := fun input =>
  match input.phase1 with
  | none => pure ()
  | some bytes =>
      match parsePhase1 codec bytes with
      | none => pure ()
      | some parsed => do
          let session ← (ServerAuthSpec.query (.inr (.accept bytes)) : OracleComp ServerAuthSpec (Option Nat))
          buildThen setup codec input parsed.1 payload other session

/-- The altered experiment's evaluated run, on the original restricted Extract family and original shared CTX cache. -/
noncomputable def run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) {Result : Type}
    (work : OracleComp ServerAuthSpec Result) (state : ControlState KemSK)
    (family : PqxdhJointDhExtractFamily.State) :
    ProbComp ((Result × ControlState KemSK) × PqxdhJointDhExtractFamily.State) :=
  (simulateQ (romReduction setup seed scalar) ((simulateQ (handler setup codec checks
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed) work).run state)).run family

/-- The concrete altered evaluator preserves every adaptive continuation. -/
theorem run_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) {A B : Type}
    (first : OracleComp ServerAuthSpec A) (next : A → OracleComp ServerAuthSpec B)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    run setup codec checks seed scalar beaconSeed (first >>= next) state family =
      run setup codec checks seed scalar beaconSeed first state family >>= fun result =>
        run setup codec checks seed scalar beaconSeed (next result.1.1) result.1.2 result.2 := by
  simp only [run, simulateQ_bind, StateT.run_bind]

/-- Pure control code preserves the complete source and both observation states. -/
theorem run_pure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) {A : Type} (value : A)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    run setup codec checks seed scalar beaconSeed (pure value) state family = pure ((value, state), family) := by
  simp only [run, simulateQ_pure, StateT.run_pure]

/-- A control query runs its exact source handler once. -/
theorem run_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    run setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query query)) state family =
      (simulateQ (romReduction setup seed scalar) ((handler setup codec checks
        (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed query).run state)).run family := by
  simp only [run, simulateQ_spec_query]

/-- Every ordinary source program is forwarded with its exact optional answer, source/cache poststate and unchanged saved map. -/
theorem forward_run {A : Type} (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : Game KemSK A) (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    (simulateQ (romReduction setup seed scalar) ((forward work).run state)).run family =
      (fun result => ((result.1.1, { state with ordinary := result.1.2 }), result.2)) <$>
        (simulateQ (romReduction setup seed scalar) (work.run state.ordinary)).run family := by
  change (simulateQ (romReduction setup seed scalar)
    ((fun result => (result.1, { state with ordinary := result.2 })) <$> work.run state.ordinary)).run family = _
  simp only [simulateQ_map, StateT.run_map]

/-- The concrete attack has at most one accept, zero public HMAC calls and one public commitment-hash request, counting every optional-rejection branch. -/
theorem adversary_budget (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (payload other : Pqxdh.Bytes) : AuthBudget (adversary setup codec payload other) 1 0 1 := by
  refine ⟨fun input => ?_, fun input => ?_, fun input => ?_⟩ <;>
  · unfold adversary
    split
    · simp
    · split
      · simp
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery], fun session => ?_⟩
        unfold buildThen
        split
        · simp
        · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
            ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery], fun response => ?_⟩
          unfold revealThen
          split
          · simp
          · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
              ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery], fun kernel => ?_⟩
            split
            · simp
            · unfold reseal
              split
              · simp
              · split
                · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
                    ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery], fun digest => ?_⟩
                  split
                  · simp
                  · split
                    · simp
                    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
                        ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery], fun _ => by simp⟩
                · simp

/-- The original secret samplers and Phase1 publication run unchanged; only the separate control handler is selected afterward. -/
noncomputable def controlBody (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (client : Adversary) (publicValue : PublicChallenge) : OracleComp PqxdhJointDhExtractRoot.RootSpec (GameState KemSK) := do
  let beaconSeed ← familyCoins sampleSeed
  let oneTime ← familyCoins PqxdhJointGapDh.sampleScalar
  let keys ← familyCoins (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let published ← familyCoins (phase1Run setup codec beaconSeed publicValue oneTime keys.1 keys.2)
  let input : AuthInput := ⟨publicValue.identity, setup.serverKeyId, published.1, none⟩
  (fun result => result.2.ordinary) <$> (simulateQ (handler setup codec checks publicValue beaconSeed) (client input)).run
    ⟨initialGameState setup publicValue published.2, fun _ => none⟩

/-- The altered reveal experiment uses the same complete constructor schedule, family table and final event state as R1. The extra saved-chain map is erased from the final observation. -/
noncomputable def controlState (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (client : Adversary) :
    ProbComp (IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State) := do
  let seed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar
  let result ← (simulateQ (romReduction setup seed scalar) (controlBody setup codec checks client publicValue)).run
    PqxdhJointDhExtractFamily.empty
  pure (seed, scalar, result.1, result.2)

/-- A pending-token build runs the observed literal tail once; every original source effect and the family cache remain visible in the complete result. -/
theorem run_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (session : Nat)
    (payload : Option Pqxdh.Bytes) (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State)
    (token : PqxdhServerRelatedRootConsumer.Returned) (pending : state.ordinary.pending session = some token) :
    run setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query (.inr (.build session payload))))
      state family = (fun result => (builtState session state result, family)) <$>
      (simulateQ (tail setup codec checks)
        (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () state.ordinary.server)).run
          ([], ([], state.ordinary.ctx)) := by
  rw [run_query]
  change (simulateQ (romReduction setup seed scalar) (build setup codec checks session payload state)).run family = _
  simp only [build, pending, romReduction]
  rw [rom_coins]
  simp only [Functor.map_map]

/-- The altered reveal is deterministic, changes no state or cache, and adds no primitive work. -/
theorem run_reveal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (keyId : Std.U64)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    run setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query (.inr (.reveal keyId)))) state family =
      pure ((reveal keyId state, state), family) := by
  rw [run_query]
  simp only [handler]
  rfl

/-- Accept runs the entire unchanged source operation and carries the exact private saved map forward. -/
theorem run_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (bytes : Pqxdh.Bytes)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    run setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query (.inr (.accept bytes)))) state family =
      (fun result => ((result.1.1, { state with ordinary := result.1.2 }), result.2)) <$>
        runAdversary setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query (.inr (.accept bytes))))
          state.ordinary family := by
  rw [run_query, runAdversary_query]
  exact forward_run setup seed scalar (acceptOracle setup codec checks
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) bytes) state family

/-- The public commitment request uses the original shared cache, with no second sampled digest or changed history. -/
theorem run_hash (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (bytes : Pqxdh.Bytes)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    run setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query (.inr (.hash bytes)))) state family =
      (fun result => ((result.1.1, { state with ordinary := result.1.2 }), result.2)) <$>
        runAdversary setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query (.inr (.hash bytes))))
          state.ordinary family := by
  rw [run_query, runAdversary_query]
  exact forward_run setup seed scalar (hashOracle bytes) state family

/-- The delivered replacement still goes through the unchanged one-shot source Beacon finish and its exact optional plaintext/state result. -/
theorem run_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (bytes : Pqxdh.Bytes)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    run setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query (.inr (.finish bytes)))) state family =
      (fun result => ((result.1.1, { state with ordinary := result.1.2 }), result.2)) <$>
        runAdversary setup codec checks seed scalar beaconSeed (liftM (ServerAuthSpec.query (.inr (.finish bytes))))
          state.ordinary family := by
  rw [run_query, runAdversary_query]
  exact forward_run setup seed scalar (finishOracle setup codec
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed bytes) state family

/-- Given the actual revealed first-send chain and the already-produced source partner/seal history, the replacement ciphertext reaches the original Beacon handler and wins W2. The following source-builder consumer supplies these operational facts. -/
theorem reseal_wins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (limit : Nat) (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (other : Pqxdh.Bytes) (nonempty : other ≠ []) (short : other.length + 88 < limit)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (reader : Reader) (e : ScalarBytes)
    (encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret)
    (good : functional.result keys.2 encapsulated.1 = some encapsulated.2)
    (bytes : Pqxdh.Bytes) (prk : HmacBlock)
    (hinputS : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar
      (PqxdhServerRelatedRootInput.message (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
        beaconSeed oneTime keys.1 reader e encapsulated)) = some bytes)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State)
    (hbeacon : state.ordinary.beacon = publishedBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed oneTime keys.2)
    (context : RawCtxSourceSend.SealContext) (different : context.plaintext.drop 8 ≠ other)
    (hghost : state.ordinary.ghost = ⟨[.session 0 (PqxdhServerRelatedRootInput.message (honestInputs setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1 reader e encapsulated))
        (some (expandRoot setup.hmac prk))], [(0, context)], none⟩)
    (hprk : family.cache bytes = some prk)
    (phase1 : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response) (original : Response)
    (originalRead : codec.read2 response.serialized = some original)
    (originalCt : codec.ciphertext original = some (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1))
    (originalEphemeral : codec.ephemeral original = some (rootArray (setup.dh.publicKey e)))
    (initial disclosed : ConcreteRatchetKernel)
    (initialized : PqxdhRootTableInitialization.initialKernelRun setup.source false (expandRoot setup.hmac prk) = ok initial)
    (disclosedChain : disclosed.refined.send_chain = initial.refined.send_chain)
    (result : (Unit × ControlState KemSK) × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (run setup codec checks seed scalar beaconSeed
      (reseal setup codec (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) phase1 none)
        (setup.joint.publicKeys beaconSeed).ed25519 other response disclosed) state family)) :
    W2 setup seed scalar result.1.2.ordinary.ghost := by
  have material := material_agree setup.source (expandRoot setup.hmac prk) initial initialized
  simp only [reseal, originalRead, originalCt, originalEphemeral, disclosedChain, material] at supported
  rw [run_bind, mem_support_bind_iff] at supported
  obtain ⟨hashed, hashRun, supported⟩ := supported
  rw [run_hash, support_map, Set.mem_image] at hashRun
  obtain ⟨nativeHash, nativeHashRun, rfl⟩ := hashRun
  obtain ⟨cache, hashState, cached, sameFamily⟩ :=
    PqxdhServerAuthNegativeControl.run_hash setup codec checks seed scalar beaconSeed _ state.ordinary family nativeHash nativeHashRun
  have hshort : ∀ key nonce ad : Pqxdh.Bytes, ∀ digest : CtxRomAuth.CtxDigest,
      ((setup.source.crypto.aeadSeal key nonce ad (Pqxdh.LE64 response.keyId.val ++ other)).1 ++
        (setup.source.crypto.aeadSeal key nonce ad (Pqxdh.LE64 response.keyId.val ++ other)).2 ++
          digest.toList).length < limit := by
    intro key nonce ad digest
    rw [protected_length _ laws.bodyLength, List.length_append, Pqxdh.LE64_length]
    omega
  split at supported
  · rename_i refused
    exact absurd refused (frame_written laws _ (hshort _ _ _ _))
  rename_i frameBytes frameWritten
  split at supported
  · rename_i refused
    exact absurd refused (phase2_written laws _ frameBytes (hshort _ _ _ _) frameWritten _ _ _ _)
  rename_i phase2 phase2Written
  rw [run_bind, mem_support_bind_iff] at supported
  obtain ⟨finished, finishRun, supported⟩ := supported
  rw [run_pure, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨decoded, decodedRead, decodedCt, decodedEphemeral, decodedIdentity, decodedId, decodedApp⟩ :=
    laws.phase2 _ phase2 phase2Written
  obtain ⟨frameNonempty, frameRead⟩ := laws.frame _ frameBytes frameWritten
  have decap : functional.result keys.2 (PqxdhPhase2InputBytes.ciphertext
      (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1)) = some encapsulated.2 := by
    rw [(PqxdhPhase2InputBytes.ciphertext_roundtrip (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1)
      encapsulated.1).2]
    exact good
  have bodyNonempty : ∀ key nonce ad : Pqxdh.Bytes, (setup.source.crypto.aeadSeal key nonce ad
      (Pqxdh.LE64 response.keyId.val ++ other)).1 ≠ [] := by
    intro key nonce ad empty
    have length := laws.bodyLength key nonce ad (Pqxdh.LE64 response.keyId.val ++ other)
    rw [empty, List.length_append, Pqxdh.LE64_length] at length
    simp at length
  have beaconInput := beacon_input_eq setup laws.nonzero seed scalar beaconSeed oneTime e decoded
    (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1) response.keyId encapsulated.2 keys.1
  rw [← server_input_eq, hinputS] at beaconInput
  obtain ⟨beacon', family', finishedEq⟩ := beacon_finish setup codec functional laws.nonzero seed scalar beaconSeed
    oneTime e keys.2 phase2 decoded (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1) response.keyId
    encapsulated.2 decodedRead decodedCt decodedEphemeral decodedIdentity decodedId decap frameBytes _ _ _ other
    nativeHash.1.1 decodedApp frameNonempty frameRead rfl rfl rfl (bodyNonempty _ _ _) nonempty
    bytes prk nativeHash.2 beaconInput (by rw [sameFamily]; exact hprk) rfl nativeHash.1.2
    (by rw [hashState]; exact hbeacon) (by
      rw [hashState]
      rw [disclosedChain, material] at cached
      exact cached)
  rw [run_finish, runAdversary_query] at finishRun
  change finished ∈ support ((fun value => ((value.1.1,
    { state with ordinary := value.1.2 }), value.2)) <$>
      (simulateQ (romReduction setup seed scalar) ((finishOracle setup codec
        (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed phase2).run nativeHash.1.2)).run nativeHash.2)
    at finishRun
  rw [finishedEq, map_pure, support_pure, Set.mem_singleton_iff] at finishRun
  subst supported
  subst finishRun
  simp only [W2, hashState, hghost, Ghost.accept, Option.some.injEq, exists_eq_left']
  refine ⟨⟨0, ?_⟩, ?_⟩
  · refine ⟨PqxdhServerRelatedRootInput.message (honestInputs setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1 reader e encapsulated),
      some (expandRoot setup.hmac prk), bytes, by simp, hinputS, ?_⟩
    simp only [PqxdhServerAuthExperiment.beaconInput, firstBeacon, List.singleton_append,
      List.findSome?_cons, Option.bind_some, rootInput]
    exact beaconInput
  · intro index _ sealedContext member same
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact different (congrArg Accepted.payload same)

/-- The actual observed build and altered reveal discharge the resealing lemma's old-chain premise. Publication liveness is a source property, consumed from accepting checks and bounded writers by the complete control theorem. -/
theorem after_accept_wins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (limit : Nat) (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload other : Pqxdh.Bytes) (different : payload ≠ other)
    (nonempty : other ≠ []) (short : other.length + 88 < limit)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (reader : Reader) (e : ScalarBytes)
    (encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret)
    (good : functional.result keys.2 encapsulated.1 = some encapsulated.2)
    (bytes : Pqxdh.Bytes) (prk : HmacBlock)
    (hinputS : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar
      (PqxdhServerRelatedRootInput.message (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
        beaconSeed oneTime keys.1 reader e encapsulated)) = some bytes)
    (state : ControlState KemSK) (family : PqxdhJointDhExtractFamily.State)
    (pending : state.ordinary.pending 0 = some ⟨expandRoot setup.hmac prk, PqxdhServerClearedRoot.pending
      (binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))
        (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1
          reader e encapsulated)⟩)
    (hbeacon : state.ordinary.beacon = publishedBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed oneTime keys.2)
    (hghost : state.ordinary.ghost = ⟨[.session 0 (PqxdhServerRelatedRootInput.message (honestInputs setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1 reader e encapsulated))
        (some (expandRoot setup.hmac prk))], [], none⟩)
    (hprk : family.cache bytes = some prk)
    (publishes : Publishes setup codec checks (PqxdhServerClearedRoot.pending
      (binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))
      (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1
        reader e encapsulated)) (expandRoot setup.hmac prk) (some payload) state.ordinary.server state.ordinary.ctx)
    (phase1 : Option Pqxdh.Bytes) (result : (Unit × ControlState KemSK) × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (run setup codec checks seed scalar beaconSeed
      (buildThen setup codec (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) phase1 none)
        (setup.joint.publicKeys beaconSeed).ed25519 payload other (some 0)) state family)) :
    W2 setup seed scalar result.1.2.ordinary.ghost := by
  simp only [buildThen] at supported
  rw [run_bind, run_build setup codec checks seed scalar beaconSeed 0 (some payload) state family _ pending,
    bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨built, builtRun, supported⟩ := supported
  have originalRun : (built.1, built.2.2) ∈ support ((simulateQ (tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source
        (PqxdhServerClearedRoot.pending (binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))
          (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1
            reader e encapsulated)) (expandRoot setup.hmac prk) (some payload) () state.ordinary.server)).run ([], state.ordinary.ctx)) := by
    rw [← program_erase setup codec checks _ ([], ([], state.ordinary.ctx)), support_map, Set.mem_image]
    exact ⟨built, builtRun, rfl⟩
  cases published : (settle state.ordinary.server built.1).1 with
  | none => exact absurd (publishes (built.1, built.2.2) originalRun) (by rw [published]; simp)
  | some response =>
      obtain ⟨initial, disclosed, initialized, disclosedReply, disclosedChain⟩ :=
        built_reveal setup codec checks 0 state _ (expandRoot setup.hmac prk) (some payload) built builtRun response published
      obtain ⟨candidate, sourceKernel, digest, frameBytes, _, _, _, ephemeral, ciphertext, _, _, _, _, _, written, sealLog⟩ :=
        build_published setup codec checks _ _ (some payload) state.ordinary.server state.ordinary.ctx
          (built.1, built.2.2) originalRun response published
      change result ∈ support (run setup codec checks seed scalar beaconSeed
        (revealThen setup codec _ _ other ((settle state.ordinary.server built.1).1))
        (builtState 0 state built).2 family) at supported
      rw [published] at supported
      simp only [revealThen] at supported
      rw [run_bind, run_reveal, pure_bind, disclosedReply] at supported
      obtain ⟨original, originalRead, originalCt, originalEphemeral, _, _, _⟩ := laws.phase2 _ response.serialized written
      rw [ciphertext] at originalCt
      rw [ephemeral] at originalEphemeral
      refine reseal_wins setup codec checks limit laws functional other nonempty short seed scalar beaconSeed oneTime
        keys reader e encapsulated good bytes prk hinputS (builtState 0 state built).2 family ?_
        (PqxdhServerRegistrationPublication.firstContext candidate (Pqxdh.LE64 candidate.key_id.val ++ payload))
        ?_ ?_ hprk phase1 response original originalRead originalCt originalEphemeral initial disclosed initialized
        disclosedChain result supported
      · exact hbeacon
      · simpa only [PqxdhServerRegistrationPublication.firstContext, drop_binding] using different
      · simp only [builtState, hghost, List.nil_append]
        rw [sealLog]
        rfl

set_option linter.deprecated false in
/-- For each actual sampled KEM pair, every run with correct decapsulation wins after one honest admission/build and the altered pre-seal reveal. The remaining failure mass is exactly bounded by the ordinary pair's correctness error. -/
theorem pair_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (limit : Nat)
    (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload other : Pqxdh.Bytes) (payloadNonempty : payload ≠ []) (otherNonempty : other ≠ [])
    (different : payload ≠ other) (allocatable : 8 + payload.length ≤ Usize.max)
    (payloadShort : payload.length + 88 < limit) (otherShort : other.length + 88 < limit)
    (below : setup.serverKeyId ≠ core.num.U64.MAX) (seed : IdentitySeed) (scalar : ScalarBytes)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) :
    Pr[fun result => ¬ W2 setup seed scalar result.1.2.ordinary.ghost |
      run setup codec acceptAll seed scalar beaconSeed
        (adversary setup codec payload other (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).1 none))
        ⟨initialGameState setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).2, fun _ => none⟩
        PqxdhJointDhExtractFamily.empty] ≤ keyPairError setup functional keys := by
  obtain ⟨phase1, written⟩ := laws.phase1Total (beaconCandidate setup
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1)
  rw [phase1Result_some setup codec _ beaconSeed oneTime keys.1 keys.2 phase1 written]
  simp only [controlInput, adversary, parse_honest setup codec laws.phase1 _ beaconSeed oneTime keys.1 phase1 written]
  rw [run_bind, run_accept, bind_map_left, PqxdhServerAuthNegativeControl.run_accept, bind_assoc]
  obtain ⟨reader, hread, hidentity, hpq, hpre, hone⟩ := laws.phase1 _ phase1 written
  change Pr[_ | (serverPrefix setup codec acceptAll phase1).run [] >>= _] ≤ _
  rw [serverPrefix_eq setup codec acceptAll laws.nonzero seed scalar beaconSeed oneTime keys.1 phase1 reader hread
    hidentity hpq hpre hone]
  simp only [acceptAll, Bool.and_self, ite_true]
  rw [bind_assoc]
  refine probEvent_bind_le_of_forall_le fun e _ => ?_
  rw [bind_assoc]
  refine le_trans (probEvent_bind_le_probEvent
    (p := fun drawn => PqxdhKemCorrectnessError.Bad setup.kem functional ⟨keys.1, keys.2, drawn.1, drawn.2⟩)
    fun encapsulated _ bad => ?_) le_rfl
  have good : functional.result keys.2 encapsulated.1 = some encapsulated.2 := not_not.mp bad
  rw [pure_bind]
  obtain ⟨first, hfirst⟩ := static_present setup laws.nonzero seed scalar
  obtain ⟨bytes, controlBytesEq⟩ : ∃ bytes, controlBytes setup seed (setup.joint.publicKeys beaconSeed).ed25519
      ⟨setup.dh.publicKey scalar, setup.dh.publicKey oneTime, keys.1⟩ e encapsulated.2 = some bytes :=
    ⟨_, by rw [controlBytes, hfirst]; rfl⟩
  have sourceInput := server_input_eq setup seed scalar beaconSeed oneTime keys.1 reader e encapsulated
  rw [controlBytesEq] at sourceInput
  rw [acceptAfter_honest setup seed scalar _ [] bytes sourceInput
    (honest_localNonzero setup laws.nonzero _ scalar rfl beaconSeed oneTime keys.1 reader e encapsulated)]
  refine probEvent_eq_zero fun result supported => ?_
  simp only [bind_assoc, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨answer, answerRun, supported⟩ := supported
  have cached := randomOracle_cached (spec := HmacOracle) _ _ _ answerRun
  apply not_not.mpr
  refine after_accept_wins setup codec acceptAll limit laws functional payload other different otherNonempty otherShort
    seed scalar beaconSeed oneTime keys reader e encapsulated good bytes answer.1 sourceInput _ _
    (by simp [initialGameState]) rfl (by simp [initialGameState, Ghost.empty]) cached ?_ (some phase1) result supported
  exact build_publishes setup codec limit laws _ _ (some payload) _ _ below (fun _ => rfl) rfl rfl
    payloadNonempty allocatable payloadShort

/-- The actual altered body samples exactly the original Beacon context and then runs its concrete handler; the source and family poststates remain in the result. -/
theorem controlBody_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (client : Adversary) (seed : IdentitySeed) (scalar : ScalarBytes) :
    (simulateQ (romReduction setup seed scalar) (controlBody setup codec checks client
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run PqxdhJointDhExtractFamily.empty =
      sampleSeed >>= fun beaconSeed => PqxdhJointGapDh.sampleScalar >>= fun oneTime => keygenRun setup >>= fun keys =>
      (fun result => (result.1.2.ordinary, result.2)) <$> run setup codec checks seed scalar beaconSeed
        (client (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).1 none))
        ⟨initialGameState setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).2, fun _ => none⟩
        PqxdhJointDhExtractFamily.empty := by
  simp only [controlBody, simulateQ_bind, StateT.run_bind, rom_coins, bind_map_left, simulateQ_map, StateT.run_map,
    romReduction]
  refine bind_congr fun beaconSeed => bind_congr fun oneTime => bind_congr fun keys => ?_
  rw [phase1Run_eq, pure_bind]
  rfl

set_option linter.deprecated false in
/-- Averaging the source attack over its unchanged complete constructor sampler bounds its failure by the ordinary ML-KEM correctness experiment. There is no assumed publication or security event. -/
theorem failure_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (limit : Nat)
    (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload other : Pqxdh.Bytes) (payloadNonempty : payload ≠ []) (otherNonempty : other ≠ [])
    (different : payload ≠ other) (allocatable : 8 + payload.length ≤ Usize.max)
    (payloadShort : payload.length + 88 < limit) (otherShort : other.length + 88 < limit)
    (below : setup.serverKeyId ≠ core.num.U64.MAX) :
    Pr[fun result => ¬ W2 setup result.1 result.2.1 result.2.2.1.ghost |
      controlState setup codec acceptAll (adversary setup codec payload other)] ≤
      Pr[= true | simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (PqxdhKemCorrectnessError.errorExperiment setup.kem)] := by
  rw [controlState]
  refine probEvent_bind_le_of_forall_le fun seed _ => probEvent_bind_le_of_forall_le fun scalar _ => ?_
  rw [bind_pure_comp, probEvent_map]
  rw [controlBody_run]
  refine probEvent_bind_le_of_forall_le fun beaconSeed _ => probEvent_bind_le_of_forall_le fun oneTime _ => ?_
  rw [probEvent_bind_eq_tsum, ← keyPairError_average setup functional]
  refine ENNReal.tsum_le_tsum fun keys => ?_
  by_cases supported : keys ∈ support (keygenRun setup)
  · refine mul_le_mul_right ?_ _
    rw [probEvent_map]
    exact pair_failure setup codec limit laws functional payload other payloadNonempty otherNonempty different
      allocatable payloadShort otherShort below seed scalar beaconSeed oneTime keys
  · rw [probOutput_eq_zero_of_not_mem_support supported, zero_mul, zero_mul]

set_option linter.deprecated false in
/-- B5b negative control: revealing the actual pre-seal chain after one real registration allows a different application payload to win W2 with probability at least one minus ordinary KEM correctness error. The headline experiment's post-registration reveal remains unchanged. -/
theorem preseal_control (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (limit : Nat)
    (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload other : Pqxdh.Bytes) (payloadNonempty : payload ≠ []) (otherNonempty : other ≠ [])
    (different : payload ≠ other) (allocatable : 8 + payload.length ≤ Usize.max)
    (payloadShort : payload.length + 88 < limit) (otherShort : other.length + 88 < limit)
    (below : setup.serverKeyId ≠ core.num.U64.MAX) :
    1 - kemError setup ≤ (Pr[fun result => W2 setup result.1 result.2.1 result.2.2.1.ghost |
      controlState setup codec acceptAll (adversary setup codec payload other)]).toReal := by
  have failures := failure_bound setup codec limit laws functional payload other payloadNonempty otherNonempty
    different allocatable payloadShort otherShort below
  have total := probEvent_compl (controlState setup codec acceptAll (adversary setup codec payload other))
    (fun result => W2 setup result.1 result.2.1 result.2.2.1.ghost)
  simp only [probFailure_eq_zero, tsub_zero] at total
  rw [kemError]
  have eventEq := ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) total
  have missLe : Pr[fun result => ¬ W2 setup result.1 result.2.1 result.2.2.1.ghost |
      controlState setup codec acceptAll (adversary setup codec payload other)] ≤ 1 := probEvent_le_one
  rw [eventEq, ENNReal.toReal_sub_of_le missLe ENNReal.one_ne_top, ENNReal.toReal_one]
  have monotone := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one) failures
  linarith

/-- Public API categories distinguish source methods from explicit adversary coin and cryptographic-oracle queries. -/
inductive ApiClass where
  | coin | accept | build | reveal | hash | finish | hmac
  deriving DecidableEq

def classify : ServerAuthSpec.Domain → ApiClass
  | .inl _ => .coin
  | .inr (.accept _) => .accept
  | .inr (.build _ _) => .build
  | .inr (.reveal _) => .reveal
  | .inr (.hash _) => .hash
  | .inr (.finish _) => .finish
  | .inr (.hmac _ _) => .hmac

def HasClass (category : ApiClass) (query : ServerAuthSpec.Domain) : Prop := classify query = category

instance (category : ApiClass) : DecidablePred (HasClass category) := fun query =>
  inferInstanceAs (Decidable (classify query = category))

/-- Every adaptive reply branch makes at most one accept, build, reveal, hash and finish, and no adversary coin or public HMAC request. Local real KDF/AEAD work remains present in the concrete adversary. -/
theorem adversary_classes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (payload other : Pqxdh.Bytes) (input : AuthInput) (category : ApiClass) :
    (adversary setup codec payload other input).IsQueryBoundP (HasClass category)
      (match category with | .coin | .hmac => 0 | _ => 1) := by
  cases category <;>
  · unfold adversary
    split
    · simp
    · split
      · simp
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨by simp [HasClass, classify], fun session => ?_⟩
        unfold buildThen
        split
        · simp
        · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
            ⟨by simp [HasClass, classify], fun response => ?_⟩
          unfold revealThen
          split
          · simp
          · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
              ⟨by simp [HasClass, classify], fun kernel => ?_⟩
            split
            · simp
            · unfold reseal
              split
              · simp
              · split
                · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
                    ⟨by simp [HasClass, classify], fun digest => ?_⟩
                  split
                  · simp
                  · split
                    · simp
                    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
                        ⟨by simp [HasClass, classify], fun _ => by simp⟩
                · simp

/-- The complete concrete adversary issues at most five API queries in total; rejected branches are included and do not create retries. -/
theorem adversary_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (payload other : Pqxdh.Bytes) (input : AuthInput) :
    (adversary setup codec payload other input).IsTotalQueryBound 5 := by
  apply (isQueryBoundP_true_iff _ _).1
  unfold adversary
  split
  · simp
  · split
    · simp
    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
        ⟨by simp, fun session => ?_⟩
      unfold buildThen
      split
      · simp
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨by simp, fun response => ?_⟩
        unfold revealThen
        split
        · simp
        · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
            ⟨by simp, fun kernel => ?_⟩
          split
          · simp
          · unfold reseal
            split
            · simp
            · split
              · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
                  ⟨by simp, fun digest => ?_⟩
                split
                · simp
                · split
                  · simp
                  · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
                      ⟨by simp, fun _ => by simp⟩
              · simp

/-- The original authentication-winning event is evaluated on the altered control service's final original state. -/
noncomputable def presealGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (client : Adversary) : ProbComp Bool := by
  classical
  exact (fun result => decide (Win setup result.1 result.2.1 result.2.2.1.ghost)) <$>
    controlState setup codec checks client

set_option linter.deprecated false in
/-- The Boolean negative-control game uses exactly the original authentication event. -/
theorem presealGame_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (client : Adversary) :
    Pr[= true | presealGame setup codec checks client] =
      Pr[fun result => Win setup result.1 result.2.1 result.2.2.1.ghost | controlState setup codec checks client] := by
  classical
  rw [presealGame, ← probEvent_eq_eq_probOutput, probEvent_map]
  congr 1
  funext result
  simp only [Function.comp_apply, decide_eq_true_eq]

set_option linter.deprecated false in
/-- The concrete pre-seal-chain adversary wins the separate Boolean authentication experiment with probability at least one minus ordinary KEM correctness error. -/
theorem preseal_reveal_control (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (limit : Nat)
    (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload other : Pqxdh.Bytes) (payloadNonempty : payload ≠ []) (otherNonempty : other ≠ [])
    (different : payload ≠ other) (allocatable : 8 + payload.length ≤ Usize.max)
    (payloadShort : payload.length + 88 < limit) (otherShort : other.length + 88 < limit)
    (below : setup.serverKeyId ≠ core.num.U64.MAX) :
    1 - kemError setup ≤ (Pr[= true | presealGame setup codec acceptAll (adversary setup codec payload other)]).toReal := by
  refine (preseal_control setup codec limit laws functional payload other payloadNonempty otherNonempty
    different allocatable payloadShort otherShort below).trans ?_
  rw [presealGame_event]
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one)
    (probEvent_mono fun _ _ wins => Or.inr (Or.inl wins))

end BeaconcryptCore.Computational.PqxdhServerAuthPresealControl

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.tail_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.tail_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.program_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.program_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.program_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.tail_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.tail_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.tail_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.tail_kdf
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.send_seal_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.send_seal_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.send_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.send_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.after_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.after_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.after_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.after_peer
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.tail_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.tail_aux
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.build_history_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.build_history_peer
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.forward_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.forward_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.built_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.built_reveal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.build_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.build_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_query
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.forward_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.forward_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.adversary_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.adversary_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_build
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_reveal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_accept
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.run_finish
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.reseal_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.reseal_wins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.after_accept_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.after_accept_wins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.pair_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.pair_failure
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.controlBody_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.controlBody_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.failure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.failure_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.preseal_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.preseal_control
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.adversary_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.adversary_classes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.adversary_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.adversary_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.presealGame_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.presealGame_event
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.preseal_reveal_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPresealControl.preseal_reveal_control
