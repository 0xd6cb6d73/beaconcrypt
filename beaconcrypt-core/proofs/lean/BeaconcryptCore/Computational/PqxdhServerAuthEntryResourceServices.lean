import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceState
import BeaconcryptCore.Computational.RawCtxChainReceiveBounds

open OracleComp OracleSpec
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerAuthSourceCosts PqxdhServerAuthTailCosts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every counted callback pays its full uniform cost through all replies and the full retained state; all other callbacks have an explicit zero-uniform contract. -/
theorem class_uniform {κ σ α : Type} {spec : OracleSpec κ}
    (impl : QueryImpl spec (StateT σ ProbComp)) (counted : spec.Domain → Bool) (cost : Nat)
    (step : ∀ query state, ((impl query).run state).IsTotalQueryBound (if counted query then cost else 0))
    (work : OracleComp spec α) (count : Nat)
    (bounded : work.IsQueryBoundP (fun query => counted query = true) count) (state : σ) :
    ((simulateQ impl work).run state).IsTotalQueryBound (cost * count) := by
  induction work using OracleComp.inductionOn generalizing count state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isTotalQueryBound_bind (step query state)
        (fun result => ih result.1 _ (bounded.2 result.1) result.2)).mono
      by_cases present : counted query = true
      · have positive : 0 < count := bounded.1.resolve_left (not_not.mpr present)
        simp only [present, ite_true]
        rw [Nat.mul_sub_left_distrib]
        have enough := Nat.mul_le_mul_left cost positive
        simp only [Nat.mul_one] at enough
        omega
      · simp only [present, Bool.false_eq_true, ite_false, Nat.zero_add, le_refl]

/-- Every actual logging tail program pays one possible 64-byte commitment sample per attempted sealing callback. The real KDF, writers and complete log/cache remain in the execution. -/
theorem logged_uniform {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (work : OracleComp PqxdhServerRegistrationPublication.TailSpec α) (qSeal : Nat)
    (bounded : work.IsQueryBoundP (fun query => PqxdhServerRegistrationPublication.callKind query = .seal) qSeal)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    ((simulateQ (tailImpl setup codec checks) work).run state).IsTotalQueryBound (64 * qSeal) := by
  rw [IsTotalQueryBound, ← isQueryBound_map_iff (f := Prod.map id forgetAux), tail_native, ← IsTotalQueryBound]
  exact registration_uniform setup codec checks _ qSeal
    (PqxdhServerRegistrationPublication.native_seal_bound work qSeal bounded .hash) _

/-- The actual logging primitive has a zero-uniform real KDF branch and a 64-byte shared-cache sealing allowance. -/
theorem logged_primitive_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (query : RawCtxSourceSend.PrimitiveSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (((PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) query).run state).IsTotalQueryBound
      (if query.isRight then 64 else 0) := by
  cases query with
  | inl request => trivial
  | inr input =>
      have bound := logged_uniform setup codec checks
        (PqxdhServerRegistrationPublication.TailSpec.query (.inl (.inr input))) 1
        ((isQueryBoundP_query_iff _ _ _).mpr (fun _ => Nat.one_pos)) state
      simpa only [simulateQ_spec_query, PqxdhServerAuthLoggedSendFactor.loggedPrim,
        Nat.mul_one, Sum.isRight, ite_true] using bound

/-- The factored send executes the actual logging seal and shares its cache; arbitrary joint challenge material adds no sampler. -/
theorem factored_send_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (challenge : RatchetKdfResponse) (entry : RawCtxSelectedChain.Kernel)
    (context : RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (((PqxdhServerAuthLoggedSendFactor.calls (fun entry _ _ => pure (entry, .None))
      (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source challenge).send entry context).run state).IsTotalQueryBound 64 := by
  change ((simulateQ (PqxdhServerAuthSendFactor.primLabels
      (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source challenge)
    (RawCtxChainSend.execute entry context)).run state).IsTotalQueryBound 64
  apply class_uniform _ Sum.isRight 64 ?_ _ 1 (RawCtxChainSend.program_seal_bound _) state
  intro query current
  cases query with
  | inl slot => trivial
  | inr pending =>
      simp only [PqxdhServerAuthSendFactor.primLabels, QueryImpl.apply_compose,
        RawCtxSourceSend.adapter, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
      exact logged_primitive_uniform setup codec checks (.inr _) current

/-- The actual auxiliary admission, erasure and optional Phase2 writer callbacks draw no randomness. -/
theorem logged_aux_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (query : PqxdhServerRegistrationPublication.AuxSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (((PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks) query).run state).IsTotalQueryBound 0 := by
  cases query <;> trivial

/-- Complete first-send publication pays its supplied send bill and every zero-uniform auxiliary callback, including all writer failures. -/
theorem generic_after_uniform {K σ Metadata PeerMetadata Consumed : Type}
    (calls : RawCtxChainOwner.Calls K (StateT σ ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ ProbComp)) (cost : Nat)
    (sendBound : ∀ entry context state, ((calls.send entry context).run state).IsTotalQueryBound cost)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound 0)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : K)
    (metadata : PeerMetadata) (server : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (state : σ) :
    ((PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata server).run state).IsTotalQueryBound cost := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, StateT.run_bind]
  apply (isTotalQueryBound_bind (n₂ := 0) (sendBound _ _ state) ?_).mono (by omega)
  rintro ⟨⟨advanced, encrypted⟩, current⟩
  apply isTotalQueryBound_bind (n₁ := 0) (n₂ := 0) (auxBound (.erase authenticated) current)
  intro erased
  cases encrypted with
  | none => trivial
  | some encrypted =>
      apply isTotalQueryBound_bind (n₁ := 0) (n₂ := 0) (auxBound (.write _) erased.2)
      rintro ⟨(_ | serialized), afterWrite⟩ <;> trivial

/-- All candidate admission, allocation and initialization failures retain the one possible send bill. -/
theorem generic_candidate_uniform {K σ Metadata PeerMetadata Consumed : Type}
    (calls : RawCtxChainOwner.Calls K (StateT σ ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ ProbComp)) (cost : Nat)
    (sendBound : ∀ entry context state, ((calls.send entry context).run state).IsTotalQueryBound cost)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound 0)
    (initial : RustM K) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (server : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (state : σ) :
    ((PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata server).run state).IsTotalQueryBound cost := by
  simp only [PqxdhInitialGenericBuilder.candidate, StateT.run_bind]
  apply (isTotalQueryBound_bind (n₁ := 0) (n₂ := cost) (auxBound (.checkIdentity _) state) ?_).mono (by omega)
  rintro ⟨valid, checked⟩
  cases valid with
  | false => trivial
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      apply (isTotalQueryBound_bind (n₁ := 0) (n₂ := cost) (auxBound .reservePeer checked) ?_).mono (by omega)
      rintro ⟨reserved, reservedState⟩
      cases reserved with
      | false => trivial
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          cases initial with
          | fail error => trivial
          | div => trivial
          | ok kernel =>
              simp only [PqxdhInitialGenericBuilder.continueRust]
              split_ifs
              · trivial
              · apply (isTotalQueryBound_bind (n₁ := 0) (n₂ := cost) (auxBound (.reservePlaintext _) reservedState) ?_).mono (by omega)
                rintro ⟨allocated, allocatedState⟩
                cases allocated with
                | false => trivial
                | true =>
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                    cases candidate.key_id_binding with
                    | fail error => trivial
                    | div => trivial
                    | ok binding =>
                        change ((ok <$> PqxdhInitialGenericPublication.afterInitialization calls aux candidate
                          (absBytes binding.bytes ++ data.getD PqxdhServerRegistrationPublication.registrationWitness)
                          kernel metadata server).run allocatedState).IsTotalQueryBound cost
                        rw [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
                        exact generic_after_uniform calls aux cost sendBound auxBound candidate _ kernel metadata server allocatedState
              · trivial

/-- The full source builder retains the send bill through all key-ID, admission, allocation and writer branches. -/
theorem generic_build_uniform {K σ Metadata PeerMetadata Consumed : Type}
    (calls : RawCtxChainOwner.Calls K (StateT σ ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ ProbComp)) (cost : Nat)
    (sendBound : ∀ entry context state, ((calls.send entry context).run state).IsTotalQueryBound cost)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound 0)
    (initial : RustM K) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (server : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (state : σ) :
    ((PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata server).run state).IsTotalQueryBound cost := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases pqxdh.server_next_key_id server.control with
  | fail error => trivial
  | div => trivial
  | ok next =>
      cases next with
      | Err error => trivial
      | Ok next =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          cases pqxdh.server_prepare_commit server.control pending
              ⟨server.server.identity, server.identityKeyId⟩
              (if (server.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => trivial
          | div => trivial
          | ok prepared =>
              cases prepared with
              | Err error => trivial
              | Ok candidate => exact generic_candidate_uniform calls aux cost sendBound auxBound initial candidate data metadata server state

/-- The concrete arbitrary108-byte selected Server service has the same one-hash uniform allowance as the real source builder. -/
theorem factor_build_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : ServerState) (state : SealState) :
    ((((factorServices setup codec checks context value).hiddenBuild token payload server)).run state).IsTotalQueryBound 64 := by
  simp only [factorServices, PqxdhServerAuthLoggedSendFactor.factored, StateT.run_map,
    IsTotalQueryBound, isQueryBound_map_iff]
  exact generic_build_uniform _ _ 64 (factored_send_uniform setup codec checks _) (logged_aux_uniform setup codec checks)
    _ token.pending payload () _ state

/-- The actual Beacon primitive keeps real zero-coin HKDF and charges one possible 64-byte shared-cache commitment per attempted opening. -/
theorem beacon_primitive_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxWholeOwner.PrimitiveSpec.Domain) (state : RawCtxSharedPrimitive.SharedState Unit) :
    (((PqxdhServerAuthBeaconFactor.nativePrim setup codec) query).run state).IsTotalQueryBound
      (if query.isRight then 64 else 0) := by
  cases query with
  | inl request => trivial
  | inr input =>
      change ((simulateQ (RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source))
        (simulateQ RawCtxSourceOpen.openLift (RawCtxSourceOpen.openInput input))).run state).IsTotalQueryBound 64
      exact RawCtxSharedPrimitive.native_uniform_bound setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source)
        0 (RawCtxSourceHkdf.kdf_uniform setup.source) _ 0 1
        (RawCtxSourceOpen.openLift_no_kdf _) (RawCtxSourceOpen.openLift_bound Sum.isLeft _ 1
          (RawCtxSourceOpen.openInput_bounds input).1) state

/-- Arbitrary raw target sequences retain the complete skip driver while paying for at most one opening callback. -/
theorem factored_receive_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (challenge : RatchetKdfResponse) (entry : RawCtxSelectedChain.Kernel) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (state : RawCtxSharedPrimitive.SharedState Unit) :
    ((simulateQ (PqxdhServerAuthBeaconFactor.primLabels (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
      setup.source challenge) (RawCtxChainReceive.execute entry target context)).run state).IsTotalQueryBound 64 := by
  apply class_uniform _ Sum.isRight 64 ?_ _ 1 (RawCtxChainReceiveBounds.program_open_bound _) state
  intro query current
  cases query with
  | inl slot => trivial
  | inr pending =>
      simp only [PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose, RawCtxWholeOwner.adapter]
      split
      · trivial
      · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map,
          IsTotalQueryBound, isQueryBound_map_iff]
        exact beacon_primitive_uniform setup codec (.inr _) current

/-- Raw parsing and validation rejection costs no randomness; every reached full receive retains its supplied bill and state. -/
theorem generic_raw_uniform {K Metadata σ : Type}
    (calls : RawCtxChainOwner.Calls K (StateT σ ProbComp)) (cost : Nat)
    (receiveBound : ∀ entry target context state, ((calls.receive entry target context).run state).IsTotalQueryBound cost)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State K Metadata) (state : σ) :
    (((RawCtxChainOwner.rawReceive calls decode raw).run owner).run state).IsTotalQueryBound cost := by
  unfold RawCtxChainOwner.rawReceive
  simp only [StateT.run]
  split
  · trivial
  · cases decoded : decode raw with
    | none => trivial
    | some frame =>
        dsimp only
        split
        · change ((RawCtxChainOwner.publish owner <$> calls.receive owner.kernel frame.sequence
            ⟨raw, frame, owner.associatedData⟩).run state).IsTotalQueryBound cost
          rw [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
          exact receiveBound _ _ _ state
        · trivial

/-- The exact arbitrary-factor Beacon tail charges every reached raw opening, including failed post-opening registration checks. -/
theorem factor_after_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (state : RawCtxSharedPrimitive.SharedState Unit) :
    (((factorServices setup codec checks context value).hiddenAfter pending).run state).IsTotalQueryBound 64 := by
  simp only [factorServices, PqxdhServerAuthBeaconFactor.factored, pure_bind]
  cases app : codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response with
  | none => trivial
  | some raw =>
      simp only [bind_pure_comp, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
      exact generic_raw_uniform _ 64 (factored_receive_uniform setup codec _) _ raw _ state

/-- A real Extract-domain table lookup samples at most one 64-byte block; cache hits retain zero draws. -/
theorem extract_table_uniform (bytes : Pqxdh.Bytes) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache) :
    ((PqxdhSecretInputKdf.HmacOracle.randomOracle bytes).run cache).IsTotalQueryBound 64 := by
  rw [randomOracle.run_eq]
  cases hit : cache bytes with
  | some value => trivial
  | none =>
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64

/-- A real honest root derivation keeps the actual joint input and public Expand while charging its one possible Extract-table sample. -/
theorem real_derive_uniform (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : PqxdhJointDhExtractFamily.Message)
    (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache) :
    ((realDerive hmac joint dh seed scalar message).run cache).IsTotalQueryBound 64 := by
  unfold realDerive
  simp only [StateT.run]
  cases input : PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => trivial
  | some bytes =>
      rw [IsTotalQueryBound, isQueryBound_map_iff]
      exact extract_table_uniform bytes cache

/-- The omitted-entry honest callback charges all remaining real-table work, including executions already marked bad. -/
theorem hidden_derive_uniform (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : PqxdhJointDhExtractFamily.Message)
    (table : HiddenTable) :
    ((hiddenDerive hmac joint dh seed scalar message).run table).IsTotalQueryBound 64 := by
  unfold hiddenDerive
  simp only [StateT.run]
  cases input : PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => trivial
  | some bytes =>
      dsimp only
      split_ifs
      · trivial
      · simp only [ordinaryHiddenDerive, IsTotalQueryBound, isQueryBound_map_iff]
        exact real_derive_uniform hmac joint dh seed scalar message table.cache

/-- Designation and prior-hit refusal only inspect the retained table and sample nothing. -/
theorem select_hidden_uniform (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : PqxdhJointDhExtractFamily.Message)
    (table : HiddenTable) :
    ((selectHidden joint dh seed scalar message).run table).IsTotalQueryBound 0 := by
  unfold selectHidden
  simp only [StateT.run]
  cases input : PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => trivial
  | some bytes =>
      dsimp only
      cases table.cache bytes <;> trivial

/-- Public reads keep all real unselected table sampling; the selected-input stop itself draws nothing. -/
theorem hidden_public_uniform (bytes : Pqxdh.Bytes) (table : HiddenTable) :
    ((hiddenPublic bytes).run table).IsTotalQueryBound 64 := by
  unfold hiddenPublic
  simp only [StateT.run]
  split_ifs
  · trivial
  · rw [IsTotalQueryBound, isQueryBound_map_iff]
    exact extract_table_uniform bytes table.cache

/-- Explicit uniform callback caps, each quantified over the complete supplied state and every typed input. The concrete factor and selecting services discharge these resource obligations. -/
structure ServiceUniform {τ : Type} (services : Services Response τ) : Prop where
  derive : ∀ message state, ((services.derive message).run state).IsTotalQueryBound 64
  table : ∀ bytes state, ((services.table bytes).run state).IsTotalQueryBound 64
  build : ∀ token payload server state, ((services.hiddenBuild token payload server).run state).IsTotalQueryBound 64
  after : ∀ pending state, ((services.hiddenAfter pending).run state).IsTotalQueryBound 64

/-- All four concrete factor callbacks satisfy their full-state uniform caps; no service cost remains assumed by the final reduction. -/
theorem factor_services_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) :
    ServiceUniform (factorServices setup codec checks context value) := by
  exact ⟨hidden_derive_uniform setup.hmac setup.joint setup.dh context.seed context.scalar,
    hidden_public_uniform, factor_build_uniform setup codec checks context value,
    factor_after_uniform setup codec checks context value⟩

/-- Replacing only designation's derivation with its zero-query table check preserves all callback caps. -/
theorem selecting_services_uniform (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (services : Services Response HiddenTable) (bounded : ServiceUniform services) :
    ServiceUniform (selectingServices setup context services) := by
  exact ⟨fun message state => (select_hidden_uniform setup.joint setup.dh context.seed context.scalar message state).mono (by omega),
    bounded.table, bounded.build, bounded.after⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.class_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.class_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.logged_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.logged_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.logged_primitive_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.logged_primitive_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factored_send_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factored_send_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.logged_aux_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.logged_aux_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.generic_after_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.generic_after_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.generic_candidate_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.generic_candidate_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.generic_build_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.generic_build_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factor_build_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factor_build_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.beacon_primitive_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.beacon_primitive_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factored_receive_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factored_receive_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.generic_raw_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.generic_raw_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factor_after_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factor_after_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.extract_table_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.extract_table_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.real_derive_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.real_derive_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_derive_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_derive_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.select_hidden_uniform' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.select_hidden_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_public_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_public_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factor_services_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.factor_services_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selecting_services_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selecting_services_uniform
