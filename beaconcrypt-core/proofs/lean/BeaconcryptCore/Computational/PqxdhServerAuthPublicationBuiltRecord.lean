import BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve

/-! Actual successful source callbacks retain the selected record and complete response-writer witnesses. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhJointKdfGame PqxdhFullSecretInputKdf CtxRomAuth
open RawCtxSelectedAuthenticationObserver (monitor)
open RawCtxSelectedMessageSealing (selectedInput)
variable {ι KemSK Reader WireResponse : Type} {baseSpec : OracleSpec ι}

/-- All writer and candidate witnesses retain the actual supplied pending token, payload and complete pre-build Server. -/
def At (codec : Codec Reader WireResponse) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (state : ServerState)
    (response : PqxdhServerRegistrationPublication.Response) (entry : CtxSuccessfulSeal) : Prop :=
  ∃ (key : Std.U64) (candidate : pqxdh.ServerRegistrationCandidate)
    (binding : pqxdh.RegistrationKeyIdBinding) (sealed : PqxdhServerAuthCtxSend.Pending)
    (encrypted : RawCtxSourceSend.Encrypted) (nonce : NonceOutput)
    (width : sealed.context.associatedData.length = 281),
    pqxdh.server_next_key_id state.control = .ok (.Ok key) ∧
    pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
      (if (state.server.peers key).isSome then .Occupied else .Available) = .ok (.Ok candidate) ∧
    candidate.key_id_binding = .ok binding ∧
    sealed.context = PqxdhServerRegistrationPublication.firstContext candidate
      (absBytes binding.bytes ++ data.getD PqxdhServerRegistrationPublication.registrationWitness) ∧
    codec.write2 (PqxdhServerRegistrationPublication.responseFields candidate encrypted) = some response.serialized ∧
    response.keyId = candidate.key_id ∧
    sealed.material = .hidden nonce ∧
    entry.input = selectedInput nonce sealed.sequence sealed.context width ∧
    codec.frameWrite ⟨sealed.sequence, sealed.context.senderId, entry.record.encode⟩ = some encrypted.ciphertext

/-- Erasing the private callback trailer retains a same-run successful response witness for every actual record, once the genuine starting record history is empty. -/
theorem compiled_at (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (state published : ServerState)
    (beforeLog afterLog : PqxdhServerAuthBuildProgram.Log)
    (before after : RawCtxSelectedAuthenticationObserver.State) (empty : before.seals = [])
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : ((some (.ok (some response, published)), afterLog), after) ∈ support
      (monitor ((PqxdhServerAuthBuildProgram.compiled source codec checks rest pending data () state).run.run beforeLog) before)) :
    ∀ entry ∈ after.seals, At codec pending data state response entry := by
  rw [← PqxdhServerAuthPublicationTrace.compiled_erase source codec checks rest pending data () state (beforeLog, []),
    RawCtxSelectedAcceptedRecord.monitor_map, support_map] at supported
  obtain ⟨⟨⟨outcome, log, trace⟩, observed⟩, reached, same⟩ := supported
  cases same
  obtain ⟨key, candidate, binding, sealed, encrypted, next, prepared, bound, contextSame,
      written, keySame, _, records⟩ := PqxdhServerAuthPublicationResponseRecord.compiled_records source codec checks rest
        pending data () state published beforeLog (log, trace) before observed response reached
  intro entry found
  rcases records entry found with old | ⟨nonce, width, hidden, input, frame⟩
  · rw [empty] at old
    cases old
  · exact ⟨key, candidate, binding, sealed, encrypted, nonce, width, next, prepared, bound,
      contextSame, written, keySame, hidden, input, frame⟩

/-- A successful selected API callback unwraps only its actual native outcome. Its original optional component effects and source settlement are preserved. -/
theorem selected_at (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (state afterState : Local KemSK)
    (before after : RawCtxSelectedAuthenticationObserver.State) (empty : before.seals = [])
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : ((some (some response), afterState), after) ∈ support
      (monitor ((PqxdhServerAuthCtxBuild.selected source codec checks rest session token payload
        state.1.1.server).run.run state) before)) :
    ∀ entry ∈ after.seals, At codec token.pending payload state.1.1.server response entry := by
  change ((some (some response), afterState), after) ∈ support (monitor
    (PqxdhServerAuthCtxBuild.post session state <$>
      (PqxdhServerAuthBuildProgram.compiled source codec checks rest token.pending payload () state.1.1.server).run.run []) before) at supported
  rw [RawCtxSelectedAcceptedRecord.monitor_map, support_map] at supported
  obtain ⟨⟨⟨outcome, log⟩, observed⟩, reached, same⟩ := supported
  have replySame := congrArg (fun result => result.1.1) same
  have observerSame : observed = after := congrArg Prod.snd same
  cases outcome with
  | none => cases replySame
  | some outcome =>
      cases outcome with
      | fail error => cases replySame
      | div => cases replySame
      | ok outcome =>
          rcases outcome with ⟨_ | actual, published⟩
          · cases replySame
          · have equal : actual = response := Option.some.inj (Option.some.inj replySame)
            subst actual
            rw [← observerSame]
            exact compiled_at source codec checks rest token.pending payload state.1.1.server published [] log
              before observed empty response reached

/-- The complete actual handler and post-callback stop retain the same successful selected response receipt; neither settlement changes the record history or public reply. -/
theorem stopped_at (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (session : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (state afterState : Local KemSK × Option Nat)
    (marked : state.1.1.2.1 session = true) (present : state.1.1.1.pending session = some token)
    (before after : RawCtxSelectedAuthenticationObserver.State) (empty : before.seals = [])
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : ((some (some response), afterState), after) ∈ support
      (monitor ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
          (.inr (.build session payload))).run.run state) before)) :
    ∀ entry ∈ after.seals, At codec token.pending payload state.1.1.1.server response entry := by
  simp only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped,
    OptionT.run_mk, StateT.run, bind_pure_comp, PqxdhServerAuthCtxHandler.handler,
    PqxdhServerAuthCtxHandler.route, PqxdhServerAuthCtxBuild.build, present, marked,
    ite_true, Functor.map_map, RawCtxSelectedAcceptedRecord.monitor_map, support_map] at supported
  obtain ⟨built, reached, equal⟩ := supported
  have sameObserver : built.2 = after := congrArg Prod.snd equal
  have normal : built.1.1 = some (some response) := by
    have sameReply := congrArg (fun result => result.1.1) equal
    have settled := (PqxdhServerAuthCtxHandlerBounds.settle_fields Q j (.inr (.build session payload)) state.1 built.1).1
    simp only [PqxdhServerAuthCtxStop.observe, settled] at sameReply
    cases reply : built.1.1 with
    | none => simp only [reply, reduceCtorEq] at sameReply
    | some value => simpa only [reply, PqxdhServerAuthCtxStop.checkpoint] using sameReply
  rw [← sameObserver]
  exact selected_at setup.source codec checks rest session token payload state.1 built.1.2 before built.2 empty
    response (by rw [← normal]; exact reached)

/-- A successful public build cannot arise from a missing token; this derives the original lookup rather than assuming a reached builder. -/
theorem build_present (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (session : Nat) (payload : Option Pqxdh.Bytes)
    (state afterState : Local KemSK × Option Nat) (response : PqxdhServerRegistrationPublication.Response)
    (supported : (some (some response), afterState) ∈ support
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
          (.inr (.build session payload))).run.run state)) :
    ∃ token, state.1.1.1.pending session = some token := by
  cases found : state.1.1.1.pending session with
  | none =>
      rw [PqxdhServerAuthPublicationSingleBuild.missing_build setup codec checks context rest Q j session payload state found,
        mem_support_pure_iff] at supported
      cases supported
  | some token => exact ⟨token, rfl⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord.compiled_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord.compiled_at
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord.selected_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord.selected_at
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord.stopped_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord.stopped_at
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord.build_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord.build_present
