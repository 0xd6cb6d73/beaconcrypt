-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationShared
import BeaconcryptCore.Computational.MldsaSharedSource
import BeaconcryptCore.Refinement.RegistrationSigningHistory
import BeaconcryptCore.Refinement.RegistrationPublication

/-!
Outgoing ML signing starts at the actual extracted hash capabilities. The request getter, digest continuation, selected ML request and signing/publication continuations are the extracted operations. Hashes use the record/authentication CTX cache. Private receipts record every reached signing call before its continuation, including a missing signature and later publication failure. The signing function is the explicit primitive implementation, with no unforgeability or desired-simulation premise.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationSigningShared

open CtxRomAuth MldsaTranscriptAuth
open BeaconcryptCore.Refinement.RegistrationSigningTrace
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)

abbrev SignReply := core.option.Option (Slice Std.U8)

structure Receipt where
  observation : Observation
  digest : CtxDigest

abbrev State := RawCtxSharedPrimitive.SharedState (List Receipt)

inductive Request where
  | hash (request : registration.HashRequest)
  | sign (request : registration.MldsaSigningRequest) (payload : Payload) (digest : CtxDigest)

abbrev Spec : OracleSpec Request
  | .hash _ => CtxDigest
  | .sign _ _ _ => SignReply

inductive Stage where
  | beacon (pending : registration.BeaconMldsaSigning)
  | server (pending : registration.ServerResponseSigning)
  | beaconStopped (effect : registration.BeaconInitEffect)
  | serverStopped (state : pqxdh.ServerState)

def continueWith {Input Result : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM Result)) : OracleComp Spec (RustM Result) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Resume exactly the source hash continuation using its actual shared-oracle digest. -/
def resumeHash (command : Command) (digest : CtxDigest) : RustM Stage := do
  match command with
  | .beacon hashing =>
    let next ← hashing.resume (.Some (RegistrationAuthenticationShared.digestArray digest))
    match next with
    | .MldsaSigningRequested pending => ok (.beacon pending)
    | other => ok (.beaconStopped other)
  | .server hashing =>
    let next ← hashing.resume (.Some (RegistrationAuthenticationShared.digestArray digest))
    match next with
    | .Ok pending => ok (.server pending)
    | .Err state => ok (.serverStopped state)

/-- The reached Beacon request signs the exact returned shared digest with the source key, role and context. -/
theorem resume_beacon_request (hashing : registration.BeaconInitHash) (digest : CtxDigest) :
    ∃ pending request, resumeHash (.beacon hashing) digest = ok (.beacon pending) ∧
      pending.request = ok request ∧ request.public_key = hashing.state.beacon_mldsa ∧
      request.role = .Beacon ∧ absBytes request.context = Pqxdh.TranscriptAuth.signingContext ∧
      absBytes request.input = Pqxdh.TranscriptAuth.signatureInput .beacon digest.toList :=
  match BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_some_exact
    hashing (RegistrationAuthenticationShared.digestArray digest) with
  | ⟨pending, resumed, _state, _fingerprint, _digest, request, requested, key, role,
      _context, contextBytes, message⟩ =>
    ⟨pending, request, by simp only [resumeHash, resumed, bind_tc_ok],
      requested, key, role, contextBytes,
      by simpa only [RegistrationAuthenticationShared.digest_array_bytes] using message⟩

/-- The reached Server request signs the exact returned shared digest with the source pinned key and context. -/
theorem resume_server_request (hashing : registration.ServerResponseHash) (digest : CtxDigest) :
    ∃ pending request, resumeHash (.server hashing) digest = ok (.server pending) ∧
      pending.request = ok request ∧ request.public_key = hashing.binding.server_pin.public_key ∧
      request.role = .Server ∧ absBytes request.context = Pqxdh.TranscriptAuth.signingContext ∧
      absBytes request.input = Pqxdh.TranscriptAuth.signatureInput .server digest.toList :=
  match BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines
    hashing (RegistrationAuthenticationShared.digestArray digest) with
  | ⟨pending, resumed, _candidate, _binding, _kernel, _ciphertext, message, requested⟩ =>
    ⟨pending, _, by simp only [resumeHash, resumed, bind_tc_ok], requested, rfl, rfl,
      TranscriptAuthInputsRefinement.signing_context_abs,
      by simpa only [RegistrationAuthenticationShared.digest_array_bytes] using message⟩

/-- Submit the selected extracted ML request and execute its source resume/publication after the actual reply. -/
def submit {Encoded : Type} (command : Command) (digest : CtxDigest) (stage : Stage)
    (encoded : core.option.Option Encoded) : OracleComp Spec (RustM (DispatchResult Encoded)) :=
  match stage with
  | .beacon pending => continueWith pending.request fun request => do
      let reply ← Spec.query (.sign request command.payload digest)
      pure (submitBeacon pending command.payload (fun _ => reply) encoded)
  | .server pending => continueWith pending.request fun request => do
      let reply ← Spec.query (.sign request command.payload digest)
      pure (submitServer pending command.payload (fun _ => reply) encoded)
  | .beaconStopped effect => pure (ok ⟨none, .beaconStopped effect⟩)
  | .serverStopped state => pure (ok ⟨none, .serverStopped state⟩)

/-- No signing request occurs before the source hash request and its actual extracted continuation. -/
def dispatch {Encoded : Type} (command : Command) (encoded : core.option.Option Encoded) :
    OracleComp Spec (RustM (DispatchResult Encoded)) :=
  continueWith command.request fun request => do
    let digest ← Spec.query (.hash request)
    continueWith (resumeHash command digest) fun stage => submit command digest stage encoded

/-- Each reached signing request is logged before any signature validation or publication can reject. -/
def implementation (sign : registration.MldsaSigningRequest → ProbComp SignReply) :
    QueryImpl Spec (StateT State ProbComp)
  | .hash request => MldsaSharedNative.authentication ((), hashBytes request)
  | .sign request payload digest => fun state =>
      (fun reply => (reply, (state.1 ++ [⟨⟨request.public_key, payload, replyBytes reply⟩, digest⟩], state.2))) <$>
        sign request

/-- The actual selected request is forwarded unchanged, including role, key, input and context. -/
theorem signing_step (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (request : registration.MldsaSigningRequest) (payload : Payload) (digest : CtxDigest) (state : State) :
    (implementation sign (.sign request payload digest)).run state =
      (fun reply => (reply, (state.1 ++ [⟨⟨request.public_key, payload, replyBytes reply⟩, digest⟩], state.2))) <$>
        sign request := rfl

/-- A chronological receipt is valid when the exact unsigned preimage was actually queried in the retained cache. -/
def Cached (state : State) : Prop :=
  ∀ receipt ∈ state.1, state.2 ((), receipt.observation.payload.transcript) = some receipt.digest

/-- Per-key histories include failed signing replies and failed later publications. -/
def historyFor (publicKey : Pqxdh.Bytes) (state : State) : List SigningCall :=
  BeaconcryptCore.Refinement.RegistrationSigningTrace.historyFor publicKey (state.1.map Receipt.observation)

/-- The exact hash call extends earlier receipts and records its actual digest at the requested unsigned preimage. -/
theorem hash_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (request : registration.HashRequest) (state : State)
    (result : CtxDigest × State)
    (supported : result ∈ support ((implementation sign (.hash request)).run state)) :
    state.2 ≤ result.2.2 ∧ result.2.2 ((), hashBytes request) = some result.1 :=
  match OracleComp.mem_support_map_peel _ ((ctxRandomOracle ((), hashBytes request)).run state.2) supported with
  | ⟨inner, queried, same⟩ => same.symm ▸ MldsaSharedAuthentication.query_cached (hashBytes request) state.2 inner queried

/-- Extending the actual shared cache preserves every earlier signing receipt. -/
theorem cached_extend (events : List Receipt) (before after : CtxRO.QueryCache)
    (extension : before ≤ after) (cached : Cached (events, before)) : Cached (events, after) :=
  fun receipt member => extension (cached receipt member)

/-- A reached signing attempt is retained independently of its reply or later source outcome. -/
theorem cached_append (state : State) (receipt : Receipt) (cached : Cached state)
    (reached : state.2 ((), receipt.observation.payload.transcript) = some receipt.digest) :
    Cached (state.1 ++ [receipt], state.2) :=
  fun event member => match List.mem_append.mp member with
  | .inl prior => cached event prior
  | .inr current => (List.mem_singleton.mp current).symm ▸ reached

private theorem map_state_apply {S X Y : Type} (mapResult : X → Y) (work : StateT S ProbComp X)
    (state : S) : (mapResult <$> work) state = Prod.map mapResult id <$> work state :=
  bind_pure_comp (Prod.map mapResult id) (work state)

/-- An actual hash step carries the entire earlier signing log to its extended shared cache. -/
theorem hash_cached_state (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (request : registration.HashRequest) (state : State) (cached : Cached state)
    (result : CtxDigest × State)
    (supported : result ∈ support ((implementation sign (.hash request)).run state)) : Cached result.2 :=
  match OracleComp.mem_support_map_peel _ ((ctxRandomOracle ((), hashBytes request)).run state.2) supported with
  | ⟨inner, queried, same⟩ =>
    same.symm ▸ cached_extend state.1 state.2 inner.2
      (MldsaSharedAuthentication.query_cached (hashBytes request) state.2 inner queried).1 cached

/-- Beacon signing preserves the receipt even if source signature validation or final publication rejects. -/
theorem submit_beacon_run {Encoded : Type} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (command : Command) (digest : CtxDigest) (pending : registration.BeaconMldsaSigning)
    (encoded : core.option.Option Encoded) (state : State) :
    (simulateQ (implementation sign) (submit command digest (.beacon pending) encoded)).run state =
      (fun reply => (submitBeacon pending command.payload (fun _ => reply) encoded,
        (state.1 ++ [⟨⟨pending.state.beacon_mldsa, command.payload, replyBytes reply⟩, digest⟩], state.2))) <$>
        sign (beaconRequest pending) := by
  simp only [submit, registration.BeaconMldsaSigning.request, continueWith,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run, map_state_apply,
    implementation, Functor.map_map, beaconRequest, Prod.map, id_eq]


private theorem server_request (pending : registration.ServerResponseSigning) :
    pending.request = ok (serverRequest pending) := rfl

/-- Server signing retains the same chronological receipt across failed final publication. -/
theorem submit_server_run {Encoded : Type} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (command : Command) (digest : CtxDigest) (pending : registration.ServerResponseSigning)
    (encoded : core.option.Option Encoded) (state : State) :
    (simulateQ (implementation sign) (submit command digest (.server pending) encoded)).run state =
      (fun reply => (submitServer pending command.payload (fun _ => reply) encoded,
        (state.1 ++ [⟨⟨pending.binding.server_pin.public_key, command.payload, replyBytes reply⟩, digest⟩], state.2))) <$>
        sign (serverRequest pending) := by
  simp only [submit, server_request, continueWith, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, StateT.run, map_state_apply, implementation, Functor.map_map,
    serverRequest, Prod.map, id_eq]

private theorem pure_cached {Result : Type} (value : Result) (state : State) (cached : Cached state)
    (result : Result × State) (supported : result ∈ support (pure (value, state) : ProbComp _)) :
    Cached result.2 :=
  let same : result = (value, state) := by
    simpa only [support_pure, Set.mem_singleton_iff] using supported
  (congrArg Prod.snd same).symm ▸ cached

/-- Actual source signature validation and publication never discard the already reached signing receipt. -/
theorem submit_cached {Encoded : Type} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (command : Command) (digest : CtxDigest) (stage : Stage) (encoded : core.option.Option Encoded)
    (state : State) (cached : Cached state)
    (reached : state.2 ((), command.payload.transcript) = some digest)
    (result : RustM (DispatchResult Encoded) × State)
    (supported : result ∈ support ((simulateQ (implementation sign) (submit command digest stage encoded)).run state)) :
    Cached result.2 :=
  match stage with
  | .beacon pending =>
    match OracleComp.mem_support_map_peel _ (sign (beaconRequest pending))
      ((congrArg (fun work => result ∈ support work)
        (submit_beacon_run sign command digest pending encoded state)).mp supported) with
    | ⟨reply, _possible, same⟩ =>
      same.symm ▸ cached_append state ⟨⟨pending.state.beacon_mldsa, command.payload, replyBytes reply⟩, digest⟩
        cached reached
  | .server pending =>
    match OracleComp.mem_support_map_peel _ (sign (serverRequest pending))
      ((congrArg (fun work => result ∈ support work)
        (submit_server_run sign command digest pending encoded state)).mp supported) with
    | ⟨reply, _possible, same⟩ =>
      same.symm ▸ cached_append state
        ⟨⟨pending.binding.server_pin.public_key, command.payload, replyBytes reply⟩, digest⟩ cached reached
  | .beaconStopped _effect => pure_cached _ state cached result supported
  | .serverStopped _previous => pure_cached _ state cached result supported

private theorem continue_cached {Input Output : Type}
    (sign : registration.MldsaSigningRequest → ProbComp SignReply) (action : RustM Input)
    (next : Input → OracleComp Spec (RustM Output)) (state : State) (cached : Cached state)
    (keeps : ∀ value result, result ∈ support ((simulateQ (implementation sign) (next value)).run state) →
      Cached result.2) (result : RustM Output × State)
    (supported : result ∈ support ((simulateQ (implementation sign) (continueWith action next)).run state)) :
    Cached result.2 :=
  match action with
  | .ok value => keeps value result supported
  | .fail _error => pure_cached _ state cached result supported
  | .div => pure_cached _ state cached result supported

/-- Actual outgoing source execution queries the requested hash before entering its signing continuation. -/
theorem dispatch_run {Encoded : Type} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (command : Command) (request : registration.HashRequest) (requested : command.request = ok request)
    (encoded : core.option.Option Encoded) (state : State) :
    (simulateQ (implementation sign) (dispatch command encoded)).run state = (do
      let hashed ← (implementation sign (.hash request)).run state
      (simulateQ (implementation sign) (continueWith (resumeHash command hashed.1)
        (fun stage => submit command hashed.1 stage encoded))).run hashed.2) := by
  simp only [dispatch, requested, continueWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-- Every reached outgoing source execution derives valid chronological receipts from its actual hash query, without a history/simulation hypothesis. -/
theorem dispatch_cached {Encoded : Type} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (command : Command) (encoded : core.option.Option Encoded) (state : State) (cached : Cached state)
    (result : RustM (DispatchResult Encoded) × State)
    (supported : result ∈ support ((simulateQ (implementation sign) (dispatch command encoded)).run state)) :
    Cached result.2 :=
  (command_request_exact command).elim fun request facts =>
    match OracleComp.mem_support_bind_peel _ _
      ((congrArg (fun work => result ∈ support work)
        (dispatch_run sign command request facts.1 encoded state)).mp supported) with
    | ⟨hashed, queried, rest⟩ =>
      let afterCached := hash_cached_state sign request state cached hashed queried
      continue_cached sign (resumeHash command hashed.1)
        (fun stage => submit command hashed.1 stage encoded) hashed.2 afterCached
        (fun stage output possible => submit_cached sign command hashed.1 stage encoded hashed.2 afterCached
          (facts.2 ▸ (hash_cached sign request state hashed queried).2) output possible)
        result rest

/-- The sign primitive cannot erase a hash receipt, including when it returns no signature. -/
theorem sign_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (request : registration.MldsaSigningRequest) (payload : Payload) (digest : CtxDigest) (state : State)
    (cached : Cached state) (reached : state.2 ((), payload.transcript) = some digest)
    (result : SignReply × State)
    (supported : result ∈ support ((implementation sign (.sign request payload digest)).run state)) :
    Cached result.2 :=
  match OracleComp.mem_support_map_peel _ (sign request) supported with
  | ⟨reply, _possible, same⟩ =>
    same.symm ▸ cached_append state ⟨⟨request.public_key, payload, replyBytes reply⟩, digest⟩ cached reached

/-- Cache receipts of the actual global log discharge the old origin theorem's per-key history premise. -/
theorem history_cached (publicKey : Pqxdh.Bytes) (state : State) (cached : Cached state) :
    MldsaSharedAuthentication.HistoryCached state.2 (historyFor publicKey state) :=
  fun call member =>
    match (BeaconcryptCore.Refinement.RegistrationSigningHistory.history_mem_iff publicKey
      (state.1.map Receipt.observation) call).mp member with
    | ⟨_event, eventMember, _selected, sameCall⟩ =>
      match List.mem_map.mp eventMember with
      | ⟨receipt, receiptMember, sameEvent⟩ =>
        let samePayload := congrArg SigningCall.payload ((congrArg Observation.call sameEvent).trans sameCall)
        ⟨receipt.digest, samePayload ▸ cached receipt receiptMember⟩

abbrev SigningSpec (Encoded : Type) :=
  (Command × core.option.Option Encoded) →ₒ RustM (DispatchResult Encoded)

/-- The private native schedule may interleave outgoing signing with all actual authentication/record primitive requests. -/
abbrev ScheduleSpec (Encoded : Type) := MldsaSharedNative.Spec + SigningSpec Encoded

noncomputable def handler {Encoded : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply) :
    QueryImpl (ScheduleSpec Encoded) (StateT State ProbComp)
  | .inl query => MldsaSharedSource.implementation source writer query
  | .inr (command, encoded) => simulateQ (implementation sign) (dispatch command encoded)

/-- The actual concrete-KDF/native interpreter preserves earlier signing receipts; an outgoing dispatch derives its new receipt. -/
theorem query_cached {Encoded : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (query : (ScheduleSpec Encoded).Domain) (state : State) (cached : Cached state)
    (result : (ScheduleSpec Encoded).Range query × State)
    (supported : result ∈ support ((handler source writer sign query).run state)) : Cached result.2 :=
  match query with
  | .inl native =>
    let preserved := MldsaSharedSource.query_auxiliary_unchanged source writer native state result supported
    let extended := MldsaSharedSource.query_cache_persists source writer native state result supported
    (show (state.1, result.2.2) = result.2 from Prod.ext preserved.symm rfl) ▸
      cached_extend state.1 state.2 result.2.2 extended cached
  | .inr (command, encoded) => dispatch_cached sign command encoded state cached result supported

/-- Arbitrary adaptive native signing/authentication/record schedules retain every reached signing receipt. -/
theorem schedule_cached {Encoded Result : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (work : OracleComp (ScheduleSpec Encoded) Result) (state : State) (cached : Cached state)
    (result : Result × State)
    (supported : result ∈ support ((simulateQ (handler source writer sign) work).run state)) : Cached result.2 :=
  OracleComp.inductionOn
    (C := fun current => ∀ entry : State, Cached entry → ∀ output,
      output ∈ support ((simulateQ (handler source writer sign) current).run entry) → Cached output.2)
    (fun value entry valid output possible => pure_cached value entry valid output possible)
    (fun query next ih entry valid output possible =>
      match OracleComp.mem_support_bind_peel _ _
        (show output ∈ support ((handler source writer sign query).run entry >>= fun step =>
          (simulateQ (handler source writer sign) (next step.1)).run step.2) from by
            simpa only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] using possible) with
      | ⟨step, reached, rest⟩ => ih step.1 step.2
          (query_cached source writer sign query entry valid step reached) output rest)
    work state cached result supported

/-- Actual source execution starts with an empty signing log and the caller's existing shared record cache. -/
noncomputable def run {Encoded Result : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (work : OracleComp (ScheduleSpec Encoded) Result) (cache : CtxRO.QueryCache) : ProbComp (Result × State) :=
  (simulateQ (handler source writer sign) work).run ([], cache)

/-- The existing ML origin theorem's exact per-key hash-history premise follows from the actual reached signing log. -/
theorem run_history_cached {Encoded Result : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (work : OracleComp (ScheduleSpec Encoded) Result) (cache : CtxRO.QueryCache) (publicKey : Pqxdh.Bytes)
    (result : Result × State) (supported : result ∈ support (run source writer sign work cache)) :
    MldsaSharedAuthentication.HistoryCached result.2.2 (historyFor publicKey result.2) :=
  history_cached publicKey result.2 (schedule_cached source writer sign work ([], cache)
    (by simp [Cached]) result supported)

end BeaconcryptCore.Computational.RegistrationSigningShared

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.resume_beacon_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.resume_beacon_request

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.resume_server_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.resume_server_request

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.signing_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.signing_step

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.history_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.history_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.cached_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.cached_extend

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.cached_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.cached_append

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.sign_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.sign_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.hash_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.submit_beacon_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.submit_beacon_run

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.submit_server_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.submit_server_run

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.submit_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.submit_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.hash_cached_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.hash_cached_state

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.dispatch_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.dispatch_run

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.dispatch_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.dispatch_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.query_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.query_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.schedule_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.schedule_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationSigningShared.run_history_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSigningShared.run_history_cached
