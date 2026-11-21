-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgram
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing
import BeaconcryptCore.Refinement.PeerOwnership

/-! The literal Builder prefix reaches a record leaf only after its own supported hash callback. This private analysis receipt retains the same request, reply and complete intermediate states; no observation or callback is added to the executable program. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdProgramCut
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterBuildProgram (Spec)
open AdapterPublicServerBuildTrace (Word)
open RegistrationNativeStageTrace (Call Path Executed)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {S Log : Type}

/-- The real source hash edge before this particular initial record capability. -/
structure HashCut (implementation : QueryImpl Spec (StateT S ProbComp))
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (control : pqxdh.ServerState)
    (initial : registration.ServerInitialKdf) (first : S) where
  pin : session.ServerAuthenticationPin
  availability : pqxdh.KeyIdAvailability
  application : Slice U8
  pending : registration.ServerAdHash
  request : registration.HashRequest
  digest : core.option.Option (Std.Array U8 64#usize)
  beforeHash : S
  afterHash : S
  leading : List (Call Spec S)
  selected : registration.begin_server_completion control pin availability token.registration.agreement application = .ok (.Ok pending)
  requested : pending.request = .ok request
  resumed : pending.resume digest = .ok (.Ok initial)
  path : Path implementation first leading beforeHash
  called : Executed implementation ⟨.inl (.inr request), beforeHash, .ok digest, afterHash⟩

/-- Prefix callbacks have no first-record/signing observation. -/
def Prefix : Spec.Domain → Prop
  | .inr (.inr (.inr _)) => False
  | _ => True

private def returned {A : Type} (_self : beaconcrypt_public_wrapper.server.Server)
    (result : RustM A) (next : A → OracleComp Spec Word) : OracleComp Spec Word :=
  match result with
  | .fail error => pure (none, .fail error)
  | .div => pure (none, .div)
  | .ok value => next value

private def checked {A Error : Type} (self : beaconcrypt_public_wrapper.server.Server)
    (result : RustM (core.result.Result A Error)) (next : A → OracleComp Spec Word) : OracleComp Spec Word :=
  match result with
  | .fail error => pure (none, .fail error)
  | .div => pure (none, .div)
  | .ok (.Err _) => pure (none, .ok (.None, self))
  | .ok (.Ok value) => next value

variable (implementation : QueryImpl Spec (StateT S ProbComp)) (events : S → List Log)
variable (quiet : ∀ query, Prefix query → ∀ before result,
  result ∈ support ((implementation query).run before) → events result.2 = events before)

private theorem pure_same (value : Word) (first : S) (result : Word × S)
    (supported : result ∈ support ((simulateQ implementation (pure value)).run first)) :
    events result.2 = events first := by
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem returned_live {A : Type} (self : beaconcrypt_public_wrapper.server.Server)
    (value : RustM A) (next : A → OracleComp Spec Word) (first : S) (result : Word × S)
    (supported : result ∈ support ((simulateQ implementation (returned self value next)).run first))
    (changed : events result.2 ≠ events first) :
    ∃ actual, value = .ok actual ∧ result ∈ support ((simulateQ implementation (next actual)).run first) := by
  cases value with
  | ok actual => exact ⟨actual, rfl, supported⟩
  | fail error | div => exact False.elim (changed (pure_same implementation events _ first result supported))

private theorem checked_live {A Error : Type} (self : beaconcrypt_public_wrapper.server.Server)
    (value : RustM (core.result.Result A Error)) (next : A → OracleComp Spec Word)
    (first : S) (result : Word × S)
    (supported : result ∈ support ((simulateQ implementation (checked self value next)).run first))
    (changed : events result.2 ≠ events first) :
    ∃ actual, value = .ok (.Ok actual) ∧ result ∈ support ((simulateQ implementation (next actual)).run first) := by
  cases value with
  | fail error | div => exact False.elim (changed (pure_same implementation events _ first result supported))
  | ok answer => cases answer with
    | Err error => exact False.elim (changed (pure_same implementation events _ first result supported))
    | Ok actual => exact ⟨actual, rfl, supported⟩

omit material platform ed in
private theorem lookup_fields (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (token : peer.ConsumedRegistration) (application : Slice U8) (lookup : peer.CompletionLookup)
    (actual : peer.begin_completion_lookup control pin token application = .ok (.Ok lookup)) :
    lookup.control = control ∧ lookup.registration = token := by
  cases next : pqxdh.server_next_key_id control with
  | fail error | div => simp only [peer.begin_completion_lookup, next] at actual; cases actual
  | ok result => cases result with
    | Err error => simp only [peer.begin_completion_lookup, next, bind_tc_ok] at actual; cases actual
    | Ok keyId =>
      simp only [peer.begin_completion_lookup, next, bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
      cases actual
      exact ⟨rfl, rfl⟩

include quiet in
private theorem adHash_live (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : registration.ServerAdHash)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability) (application : Slice U8)
    (selected : registration.begin_server_completion self.control pin availability token.registration.agreement application = .ok (.Ok pending))
    (first : S) (result : Word × S)
    (supported : result ∈ support ((simulateQ implementation (RegistrationNativePlatformPublicAdapterBuildProgram.adHash self pending)).run first))
    (changed : events result.2 ≠ events first) :
    ∃ (initial : registration.ServerInitialKdf) (cut : HashCut implementation token self.control initial first),
      events cut.afterHash = events first ∧
      result ∈ support ((simulateQ implementation (RegistrationNativePlatformPublicAdapterBuildProgram.reserved self initial)).run cut.afterHash) := by
  change result ∈ support ((simulateQ implementation (returned self pending.request fun request => do
    let reply ← Spec.query (.inl (.inr request))
    returned self reply fun digest => checked self (pending.resume digest)
      (RegistrationNativePlatformPublicAdapterBuildProgram.reserved self))).run first) at supported
  obtain ⟨request, requested, supported⟩ := returned_live implementation events self pending.request _ first result supported changed
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, supported⟩ := supported
  have same := quiet (.inl (.inr request)) True.intro first middle called
  have later : events result.2 ≠ events middle.2 := fun equal => changed (equal.trans same)
  obtain ⟨digest, actualReply, supported⟩ := returned_live implementation events self middle.1 _ middle.2 result supported later
  obtain ⟨initial, resumed, reached⟩ := checked_live implementation events self (pending.resume digest) _ middle.2 result supported later
  refine ⟨initial, ⟨pin, availability, application, pending, request, digest, first, middle.2, [],
    selected, requested, resumed, .nil _, ?_⟩, same, reached⟩
  change (.ok digest, middle.2) ∈ support ((implementation (.inl (.inr request))).run first)
  rw [← actualReply]
  exact called

include quiet in
private theorem lookup_live (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.CompletionLookup) (plaintext : Slice U8)
    (control : pending.control = self.control) (moved : pending.registration = token.registration)
    (first : S) (result : Word × S)
    (supported : result ∈ support ((simulateQ implementation (RegistrationNativePlatformPublicAdapterBuildProgram.lookup self pending plaintext)).run first))
    (changed : events result.2 ≠ events first) :
    ∃ (initial : registration.ServerInitialKdf) (cut : HashCut implementation token self.control initial first),
      events cut.afterHash = events first ∧
      result ∈ support ((simulateQ implementation (RegistrationNativePlatformPublicAdapterBuildProgram.reserved self initial)).run cut.afterHash) := by
  change result ∈ support ((simulateQ implementation (returned self pending.request fun identifier =>
    returned self (CoreModels.core.slice.Slice.len plaintext) fun size =>
    returned self (transport.registration_response_len size identifier) fun optional => match optional with
    | .None => pure (none, .ok (.None, self))
    | .Some _ => do
      let reply ← Spec.query (.inr (.inl (self.known_ids, identifier)))
      returned self reply fun occupied => checked self (pending.resume occupied)
        (RegistrationNativePlatformPublicAdapterBuildProgram.adHash self))).run first) at supported
  obtain ⟨identifier, _requested, supported⟩ := returned_live implementation events self pending.request _ first result supported changed
  obtain ⟨size, _size, supported⟩ := returned_live implementation events self (CoreModels.core.slice.Slice.len plaintext) _ first result supported changed
  obtain ⟨optional, _capacity, supported⟩ := returned_live implementation events self (transport.registration_response_len size identifier) _ first result supported changed
  cases optional with
  | none => exact False.elim (changed (pure_same implementation events _ first result supported))
  | some capacity =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, supported⟩ := supported
    have same := quiet (.inr (.inl (self.known_ids, identifier))) True.intro first middle called
    have later : events result.2 ≠ events middle.2 := fun equal => changed (equal.trans same)
    obtain ⟨occupied, _reply, supported⟩ := returned_live implementation events self middle.1 _ middle.2 result supported later
    obtain ⟨selected, resumed, supported⟩ := checked_live implementation events self (pending.resume occupied) _ middle.2 result supported later
    have selectedRun : registration.begin_server_completion self.control pending.pin
        (if occupied then .Occupied else .Available) token.registration.agreement pending.application = .ok (.Ok selected) := by
      simpa only [PeerOwnership.completion_lookup_resume, control, moved] using resumed
    obtain ⟨initial, cut, logs, reached⟩ := adHash_live implementation events quiet token self selected pending.pin
      (if occupied then .Occupied else .Available) pending.application selectedRun middle.2 result supported later
    let edge : Call Spec S := ⟨.inr (.inl (self.known_ids, identifier)), first, middle.1, middle.2⟩
    exact ⟨initial, { cut with leading := edge :: cut.leading, path := .cons edge called _ _ cut.path }, logs.trans same, reached⟩

include quiet in
/-- A genuinely new observation in the literal Builder requires its actual hash callback, then the same reserved continuation and final outcome. -/
theorem program_live (self : beaconcrypt_public_wrapper.server.Server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (first : S) (result : Word × S)
    (supported : result ∈ support ((simulateQ implementation (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run first))
    (changed : events result.2 ≠ events first) :
    ∃ (initial : registration.ServerInitialKdf) (cut : HashCut implementation token self.control initial first),
      events cut.afterHash = events first ∧
      result ∈ support ((simulateQ implementation (RegistrationNativePlatformPublicAdapterBuildProgram.reserved self initial)).run cut.afterHash) := by
  change result ∈ support ((simulateQ implementation (returned self (transport.normalize_registration_application data) fun application =>
    returned self (beaconcrypt_public_wrapper.server.registration_application_bytes application) fun plaintext => do
      let reply ← Spec.query (.inl (.inl self))
      returned self reply fun optional => match optional with
      | .None => pure (none, .ok (.None, self))
      | .Some pin => checked self (peer.begin_completion_lookup self.control pin token.registration plaintext)
        (fun pending => RegistrationNativePlatformPublicAdapterBuildProgram.lookup self pending plaintext))).run first) at supported
  obtain ⟨application, _normalized, supported⟩ := returned_live implementation events self (transport.normalize_registration_application data) _ first result supported changed
  obtain ⟨plaintext, _bytes, supported⟩ := returned_live implementation events self (beaconcrypt_public_wrapper.server.registration_application_bytes application) _ first result supported changed
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, supported⟩ := supported
  have same := quiet (.inl (.inl self)) True.intro first middle called
  have later : events result.2 ≠ events middle.2 := fun equal => changed (equal.trans same)
  obtain ⟨optional, _reply, supported⟩ := returned_live implementation events self middle.1 _ middle.2 result supported later
  cases optional with
  | none => exact False.elim (later (pure_same implementation events _ middle.2 result supported))
  | some pin =>
    obtain ⟨pending, begun, supported⟩ := checked_live implementation events self
      (peer.begin_completion_lookup self.control pin token.registration plaintext) _ middle.2 result supported later
    obtain ⟨control, moved⟩ := lookup_fields self.control pin token.registration plaintext pending begun
    obtain ⟨initial, cut, logs, reached⟩ := lookup_live implementation events quiet token self pending plaintext
      control moved middle.2 result supported later
    let edge : Call Spec S := ⟨.inl (.inl self), first, middle.1, middle.2⟩
    exact ⟨initial, { cut with leading := edge :: cut.leading, path := .cons edge called _ _ cut.path }, logs.trans same, reached⟩

include quiet in
/-- A new observation comes from the same complete leaf after the actual source hash and reservation prefix, retaining all later return branches. -/
theorem program_call
    (appends : ∀ query before result, result ∈ support ((implementation query).run before) →
      ∃ suffix, events result.2 = events before ++ suffix)
    (self : beaconcrypt_public_wrapper.server.Server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (first : S) (result : Word × S)
    (supported : result ∈ support ((simulateQ implementation (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data)).run first))
    (suffix : List Log) (observed : events result.2 = events first ++ suffix)
    (item : Log) (present : item ∈ suffix) :
    ∃ (leading trailing : List (Call Spec S)) (call : Call Spec S),
      Path implementation first leading call.before ∧ Executed implementation call ∧
      Path implementation call.after trailing result.2 ∧
      ∃ (current : beaconcrypt_public_wrapper.server.Server) (initial : registration.ServerInitialKdf),
        call.query = .inr (.inr (.inr (current, initial))) ∧ current.control = self.control ∧
      ∃ (ad : HashCut implementation token self.control initial first) (between : List (Call Spec S)),
        Path implementation ad.afterHash between call.before ∧
      ∃ emitted, events call.after = events call.before ++ emitted ∧ item ∈ emitted := by
  have changed : events result.2 ≠ events first := by
    intro same
    have empty : suffix = [] :=
      List.append_cancel_left (observed.symm.trans (same.trans (List.append_nil _).symm))
    rw [empty] at present
    cases present
  obtain ⟨initial, ad, hashLog, reservedSupported⟩ :=
    program_live implementation events quiet self token data first result supported changed
  let allowed : Spec.Domain → Prop := fun query => match query with
    | .inr (.inr (.inr (current, next))) => current.control = self.control ∧ next = initial
    | _ => True
  have safe : (RegistrationNativePlatformPublicAdapterBuildProgram.reserved self initial).AllQueriesSatisfy allowed := by
    unfold RegistrationNativePlatformPublicAdapterBuildProgram.reserved
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨True.intro, ?_⟩
    intro reply
    cases reply with
    | fail error | div => exact allQueriesSatisfy_pure _ _
    | ok pair =>
      rcases pair with ⟨answer, known⟩
      cases answer with
      | Err error => exact allQueriesSatisfy_pure _ _
      | Ok value =>
        change AllQueriesSatisfy ((fun result : (AdapterPublicServerBuildTrace.Publication × RustM AdapterPublicServerBuildBody.Reply) =>
          (some result.1, result.2)) <$> (Spec.query (.inr (.inr (.inr ({self with known_ids := known}, initial)))) :
            OracleComp Spec (AdapterPublicServerBuildTrace.Publication × RustM AdapterPublicServerBuildBody.Reply))) allowed
        rw [allQueriesSatisfy_def, isQueryBound_map_iff, ← allQueriesSatisfy_def, allQueriesSatisfy_query_iff]
        exact ⟨rfl, rfl⟩
  have reservedObserved : events result.2 = events ad.afterHash ++ suffix := by
    simpa only [hashLog] using observed
  have quietMarked : ∀ query, ¬¬Prefix query → ∀ before result,
      result ∈ support ((implementation query).run before) → events result.2 = events before := by
    classical
    intro query permitted before result called
    exact quiet query (not_not.mp permitted) before result called
  obtain ⟨leading, trailing, call, beforePath, called, afterPath, permitted, marked, emitted, logEq, seen⟩ :=
    RegistrationNativePlatformPublicAdapterSourceLogCrossing.crossing implementation events appends allowed
      (fun query => ¬Prefix query) quietMarked
      (RegistrationNativePlatformPublicAdapterBuildProgram.reserved self initial) safe
      ad.afterHash result reservedSupported suffix reservedObserved item present
  let hashCall : Call Spec S := ⟨.inl (.inr ad.request), ad.beforeHash, .ok ad.digest, ad.afterHash⟩
  refine ⟨ad.leading ++ hashCall :: leading, trailing, call,
    ad.path.append (.cons hashCall ad.called _ _ beforePath), called, afterPath, ?_⟩
  cases queryEq : call.query with
  | inl query =>
    simp only [Prefix, queryEq] at marked
    exact False.elim (marked True.intro)
  | inr query => cases query with
    | inl pair =>
      simp only [Prefix, queryEq] at marked
      exact False.elim (marked True.intro)
    | inr query => cases query with
      | inl known =>
        simp only [Prefix, queryEq] at marked
        exact False.elim (marked True.intro)
      | inr pair =>
        have permittedPair : pair.1.control = self.control ∧ pair.2 = initial := by
          simpa only [allowed, queryEq] using permitted
        obtain ⟨controlEq, initialEq⟩ := permittedPair
        refine ⟨pair.1, initial, ?_, controlEq, ad, leading, beforePath, emitted, logEq, seen⟩
        exact congrArg (fun pair : beaconcrypt_public_wrapper.server.Server × registration.ServerInitialKdf =>
          Sum.inr (Sum.inr (Sum.inr pair)) : _ → Spec.Domain) (Prod.ext rfl initialEq)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdProgramCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdProgramCut.program_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdProgramCut.program_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdProgramCut.program_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdProgramCut.program_call
