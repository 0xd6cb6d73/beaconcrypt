-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthNative

/-! Exact volatile registration-set admission from the original source handlers. The complete native experiment supplies fresh append and replay exclusion. A separate finite-trace mutex abstraction matches only the consumed-set projection; it is not a compiler for applied-pi processes or an additional cryptographic assumption. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationAdmission
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhServerRootPreparation PqxdhServerStaticDhSource
theorem state_bind {σ α β : Type} (work : StateT σ ProbComp α)
    (next : α → StateT σ ProbComp β) (state : σ) :
    (work >>= next) state = work state >>= fun result => next result.1 result.2 := rfl

theorem lifted_state {α σ : Type} (work : ProbComp α) (state : σ) (result : α × σ)
    (supported : result ∈ support ((StateT.lift work : StateT σ ProbComp α) state)) :
    result.2 = state := by
  change result ∈ support (work >>= fun value => pure (value, state)) at supported
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨value, _, rfl⟩ := supported
  rfl

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every preparation callback retains the full consumed-registration set, including rejected primitive calls. -/
theorem prefix_step_preserves (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (query : (Spec Reader ScalarBytes PeerEncoding).Domain)
    (consumed : List Pqxdh.Bytes) (result : (Spec Reader ScalarBytes PeerEncoding).Range query × List Pqxdh.Bytes)
    (supported : result ∈ support ((prefixImpl setup.serverDomain (serverAux setup codec checks)
      (fun _ => pure ())) query consumed)) : result.2 = consumed := by
  cases query <;> simp only [prefixImpl, serverAux, support_pure,
    Set.mem_singleton_iff] at supported
  all_goals try exact congrArg Prod.snd supported
  all_goals exact lifted_state _ _ _ supported

/-- The complete preparation program cannot mutate admission state. -/
theorem prefix_program_preserves (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) {α : Type} (program : OracleComp (Spec Reader ScalarBytes PeerEncoding) α)
    (consumed : List Pqxdh.Bytes) (result : α × List Pqxdh.Bytes)
    (supported : result ∈ support ((simulateQ (prefixImpl setup.serverDomain
      (serverAux setup codec checks) (fun _ => pure ())) program).run consumed)) : result.2 = consumed := by
  exact run_rel _ (fun before after => after = before) (fun _ => rfl)
    (fun _ _ _ first second => second.trans first)
    (prefix_step_preserves setup codec checks) program consumed result supported

/-- The exact consumed pair rejects before reservation, generation or encapsulation. -/
theorem collect_consumed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (verified : Verified Reader) (consumed : List Pqxdh.Bytes)
    (used : registrationId verified ∈ consumed) :
    ((simulateQ (prefixImpl setup.serverDomain (serverAux setup codec checks) (fun _ => pure ()))
      (collectVerified verified)).run consumed) = pure (none, consumed) := by
  simp only [collectVerified, OptionT.run_bind, OptionT.run_monadLift, Option.elimM,
    bind_map_left, simulateQ_bind, simulateQ_spec_query, prefixImpl, serverAux,
    StateT.run, state_bind, pure_bind, used, ite_true, Option.elim_some, OptionT.run_failure,
    simulateQ_pure]
  rfl

/-- Successful collection retains exactly the verified fields used for the consumed-ID check. -/
theorem collect_verified {E Shared A : Type}
    (impl : QueryImpl (Spec Reader E Shared) (StateT A ProbComp))
    (verified : Verified Reader) (initial final : A) (input : Inputs Reader E Shared)
    (reached : (some input, final) ∈ support ((simulateQ impl (collectVerified verified)).run initial)) :
    input.verified = verified := by
  simp only [collectVerified, OptionT.run_bind, OptionT.run_monadLift, Option.elimM,
    bind_map_left, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
  repeat' first
    | (simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
        OptionT.run_failure, Option.elimM, bind_map_left, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true, Option.elim_none, Option.elim_some,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq, Option.some_ne_none, false_and] at reached)
    | (obtain ⟨⟨reply, state⟩, step, reached⟩ := reached; cases reply)
    | (split at reached)
  all_goals simp_all

/-- Every successful raw prefix checked this exact pair as absent in the unchanged source set. -/
theorem prefix_fresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (raw : Pqxdh.Bytes) (consumed final : List Pqxdh.Bytes)
    (input : Inputs Reader ScalarBytes PeerEncoding)
    (reached : (some input, final) ∈ support ((serverPrefix setup codec checks raw).run consumed)) :
    registrationId input.verified ∉ consumed := by
  simp only [serverPrefix, collect, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨⟨verified, afterVerify⟩, checked, reached⟩ := reached
  have same := prefix_program_preserves setup codec checks (verifyInput raw) consumed
    (verified, afterVerify) checked
  dsimp only at same
  subst afterVerify
  cases verified with
  | none => simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some_ne_none, false_and] at reached
  | some verified =>
      have fields := collect_verified _ verified consumed final input reached
      rw [fields]
      intro used
      rw [collect_consumed setup codec checks verified consumed used] at reached
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        Option.some_ne_none, false_and] at reached

/-- Consumption happens exactly on a successful root return; every failed root leaves the set untouched. -/
theorem client_consumed (index : Nat) (serverBinding : pqxdh.ServerBinding)
    (input : Inputs Reader ScalarBytes PeerEncoding) (state : GameState KemSK)
    (result : RustM (Option PqxdhServerRelatedRootConsumer.Returned) × GameState KemSK)
    (supported : result ∈ support ((simulateQ (sessionImpl index)
      (PqxdhServerRelatedRootConsumer.client serverBinding input)).run state)) :
    result.2.server.consumed = match result.1 with
      | .ok (some token) => state.server.consumed ++ [absBytes token.pending.registration_id.bytes]
      | _ => state.server.consumed := by
  classical
  simp only [PqxdhServerRelatedRootConsumer.client, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨erased, erasedRun, supported⟩ := supported
  simp only [sessionImpl, StateT.run_pure, support_pure, Set.mem_singleton_iff] at erasedRun
  subst erasedRun
  by_cases valid : PqxdhServerRelatedRootInput.localNonzero input
  · simp only [valid, not_true_eq_false, ite_false, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨derived, derivedRun, supported⟩ := supported
    simp only [sessionImpl, sessionFamily, StateT.run_bind, mem_support_bind_iff] at derivedRun
    obtain ⟨forwarded, forwardedRun, derivedRun⟩ := derivedRun
    have same := forward_support _ _ _ forwardedRun
    simp only [record_run, StateT.run_pure, support_pure, Set.mem_singleton_iff, same] at derivedRun
    obtain ⟨_, rfl, rfl⟩ := derivedRun
    obtain ⟨erasedInput, erasedInputRun, supported⟩ := supported
    simp only [sessionImpl, StateT.run_pure, support_pure, Set.mem_singleton_iff] at erasedInputRun
    subst erasedInputRun
    cases hreply : forwarded.1 with
    | none =>
        simp only [hreply, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        rfl
    | some root =>
        simp only [hreply, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
          StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
        obtain ⟨consumedRun, consumedMember, supported⟩ := supported
        simp only [sessionImpl] at consumedMember
        subst consumedMember
        subst supported
        rfl
  · simp only [valid, not_false_eq_true, ite_true, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl

/-- The consumed token bytes are exactly the checked 64-byte identity/one-time pair. -/
theorem pending_registration_bytes {E Shared : Type} (serverBinding : pqxdh.ServerBinding)
    (input : Inputs Reader E Shared) :
    absBytes (PqxdhServerClearedRoot.pending serverBinding input).registration_id.bytes =
      registrationId input.verified := by
  simp [PqxdhServerClearedRoot.pending, PqxdhServerClearedRoot.registrationIdValue,
    registrationId, absBytes, List.map_map, Function.comp_def]

/-- Every complete raw admission either leaves the consumed set unchanged or appends exactly one previously absent source registration ID. -/
theorem accept_consumed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    (result.1 = none ∧ result.2.server.consumed = state.server.consumed) ∨
      ∃ index token, result.1 = some index ∧ result.2.pending index = some token ∧
        absBytes token.pending.registration_id.bytes ∉ state.server.consumed ∧
        result.2.server.consumed = state.server.consumed ++ [absBytes token.pending.registration_id.bytes] := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨collectedMember, same⟩ := liftCoins_mem _ _ _ lifted
  have preserved := prefix_program_preserves setup codec checks (collect raw)
    state.server.consumed collected.1 collectedMember
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact Or.inl ⟨rfl, preserved⟩
  | some input =>
      have fresh := prefix_fresh setup codec checks raw state.server.consumed collected.1.2 input
        (by simpa only [← hc] using collectedMember)
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      have changed := client_consumed state.sessions (binding setup publicValue) input _ returned derived
      obtain ⟨_, _, _, _, tokenFields⟩ := client_run state.sessions (binding setup publicValue) input _ returned derived
      rcases returned with ⟨outcome, after⟩
      dsimp only at changed tokenFields
      rcases outcome with (_ | token) | error | _
      all_goals simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      all_goals subst supported
      · exact Or.inl ⟨rfl, changed.trans preserved⟩
      · have fields := (tokenFields token rfl).2.2
        have bytes := (congrArg (fun pending => absBytes pending.registration_id.bytes) fields).trans
          (pending_registration_bytes (binding setup publicValue) input)
        exact Or.inr ⟨state.sessions, token, rfl, Function.update_self ..,
          bytes ▸ fresh, changed.trans (by rw [preserved])⟩
      · exact Or.inl ⟨rfl, changed.trans preserved⟩
      · exact Or.inl ⟨rfl, changed.trans preserved⟩

/-- Response construction cannot undo consumption, including every failed writer or commit. -/
theorem build_consumed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run state)) :
    result.2.server.consumed = state.server.consumed := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending session with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some token =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨tail, lifted, supported⟩ := supported
      obtain ⟨tailMember, same⟩ := liftCoins_mem _ _ _ lifted
      have outcome := build_support (tailImpl setup codec checks) setup.source
        (tailImpl_kdf setup codec checks) token.pending token.root payload () state.server
        ([], state.ctx) tail.1 tailMember
      simp only [same, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      rcases outcome with unchanged | ⟨candidate, kernel, response, published, _⟩
      · rw [unchanged]
        rfl
      · rw [published]
        rfl

/-- The entire Beacon finish leaves the Server's consumed set unchanged. -/
theorem finish_consumed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option Pqxdh.Bytes × GameState KemSK)
    (supported : result ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run state)) :
    result.2.server.consumed = state.server.consumed := by
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

/-- Every non-admission capability preserves the set, including response failure and post-registration reveals. -/
theorem handler_consumed_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (notAccept : ¬ IsAcceptQuery query) (state : GameState KemSK)
    (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    result.2.server.consumed = state.server.consumed := by
  rcases query with coin | query
  · rw [forward_support _ _ _ supported]
  cases query with
  | accept raw => exact (notAccept trivial).elim
  | build index payload => exact build_consumed setup codec checks index payload state result supported
  | finish raw => exact finish_consumed setup codec publicValue beaconSeed raw state result supported
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

/-- The source set grows only by fresh append. The ordered list is a private history representation, not a new protocol field. -/
def AdmissionStep (before after : List Pqxdh.Bytes) : Prop :=
  after = before ∨ ∃ rid, rid ∉ before ∧ after = before ++ [rid]

/-- Every original adaptive API step implements the admission transition. -/
theorem handler_admission (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    AdmissionStep state.server.consumed result.2.server.consumed := by
  cases query with
  | inl coin => exact Or.inl (handler_consumed_quiet setup codec checks publicValue beaconSeed _ (by simp [IsAcceptQuery]) state result supported)
  | inr query =>
      cases query with
      | accept raw =>
          rcases accept_consumed setup codec checks publicValue raw state result supported with
            ⟨_, same⟩ | ⟨index, token, _, _, fresh, changed⟩
          · exact Or.inl same
          · exact Or.inr ⟨_, fresh, changed⟩
      | _ => exact Or.inl (handler_consumed_quiet setup codec checks publicValue beaconSeed _ (by simp [IsAcceptQuery]) state result supported)

/-- An admission step preserves all old entries and cannot introduce a duplicate. -/
theorem admission_invariant (before after : List Pqxdh.Bytes) (step : AdmissionStep before after) :
    before.IsPrefix after ∧ (before.Nodup → after.Nodup) := by
  rcases step with rfl | ⟨rid, fresh, rfl⟩
  · exact ⟨List.prefix_rfl, id⟩
  · refine ⟨⟨[rid], rfl⟩, ?_⟩
    intro unique
    rw [List.nodup_append]
    refine ⟨unique, by simp, ?_⟩
    intro left member right single equal
    simp only [List.mem_singleton] at single
    exact fresh ((equal.trans single) ▸ member)

/-- Any adaptive continuation preserves old consumption and uniqueness, with no session or query cap needed. -/
theorem program_consumed {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (program : OracleComp ServerAuthSpec α) (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run state)) :
    state.server.consumed.IsPrefix result.2.server.consumed ∧
      (state.server.consumed.Nodup → result.2.server.consumed.Nodup) := by
  exact run_rel _ (fun before after => before.server.consumed.IsPrefix after.server.consumed ∧
    (before.server.consumed.Nodup → after.server.consumed.Nodup))
    (fun _ => ⟨List.prefix_rfl, id⟩)
    (fun _ _ _ first second => ⟨first.1.trans second.1, second.2 ∘ first.2⟩)
    (fun query before after member => admission_invariant _ _
      (handler_admission setup codec checks publicValue beaconSeed query before after member))
    program state result supported

/-- Every token actually returned by admission carries its newly inserted pair and records that pair as previously absent. -/
theorem accepted_id (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state))
    (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (returned : result.1 = some index) (stored : result.2.pending index = some token) :
    absBytes token.pending.registration_id.bytes ∉ state.server.consumed ∧
      result.2.server.consumed = state.server.consumed ++ [absBytes token.pending.registration_id.bytes] := by
  rcases accept_consumed setup codec checks publicValue raw state result supported with
    ⟨none, _⟩ | ⟨other, actual, found, slot, fresh, changed⟩
  · simp only [returned, Option.some_ne_none] at none
  · have same := Option.some.inj (found.symm.trans returned)
    subst other
    have sameToken := Option.some.inj (slot.symm.trans stored)
    subst actual
    exact ⟨fresh, changed⟩

/-- No successfully admitted pair can be admitted again after an arbitrary adaptive continuation. The bytes and identities need not be honest and the response need never be built. -/
theorem no_reacceptance {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (raw firstRaw : Pqxdh.Bytes) (initial : GameState KemSK)
    (first : Option Nat × GameState KemSK)
    (firstRun : first ∈ support ((acceptOracle setup codec checks publicValue firstRaw).run initial))
    (firstIndex : Nat) (firstToken : PqxdhServerRelatedRootConsumer.Returned)
    (firstReturned : first.1 = some firstIndex) (firstStored : first.2.pending firstIndex = some firstToken)
    (program : OracleComp ServerAuthSpec α) (middle : α × GameState KemSK)
    (middleRun : middle ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run first.2))
    (last : Option Nat × GameState KemSK)
    (lastRun : last ∈ support ((acceptOracle setup codec checks publicValue raw).run middle.2))
    (lastIndex : Nat) (lastToken : PqxdhServerRelatedRootConsumer.Returned)
    (lastReturned : last.1 = some lastIndex) (lastStored : last.2.pending lastIndex = some lastToken) :
    absBytes firstToken.pending.registration_id.bytes ≠ absBytes lastToken.pending.registration_id.bytes := by
  have firstId := accepted_id setup codec checks publicValue firstRaw initial first firstRun
    firstIndex firstToken firstReturned firstStored
  have lastId := accepted_id setup codec checks publicValue raw middle.2 last lastRun
    lastIndex lastToken lastReturned lastStored
  have retained := (program_consumed setup codec checks publicValue beaconSeed program first.2 middle middleRun).1
  have present : absBytes firstToken.pending.registration_id.bytes ∈ first.2.server.consumed := by
    rw [firstId.2]
    simp
  intro equal
  exact lastId.1 (equal ▸ retained.subset present)

/-- The literal native acceptance has the same exact failure-or-fresh-append behavior, retaining the shared primitive state. -/
theorem native_accept_consumed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthNative.NativeState KemSK)
    (result : Option Nat × PqxdhServerAuthNative.NativeState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthNative.nativeAccept setup codec checks seed scalar raw).run state)) :
    (result.1 = none ∧ result.2.2.server.consumed = state.2.server.consumed) ∨
      ∃ index token, result.1 = some index ∧ result.2.2.pending index = some token ∧
        absBytes token.pending.registration_id.bytes ∉ state.2.server.consumed ∧
        result.2.2.server.consumed = state.2.server.consumed ++ [absBytes token.pending.registration_id.bytes] := by
  apply accept_consumed setup codec checks (challenge setup.joint setup.dh seed scalar) raw state.2 (result.1, result.2.2)
  apply PqxdhServerAuthNative.evaluate_support setup seed scalar _ state result
  rw [PqxdhServerAuthNative.accept_native]
  exact supported

/-- The actual constructor order and complete native adaptive experiment start with an empty set and never duplicate any consumed pair. All origin, seed-compromise, rejection and unbuilt-session choices remain unrestricted. -/
theorem source_ordered_unique (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthNative.sourceOrderedState setup codec checks revealSeed adversary)) :
    result.2.2.1.server.consumed.Nodup := by
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
  exact (program_consumed setup codec checks (challenge setup.joint setup.dh seed scalar)
    beaconSeed _ _ (final.1, final.2.2) original).2 (by simp [initialGameState])

/-- Registration IDs have their actual fixed width, without a hash or collision assumption. -/
theorem registration_width (verified : Verified Reader) : (registrationId verified).length = 64 := by
  simp [registrationId]

/-- Exact source registration-ID equality is precisely equality of the two 32-byte fields. Prekey and KEM changes do not create a new consumed-set key. -/
theorem registration_eq_iff (left right : Verified Reader) :
    registrationId left = registrationId right ↔
      left.identity.toList = right.identity.toList ∧ left.keys.oneTime.toList = right.keys.oneTime.toList := by
  constructor
  · intro same
    have first := congrArg (List.take 32) same
    have second := congrArg (List.drop 32) same
    exact ⟨by simpa [registrationId] using first, by simpa [registrationId] using second⟩
  · rintro ⟨identity, oneTime⟩
    simp only [registrationId, identity, oneTime]

/-- Volatile owner state at the consumed-set boundary. A lease denotes a held mutex after the exact pair passed the source freshness test. -/
structure Owner where
  consumed : List Pqxdh.Bytes
  lease : Option Pqxdh.Bytes
  deriving DecidableEq

inductive OwnerAction where
  | enter : Pqxdh.Bytes → OwnerAction
  | abort
  | commit

/-- A busy owner cannot start another request. Failure releases the owner without consumption; successful root completion consumes the reserved pair and releases it. -/
def ownerStep (action : OwnerAction) (state : Owner) : Owner :=
  match action with
  | .enter rid => match state.lease with
    | some _ => state
    | none => if rid ∈ state.consumed then state else { state with lease := some rid }
  | .abort => { state with lease := none }
  | .commit => match state.lease with
    | none => state
    | some rid => ⟨state.consumed ++ [rid], none⟩

/-- The mutex makes freshness stable throughout the whole private root computation. -/
def LeaseFresh (state : Owner) : Prop := ∀ rid, state.lease = some rid → rid ∉ state.consumed

/-- The invariant follows from the actual check/acquire and release operations, never from an assumed replay conclusion. -/
theorem owner_step_fresh (action : OwnerAction) (state : Owner) (valid : LeaseFresh state) :
    LeaseFresh (ownerStep action state) := by
  cases action with
  | enter rid =>
      cases old : state.lease with
      | some previous => simpa only [ownerStep, old] using valid
      | none =>
          by_cases used : rid ∈ state.consumed
          · simpa only [ownerStep, old, used, ite_true] using valid
          · simp only [ownerStep, old, used, ite_false, LeaseFresh, Option.some.injEq]
            intro other same
            subst other
            exact used
  | abort => simp [ownerStep, LeaseFresh]
  | commit => cases old : state.lease <;> simp_all [ownerStep, LeaseFresh]

/-- Every mutex/table transition implements exactly the same fresh-append relation as native source admission. -/
theorem owner_step_admission (action : OwnerAction) (state : Owner) (valid : LeaseFresh state) :
    AdmissionStep state.consumed (ownerStep action state).consumed := by
  cases action with
  | enter rid =>
      cases old : state.lease with
      | some previous => exact Or.inl (by simp [ownerStep, old])
      | none => by_cases used : rid ∈ state.consumed <;>
          simp only [ownerStep, old, used, ite_true, ite_false] <;> exact Or.inl rfl
  | abort => exact Or.inl rfl
  | commit =>
      cases old : state.lease with
      | none => exact Or.inl (by simp [ownerStep, old])
      | some rid => exact Or.inr ⟨rid, valid rid old, by simp [ownerStep, old]⟩

/-- Arbitrary finite interleavings of attempts and root outcomes, with no bound on their length. -/
def ownerRun (actions : List OwnerAction) (state : Owner) : Owner :=
  actions.foldl (fun current action => ownerStep action current) state

/-- Every finite process trace preserves both the held-lease invariant and consumed-set uniqueness. -/
theorem owner_run_unique (actions : List OwnerAction) (state : Owner) (valid : LeaseFresh state)
    (unique : state.consumed.Nodup) :
    LeaseFresh (ownerRun actions state) ∧ (ownerRun actions state).consumed.Nodup := by
  induction actions generalizing state with
  | nil => exact ⟨valid, unique⟩
  | cons action actions ih =>
      exact ih (ownerStep action state) (owner_step_fresh action state valid)
        ((admission_invariant _ _ (owner_step_admission action state valid)).2 unique)

/-- The owner starts empty and unlocked. No consumed pair can occur twice in any finite prefix of its unbounded service. -/
theorem owner_empty_unique (actions : List OwnerAction) :
    (ownerRun actions ⟨[], none⟩).consumed.Nodup :=
  (owner_run_unique actions ⟨[], none⟩ (by simp [LeaseFresh]) (by simp)).2

/-- Each actual atomic source-set transition has a concrete idle-to-idle owner trace. The cryptographic prefix and optional return are supplied by `accept_consumed`; this equation concerns only their consumed-set projection. -/
theorem admission_owner_trace (before after : List Pqxdh.Bytes) (step : AdmissionStep before after) :
    ∃ actions, ownerRun actions ⟨before, none⟩ = ⟨after, none⟩ := by
  rcases step with rfl | ⟨rid, fresh, rfl⟩
  · exact ⟨[.abort], rfl⟩
  · exact ⟨[.enter rid, .commit], by simp [ownerRun, ownerStep, fresh]⟩

/-- Concatenating private owner transitions preserves their exact chronological state effect. -/
theorem owner_run_append (first second : List OwnerAction) (state : Owner) :
    ownerRun (first ++ second) state = ownerRun second (ownerRun first state) := by
  simp only [ownerRun, List.foldl_append]

/-- Every complete adaptive source execution has an owner trace with precisely the same consumed-set endpoints. This is a projection of actual source support, not an assumption about origin tables. -/
theorem program_owner_trace {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (program : OracleComp ServerAuthSpec α) (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run state)) :
    ∃ actions, ownerRun actions ⟨state.server.consumed, none⟩ = ⟨result.2.server.consumed, none⟩ := by
  apply run_rel _ (fun before after => ∃ actions,
    ownerRun actions ⟨before.server.consumed, none⟩ = ⟨after.server.consumed, none⟩)
    (fun _ => ⟨[], rfl⟩) ?_ ?_ program state result supported
  · intro before middle after first second
    obtain ⟨firstActions, firstSame⟩ := first
    obtain ⟨secondActions, secondSame⟩ := second
    exact ⟨firstActions ++ secondActions, by rw [owner_run_append, firstSame, secondSame]⟩
  · intro query before after member
    exact admission_owner_trace _ _
      (handler_admission setup codec checks publicValue beaconSeed query before after member)

/-- Only attempted accept calls can increase the set; every such attempt adds at most one entry, including unsuccessful calls. -/
theorem handler_consumed_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (query : ServerAuthSpec.Domain) (state : GameState KemSK)
    (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    result.2.server.consumed.length ≤ state.server.consumed.length + if IsAcceptQuery query then 1 else 0 := by
  by_cases accept : IsAcceptQuery query
  · simp only [accept, ite_true]
    rcases handler_admission setup codec checks publicValue beaconSeed query state result supported with
      same | ⟨rid, _, same⟩
    · simp [same]
    · simp [same]
  · rw [handler_consumed_quiet setup codec checks publicValue beaconSeed query accept state result supported]
    simp [accept]

/-- The actual adaptive source appends at most the all-attempt acceptance budget. Primitive callbacks and failed calls retain their existing separate source bills. -/
theorem program_consumed_count {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (program : OracleComp ServerAuthSpec α) (qAccept : Nat)
    (bounded : program.IsQueryBoundP IsAcceptQuery qAccept)
    (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run state)) :
    result.2.server.consumed.length ≤ state.server.consumed.length + qAccept := by
  exact run_count _ IsAcceptQuery (fun current => current.server.consumed.length)
    (handler_consumed_count setup codec checks publicValue beaconSeed) program qAccept bounded state result supported

/-- The complete native experiment, in actual constructor order, supplies an empty-owner trace for its consumed-set projection. Original sampling, replies and every private state remain in the supported source execution. -/
theorem source_ordered_owner (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthNative.sourceOrderedState setup codec checks revealSeed adversary)) :
    ∃ actions, ownerRun actions ⟨[], none⟩ = ⟨result.2.2.1.server.consumed, none⟩ := by
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
  exact program_owner_trace setup codec checks (challenge setup.joint setup.dh seed scalar)
    beaconSeed _ _ (final.1, final.2.2) original

/-- The complete native experiment consumes at most the adversary's all-attempt acceptance cap. No bound on successful responses, honest identities or local primitive work is substituted for that cap. -/
theorem source_ordered_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (revealSeed : Bool) (adversary : Adversary) (qAccept : Nat)
    (bounded : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery qAccept)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (PqxdhServerAuthNative.sourceOrderedState setup codec checks revealSeed adversary)) :
    result.2.2.1.server.consumed.length ≤ qAccept := by
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
  simpa only [initialGameState, List.length_nil, Nat.zero_add] using
    program_consumed_count setup codec checks (challenge setup.joint setup.dh seed scalar)
      beaconSeed _ qAccept (bounded _) _ (final.1, final.2.2) original

end BeaconcryptCore.Computational.PqxdhRegistrationAdmission

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.state_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.state_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.lifted_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.lifted_state

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.prefix_step_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.prefix_step_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.prefix_program_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.prefix_program_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.collect_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.collect_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.collect_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.collect_verified

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.prefix_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.prefix_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.client_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.client_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.pending_registration_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.pending_registration_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.accept_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.accept_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.build_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.build_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.finish_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.finish_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.handler_consumed_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.handler_consumed_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.handler_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.handler_admission

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.admission_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.admission_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.program_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.program_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.accepted_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.accepted_id

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.no_reacceptance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.no_reacceptance

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.native_accept_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.native_accept_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.source_ordered_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.source_ordered_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.registration_width' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.registration_width

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.registration_eq_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.registration_eq_iff

-- The UInt8 order instance used by ownerStep's membership test in Lean 4.35 contains a Classical.propDecidable proof, which also reaches Quot.sound through classical excluded middle. These six unchanged statements inherit all three standard logical axioms through ownerStep or ownerRun.
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_step_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_step_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_step_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_step_admission

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_run_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_run_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_empty_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_empty_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.admission_owner_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.admission_owner_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_run_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.owner_run_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.program_owner_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.program_owner_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.handler_consumed_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.handler_consumed_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.program_consumed_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.program_consumed_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.source_ordered_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.source_ordered_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationAdmission.source_ordered_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationAdmission.source_ordered_count
