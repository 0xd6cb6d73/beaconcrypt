-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
import BeaconcryptCore.Computational.RegistrationNativeInitFinal

/-! Native token provenance is proved at the source table, before any later root or ratchet state can overwrite private inputs. Only actual accepted agreement output can add a token; completion only removes one. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTokenSource
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
attribute [local irreducible] RegistrationReplaySchedule.consume RegistrationWorldAuthentication.begin
  RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree RegistrationNativeExperiment.handler
variable {n : Nat} {ι KemSK Value Reader Response : Type} {base : OracleSpec ι}

def Present (token : peer.ConsumedRegistration) (before : State n) : Prop := some token ∈ before.sessions

def Born (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n)
    (token : peer.ConsumedRegistration) : Prop :=
  ∃ accepted afterAgreement history,
    (.ok (.ServerComplete accepted), afterAgreement) ∈ support
      ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before) ∧
    RegistrationReplaySchedule.consume accepted afterAgreement.consumed = .ok (.Some token, history)

private theorem pure_present (value : Value) (before : State n) (result : Value × State n)
    (supported : result ∈ support ((pure value : StateT (State n) ProbComp Value).run before))
    (token : peer.ConsumedRegistration) (present : Present token result.2) : Present token before := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact present

private theorem authenticate_sessions (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n) (result : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication) × State n)
    (supported : result ∈ support ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before)) :
    result.2.sessions = before.sessions := by
  rw [RegistrationNativeInitAuthentication.authenticate, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

private theorem agree_sessions (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n)
    (result : RustM agreement.AgreementEffect × State n)
    (supported : result ∈ support ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)) :
    result.2.sessions = before.sessions := by
  simp only [RegistrationServerNativeSource.agree, StateT.run, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

/-- A source retain either preserves an old token or inserts exactly the consumed agreement returned by replay insertion. -/
theorem retain (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (accepted : agreement.ServerAgreement)
    (before : State n) (result : RustM (Option Nat) × State n)
    (supported : result ∈ support ((RegistrationServerNativeSource.retain created accepted).run before))
    (token : peer.ConsumedRegistration) (present : Present token result.2) :
    Present token before ∨ ∃ history, RegistrationReplaySchedule.consume accepted before.consumed = .ok (.Some token, history) := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore,
    StateT.run] at supported
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div =>
      simp only [consumed, map_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl present
  | ok answer =>
      rcases answer with ⟨option, history⟩
      cases option with
      | none =>
          simp only [consumed, map_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact Or.inl present
      | some actual =>
          simp only [consumed, map_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          change some token ∈ before.sessions ++ [some actual] at present
          rcases List.mem_append.mp present with old | added
          · exact Or.inl old
          · have same : token = actual := Option.some.inj (List.mem_singleton.mp added)
            subst actual
            exact Or.inr ⟨history, rfl⟩

/-- A token present after the actual post-authentication continuation was already present or came from an actually supported agreement completion and replay consume. -/
theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n)
    (result : RustM (Option Nat) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run before))
    (token : peer.ConsumedRegistration) (present : Present token result.2) :
    Present token before ∨ Born setup checks representation created packet authenticated before token := by
  simp only [RegistrationServerSdkSource.afterAuthentication, StateT.run] at supported
  split_ifs at supported with replay reserved
  · exact Or.inl (pure_present _ before result supported token present)
  · rw [mem_support_bind_iff] at supported
    obtain ⟨completed, agreed, continued⟩ := supported
    rcases completed with ⟨effect, afterAgreement⟩
    have same : afterAgreement.sessions = before.sessions := agree_sessions setup checks representation created packet authenticated before (effect, afterAgreement) agreed
    change (effect, afterAgreement) ∈ support ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before) at agreed
    cases answer : effect with
    | fail error | div =>
        simp only [answer] at continued
        have old := pure_present _ afterAgreement result continued token present
        exact Or.inl (by simpa only [Present, same] using old)
    | ok effect => cases effect with
      | ServerComplete accepted =>
          simp only [answer] at continued
          rcases retain created accepted afterAgreement result continued token present with old | ⟨history, consumed⟩
          · exact Or.inl (by simpa only [Present, same] using old)
          · exact Or.inr ⟨accepted, afterAgreement, history, by simpa only [answer] using agreed, consumed⟩
      | _ =>
          simp only [answer] at continued
          have old := pure_present _ afterAgreement result continued token present
          exact Or.inl (by simpa only [Present, same] using old)
  · exact Or.inl (pure_present _ before result supported token present)

/-- Every actual SDK accept token has an actual mandatory authentication prefix and supported same-call agreement birth, or was already present. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n) (result : RustM (Option Nat) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before))
    (token : peer.ConsumedRegistration) (present : Present token result.2) :
    Present token before ∨ ∃ events authenticated afterAuthentication,
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before) ∧
      Born setup checks representation created packet authenticated afterAuthentication token := by
  rw [RegistrationServerSdkSource.accept, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨checked, queried, continued⟩ := supported
  rcases checked with ⟨reply, afterAuth⟩
  have same : afterAuth.sessions = before.sessions := authenticate_sessions setup codec route verify created packet before (reply, afterAuth) queried
  change (reply, afterAuth) ∈ support ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before) at queried
  cases responseEq : reply with
  | fail error | div =>
      simp only [responseEq] at continued
      have old := pure_present _ afterAuth result continued token present
      exact Or.inl (by simpa only [Present, same] using old)
  | ok checked =>
      rcases checked with ⟨events, authentication⟩
      cases authentication with
      | Accepted authenticated =>
          simp only [responseEq] at continued
          rcases afterAuthentication setup checks representation created packet authenticated afterAuth result continued token present with old | born
          · exact Or.inl (by simpa only [Present, same] using old)
          · exact Or.inr ⟨events, authenticated, afterAuth, by simpa only [responseEq] using queried, born⟩
      | _ =>
          simp only [responseEq] at continued
          have old := pure_present _ afterAuth result continued token present
          exact Or.inl (by simpa only [Present, same] using old)

private theorem world_sessions (work : StateT (RegistrationServerRootCompiler.Local n) ProbComp Value)
    (before : State n) (result : Value × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.world work).run before)) :
    result.2.sessions = before.sessions := by
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

private theorem commit_sessions (value : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes))
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.commit value).run before)) :
    result.2.sessions = before.sessions := by
  cases value with
  | fail error | div =>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | ok answer => cases answer <;>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported <;>
      cases supported <;> rfl

private theorem fromInitial_sessions (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf)
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.fromInitial setup codec sign encode control pending).run before)) :
    result.2.sessions = before.sessions := by
  rw [RegistrationServerSdkSource.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  exact (commit_sessions middle.1 middle.2 result continued).trans (world_sessions _ before middle queried)

private theorem afterOccupancy_sessions (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool)
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied).run before)) :
    result.2.sessions = before.sessions := by
  unfold RegistrationServerSdkSource.afterOccupancy at supported
  cases resumed : lookup.resume occupied with
  | fail error | div =>
      simp only [resumed, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | ok answer => cases answer with
    | Err previous =>
        simp only [resumed, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        rfl
    | Ok pending =>
        simp only [resumed, StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨hashed, queried, continued⟩ := supported
        rcases hashed with ⟨reply, afterHash⟩
        have same : afterHash.sessions = before.sessions := world_sessions _ before (reply, afterHash) queried
        cases replyEq : reply with
        | fail error | div =>
            simp only [replyEq, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
            cases continued
            exact same
        | ok answer => cases answer with
          | Err previous =>
              simp only [replyEq, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
              cases continued
              exact same
          | Ok initial =>
              simp only [replyEq] at continued
              split_ifs at continued with reserved
              · exact (fromInitial_sessions setup codec sign encode control initial afterHash result continued).trans same
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
                cases continued
                exact same

/-- Native completion retains exactly the already-moved token table through all later gates and publication outcomes. -/
theorem complete_sessions (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) (before : State n)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.complete setup codec checks sign encode token application).run before)) :
    result.2.sessions = before.sessions := by
  simp only [RegistrationServerSdkSource.complete, StateT.run] at supported
  cases looked : peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div =>
      simp only [looked, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | ok answer => cases answer with
    | Err previous =>
        simp only [looked, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        rfl
    | Ok lookup =>
        simp only [looked] at supported
        cases requested : lookup.request with
        | fail error | div =>
            simp only [requested, support_pure, Set.mem_singleton_iff] at supported
            cases supported
            rfl
        | ok keyId =>
            simp only [requested] at supported
            split_ifs at supported with admitted
            · rw [mem_support_bind_iff] at supported
              obtain ⟨occupied, queried, continued⟩ := supported
              exact (afterOccupancy_sessions setup codec checks sign encode before.control lookup occupied.1 occupied.2 result continued).trans
                (world_sessions _ before occupied queried)
            · simp only [support_pure, Set.mem_singleton_iff] at supported
              cases supported
              rfl

/-- Taking a token can only remove a table entry; any surviving live token was already in the original table. -/
theorem take_present (handle : Nat) (before : State n) (token : peer.ConsumedRegistration)
    (present : Present token (RegistrationServerSdkSource.take handle before).2) : Present token before := by
  unfold RegistrationServerSdkSource.take at present
  cases found : before.sessions[handle]? with
  | none => simpa only [found, Present] using present
  | some entry => cases entry with
    | none => simpa only [found, Present] using present
    | some moved =>
        simp only [found, Present] at present
        have origin := List.mem_or_eq_of_mem_set present
        rcases origin with old | same
        · exact old
        · cases same

/-- Actual build never creates a token, including cancellation and every later failure. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) (before : State n)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before))
    (token : peer.ConsumedRegistration) (present : Present token result.2) : Present token before := by
  simp only [RegistrationServerSdkSource.build, StateT.run] at supported
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk option current =>
      have same : (RegistrationServerSdkSource.take handle before).2 = current := congrArg Prod.snd taken
      simp only [taken] at supported
      apply take_present handle before token
      rw [same]
      cases option with
      | none => exact pure_present _ current result supported token present
      | some moved => cases application with
        | none => exact pure_present _ current result supported token present
        | some application =>
            have unchanged := complete_sessions setup codec checks sign encode moved application current result supported
            simpa only [Present, unchanged] using present

/-- A successful native replay consume carries exactly its actual completed agreement. -/
theorem consume_agreement (accepted : agreement.ServerAgreement) (before after : RegistrationReplaySchedule.State)
    (token : peer.ConsumedRegistration)
    (consumed : RegistrationReplaySchedule.consume accepted before = .ok (.Some token, after)) :
    token.agreement = accepted := by
  cases found : before.contains (PqxdhRefinement.absBytes accepted.pending.registration_id.bytes) with
  | false =>
      rw [RegistrationReplaySchedule.consume_fresh accepted before found] at consumed
      cases consumed
      rfl
  | true =>
      rw [RegistrationReplaySchedule.consume_replayed accepted before found] at consumed
      cases consumed

/-- A moved token is literally a live entry in the source table before take. -/
theorem take_origin (handle : Nat) (before current : State n) (token : peer.ConsumedRegistration)
    (taken : RegistrationServerSdkSource.take handle before = (some token, current)) :
    before.sessions[handle]? = some (some token) ∧ current.sessions = before.sessions.set handle none := by
  unfold RegistrationServerSdkSource.take at taken
  cases found : before.sessions[handle]? with
  | none => simp only [found] at taken; cases taken
  | some entry => cases entry with
    | none => simp only [found] at taken; cases taken
    | some moved =>
        simp only [found, Prod.mk.injEq, Option.some.injEq] at taken
        rcases taken with ⟨same, currentEq⟩
        subst moved
        subst current
        exact ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeTokenSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenSource.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenSource.retain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenSource.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenSource.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenSource.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenSource.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenSource.complete_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenSource.complete_sessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenSource.take_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenSource.take_present

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenSource.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenSource.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenSource.consume_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenSource.consume_agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenSource.take_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenSource.take_origin
