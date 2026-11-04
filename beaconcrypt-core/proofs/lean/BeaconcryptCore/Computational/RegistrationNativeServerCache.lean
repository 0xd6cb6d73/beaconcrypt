-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached

/-! The actual complete native Server callbacks retain every earlier shared CTX cache entry. The proof carries an arbitrary fixed earlier cache through real authentication, root agreement, first-record signing, failure and moved-handle publication paths. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerCache
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationWorldAgreement (State)
variable {n : Nat} {ι KemSK Auxiliary Value Next Reader Response Encoded : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationServerNativeSource.authenticate RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin
  RegistrationWorldAuthentication.program RegistrationAuthenticationExecutor.execute registration.begin_init_authentication
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

variable {anchor : CtxRomAuth.CtxRO.QueryCache}

private def Valid (before : State n Auxiliary) : Prop := anchor ≤ before.world.1.primitive.2
private def Keeps (work : StateT (State n Auxiliary) ProbComp Value) : Prop :=
  ∀ before, Valid (anchor := anchor) before → ∀ result, result ∈ support (work.run before) → Valid (anchor := anchor) result.2

private theorem pure_keeps (value : Value) : Keeps (anchor := anchor) (pure value : StateT (State n Auxiliary) ProbComp Value) := by
  intro before valid result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact valid
private theorem bind_keeps (work : StateT (State n Auxiliary) ProbComp Value)
    (next : Value → StateT (State n Auxiliary) ProbComp Next) (first : Keeps (anchor := anchor) work)
    (rest : ∀ value, Keeps (anchor := anchor) (next value)) : Keeps (anchor := anchor) (work >>= next) := by
  intro before valid result supported
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1 middle.2 (first before valid middle reached) result continued

private theorem shared_facts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : State n Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.shared setup codec query).run before)) :
    before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 ∧ result.2.world.2 = before.world.2 := by
  cases query with
  | inl query =>
      simp only [RegistrationWorldRecords.shared, StateT.run, support_map] at supported
      obtain ⟨inner, possible, same⟩ := supported
      cases same
      exact ⟨RegistrationWorldCache.effects_cache _ before.world.1 inner possible, rfl⟩
  | inr query =>
      simp only [RegistrationWorldRecords.shared, RegistrationWorldRecords.record, StateT.run, support_map] at supported
      obtain ⟨inner, possible, same⟩ := supported
      cases same
      exact ⟨RegistrationWorldCache.primitive_cache setup codec query before.world.1.primitive inner possible, rfl⟩

private theorem shared_program_facts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp MldsaSharedNative.Spec Value) (before : State n Auxiliary)
    (result : Value × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldRecords.shared setup codec) work).run before)) :
    before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 ∧ result.2.world.2 = before.world.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨le_refl _, rfl⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      obtain ⟨cached, receipts⟩ := shared_facts setup codec query before middle reached
      obtain ⟨laterCache, laterReceipts⟩ := ih middle.1 middle.2 result continued
      exact ⟨cached.trans laterCache, laterReceipts.trans receipts⟩

private theorem records_query_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) : Keeps (anchor := anchor) (RegistrationWorldRecords.handler (n := n) (Auxiliary := Auxiliary) setup codec query) := by
  intro before valid result supported
  simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  obtain ⟨cached, _receipts⟩ := shared_program_facts setup codec (RegistrationRecordPrimitives.callbacks setup.source query) before inner possible
  exact valid.trans cached

private theorem records_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) :
    Keeps (anchor := anchor) (simulateQ (RegistrationWorldRecords.handler (n := n) (Auxiliary := Auxiliary) setup codec) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (records_query_keeps setup codec query) ih

private theorem capability_keeps (query : PqxdhRecordLiftInterface.Capability n) :
    Keeps (anchor := anchor) (RegistrationWorldServerCompletion.capability (Auxiliary := Auxiliary) query) := by
  intro before valid result supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact valid.trans (RegistrationWorldCache.effects_cache (.inr query) before.world.1 inner possible)

private theorem signing_query_cache
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldSigning.State n)
    (result : RegistrationSigningShared.Spec.Range query × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((RegistrationWorldSigning.outgoing sign query).run before)) :
    before.1.primitive.2 ≤ result.2.1.primitive.2 := by
  cases query with
  | hash request =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at supported
      obtain ⟨inner, reached, same⟩ := supported
      cases same
      exact RegistrationWorldCache.effects_cache _ before.1 inner reached
  | sign request payload digest =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at supported
      obtain ⟨inner, reached, same⟩ := supported
      cases same
      exact (RegistrationWorldCache.sampled_cache (sign request) before.1 inner reached).ge

private theorem signing_program_cache {Output : Type}
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Output) (before : RegistrationWorldSigning.State n)
    (result : Output × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((simulateQ (RegistrationWorldSigning.outgoing sign) work).run before)) :
    before.1.primitive.2 ≤ result.2.1.primitive.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact (signing_query_cache sign query before middle queried).trans (ih middle.1 middle.2 result continued)

/-- Actual response hashing and every attempted signature extend the arbitrary earlier cache before any writer can fail. -/
private theorem signing (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    ∀ (before : State n Auxiliary), Valid (anchor := anchor) before → ∀ result,
      result ∈ support ((RegistrationWorldServerCompletion.signing sign encode pending).run before) → Valid (anchor := anchor) result.2 := by
  intro before valid result supported
  simp only [RegistrationWorldServerCompletion.signing, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact valid.trans (signing_program_cache sign (RegistrationWorldServerPublication.program encode pending) before.world inner possible)

private theorem install_keeps (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    Keeps (anchor := anchor) (RegistrationWorldServerCompletion.install (n := n) (Auxiliary := Auxiliary) control published) := by
  cases moved : peer.begin_peer_insert control published with
  | fail error | div =>
      unfold RegistrationWorldServerCompletion.install
      rw [moved]
      exact pure_keeps _
  | ok result => cases result with
    | Err previous =>
        unfold RegistrationWorldServerCompletion.install
        rw [moved]
        exact pure_keeps _
    | Ok pending =>
        rw [RegistrationWorldServerCompletion.install_native control published pending moved]
        exact bind_keeps _ _ (capability_keeps _) (fun _ => pure_keeps _)

/-- Native publication and peer insertion preserve the arbitrary earlier cache through success and failure. -/
private theorem publish (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    ∀ (before : State n Auxiliary), Valid (anchor := anchor) before → ∀ result,
      result ∈ support ((RegistrationWorldServerCompletion.publish sign encode control pending).run before) → Valid (anchor := anchor) result.2 := by
  have law : Keeps (anchor := anchor) (RegistrationWorldServerCompletion.publish sign encode control pending : StateT (State n Auxiliary) ProbComp _) := by
    unfold RegistrationWorldServerCompletion.publish
    apply bind_keeps _ _ (signing sign encode pending)
    intro result
    cases result with
    | fail error | div => exact pure_keeps _
    | ok outcome => cases outcome with
      | Err previous => exact pure_keeps _
      | Ok published => exact install_keeps control published
  exact law

/-- The actual first-record controller and response publication preserve the arbitrary earlier cache. -/
private theorem fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    ∀ (before : State n Auxiliary), Valid (anchor := anchor) before → ∀ result,
      result ∈ support ((RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending).run before) → Valid (anchor := anchor) result.2 := by
  have law : Keeps (anchor := anchor) (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending : StateT (State n Auxiliary) ProbComp _) := by
    unfold RegistrationWorldServerCompletion.fromInitial
    apply bind_keeps _ _ (records_keeps setup codec _)
    intro record
    cases record with
    | fail error | div => exact pure_keeps _
    | ok outcome => cases outcome with
      | Err previous => exact pure_keeps _
      | Ok hashed => exact publish sign encode control hashed
  exact law

private def FrontValid (before : RegistrationServerFrontendCompiler.State n) : Prop :=
  anchor ≤ before.world.world.1.primitive.2
private def FrontKeeps (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) : Prop :=
  ∀ before, FrontValid (anchor := anchor) before → ∀ result, result ∈ support (work.run before) → FrontValid (anchor := anchor) result.2

private theorem front_pure (value : Value) : FrontKeeps (anchor := anchor) (pure value : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) := by
  intro before valid result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact valid
private theorem front_bind (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (next : Value → StateT (RegistrationServerFrontendCompiler.State n) ProbComp Next)
    (first : FrontKeeps (anchor := anchor) work) (rest : ∀ value, FrontKeeps (anchor := anchor) (next value)) : FrontKeeps (anchor := anchor) (work >>= next) := by
  intro before valid result supported
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1 middle.2 (first before valid middle reached) result continued

private theorem front_world (work : StateT (RegistrationServerRootCompiler.Local n) ProbComp Value)
    (keeps : Keeps (anchor := anchor) work) : FrontKeeps (anchor := anchor) (RegistrationServerSdkSource.world work) := by
  intro before valid result supported
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact keeps before.world valid inner possible

private theorem front_commit (published : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)) :
    FrontKeeps (anchor := anchor) (RegistrationServerSdkSource.commit (n := n) published) := by
  intro before valid result supported
  cases published with
  | fail error | div =>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact valid
  | ok outcome => cases outcome <;>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported <;>
      cases supported <;> exact valid

private theorem sdk_fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    FrontKeeps (anchor := anchor) (RegistrationServerSdkSource.fromInitial (n := n) setup codec sign encode control pending) := by
  unfold RegistrationServerSdkSource.fromInitial
  exact front_bind _ _ (front_world _ (fromInitial setup codec sign encode control pending)) front_commit

private theorem afterOccupancy (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    FrontKeeps (anchor := anchor) (RegistrationServerSdkSource.afterOccupancy (n := n) setup codec checks sign encode control lookup occupied) := by
  unfold RegistrationServerSdkSource.afterOccupancy
  cases resumed : lookup.resume occupied with
  | fail error | div =>
      dsimp only
      exact front_pure _
  | ok outcome => cases outcome with
    | Err previous =>
        dsimp only
        exact front_pure _
    | Ok pending =>
        dsimp only
        split
        · exact sdk_fromInitial setup codec sign encode control pending
        · exact front_pure _

private theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice Std.U8) :
    FrontKeeps (anchor := anchor) (RegistrationServerSdkSource.complete (n := n) setup codec checks sign encode token application) := by
  intro before valid result supported
  simp only [RegistrationServerSdkSource.complete, StateT.run] at supported
  cases looked : peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div =>
      simp only [looked, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact valid
  | ok outcome => cases outcome with
    | Err previous =>
        simp only [looked, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact valid
    | Ok lookup =>
        simp only [looked] at supported
        cases requested : lookup.request with
        | fail error | div =>
            simp only [requested, support_pure, Set.mem_singleton_iff] at supported
            cases supported
            exact valid
        | ok keyId =>
            simp only [requested] at supported
            split_ifs at supported with admitted
            · simp only [mem_support_bind_iff] at supported
              obtain ⟨occupied, first, continued⟩ := supported
              have current := front_world _ (capability_keeps (.peerPresent keyId)) before valid occupied first
              exact afterOccupancy setup codec checks sign encode before.control lookup occupied.1 occupied.2 current result continued
            · simp only [support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact valid

private theorem take_world (handle : Nat) (before : RegistrationServerFrontendCompiler.State n) :
    (RegistrationServerSdkSource.take handle before).2.world = before.world := by
  cases found : before.sessions[handle]? with
  | none => simp only [RegistrationServerSdkSource.take, found]
  | some option => cases option <;> simp only [RegistrationServerSdkSource.take, found]

/-- Every moved-handle SDK build retains the arbitrary earlier cache through raw cancellation, signing/encoding and installation failure. -/
private theorem build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice Std.U8)) :
    ∀ (before : RegistrationServerFrontendCompiler.State n), FrontValid (anchor := anchor) before → ∀ result,
      result ∈ support ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before) → FrontValid (anchor := anchor) result.2 := by
  intro before valid result supported
  simp only [RegistrationServerSdkSource.build, StateT.run] at supported
  have unchanged := take_world handle before
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk token current =>
      rw [taken] at unchanged
      have currentValid : FrontValid (anchor := anchor) current := by
        change anchor ≤ current.world.world.1.primitive.2
        rw [unchanged]
        exact valid
      cases token with
      | none =>
          simp only [taken, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact currentValid
      | some token =>
          simp only [taken] at supported
          cases application with
          | none =>
              simp only [support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact currentValid
          | some application => exact complete setup codec checks sign encode token application current currentValid result supported

/-- Mandatory authentication and all actual post-authentication gates retain the arbitrary earlier cache. -/
private theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    ∀ (before : RegistrationServerFrontendCompiler.State n), FrontValid (anchor := anchor) before → ∀ result,
      result ∈ support ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before) → FrontValid (anchor := anchor) result.2 := by
  intro before valid result supported
  simp only [RegistrationServerSdkSource.accept, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨checked, first, continued⟩ := supported
  rw [RegistrationNativeInitAuthentication.authenticate setup codec route verify created packet before, support_map] at first
  obtain ⟨inner, possible, same⟩ := first
  cases same
  simp only [RegistrationWorldAuthentication.begin] at possible
  have extension : before.world.world.1.primitive.2 ≤ inner.2.primitive.2 :=
    RegistrationWorldCache.program_cache
    (Result := RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) setup codec route
    (RegistrationWorldAuthentication.program setup.source.crypto verify before.pin packet)
    before.world.world.1 inner possible
  have current : FrontValid (anchor := anchor) (RegistrationNativeInitAuthentication.withWorld before inner.2) :=
    valid.trans extension
  rcases inner with ⟨reply, middle⟩
  dsimp only [Prod.map, id] at continued
  cases reply with
  | fail error | div =>
      simp only [StateT.run, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact current
  | ok reply =>
      rcases reply with ⟨events, authentication⟩
      cases authentication with
      | Accepted authenticated =>
          have sameSummary := RegistrationNativeInitFinal.afterAuthentication setup checks representation created packet authenticated
            (RegistrationNativeInitAuthentication.withWorld before middle) result continued
          change anchor ≤ (RegistrationNativeInitFinal.summary result.2).2
          rw [sameSummary]
          exact current
      | _ =>
          simp only [StateT.run, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued
          cases continued
          exact current

/-- Complete actual SDK builds retain every earlier shared cache entry on all supported outcomes, including failed publication. -/
theorem build_cache (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice Std.U8)) (before : RegistrationServerFrontendCompiler.State n)
    (result : RustM (Option (Std.U64 × Pqxdh.Bytes)) × RegistrationServerFrontendCompiler.State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before)) :
    before.world.world.1.primitive.2 ≤ result.2.world.world.1.primitive.2 :=
  build (anchor := before.world.world.1.primitive.2) setup codec checks sign encode handle application before (le_refl _) result supported

/-- Mandatory native authentication and the complete source agreement/replay path extend that same actual cache. -/
theorem accept_cache (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before : RegistrationServerFrontendCompiler.State n)
    (result : RustM (Option Nat) × RegistrationServerFrontendCompiler.State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before)) :
    before.world.world.1.primitive.2 ≤ result.2.world.world.1.primitive.2 :=
  accept (anchor := before.world.world.1.primitive.2) setup codec checks route verify representation created packet before (le_refl _) result supported

end BeaconcryptCore.Computational.RegistrationNativeServerCache
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerCache.build_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerCache.build_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerCache.accept_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerCache.accept_cache
