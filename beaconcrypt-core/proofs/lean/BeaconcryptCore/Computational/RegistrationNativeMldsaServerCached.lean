-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitFinal
import BeaconcryptCore.Computational.RegistrationNativeWorldCache

/-! Actual Server agreement, first-record, signing/publication and moved-handle callbacks preserve validity of the chronological global ML signing receipts in their single current CTX cache. Source hash-before-sign ordering supplies every new receipt; signature and publication success are never assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationWorldAgreement (State)
variable {n : Nat} {ι KemSK Auxiliary Value Next Reader Response Encoded : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationServerNativeSource.authenticate RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin
  RegistrationWorldAuthentication.program RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

def Valid (before : State n Auxiliary) : Prop := RegistrationSigningShared.Cached (RegistrationWorldSigning.project before.world)
private def Keeps (work : StateT (State n Auxiliary) ProbComp Value) : Prop :=
  ∀ before, Valid before → ∀ result, result ∈ support (work.run before) → Valid result.2

private theorem pure_keeps (value : Value) : Keeps (pure value : StateT (State n Auxiliary) ProbComp Value) := by
  intro before valid result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact valid
private theorem bind_keeps (work : StateT (State n Auxiliary) ProbComp Value)
    (next : Value → StateT (State n Auxiliary) ProbComp Next) (first : Keeps work)
    (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
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
    (query : RegistrationRecordPrimitives.Spec.Domain) : Keeps (RegistrationWorldRecords.handler (n := n) (Auxiliary := Auxiliary) setup codec query) := by
  intro before valid result supported
  simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  obtain ⟨cached, receipts⟩ := shared_program_facts setup codec (RegistrationRecordPrimitives.callbacks setup.source query) before inner possible
  change RegistrationSigningShared.Cached (inner.2.world.2, inner.2.world.1.primitive.2)
  rw [receipts]
  exact RegistrationSigningShared.cached_extend before.world.2 _ _ cached valid

private theorem records_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) :
    Keeps (simulateQ (RegistrationWorldRecords.handler (n := n) (Auxiliary := Auxiliary) setup codec) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (records_query_keeps setup codec query) ih

private theorem capability_keeps (query : PqxdhRecordLiftInterface.Capability n) :
    Keeps (RegistrationWorldServerCompletion.capability (Auxiliary := Auxiliary) query) := by
  intro before valid result supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact RegistrationSigningShared.cached_extend before.world.2 _ _
    (RegistrationWorldCache.effects_cache (.inr query) before.world.1 inner possible) valid

/-- The AD transcript hash extends the shared cache without changing any earlier Server signing receipt. -/
theorem adHash (pending : registration.ServerAdHash) :
    Keeps (RegistrationWorldServerCompletion.adHash (n := n) (Auxiliary := Auxiliary) pending) := by
  unfold RegistrationWorldServerCompletion.adHash
  cases pending.request with
  | fail error | div => exact pure_keeps _
  | ok request =>
      apply bind_keeps _ _ (capability_keeps _)
      intro digest
      exact pure_keeps _

/-- Actual response hashing and every attempted signature retain a valid chronological receipt before any writer can fail. -/
theorem signing (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    ∀ (before : State n Auxiliary), Valid before → ∀ result,
      result ∈ support ((RegistrationWorldServerCompletion.signing sign encode pending).run before) → Valid result.2 := by
  intro before valid result supported
  simp only [RegistrationWorldServerCompletion.signing, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact RegistrationWorldServerPublication.world_cached sign encode pending before.world valid inner possible

private theorem install_keeps (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    Keeps (RegistrationWorldServerCompletion.install (n := n) (Auxiliary := Auxiliary) control published) := by
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

/-- Native publication and peer insertion retain the new signing receipt through success and failure. -/
theorem publish (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    ∀ (before : State n Auxiliary), Valid before → ∀ result,
      result ∈ support ((RegistrationWorldServerCompletion.publish sign encode control pending).run before) → Valid result.2 := by
  have law : Keeps (RegistrationWorldServerCompletion.publish sign encode control pending : StateT (State n Auxiliary) ProbComp _) := by
    unfold RegistrationWorldServerCompletion.publish
    apply bind_keeps _ _ (signing sign encode pending)
    intro result
    cases result with
    | fail error | div => exact pure_keeps _
    | ok outcome => cases outcome with
      | Err previous => exact pure_keeps _
      | Ok published => exact install_keeps control published
  exact law

/-- The actual first-record controller and response publication preserve all earlier and newly attempted ML receipts. -/
theorem fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    ∀ (before : State n Auxiliary), Valid before → ∀ result,
      result ∈ support ((RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending).run before) → Valid result.2 := by
  have law : Keeps (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending : StateT (State n Auxiliary) ProbComp _) := by
    unfold RegistrationWorldServerCompletion.fromInitial
    apply bind_keeps _ _ (records_keeps setup codec _)
    intro record
    cases record with
    | fail error | div => exact pure_keeps _
    | ok outcome => cases outcome with
      | Err previous => exact pure_keeps _
      | Ok hashed => exact publish sign encode control hashed
  exact law

def FrontValid (before : RegistrationServerFrontendCompiler.State n) : Prop :=
  RegistrationSigningShared.Cached (RegistrationNativeInitFinal.summary before)
private def FrontKeeps (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) : Prop :=
  ∀ before, FrontValid before → ∀ result, result ∈ support (work.run before) → FrontValid result.2

private theorem front_pure (value : Value) : FrontKeeps (pure value : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) := by
  intro before valid result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact valid
private theorem front_bind (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (next : Value → StateT (RegistrationServerFrontendCompiler.State n) ProbComp Next)
    (first : FrontKeeps work) (rest : ∀ value, FrontKeeps (next value)) : FrontKeeps (work >>= next) := by
  intro before valid result supported
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1 middle.2 (first before valid middle reached) result continued

private theorem front_world (work : StateT (RegistrationServerRootCompiler.Local n) ProbComp Value)
    (keeps : Keeps work) : FrontKeeps (RegistrationServerSdkSource.world work) := by
  intro before valid result supported
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact keeps before.world valid inner possible

private theorem front_commit (published : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)) :
    FrontKeeps (RegistrationServerSdkSource.commit (n := n) published) := by
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
    FrontKeeps (RegistrationServerSdkSource.fromInitial (n := n) setup codec sign encode control pending) := by
  unfold RegistrationServerSdkSource.fromInitial
  exact front_bind _ _ (front_world _ (fromInitial setup codec sign encode control pending)) front_commit

private theorem afterOccupancy (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    FrontKeeps (RegistrationServerSdkSource.afterOccupancy (n := n) setup codec checks sign encode control lookup occupied) := by
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
        apply front_bind _ _ (front_world _ (adHash pending))
        intro hashed
        cases hashed with
        | fail error | div => exact front_pure _
        | ok result => cases result with
          | Err previous => exact front_pure _
          | Ok initial =>
              dsimp only
              split
              · exact sdk_fromInitial setup codec sign encode control initial
              · exact front_pure _

private theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice Std.U8) :
    FrontKeeps (RegistrationServerSdkSource.complete (n := n) setup codec checks sign encode token application) := by
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

/-- Every moved-handle SDK build retains valid global ML hash receipts, through raw cancellation, signing/encoding and installation failure. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice Std.U8)) :
    ∀ (before : RegistrationServerFrontendCompiler.State n), FrontValid before → ∀ result,
      result ∈ support ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before) → FrontValid result.2 := by
  intro before valid result supported
  simp only [RegistrationServerSdkSource.build, StateT.run] at supported
  have unchanged := take_world handle before
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk token current =>
      rw [taken] at unchanged
      have currentValid : FrontValid current := by
        change RegistrationSigningShared.Cached (RegistrationWorldSigning.project current.world.world)
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

/-- Mandatory authentication and all actual post-authentication gates retain valid prior ML receipts. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) :
    ∀ (before : RegistrationServerFrontendCompiler.State n), FrontValid before → ∀ result,
      result ∈ support ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before) → FrontValid result.2 := by
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
  have current : FrontValid (RegistrationNativeInitAuthentication.withWorld before inner.2) :=
    RegistrationSigningShared.cached_extend before.world.world.2 _ _ extension valid
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
          change RegistrationSigningShared.Cached (RegistrationNativeInitFinal.summary result.2)
          rw [sameSummary]
          exact current
      | _ =>
          simp only [StateT.run, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued
          cases continued
          exact current

private theorem pin_valid (binding : pqxdh.ServerBinding) (publicKey : Std.Array Std.U8 1952#usize)
    (before : RegistrationWorldServerReplay.Global n Auxiliary) (valid : Valid before.2)
    (result : RustM (core.option.Option session.ServerAuthenticationPin) × RegistrationWorldServerReplay.Global n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerFrontend.initializePin binding publicKey).run before)) :
    Valid result.2.2 := by
  simp only [RegistrationWorldServerFrontend.initializePin, StateT.run,
    support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact valid

/-- Successful actual Server startup begins with a valid empty signing history and retains it through pure exact-pin selection. -/
theorem start (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (publicKey : Std.Array Std.U8 1952#usize) (auxiliary : Auxiliary)
    (before after : PqxdhRecordLiftWorld.State n)
    (native : RegistrationWorldServerFrontend.State n Auxiliary)
    (supported : (.ok (.Some native), after) ∈ support
      ((RegistrationWorldServerFrontend.start created publicKey auxiliary).run before)) :
    Valid native.global.2 := by
  simp only [RegistrationWorldServerFrontend.start, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨installed, _first, continued⟩ := supported
  obtain ⟨pinned, possible, returned⟩ := continued
  have emptyValid : Valid (⟨auxiliary, [], [], (installed.2, [])⟩ : State n Auxiliary) := by
    simp only [Valid, RegistrationWorldSigning.project, RegistrationSigningShared.Cached,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  have valid := pin_valid ⟨created.server.server.identity, created.server.server.metadata.sender⟩ publicKey
    (PqxdhJointDhExtractFamily.empty, ⟨auxiliary, [], [], (installed.2, [])⟩) emptyValid pinned possible
  simp only [support_pure, Set.mem_singleton_iff] at returned
  rcases pinned with ⟨reply, current⟩
  cases reply with
  | fail error | div => cases returned
  | ok option => cases option with
    | none => cases returned
    | some pin =>
        cases returned
        exact valid

end BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.signing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.publish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.fromInitial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.adHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached.adHash
