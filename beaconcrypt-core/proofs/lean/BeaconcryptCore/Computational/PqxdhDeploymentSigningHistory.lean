-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentProvenance

/-! The `NoBundleFailure` signing-history lemma of the common deployment experiment (CE-7). The experiment's transcript lives in the ledger of the compiled program, and the owners' chronological signing history lives in the private identity pool of the annotated initialized source execution; neither the deployment game nor the compile lemma relates the two. This module relates them along the stacked execution of the secrecy layer, the compiler and the annotated Server schedule (`execution`), query by query, with the invariant `Signed`: the public-transcript invariant `Agree` of `PqxdhDeploymentEligibility` for the projected native state, slot ownership, distinct owner identity indices, empty signing histories beyond the created seeds, nothing recorded for uncreated owners, and, for every owner whose bundle calls made in Fresh never failed, the history `History`: while publicly Fresh it has published nothing and signed nothing, and afterwards its first published bundle is the Phase 1 writer output of the candidate it signed with its own identity key over one key tuple, and its signing history is exactly the three messages of that tuple. Registration commands are forwarded unchanged by the compiler; a bundle signs only at its own owner's index and only in Fresh (`trace_cases`), a create appends an owner at a new index, a finish neither signs nor changes an identity, and every other source command, in particular the Server kernel reveals, established-kernel reads and BLAKE2b queries of the compiled record and secrecy commands, keeps the owner registry, the seeds and every signing history (`quiet_step`, `quiet_program`). `signed_source` establishes the invariant on every outcome of the annotated initialized execution of the compiled program from empty pools, and `signing_history` is the lemma the plan names: under `NoBundleFailureAt`, an owner's whole signing history is empty or the three messages of the one tuple of its published bundle. The statements are deterministic support facts; no codec law and no security assumption is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result : Type}

/-- The registration commands that act on the owner registry: create, bundle and finish. -/
def ownerCommand : (Spec KemSK).Domain → Bool
  | .inl (.inr (.create _ _)) => true
  | .inl (.inr (.bundle _)) => true
  | .inl (.inr (.finish _ _)) => true
  | _ => false

/-- A step keeps the owner registry, the private identity seeds, every signing history and the Server identity. -/
structure Kept (before after : PqxdhRegistrationJointSchedule.State KemSK) : Prop where
  owners : after.owners = before.owners
  seeds : after.pool.1.seeds = before.pool.1.seeds
  messages : ∀ index, messagesAt index after.pool.1.transcript = messagesAt index before.pool.1.transcript
  identity : after.shared.2.server.server.identity = before.shared.2.server.server.identity

theorem kept_refl (state : PqxdhRegistrationJointSchedule.State KemSK) : Kept state state :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

theorem kept_trans (first second third : PqxdhRegistrationJointSchedule.State KemSK) (left : Kept first second)
    (right : Kept second third) : Kept first third :=
  ⟨right.owners.trans left.owners, right.seeds.trans left.seeds, fun index => (right.messages index).trans
    (left.messages index), right.identity.trans left.identity⟩

/-- Recording an observation that is not a signature keeps every signing history. -/
theorem record_messages (query : PqxdhDynamicIdentityPool.DynamicSpec.Domain)
    (answer : PqxdhDynamicIdentityPool.DynamicSpec.Range query) (state : PqxdhDynamicIdentityPool.SourceState)
    (notSign : ∀ selected message, query ≠ .inr (.service selected (.sign message))) (index : Nat) :
    messagesAt index (PqxdhDynamicIdentityPool.record query answer state).transcript = messagesAt index state.transcript := by
  simp only [PqxdhDynamicIdentityPool.record, PqxdhRegistrationJointSigningTranscript.append]
  rcases query with coin | request
  · simp [messagesAt, PqxdhRegistrationJointSigningTranscript.messageAt]
  · cases request with
    | create => simp [messagesAt, PqxdhRegistrationJointSigningTranscript.messageAt]
    | reveal selected => simp [messagesAt, PqxdhRegistrationJointSigningTranscript.messageAt]
    | service selected request =>
        cases request with
        | sign message => exact absurd rfl (notSign selected message)
        | _ => simp [messagesAt, PqxdhRegistrationJointSigningTranscript.messageAt]

/-- The Server's raw-accept prefix records only static DH requests, so it keeps every signing history. -/
theorem accept_messages (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointFinish.State KemSK) (result : Option Nat × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex
      raw).run state)) (index : Nat) :
    messagesAt index result.2.1.1.transcript = messagesAt index state.1.1.transcript := by
  have prefixKept : ∀ (start : PqxdhRegistrationJointServerPrefix.State KemSK (List Pqxdh.Bytes)),
      ∀ reached ∈ support ((simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
        (serverAux setup codec checks)) (PqxdhServerRootPreparation.collect raw)).run start),
        messagesAt index reached.2.1.1.transcript = messagesAt index start.1.1.transcript := by
    intro start
    refine OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _
      (fun current => messagesAt index current.1.1.transcript = messagesAt index start.1.1.transcript) ?_ _ start rfl
    intro query current held reached member
    cases query with
    | staticDh input =>
        simp only [PqxdhRegistrationJointServerPrefix.annotated, PqxdhServerStaticDhSource.nativeImpl, StateT.run_bind,
          mem_support_bind_iff] at member
        obtain ⟨_, visited, rfl⟩ := member
        change _ ∈ support (pure _ : ProbComp _) at visited
        rw [support_pure, Set.mem_singleton_iff] at visited
        subst visited
        rw [← held]
        exact record_messages _ _ _ (by intro selected message; simp) index
    | _ =>
        rw [PqxdhDeploymentQuiet.onAux_pool _ current reached member]
        exact held
  simp only [PqxdhRegistrationJointServerAccept.source, PqxdhRegistrationJointServerAccept.run, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨_, afterGet⟩, getMember, ⟨collected, afterPrepare⟩, prepareMember, tailMember⟩ := supported
  simp only [PqxdhRegistrationJointFinish.onNative, StateT.run, support_map, Set.mem_image] at getMember tailMember
  obtain ⟨_, _, getEq⟩ := getMember
  obtain ⟨_, _, rfl⟩ := tailMember
  simp only [Prod.mk.injEq] at getEq
  obtain ⟨_, rfl⟩ := getEq
  simp only [PqxdhRegistrationJointServerAccept.sourcePrepare, StateT.run, support_map, Set.mem_image] at prepareMember
  obtain ⟨reached, reachedMember, same⟩ := prepareMember
  simp only [Prod.mk.injEq] at same
  obtain ⟨_, rfl⟩ := same
  exact prefixKept _ reached reachedMember

/-- A finish records only decapsulation and static DH requests, so it keeps every signing history. -/
theorem finish_messages (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex kemIndex : Nat)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state)) (index : Nat) :
    messagesAt index result.2.1.1.transcript = messagesAt index state.1.1.transcript := by
  refine OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _
    (fun current => messagesAt index current.1.1.transcript = messagesAt index state.1.1.transcript) ?_ _ state rfl
    result supported
  intro query current held reached member
  rcases query with query | query
  · simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onPool, StateT.run, support_map,
      Set.mem_image] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    cases query with
    | decapsulate ciphertext key =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_map, Set.mem_image] at innerMember
        obtain ⟨_, _, rfl⟩ := innerMember
        exact held
    | dhIdentity seed point =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        rw [← held]
        exact record_messages _ _ _ (by intro selected message; simp) index
    | _ =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_map, Set.mem_image] at innerMember
        obtain ⟨_, _, rfl⟩ := innerMember
        exact held
  · simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onNative, StateT.run, support_map,
      Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact held

/-- A current-field read keeps the owner registry, the seeds, every signing history and the Server identity: an identity read records only a reveal observation. -/
theorem read_kept (request : Nat × PqxdhRegistrationJointLiveRead.Field) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    Kept state (PqxdhRegistrationJointLiveRead.sourceStep request state).2 := by
  unfold PqxdhRegistrationJointLiveRead.sourceStep
  split
  · exact kept_refl state
  · rename_i entry _
    refine ⟨rfl, (PqxdhRegistrationJointLiveRead.entry_slots request.2 entry state.pool).1, fun index => ?_, rfl⟩
    cases field : request.2 with
    | identity =>
        simp only [PqxdhRegistrationJointLiveRead.entrySource]
        exact record_messages _ _ _ (by intro selected message; simp) index
    | kem =>
        simp only [PqxdhRegistrationJointLiveRead.entrySource]
        split <;> rfl
    | _ => simp only [PqxdhRegistrationJointLiveRead.entrySource]

/-- Every source command other than create, bundle and finish keeps the owner registry, the seeds, every signing history and the Server identity. -/
theorem quiet_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain) (notOwner : ownerCommand query = false)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (result : (Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      query).run state)) :
    Kept state result.2 := by
  have native : (result.1, PqxdhRegistrationJointSchedule.source result.2) ∈ support
      ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query).run
        (PqxdhRegistrationJointSchedule.source state)) := by
    rw [← PqxdhRegistrationJointServerSchedule.query_native, support_map]
    exact ⟨result, supported, rfl⟩
  have sharedKept : ∀ {Value : Type} (work : NativeGame KemSK Value)
      (reached : Value × PqxdhRegistrationJointSchedule.State KemSK),
      reached ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state) →
      PqxdhRegistrationJointSchedule.source reached.2 = { PqxdhRegistrationJointSchedule.source state with
        shared := reached.2.shared } ∧ reached.2.owners = state.owners ∧ reached.2.pool = state.pool := by
    intro Value work reached member
    simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨rfl, rfl, rfl⟩
  rcases query with (coin | request) | read
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      PqxdhRegistrationJointSchedule.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact kept_refl state
  · cases request with
    | create pin keyId => simp [ownerCommand] at notOwner
    | bundle address => simp [ownerCommand] at notOwner
    | finish address raw => simp [ownerCommand] at notOwner
    | accept raw =>
        have alike := PqxdhDeploymentEligibility.shared_alike setup codec checks seed (.accept raw) trivial _ _ native
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointServerSchedule.onBackend,
          StateT.run, support_map, Set.mem_image] at supported
        obtain ⟨accepted, acceptedMember, rfl⟩ := supported
        exact ⟨rfl, (PqxdhRegistrationJointServerAccept.source_slots setup codec checks seed identityIndex raw
          (state.pool, state.shared) accepted acceptedMember).1, fun index => accept_messages setup codec checks seed
            identityIndex raw (state.pool, state.shared) accepted acceptedMember index, alike.1⟩
    | build session payload =>
        have alike := PqxdhDeploymentEligibility.shared_alike setup codec checks seed (.build session payload) trivial _ _
          native
        obtain ⟨_, owners, pool⟩ := sharedKept _ result supported
        exact ⟨owners, by rw [pool], fun _ => by rw [pool], alike.1⟩
    | hmac key message =>
        have alike := PqxdhDeploymentEligibility.shared_alike setup codec checks seed (.hmac key message) trivial _ _
          native
        obtain ⟨_, owners, pool⟩ := sharedKept _ result supported
        exact ⟨owners, by rw [pool], fun _ => by rw [pool], alike.1⟩
    | hash bytes =>
        have alike := PqxdhDeploymentEligibility.shared_alike setup codec checks seed (.hash bytes) trivial _ _ native
        obtain ⟨_, owners, pool⟩ := sharedKept _ result supported
        exact ⟨owners, by rw [pool], fun _ => by rw [pool], alike.1⟩
    | reveal keyId =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.onShared, StateT.run, localState,
          support_map, Set.mem_image] at supported
        obtain ⟨_, member, rfl⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact kept_refl state
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source, StateT.run,
      support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact read_kept read state

/-- A source query is an owner command exactly when its source kind is create, bundle or finish. -/
theorem ownerCommand_kind (query : (Spec KemSK).Domain) :
    ownerCommand query = true ↔ PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 1 ∨
      PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 2 ∨
      PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 5 := by
  rcases query with (coin | request) | read
  · simp [ownerCommand, PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind]
  · cases request <;> simp [ownerCommand, PqxdhRegistrationJointRevealCosts.sourceKind,
      PqxdhRegistrationSchedule.sourceKind]
  · simp [ownerCommand, PqxdhRegistrationJointRevealCosts.sourceKind]

/-- A source program with no create, bundle or finish command keeps the owner registry, the seeds, every signing history and the Server identity along its whole run. -/
theorem quiet_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result)
    (noCreate : program.IsQueryBoundP (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query =
      .inl 1) 0)
    (noBundle : program.IsQueryBoundP (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query =
      .inl 2) 0)
    (noFinish : program.IsQueryBoundP (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query =
      .inl 5) 0)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (result : Result × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex) program).run state)) :
    Kept state result.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact kept_refl state
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at noCreate noBundle noFinish
      obtain ⟨createAllowed, createRest⟩ := noCreate
      obtain ⟨bundleAllowed, bundleRest⟩ := noBundle
      obtain ⟨finishAllowed, finishRest⟩ := noFinish
      have notCreate : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 1 := by
        rcases createAllowed with free | impossible
        · exact free
        · omega
      have notBundle : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 2 := by
        rcases bundleAllowed with free | impossible
        · exact free
        · omega
      have notFinish : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 5 := by
        rcases finishAllowed with free | impossible
        · exact free
        · omega
      have notOwner : ownerCommand query = false := by
        cases owner : ownerCommand query
        · rfl
        · rcases (ownerCommand_kind query).mp owner with kind | kind | kind
          · exact absurd kind notCreate
          · exact absurd kind notBundle
          · exact absurd kind notFinish
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
      have createNext := createRest reply
      have bundleNext := bundleRest reply
      have finishNext := finishRest reply
      simp only [notCreate, notBundle, notFinish, ite_false] at createNext bundleNext finishNext
      exact kept_trans _ _ _ (quiet_step setup codec checks seed identityIndex query notOwner state _ first)
        (ih reply createNext bundleNext finishNext middle second)

/-- The source execution of the compiled program of a complete-interface program, from a ledger, a local state and a joint source state, with the secrecy layer, the compiler and the annotated Server schedule stacked. -/
noncomputable def execution (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds) (seed : IdentitySeed)
    (identityIndex : Nat) (program : OracleComp PqxdhDeploymentInterface.FullSpec X)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (copies : PqxdhDeploymentCompile.Local)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    ProbComp (((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) ×
      PqxdhRegistrationJointSchedule.State KemSK) :=
  (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex)
    ((simulateQ (PqxdhDeploymentCompile.compileImpl setup codec route)
      ((simulateQ (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds) program).run
        ledger)).run copies)).run state

/-- The stacked execution of a bind is the execution of the first program followed by the execution of the continuation from the reached ledger, local state and joint state. -/
theorem execution_bind {Y : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds) (seed : IdentitySeed)
    (identityIndex : Nat) (program : OracleComp PqxdhDeploymentInterface.FullSpec X)
    (next : X → OracleComp PqxdhDeploymentInterface.FullSpec Y)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (copies : PqxdhDeploymentCompile.Local)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    execution setup codec checks route bounds seed identityIndex (program >>= next) ledger copies state =
      execution setup codec checks route bounds seed identityIndex program ledger copies state >>= fun reached =>
        execution setup codec checks route bounds seed identityIndex (next reached.1.1.1) reached.1.1.2 reached.1.2
          reached.2 := by
  simp only [execution, simulateQ_bind, StateT.run_bind]

/-- The signing history of an owner whose bundle calls made in Fresh never failed: while it is publicly Fresh it has published nothing and signed nothing; after that it has published exactly one bundle, which is the Phase 1 writer output of the candidate it signed with its own identity key over one key tuple, and its signing history is exactly the three messages of that tuple. -/
def History (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (transcript : List PqxdhDeploymentInterface.Entry)
    (owner : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK) (pool : PqxdhDynamicIdentityPool.SourceState) :
    Prop :=
  (PqxdhDeploymentTranscript.phase transcript owner = .fresh ∧ PqxdhDeploymentTranscript.bundleOf transcript owner = none ∧
      messagesAt entry.identityIndex pool.transcript = []) ∨
    (PqxdhDeploymentTranscript.phase transcript owner ≠ .fresh ∧
      ∃ bytes keys, PqxdhDeploymentTranscript.bundleOf transcript owner = some bytes ∧
        codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint entry.owner.beacon.identity
          (setup.joint.publicKeys entry.owner.beacon.identity).ed25519 keys) = some bytes ∧
        messagesAt entry.identityIndex pool.transcript = PqxdhRegistrationJointIssuedAttempts.messages keys)

/-- The run invariant between the compiled program's transcript and the joint source state: the public-transcript invariant `Agree` for the projected native state, slot ownership, distinct owner identity indices, empty signing histories beyond the created seeds, nothing recorded for uncreated owners, and the signing history of every owner without a failed bundle call in Fresh. -/
structure Signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity)
    (transcript : List PqxdhDeploymentInterface.Entry) (state : PqxdhRegistrationJointSchedule.State KemSK) : Prop where
  agree : PqxdhDeploymentEligibility.Agree setup codec server transcript (PqxdhRegistrationJointSchedule.source state)
  owned : PqxdhRegistrationJointSchedule.Invariant state
  distinct : ∀ (first second : Nat) (firstEntry secondEntry : PqxdhRegistrationJointOwnership.Entry KemSK),
    state.owners[first]? = some firstEntry → state.owners[second]? = some secondEntry →
      firstEntry.identityIndex = secondEntry.identityIndex → first = second
  future : ∀ index, state.pool.1.seeds.length ≤ index → messagesAt index state.pool.1.transcript = []
  absent : ∀ owner, state.owners.length ≤ owner →
    (PqxdhDeploymentTranscript.summarize transcript).failures owner = false ∧
      PqxdhDeploymentTranscript.bundleOf transcript owner = none
  history : ∀ owner (entry : PqxdhRegistrationJointOwnership.Entry KemSK), state.owners[owner]? = some entry →
    (PqxdhDeploymentTranscript.summarize transcript).failures owner = false →
      History setup codec transcript owner entry state.pool.1

/-- A first successful bundle lookup is unchanged by an entry that is not a successful bundle. -/
theorem bundleOf_other (transcript : List PqxdhDeploymentInterface.Entry) (entry : PqxdhDeploymentInterface.Entry)
    (notBundle : ∀ owner bytes, entry ≠ ⟨.inl (.inr (.bundle owner)), some bytes⟩) (owner : Nat) :
    PqxdhDeploymentTranscript.bundleOf (transcript ++ [entry]) owner = PqxdhDeploymentTranscript.bundleOf transcript owner := by
  unfold PqxdhDeploymentTranscript.bundleOf
  rw [List.findSome?_append]
  cases found : transcript.findSome? _ with
  | some bytes => rfl
  | none =>
      rcases entry with ⟨(coin | command) | secrecy, reply⟩
      · simp
      · cases command with
        | bundle index =>
            cases reply with
            | none => simp
            | some bytes => exact absurd rfl (notBundle index bytes)
        | _ => simp
      · simp

/-- The invariant survives a step that keeps the owner registry, the seeds, every signing history and the Server identity, with a new entry that changes no summary, is not a successful bundle, and keeps `Agree`. -/
theorem signed_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity)
    (transcript : List PqxdhDeploymentInterface.Entry) (before after : PqxdhRegistrationJointSchedule.State KemSK)
    (entry : PqxdhDeploymentInterface.Entry) (signed : Signed setup codec server transcript before) (kept : Kept before after)
    (owned : PqxdhRegistrationJointSchedule.Invariant after)
    (agree : PqxdhDeploymentEligibility.Agree setup codec server (transcript ++ [entry])
      (PqxdhRegistrationJointSchedule.source after))
    (summary : PqxdhDeploymentTranscript.step (PqxdhDeploymentTranscript.summarize transcript) entry =
      PqxdhDeploymentTranscript.summarize transcript)
    (notBundle : ∀ owner bytes, entry ≠ ⟨.inl (.inr (.bundle owner)), some bytes⟩) :
    Signed setup codec server (transcript ++ [entry]) after := by
  have summarized : PqxdhDeploymentTranscript.summarize (transcript ++ [entry]) =
      PqxdhDeploymentTranscript.summarize transcript := by
    rw [PqxdhDeploymentTranscript.summarize_append, summary]
  have phases : ∀ owner, PqxdhDeploymentTranscript.phase (transcript ++ [entry]) owner =
      PqxdhDeploymentTranscript.phase transcript owner := by
    intro owner
    simp only [PqxdhDeploymentTranscript.phase, summarized]
  refine ⟨agree, owned, ?_, ?_, ?_, ?_⟩
  · intro first second firstEntry secondEntry firstFound secondFound same
    rw [kept.owners] at firstFound secondFound
    exact signed.distinct first second firstEntry secondEntry firstFound secondFound same
  · intro index beyond
    rw [kept.messages index]
    exact signed.future index (by rw [← kept.seeds]; exact beyond)
  · intro owner beyond
    rw [summarized, bundleOf_other transcript entry notBundle owner]
    exact signed.absent owner (by rw [← kept.owners]; exact beyond)
  · intro owner current found clean
    rw [kept.owners] at found
    rw [summarized] at clean
    have held := signed.history owner current found clean
    unfold History at held ⊢
    rw [phases owner, bundleOf_other transcript entry notBundle owner, kept.messages current.identityIndex]
    exact held

/-- One bundle trace of an owner: either nothing is signed and the owner is unchanged, or the owner is publicly Fresh and one key tuple is signed at its index, after which either the writer fails and the owner is unchanged, or the bundle is published: its bytes are the writer output of the candidate the owner signed over that tuple with its own identity key, and the owner moves to InitSent with the same identity. -/
theorem trace_cases (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhDynamicIdentityPool.SourceState)
    (supported : result ∈ support (PqxdhRegistrationJointBundle.trace setup codec identityIndex owner pool)) :
    result = ((none, owner), pool) ∨
      ∃ keys, result.2 = PqxdhJointPhase1SourceWriter.signedState setup.joint owner.beacon.identity identityIndex keys pool ∧
        PqxdhDeploymentEligibility.phaseClass owner.beacon.phase = .fresh ∧
        (result.1 = (none, owner) ∨ ∃ bytes, result.1.1 = some bytes ∧
          codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint owner.beacon.identity
            (setup.joint.publicKeys owner.beacon.identity).ed25519 keys) = some bytes ∧
          result.1.2.beacon.identity = owner.beacon.identity ∧
          PqxdhDeploymentEligibility.phaseClass result.1.2.beacon.phase = .initSent) := by
  have after : ∀ generated, (PqxdhRegistrationJointBundle.after setup codec identityIndex owner generated pool) =
      ((none, owner), pool) ∨
      ∃ keys, (PqxdhRegistrationJointBundle.after setup codec identityIndex owner generated pool).2 =
          PqxdhJointPhase1SourceWriter.signedState setup.joint owner.beacon.identity identityIndex keys pool ∧
        PqxdhDeploymentEligibility.phaseClass owner.beacon.phase = .fresh ∧
        ((PqxdhRegistrationJointBundle.after setup codec identityIndex owner generated pool).1 = (none, owner) ∨
          ∃ bytes, (PqxdhRegistrationJointBundle.after setup codec identityIndex owner generated pool).1.1 = some bytes ∧
          codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint owner.beacon.identity
            (setup.joint.publicKeys owner.beacon.identity).ed25519 keys) = some bytes ∧
          (PqxdhRegistrationJointBundle.after setup codec identityIndex owner generated pool).1.2.beacon.identity =
            owner.beacon.identity ∧
          PqxdhDeploymentEligibility.phaseClass
            (PqxdhRegistrationJointBundle.after setup codec identityIndex owner generated pool).1.2.beacon.phase =
              .initSent) := by
    intro generated
    unfold PqxdhRegistrationJointBundle.after
    cases prepared : PqxdhBeaconPhase1Publication.prepare owner generated with
    | none => exact Or.inl rfl
    | some ready =>
        have fresh : PqxdhDeploymentEligibility.phaseClass owner.beacon.phase = .fresh := by
          unfold PqxdhBeaconPhase1Publication.prepare at prepared
          cases phase : owner.beacon.phase <;> simp only [phase] at prepared <;> first | rfl | simp at prepared
        right
        refine ⟨⟨setup.dh.publicKey ready.prekey, setup.dh.publicKey ready.oneTime, ready.kem.1⟩, ?_, fresh, ?_⟩
        · dsimp only
          split <;> rfl
        · dsimp only
          split
          · exact Or.inl rfl
          · rename_i bytes written
            exact Or.inr ⟨bytes, rfl, written, rfl, rfl⟩
  unfold PqxdhRegistrationJointBundle.trace at supported
  split at supported
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨scalar, _, rfl⟩ := supported
    exact after (some scalar)
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact after none
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact Or.inl rfl

/-- Every source program keeps slot ownership of every owner. -/
theorem program_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state)
    (result : Result × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex) program).run state)) :
    PqxdhRegistrationJointSchedule.Invariant result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ PqxdhRegistrationJointSchedule.Invariant
    (fun query current held next member => PqxdhRegistrationJointServerSchedule.query_owned setup codec checks seed
      identityIndex query current next held member) program state owned result supported

/-- A registration request of the annotated Server schedule projects to the native source14 handler. -/
theorem joint_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (request : PqxdhRegistrationSchedule.Request)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (result : PqxdhRegistrationSchedule.QuerySpec request × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      (.inl (.inr request))).run state)) :
    (result.1, PqxdhRegistrationJointSchedule.source result.2) ∈ support
      ((PqxdhRegistrationSchedule.handler setup codec checks seed (.inr request)).run
        (PqxdhRegistrationJointSchedule.source state)) := by
  have native := PqxdhRegistrationJointServerSchedule.query_native setup codec checks seed identityIndex
    (.inl (.inr request)) state
  have member : (result.1, PqxdhRegistrationJointSchedule.source result.2) ∈ support
      ((fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
        (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
          (.inl (.inr request))).run state) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [native] at member
  exact member

/-- `Agree` after a registration request of the annotated Server schedule, through the native handler of the deployment experiment, when the deployment command is that request behind a reply conversion. -/
theorem agree_request (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (identityIndex : Nat)
    (server : RawCtxServerRouting.Identity) (transcript : List PqxdhDeploymentInterface.Entry)
    (query : PqxdhDeploymentInterface.Spec.Domain) (request : PqxdhRegistrationSchedule.Request)
    (convert : PqxdhRegistrationSchedule.QuerySpec request → PqxdhDeploymentInterface.Spec.Range query)
    (same : ∀ (state : PqxdhDeploymentNative.State KemSK),
      (PqxdhDeploymentNative.handler setup codec checks route seed query).run state =
        (fun result => (convert result.1, { state with native := result.2 })) <$>
          (PqxdhRegistrationSchedule.handler setup codec checks seed (.inr request)).run state.native)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (agree : PqxdhDeploymentEligibility.Agree setup codec server transcript (PqxdhRegistrationJointSchedule.source state))
    (answer : PqxdhRegistrationSchedule.QuerySpec request) (after : PqxdhRegistrationJointSchedule.State KemSK)
    (supported : (answer, after) ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex (.inl (.inr request))).run state)) :
    PqxdhDeploymentEligibility.Agree setup codec server (transcript ++ [⟨.inl query, convert answer⟩])
      (PqxdhRegistrationJointSchedule.source after) := by
  have native := joint_native setup codec checks seed identityIndex request state (answer, after) supported
  have lifted : (convert answer, (⟨PqxdhRegistrationJointSchedule.source after, 0, fun _ => 0, []⟩ :
      PqxdhDeploymentNative.State KemSK)) ∈ support ((PqxdhDeploymentNative.handler setup codec checks route seed
        query).run ⟨PqxdhRegistrationJointSchedule.source state, 0, fun _ => 0, []⟩) := by
    rw [same, support_map]
    exact ⟨_, native, rfl⟩
  exact PqxdhDeploymentEligibility.command_step setup codec checks route seed server query transcript _
    agree _ lifted

/-- One forwarded registration request of the compiled program: its reply and the annotated schedule step. -/
theorem forwarded_support {Value : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (request : PqxdhRegistrationSchedule.Request)
    (finish : PqxdhRegistrationSchedule.QuerySpec request → Value)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (result : Value × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex) (finish <$> PqxdhDeploymentCompile.forward (KemSK := KemSK) request)).run state)) :
    ∃ answer after, (answer, after) ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex (.inl (.inr request))).run state) ∧ result = (finish answer, after) := by
  simp only [PqxdhDeploymentCompile.forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map,
    Set.mem_image] at supported
  obtain ⟨⟨answer, after⟩, member, rfl⟩ := supported
  exact ⟨answer, after, member, rfl⟩

/-- A kept step projects to an alike native state. -/
theorem kept_alike (before after : PqxdhRegistrationJointSchedule.State KemSK) (kept : Kept before after) :
    PqxdhDeploymentEligibility.Alike (PqxdhRegistrationJointSchedule.source before)
      (PqxdhRegistrationJointSchedule.source after) := by
  refine ⟨kept.identity, ?_, fun index => ?_⟩
  · simp only [PqxdhRegistrationJointSchedule.source, List.length_map, kept.owners]
  · simp only [PqxdhRegistrationJointSchedule.source, List.getElem?_map, kept.owners]

/-- A kept step with a new entry that changes no summary and is neither a build nor a bundle keeps the invariant. -/
theorem signed_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity)
    (transcript : List PqxdhDeploymentInterface.Entry) (before after : PqxdhRegistrationJointSchedule.State KemSK)
    (entry : PqxdhDeploymentInterface.Entry) (signed : Signed setup codec server transcript before)
    (kept : Kept before after) (owned : PqxdhRegistrationJointSchedule.Invariant after)
    (summary : PqxdhDeploymentTranscript.step (PqxdhDeploymentTranscript.summarize transcript) entry =
      PqxdhDeploymentTranscript.summarize transcript)
    (build : PqxdhDeploymentEligibility.BuildShaped codec server entry)
    (bundle : PqxdhDeploymentEligibility.BundleShaped setup codec (PqxdhRegistrationJointSchedule.source after) entry)
    (notBundle : ∀ owner bytes, entry ≠ ⟨.inl (.inr (.bundle owner)), some bytes⟩) :
    Signed setup codec server (transcript ++ [entry]) after :=
  signed_kept setup codec server transcript before after entry signed kept owned
    (PqxdhDeploymentEligibility.agree_extend setup codec server transcript _ _ entry signed.agree
      (kept_alike before after kept) (by rw [summary]) (by rw [summary]) build bundle) summary notBundle

/-- A forwarded registration request other than create, bundle and finish keeps the invariant. -/
theorem forwarded_signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (identityIndex : Nat)
    (server : RawCtxServerRouting.Identity) (transcript : List PqxdhDeploymentInterface.Entry)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (signed : Signed setup codec server transcript state)
    (query : PqxdhDeploymentInterface.Spec.Domain) (request : PqxdhRegistrationSchedule.Request)
    (notOwner : ownerCommand (KemSK := KemSK) (.inl (.inr request)) = false)
    (convert : PqxdhRegistrationSchedule.QuerySpec request → PqxdhDeploymentInterface.Spec.Range query)
    (same : ∀ (current : PqxdhDeploymentNative.State KemSK),
      (PqxdhDeploymentNative.handler setup codec checks route seed query).run current =
        (fun result => (convert result.1, { current with native := result.2 })) <$>
          (PqxdhRegistrationSchedule.handler setup codec checks seed (.inr request)).run current.native)
    (summary : ∀ answer, PqxdhDeploymentTranscript.step (PqxdhDeploymentTranscript.summarize transcript)
      ⟨.inl query, convert answer⟩ = PqxdhDeploymentTranscript.summarize transcript)
    (notBundle : ∀ answer owner bytes, (⟨.inl query, convert answer⟩ : PqxdhDeploymentInterface.Entry) ≠
      ⟨.inl (.inr (.bundle owner)), some bytes⟩)
    (answer : PqxdhRegistrationSchedule.QuerySpec request) (after : PqxdhRegistrationJointSchedule.State KemSK)
    (member : (answer, after) ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex (.inl (.inr request))).run state)) :
    Signed setup codec server (transcript ++ [⟨.inl query, convert answer⟩]) after :=
  signed_kept setup codec server transcript state after _ signed
    (quiet_step setup codec checks seed identityIndex (.inl (.inr request)) notOwner state (answer, after) member)
    (PqxdhRegistrationJointServerSchedule.query_owned setup codec checks seed identityIndex (.inl (.inr request)) state
      (answer, after) signed.owned member)
    (agree_request setup codec checks route seed identityIndex server transcript query request convert same state
      signed.agree answer after member) (summary answer) (notBundle answer)

/-- A create of a parsed pin appends one Fresh owner at a new identity index and keeps the invariant. -/
theorem create_signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (identityIndex : Nat)
    (server : RawCtxServerRouting.Identity) (transcript : List PqxdhDeploymentInterface.Entry)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (signed : Signed setup codec server transcript state)
    (pin : Pqxdh.Bytes) (word : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (parsed : PqxdhDeploymentInterface.parsePin pin = some word)
    (index : Nat) (after : PqxdhRegistrationJointSchedule.State KemSK)
    (member : (index, after) ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex (.inl (.inr (.create word keyId)))).run state)) :
    Signed setup codec server (transcript ++ [⟨.inl (.inr (.create pin keyId)), some index⟩]) after := by
  have agree := agree_request setup codec checks route seed identityIndex server transcript (.inr (.create pin keyId))
    (.create word keyId) some (fun current => by
      simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_map, PqxdhDeploymentCompileStep.onNative_run,
        Functor.map_map]
      rfl) state signed.agree index after member
  have owned := PqxdhRegistrationJointServerSchedule.query_owned setup codec checks seed identityIndex
    (.inl (.inr (.create word keyId))) state (index, after) signed.owned member
  simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
    PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create, StateT.run, support_map,
    Set.mem_image] at member
  obtain ⟨material, _, made⟩ := member
  simp only [PqxdhRegistrationJointSchedule.created, Prod.mk.injEq] at made
  obtain ⟨rfl, rfl⟩ := made
  have seeds : (PqxdhRegistrationJointCreation.serviceView setup state.pool material).2.1.seeds =
      state.pool.1.seeds ++ [material.seed] := rfl
  have messages : ∀ position, messagesAt position
      (PqxdhRegistrationJointCreation.serviceView setup state.pool material).2.1.transcript =
      messagesAt position state.pool.1.transcript := by
    intro position
    exact record_messages _ _ _ (by intro selected message; simp) position
  have summarized : PqxdhDeploymentTranscript.summarize (transcript ++ [⟨.inl (.inr (.create pin keyId)),
      some state.owners.length⟩]) = { PqxdhDeploymentTranscript.summarize transcript with
        owners := (PqxdhDeploymentTranscript.summarize transcript).owners ++ [(word, keyId)]
        phases := Function.update (PqxdhDeploymentTranscript.summarize transcript).phases state.owners.length .fresh } := by
    rw [PqxdhDeploymentTranscript.summarize_append]
    simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, parsed]
  have bundles : ∀ owner, PqxdhDeploymentTranscript.bundleOf (transcript ++ [⟨.inl (.inr (.create pin keyId)),
      some state.owners.length⟩]) owner = PqxdhDeploymentTranscript.bundleOf transcript owner :=
    bundleOf_other transcript _ (by simp)
  have bound : ∀ (owner : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK), state.owners[owner]? = some entry →
      entry.identityIndex < state.pool.1.seeds.length := by
    intro owner entry found
    exact (List.getElem?_eq_some_iff.mp (signed.owned entry (List.mem_of_getElem? found)).1).1
  have lookup : ∀ owner : Nat, (state.owners ++ [PqxdhRegistrationJointSchedule.birth word keyId state.pool material])[owner]? =
      if owner < state.owners.length then state.owners[owner]?
      else if owner = state.owners.length then some (PqxdhRegistrationJointSchedule.birth word keyId state.pool material)
      else none := by
    intro owner
    by_cases below : owner < state.owners.length
    · simp [List.getElem?_append_left below, below]
    · by_cases equal : owner = state.owners.length
      · subst equal
        simp
      · rw [List.getElem?_append_right (by omega)]
        simp only [below, equal, ite_false]
        rw [List.getElem?_eq_none]
        simp only [List.length_singleton]
        omega
  refine ⟨agree, owned, ?_, ?_, ?_, ?_⟩
  · intro first second firstEntry secondEntry firstFound secondFound same
    rw [lookup] at firstFound secondFound
    split at firstFound <;> split at secondFound
    · exact signed.distinct first second firstEntry secondEntry firstFound secondFound same
    · split at secondFound
      · simp only [Option.some.injEq] at secondFound
        subst secondFound
        have := bound first firstEntry firstFound
        simp [PqxdhRegistrationJointSchedule.birth] at same
        omega
      · cases secondFound
    · split at firstFound
      · simp only [Option.some.injEq] at firstFound
        subst firstFound
        have := bound second secondEntry secondFound
        simp [PqxdhRegistrationJointSchedule.birth] at same
        omega
      · cases firstFound
    · split at firstFound <;> split at secondFound
      · omega
      all_goals cases firstFound <;> cases secondFound
  · intro position beyond
    simp only [seeds, List.length_append, List.length_singleton] at beyond
    simp only [messages]
    exact signed.future position (by omega)
  · intro owner beyond
    simp only [List.length_append, List.length_singleton] at beyond
    rw [summarized, bundles]
    exact signed.absent owner (by omega)
  · intro owner entry found clean
    rw [summarized] at clean
    rw [lookup] at found
    unfold History
    simp only [PqxdhDeploymentTranscript.phase, summarized, bundles, messages]
    split at found
    · rename_i below
      have held := signed.history owner entry found clean
      unfold History at held
      simp only [PqxdhDeploymentTranscript.phase] at held
      rw [Function.update_of_ne (by omega)]
      exact held
    · split at found
      · rename_i _ equal
        subst equal
        simp only [Option.some.injEq] at found
        subst found
        left
        refine ⟨Function.update_self .., (signed.absent _ (le_refl _)).2, ?_⟩
        exact signed.future _ (le_refl _)
      · cases found

/-- A finish entry changes only the public phase of its owner, and only from InitSent to Established or Aborted. -/
theorem finish_summary (transcript : List PqxdhDeploymentInterface.Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (answer : Option Pqxdh.Bytes) :
    (PqxdhDeploymentTranscript.summarize (transcript ++ [⟨.inl (.inr (.finish owner raw)), answer⟩])).failures =
        (PqxdhDeploymentTranscript.summarize transcript).failures ∧
      (∀ other, other ≠ owner → PqxdhDeploymentTranscript.phase (transcript ++ [⟨.inl (.inr (.finish owner raw)), answer⟩])
        other = PqxdhDeploymentTranscript.phase transcript other) ∧
      (PqxdhDeploymentTranscript.phase (transcript ++ [⟨.inl (.inr (.finish owner raw)), answer⟩]) owner = .fresh ↔
        PqxdhDeploymentTranscript.phase transcript owner = .fresh) := by
  simp only [PqxdhDeploymentTranscript.phase, PqxdhDeploymentTranscript.summarize_append, PqxdhDeploymentTranscript.step,
    PqxdhDeploymentTranscript.stepCommand]
  by_cases sent : (PqxdhDeploymentTranscript.summarize transcript).phases owner = .initSent
  · cases answer <;> simp (config := { contextual := true }) [sent]
  · cases answer <;> simp [sent]

/-- A finish keeps the invariant: it replaces at most its owner by one with the same identity and leaves every signing history unchanged. -/
theorem finish_signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (identityIndex : Nat)
    (server : RawCtxServerRouting.Identity) (transcript : List PqxdhDeploymentInterface.Entry)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (signed : Signed setup codec server transcript state)
    (owner : Nat) (raw : Pqxdh.Bytes) (answer : Option Pqxdh.Bytes) (after : PqxdhRegistrationJointSchedule.State KemSK)
    (member : (answer, after) ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex (.inl (.inr (.finish owner raw)))).run state)) :
    Signed setup codec server (transcript ++ [⟨.inl (.inr (.finish owner raw)), answer⟩]) after := by
  have agree := agree_request setup codec checks route seed identityIndex server transcript (.inr (.finish owner raw))
    (.finish owner raw) id (fun _ => rfl) state signed.agree answer after member
  have owned := PqxdhRegistrationJointServerSchedule.query_owned setup codec checks seed identityIndex
    (.inl (.inr (.finish owner raw))) state (answer, after) signed.owned member
  obtain ⟨failures, others, freshness⟩ := finish_summary transcript owner raw answer
  have bundles : ∀ other, PqxdhDeploymentTranscript.bundleOf (transcript ++ [⟨.inl (.inr (.finish owner raw)),
      answer⟩]) other = PqxdhDeploymentTranscript.bundleOf transcript other :=
    bundleOf_other transcript _ (by simp)
  simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
    PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish, StateT.run] at member
  split at member
  · rename_i missing
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
    obtain ⟨rfl, settled⟩ := member
    rw [settled] at agree owned ⊢
    have absent : PqxdhDeploymentTranscript.phase transcript owner = .absent := by
      rw [signed.agree.phases owner]
      simp [PqxdhRegistrationJointSchedule.source, missing, PqxdhDeploymentEligibility.nativePhase]
    refine signed_kept setup codec server transcript state state _ signed (kept_refl state) owned agree ?_ (by simp)
    simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand]
    simp only [PqxdhDeploymentTranscript.phase] at absent
    simp [absent]
  · rename_i entry found
    simp only [support_map, Set.mem_image] at member
    obtain ⟨reached, reachedMember, same⟩ := member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    have slots := PqxdhRegistrationJointFinish.annotated_program_slots setup codec entry.identityIndex entry.kemIndex _
      (state.pool, state.shared) reached reachedMember
    have messages := finish_messages setup codec entry.identityIndex entry.kemIndex raw entry.owner
      (state.pool, state.shared) reached reachedMember
    have bound : owner < state.owners.length := (List.getElem?_eq_some_iff.mp found).1
    have lookup : ∀ other : Nat, (state.owners.set owner { entry with owner := reached.1.2 })[other]? =
        if other = owner then some { entry with owner := reached.1.2 } else state.owners[other]? := by
      intro other
      by_cases same : other = owner
      · subst same
        simp [List.getElem?_set_self bound]
      · simp [List.getElem?_set_ne (Ne.symm same), same]
    have identity : reached.1.2.beacon.identity = entry.owner.beacon.identity := by
      have atOwner : (state.owners.set owner { entry with owner := reached.1.2 })[owner]? =
          some { entry with owner := reached.1.2 } := by
        rw [lookup]
        simp
      have now := (owned { entry with owner := reached.1.2 } (List.mem_of_getElem? atOwner)).1
      have before := (signed.owned entry (List.mem_of_getElem? found)).1
      change reached.2.1.1.seeds[entry.identityIndex]? = some reached.1.2.beacon.identity at now
      rw [slots.1, before] at now
      exact (Option.some.inj now).symm
    refine ⟨agree, owned, ?_, ?_, ?_, ?_⟩
    · intro first second firstEntry secondEntry firstFound secondFound same
      change (state.owners.set owner { entry with owner := reached.1.2 })[first]? = some firstEntry at firstFound
      change (state.owners.set owner { entry with owner := reached.1.2 })[second]? = some secondEntry at secondFound
      rw [lookup] at firstFound secondFound
      split at firstFound <;> split at secondFound
      · rename_i firstSame secondSame
        exact firstSame.trans secondSame.symm
      · rename_i firstSame _
        simp only [Option.some.injEq] at firstFound
        subst firstFound
        exact firstSame.trans (signed.distinct owner second entry secondEntry found secondFound same)
      · rename_i _ secondSame
        simp only [Option.some.injEq] at secondFound
        subst secondFound
        exact (signed.distinct first owner firstEntry entry firstFound found same).trans secondSame.symm
      · exact signed.distinct first second firstEntry secondEntry firstFound secondFound same
    · intro position beyond
      change messagesAt position reached.2.1.1.transcript = []
      rw [messages position]
      exact signed.future position (by rw [← slots.1]; exact beyond)
    · intro other beyond
      change (state.owners.set owner { entry with owner := reached.1.2 }).length ≤ other at beyond
      rw [List.length_set] at beyond
      rw [failures, bundles]
      exact signed.absent other beyond
    · intro other current currentFound clean
      change (state.owners.set owner { entry with owner := reached.1.2 })[other]? = some current at currentFound
      rw [failures] at clean
      rw [lookup] at currentFound
      unfold History
      change (_ ∧ _ ∧ messagesAt current.identityIndex reached.2.1.1.transcript = []) ∨ _
      rw [bundles, messages current.identityIndex]
      split at currentFound
      · rename_i sameOwner
        subst sameOwner
        simp only [Option.some.injEq] at currentFound
        subst currentFound
        have held := signed.history other entry found clean
        unfold History at held
        rcases held with ⟨fresh, none, empty⟩ | ⟨notFresh, bytes, keys, published, written, history⟩
        · exact Or.inl ⟨freshness.mpr fresh, none, empty⟩
        · refine Or.inr ⟨fun now => notFresh (freshness.mp now), bytes, keys, published, ?_, history⟩
          simpa only [identity] using written
      · rename_i different
        have held := signed.history other current currentFound clean
        unfold History at held
        rw [others other different]
        exact held

/-- A bundle entry can only set the first successful bundle of its own owner. -/
theorem bundleOf_bundle (transcript : List PqxdhDeploymentInterface.Entry) (owner : Nat) (reply : Option Pqxdh.Bytes)
    (other : Nat) :
    PqxdhDeploymentTranscript.bundleOf (transcript ++ [⟨.inl (.inr (.bundle owner)), reply⟩]) other =
      if other = owner then (PqxdhDeploymentTranscript.bundleOf transcript other).or reply
      else PqxdhDeploymentTranscript.bundleOf transcript other := by
  unfold PqxdhDeploymentTranscript.bundleOf
  rw [List.findSome?_append]
  by_cases same : other = owner
  · subst same
    cases reply <;> simp
  · cases reply <;> simp [same, Ne.symm same]

/-- A rejected bundle call of a publicly Fresh owner flags it; whatever it signed stays at its own index and the invariant survives. -/
theorem signed_flag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity)
    (transcript : List PqxdhDeploymentInterface.Entry) (before after : PqxdhRegistrationJointSchedule.State KemSK)
    (signed : Signed setup codec server transcript before) (owner : Nat)
    (entry : PqxdhRegistrationJointOwnership.Entry KemSK) (found : before.owners[owner]? = some entry)
    (fresh : PqxdhDeploymentTranscript.phase transcript owner = .fresh)
    (owners : after.owners = before.owners) (seeds : after.pool.1.seeds = before.pool.1.seeds)
    (messages : ∀ index, index ≠ entry.identityIndex →
      messagesAt index after.pool.1.transcript = messagesAt index before.pool.1.transcript)
    (owned : PqxdhRegistrationJointSchedule.Invariant after)
    (agree : PqxdhDeploymentEligibility.Agree setup codec server
      (transcript ++ [⟨.inl (.inr (.bundle owner)), none⟩]) (PqxdhRegistrationJointSchedule.source after)) :
    Signed setup codec server (transcript ++ [⟨.inl (.inr (.bundle owner)), none⟩]) after := by
  have summarized : PqxdhDeploymentTranscript.summarize (transcript ++ [⟨.inl (.inr (.bundle owner)), none⟩]) =
      { PqxdhDeploymentTranscript.summarize transcript with
        failures := Function.update (PqxdhDeploymentTranscript.summarize transcript).failures owner true } := by
    rw [PqxdhDeploymentTranscript.summarize_append]
    simp only [PqxdhDeploymentTranscript.phase] at fresh
    simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, fresh, ite_true]
  have bundles : ∀ other, PqxdhDeploymentTranscript.bundleOf (transcript ++ [⟨.inl (.inr (.bundle owner)), none⟩])
      other = PqxdhDeploymentTranscript.bundleOf transcript other := by
    intro other
    rw [bundleOf_bundle]
    split <;> simp
  have bound : owner < before.owners.length := (List.getElem?_eq_some_iff.mp found).1
  have created : entry.identityIndex < before.pool.1.seeds.length :=
    (List.getElem?_eq_some_iff.mp (signed.owned entry (List.mem_of_getElem? found)).1).1
  refine ⟨agree, owned, ?_, ?_, ?_, ?_⟩
  · intro first second firstEntry secondEntry firstFound secondFound same
    rw [owners] at firstFound secondFound
    exact signed.distinct first second firstEntry secondEntry firstFound secondFound same
  · intro index beyond
    rw [seeds] at beyond
    rw [messages index (by omega)]
    exact signed.future index beyond
  · intro other beyond
    rw [owners] at beyond
    rw [summarized, bundles]
    simp only [Function.update_of_ne (show other ≠ owner by omega)]
    exact signed.absent other beyond
  · intro other current currentFound clean
    rw [summarized] at clean
    by_cases same : other = owner
    · subst same
      simp at clean
    · simp only [Function.update_of_ne same] at clean
      rw [owners] at currentFound
      have held := signed.history other current currentFound clean
      have distinct : current.identityIndex ≠ entry.identityIndex := fun equal =>
        same (signed.distinct other owner current entry currentFound found equal)
      unfold History at held ⊢
      simp only [PqxdhDeploymentTranscript.phase, summarized] at held ⊢
      rw [bundles, messages current.identityIndex distinct]
      exact held

/-- A bundle keeps the invariant: an owner that is not publicly Fresh signs nothing; a publicly Fresh owner either is flagged by a rejected bundle call, or publishes the writer output of the candidate it signed over the one tuple that its signing history now holds. -/
theorem bundle_signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (identityIndex : Nat)
    (server : RawCtxServerRouting.Identity) (transcript : List PqxdhDeploymentInterface.Entry)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (signed : Signed setup codec server transcript state)
    (owner : Nat) (answer : Option Pqxdh.Bytes) (after : PqxdhRegistrationJointSchedule.State KemSK)
    (member : (answer, after) ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex (.inl (.inr (.bundle owner)))).run state)) :
    Signed setup codec server (transcript ++ [⟨.inl (.inr (.bundle owner)), answer⟩]) after := by
  have agree := agree_request setup codec checks route seed identityIndex server transcript (.inr (.bundle owner))
    (.bundle owner) id (fun _ => rfl) state signed.agree answer after member
  have owned := PqxdhRegistrationJointServerSchedule.query_owned setup codec checks seed identityIndex
    (.inl (.inr (.bundle owner))) state (answer, after) signed.owned member
  simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
    PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle, StateT.run] at member
  split at member
  · rename_i missing
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
    obtain ⟨rfl, settled⟩ := member
    rw [settled] at agree owned ⊢
    have absent : (PqxdhDeploymentTranscript.summarize transcript).phases owner = .absent := by
      have phases := signed.agree.phases owner
      simp only [PqxdhDeploymentTranscript.phase] at phases
      rw [phases]
      simp [PqxdhRegistrationJointSchedule.source, missing, PqxdhDeploymentEligibility.nativePhase]
    exact signed_kept setup codec server transcript state state _ signed (kept_refl state) owned agree
      (by simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, absent]) (by simp)
  · rename_i entry found
    simp only [support_map, Set.mem_image] at member
    obtain ⟨traced, tracedMember, same⟩ := member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    have phaseEq : PqxdhDeploymentTranscript.phase transcript owner =
        PqxdhDeploymentEligibility.phaseClass entry.owner.beacon.phase := by
      rw [signed.agree.phases owner]
      simp [PqxdhRegistrationJointSchedule.source, found, PqxdhDeploymentEligibility.nativePhase]
    have bound : owner < state.owners.length := (List.getElem?_eq_some_iff.mp found).1
    have created : entry.identityIndex < state.pool.1.seeds.length :=
      (List.getElem?_eq_some_iff.mp (signed.owned entry (List.mem_of_getElem? found)).1).1
    have restore : state.owners.set owner { entry with owner := entry.owner } = state.owners :=
      PqxdhDeploymentCompileRegistration.set_found _ _ _ found
    rcases trace_cases setup codec entry.identityIndex entry.owner state.pool.1 traced tracedMember with
      unchanged | ⟨keys, signedPool, freshClass, outcome⟩
    · subst unchanged
      by_cases fresh : PqxdhDeploymentTranscript.phase transcript owner = .fresh
      · exact signed_flag setup codec server transcript state _ signed owner entry found fresh restore rfl
          (fun _ _ => rfl) owned agree
      · simp only [PqxdhDeploymentTranscript.phase] at fresh
        exact signed_kept setup codec server transcript state _ _ signed ⟨restore, rfl, fun _ => rfl, rfl⟩ owned agree
          (by simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, fresh]) (by simp)
    · have fresh : PqxdhDeploymentTranscript.phase transcript owner = .fresh := phaseEq.trans freshClass
      have kept : ∀ index, index ≠ entry.identityIndex →
          messagesAt index traced.2.transcript = messagesAt index state.pool.1.transcript := by
        intro index different
        rw [signedPool, PqxdhRegistrationJointSigningTranscript.signed]
        simp [Ne.symm different]
      have seeds : traced.2.seeds = state.pool.1.seeds := by
        rw [signedPool]
        rfl
      rcases outcome with rejected | ⟨bytes, published, written, identity, initSent⟩
      · rw [rejected] at agree owned ⊢
        exact signed_flag setup codec server transcript state _ signed owner entry found fresh restore seeds kept owned
          agree
      · rw [published] at agree owned ⊢
        have summarized : PqxdhDeploymentTranscript.summarize
            (transcript ++ [⟨.inl (.inr (.bundle owner)), some bytes⟩]) =
              { PqxdhDeploymentTranscript.summarize transcript with
                phases := Function.update (PqxdhDeploymentTranscript.summarize transcript).phases owner .initSent } := by
          rw [PqxdhDeploymentTranscript.summarize_append]
          simp only [PqxdhDeploymentTranscript.phase] at fresh
          simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, fresh, ite_true]
        have lookup : ∀ other : Nat, (state.owners.set owner { entry with owner := traced.1.2 })[other]? =
            if other = owner then some { entry with owner := traced.1.2 } else state.owners[other]? := by
          intro other
          by_cases same : other = owner
          · subst same
            simp [List.getElem?_set_self bound]
          · simp [List.getElem?_set_ne (Ne.symm same), same]
        refine ⟨agree, owned, ?_, ?_, ?_, ?_⟩
        · intro first second firstEntry secondEntry firstFound secondFound same
          change (state.owners.set owner { entry with owner := traced.1.2 })[first]? = some firstEntry at firstFound
          change (state.owners.set owner { entry with owner := traced.1.2 })[second]? = some secondEntry at secondFound
          rw [lookup] at firstFound secondFound
          split at firstFound <;> split at secondFound
          · rename_i firstSame secondSame
            exact firstSame.trans secondSame.symm
          · rename_i firstSame _
            simp only [Option.some.injEq] at firstFound
            subst firstFound
            exact firstSame.trans (signed.distinct owner second entry secondEntry found secondFound same)
          · rename_i _ secondSame
            simp only [Option.some.injEq] at secondFound
            subst secondFound
            exact (signed.distinct first owner firstEntry entry firstFound found same).trans secondSame.symm
          · exact signed.distinct first second firstEntry secondEntry firstFound secondFound same
        · intro index beyond
          change traced.2.seeds.length ≤ index at beyond
          change messagesAt index traced.2.transcript = []
          rw [seeds] at beyond
          rw [kept index (by omega)]
          exact signed.future index beyond
        · intro other beyond
          change (state.owners.set owner { entry with owner := traced.1.2 }).length ≤ other at beyond
          rw [List.length_set] at beyond
          rw [summarized, bundleOf_bundle]
          simp only [show other ≠ owner by omega, ite_false]
          exact signed.absent other beyond
        · intro other current currentFound clean
          change (state.owners.set owner { entry with owner := traced.1.2 })[other]? = some current at currentFound
          rw [summarized] at clean
          rw [lookup] at currentFound
          unfold History
          simp only [PqxdhDeploymentTranscript.phase, summarized]
          rw [bundleOf_bundle]
          split at currentFound
          · rename_i sameOwner
            subst sameOwner
            simp only [Option.some.injEq] at currentFound
            subst currentFound
            have held := signed.history other entry found clean
            unfold History at held
            have publishedBefore : PqxdhDeploymentTranscript.bundleOf transcript other = none := by
              rcases held with ⟨_, none, _⟩ | ⟨notFresh, _⟩
              · exact none
              · exact absurd fresh notFresh
            have emptyBefore : messagesAt entry.identityIndex state.pool.1.transcript = [] := by
              rcases held with ⟨_, _, empty⟩ | ⟨notFresh, _⟩
              · exact empty
              · exact absurd fresh notFresh
            right
            refine ⟨by simp [Function.update_self], bytes, keys, by simp [publishedBefore], ?_, ?_⟩
            · simpa only [identity] using written
            · change messagesAt entry.identityIndex traced.2.transcript = _
              rw [signedPool, PqxdhRegistrationJointSigningTranscript.signed, emptyBefore]
              simp
          · rename_i different
            simp only [different, ite_false, Function.update_of_ne different]
            have held := signed.history other current currentFound clean
            unfold History at held
            have distinct : current.identityIndex ≠ entry.identityIndex := fun equal =>
              different (signed.distinct other owner current entry currentFound found equal)
            change (_ ∧ _ ∧ messagesAt current.identityIndex traced.2.transcript = []) ∨
              (_ ∧ ∃ bytes keys, _ ∧ _ ∧ messagesAt current.identityIndex traced.2.transcript = _)
            rw [kept current.identityIndex distinct]
            exact held

/-- Every native command of the compiled program, run through the annotated Server schedule, keeps the invariant with the command and its reply appended to the transcript. -/
theorem native_signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (identityIndex : Nat)
    (server : RawCtxServerRouting.Identity) (transcript : List PqxdhDeploymentInterface.Entry)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (signed : Signed setup codec server transcript state)
    (query : PqxdhDeploymentInterface.Spec.Domain) (copies : PqxdhDeploymentCompile.Local)
    (result : (PqxdhDeploymentInterface.Spec.Range query × PqxdhDeploymentCompile.Local) ×
      PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex) ((PqxdhDeploymentCompile.compileImpl setup codec route query).run copies)).run state)) :
    Signed setup codec server (transcript ++ [⟨.inl query, result.1.1⟩]) result.2 := by
  have quietRecord : ∀ (command : PqxdhDeploymentInterface.Command),
      PqxdhDeploymentCompileBudget.commandKind (.inr command) = 8 ∨
        PqxdhDeploymentCompileBudget.commandKind (.inr command) = 9 ∨
        PqxdhDeploymentCompileBudget.commandKind (.inr command) = 10 ∨
        PqxdhDeploymentCompileBudget.commandKind (.inr command) = 11 →
      ∀ (result : (PqxdhDeploymentInterface.Spec.Range (.inr command) × PqxdhDeploymentCompile.Local) ×
        PqxdhRegistrationJointSchedule.State KemSK),
      result ∈ support ((simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed
        identityIndex) ((PqxdhDeploymentCompile.compileImpl setup codec route (.inr command)).run copies)).run state) →
      Kept state result.2 ∧ PqxdhRegistrationJointSchedule.Invariant result.2 := by
    intro command record result member
    have zero : ∀ kind : Fin 9, kind = 1 ∨ kind = 2 ∨ kind = 5 →
        ((PqxdhDeploymentCompile.compileImpl setup codec route (.inr command)).run copies).IsQueryBoundP
          (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inl kind) 0 := by
      intro kind owner
      have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl kind) (.inr command) copies
      have costZero : PqxdhDeploymentCompileBudget.cost (.inl kind)
          (PqxdhDeploymentCompileBudget.commandKind (.inr command)) = 0 := by
        rcases owner with rfl | rfl | rfl <;> rcases record with hit | hit | hit | hit <;>
          simp [hit, PqxdhDeploymentCompileBudget.cost, PqxdhDeploymentCompileBudget.unit]
      rwa [costZero] at bound
    exact ⟨quiet_program setup codec checks seed identityIndex _ (zero 1 (Or.inl rfl)) (zero 2 (Or.inr (Or.inl rfl)))
        (zero 5 (Or.inr (Or.inr rfl))) state result member,
      program_owned setup codec checks seed identityIndex _ state signed.owned result member⟩
  rcases query with coin | command
  · simp only [PqxdhDeploymentCompile.compileImpl, StateT.run_lift, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
      PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      PqxdhRegistrationJointSchedule.handler] at supported
    obtain ⟨⟨value, after⟩, member, rfl⟩ := supported
    obtain ⟨_, _, same⟩ := member
    cases same
    exact signed_quiet setup codec server transcript state state _ signed (kept_refl state) signed.owned rfl trivial
      trivial (by simp)
  · cases command with
    | create pin keyId =>
        cases parsed : PqxdhDeploymentInterface.parsePin pin with
        | none =>
            simp only [PqxdhDeploymentCompile.compileImpl, parsed] at supported
            subst supported
            exact signed_quiet setup codec server transcript state state _ signed (kept_refl state) signed.owned
              (by simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand]) trivial trivial
              (by simp)
        | some word =>
            have shape : (PqxdhDeploymentCompile.compileImpl setup codec route (.inr (.create pin keyId))).run copies =
                (fun index => (some index, { copies with
                  log := { copies.log with owners := copies.log.owners ++ [(word, keyId)] } })) <$>
                  PqxdhDeploymentCompile.forward (KemSK := KemSK) (.create word keyId) := by
              simp only [PqxdhDeploymentCompile.compileImpl, parsed, bind_pure_comp]
              rfl
            rw [shape] at supported
            obtain ⟨index, after, member, rfl⟩ := forwarded_support setup codec checks seed identityIndex _ _ state _
              supported
            exact create_signed setup codec checks route seed identityIndex server transcript state signed pin word keyId
              parsed index after member
    | bundle owner =>
        have shape : (PqxdhDeploymentCompile.compileImpl setup codec route (.inr (.bundle owner))).run copies =
            (fun answer => (answer, { copies with
              log := (PqxdhDeploymentCompile.logReply copies.log (.bundle owner) answer) })) <$>
              PqxdhDeploymentCompile.forward (KemSK := KemSK) (.bundle owner) := by
          rfl
        rw [shape] at supported
        obtain ⟨answer, after, member, rfl⟩ := forwarded_support setup codec checks seed identityIndex _ _ state _ supported
        exact bundle_signed setup codec checks route seed identityIndex server transcript state signed owner answer
          after member
    | finish owner raw =>
        have shape : (PqxdhDeploymentCompile.compileImpl setup codec route (.inr (.finish owner raw))).run copies =
            (fun answer => (answer, { copies with
              log := (PqxdhDeploymentCompile.logReply copies.log (.finish owner raw) answer) })) <$>
              PqxdhDeploymentCompile.forward (KemSK := KemSK) (.finish owner raw) := by
          rfl
        rw [shape] at supported
        obtain ⟨answer, after, member, rfl⟩ := forwarded_support setup codec checks seed identityIndex _ _ state _ supported
        exact finish_signed setup codec checks route seed identityIndex server transcript state signed owner raw answer
          after member
    | accept raw =>
        have shape : (PqxdhDeploymentCompile.compileImpl setup codec route (.inr (.accept raw))).run copies =
            (fun answer => (answer, { copies with log := PqxdhDeploymentCompile.logReply copies.log (.accept raw) answer }))
              <$> PqxdhDeploymentCompile.forward (KemSK := KemSK) (.accept raw) := by
          rfl
        rw [shape] at supported
        obtain ⟨answer, after, member, rfl⟩ := forwarded_support setup codec checks seed identityIndex _ _ state _ supported
        exact forwarded_signed setup codec checks route seed identityIndex server transcript state signed
          (.inr (.accept raw)) (.accept raw) rfl id (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => by simp) answer after member
    | build session payload =>
        have shape : (PqxdhDeploymentCompile.compileImpl setup codec route (.inr (.build session payload))).run copies =
            (fun answer => (answer, { copies with
              log := (PqxdhDeploymentCompile.logReply copies.log (.build session payload) answer) })) <$>
              PqxdhDeploymentCompile.forward (KemSK := KemSK) (.build session payload) := by
          rfl
        rw [shape] at supported
        obtain ⟨answer, after, member, rfl⟩ := forwarded_support setup codec checks seed identityIndex _ _ state _ supported
        exact forwarded_signed setup codec checks route seed identityIndex server transcript state signed
          (.inr (.build session payload)) (.build session payload) rfl id (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => by simp) answer after member
    | hmac key message =>
        have shape : (PqxdhDeploymentCompile.compileImpl setup codec route (.inr (.hmac key message))).run copies =
            (fun answer => (answer, copies)) <$> PqxdhDeploymentCompile.forward (KemSK := KemSK) (.hmac key message) := by
          simp only [PqxdhDeploymentCompile.compileImpl, StateT.run_lift, bind_pure_comp]
          rfl
        rw [shape] at supported
        obtain ⟨answer, after, member, rfl⟩ := forwarded_support setup codec checks seed identityIndex _ _ state _ supported
        exact forwarded_signed setup codec checks route seed identityIndex server transcript state signed
          (.inr (.hmac key message)) (.hmac key message) rfl id (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => by simp) answer after member
    | hash bytes =>
        have shape : (PqxdhDeploymentCompile.compileImpl setup codec route (.inr (.hash bytes))).run copies =
            (fun answer => (answer, copies)) <$> PqxdhDeploymentCompile.forward (KemSK := KemSK) (.hash bytes) := by
          simp only [PqxdhDeploymentCompile.compileImpl, StateT.run_lift, bind_pure_comp]
          rfl
        rw [shape] at supported
        obtain ⟨answer, after, member, rfl⟩ := forwarded_support setup codec checks seed identityIndex _ _ state _ supported
        exact forwarded_signed setup codec checks route seed identityIndex server transcript state signed
          (.inr (.hash bytes)) (.hash bytes) rfl id (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => by simp) answer after member
    | serverSend kid plaintext =>
        obtain ⟨kept, owned⟩ := quietRecord _ (Or.inl rfl) result supported
        exact signed_quiet setup codec server transcript state _ _ signed kept owned rfl trivial trivial (by simp)
    | serverRaw raw =>
        obtain ⟨kept, owned⟩ := quietRecord _ (Or.inr (Or.inl rfl)) result supported
        exact signed_quiet setup codec server transcript state _ _ signed kept owned rfl trivial trivial (by simp)
    | beaconSend index plaintext =>
        obtain ⟨kept, owned⟩ := quietRecord _ (Or.inr (Or.inr (Or.inl rfl))) result supported
        exact signed_quiet setup codec server transcript state _ _ signed kept owned rfl trivial trivial (by simp)
    | beaconRaw index raw =>
        obtain ⟨kept, owned⟩ := quietRecord _ (Or.inr (Or.inr (Or.inr rfl))) result supported
        exact signed_quiet setup codec server transcript state _ _ signed kept owned rfl trivial trivial (by simp)

/-- A secrecy command of the complete interface keeps the invariant: it issues only experiment coins and sends, which the compiler turns into local record work with Server kernel reveals, established-kernel reads and BLAKE2b queries. -/
theorem secrecy_signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds) (seed : IdentitySeed)
    (identityIndex : Nat) (server : RawCtxServerRouting.Identity) (ledger : PqxdhDeploymentSecrecy.Ledger)
    (copies : PqxdhDeploymentCompile.Local) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (signed : Signed setup codec server ledger.transcript state) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (result : ((Option RawCtxSourceSend.Encrypted × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) ×
      PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex) ((simulateQ (PqxdhDeploymentCompile.compileImpl setup codec route)
        ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds (.inr secrecy)).run
          ledger)).run copies)).run state)) :
    Signed setup codec server result.1.1.2.transcript result.2 := by
  have zero : ∀ kind : Fin 9, kind = 1 ∨ kind = 2 ∨ kind = 5 →
      ((simulateQ (PqxdhDeploymentCompile.compileImpl setup codec route)
        ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds (.inr secrecy)).run
          ledger)).run copies).IsQueryBoundP
        (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inl kind) 0 := by
    intro kind owner
    have bound := FinitePartitionQueryBounds.weighted_bound PqxdhDeploymentCompileBudget.commandKind
      (PqxdhDeploymentCompileBudget.cost (.inl kind))
      (fun core => PqxdhDeploymentCompileSecrecy.wrapCost bounds core (PqxdhDeploymentInterface.queryClass
        (.inr secrecy)))
      (PqxdhDeploymentCompile.compileImpl setup codec route)
      (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inl kind) _
      (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto codec setup.serverKeyId bounds core
        (.inr secrecy) ledger)
      (fun query current => PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl kind) query current) copies
    have total : (∑ core, PqxdhDeploymentCompileBudget.cost (.inl kind) core *
        PqxdhDeploymentCompileSecrecy.wrapCost bounds core (PqxdhDeploymentInterface.queryClass (.inr secrecy))) = 0 := by
      rcases owner with rfl | rfl | rfl <;> rcases secrecy with ⟨handle, left, right⟩ | ⟨handle, length⟩ <;>
        simp [Fin.sum_univ_succ, PqxdhDeploymentCompileBudget.cost, PqxdhDeploymentCompileBudget.unit,
          PqxdhDeploymentCompileSecrecy.wrapCost, PqxdhDeploymentInterface.queryClass]
    rwa [total] at bound
  have kept := quiet_program setup codec checks seed identityIndex _ (zero 1 (Or.inl rfl)) (zero 2 (Or.inr (Or.inl rfl)))
    (zero 5 (Or.inr (Or.inr rfl))) state result supported
  have owned := program_owned setup codec checks seed identityIndex _ state signed.owned result supported
  have compiled : result.1 ∈ support ((simulateQ (PqxdhDeploymentCompile.compileImpl setup codec route)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds (.inr secrecy)).run
        ledger)).run copies) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex) _ state
    rw [StateT.run'_eq, support_map]
    exact ⟨result, supported, rfl⟩
  have recorded : result.1.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId
      bounds (.inr secrecy)).run ledger) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentCompile.compileImpl setup codec route) _ copies
    rw [StateT.run'_eq, support_map]
    exact ⟨result.1, compiled, rfl⟩
  rw [PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy ledger
    result.1.1 recorded]
  exact signed_quiet setup codec server ledger.transcript state result.2 _ signed kept owned rfl trivial trivial (by simp)

/-- One query of the complete interface, run through the secrecy layer, the compiler and the annotated Server schedule, keeps the invariant between the ledger's transcript and the joint source state. -/
theorem query_signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds) (seed : IdentitySeed)
    (identityIndex : Nat) (server : RawCtxServerRouting.Identity) (query : PqxdhDeploymentInterface.Query)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (copies : PqxdhDeploymentCompile.Local)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (signed : Signed setup codec server ledger.transcript state)
    (result : ((PqxdhDeploymentInterface.FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) ×
      PqxdhDeploymentCompile.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support (execution setup codec checks route bounds seed identityIndex
      (liftM (OracleSpec.query query)) ledger copies state)) :
    Signed setup codec server result.1.1.2.transcript result.2 := by
  simp only [execution, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map] at supported
  rcases query with native | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, simulateQ_map,
      StateT.run_map, support_map] at supported
    obtain ⟨step, stepMember, rfl⟩ := supported
    exact native_signed setup codec checks route seed identityIndex server ledger.transcript state signed native copies
      step stepMember
  · exact secrecy_signed setup codec checks route bounds seed identityIndex server ledger copies state signed secrecy
      result supported

/-- The invariant along the whole stacked execution of any complete-interface program. -/
theorem execution_signed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds) (seed : IdentitySeed)
    (identityIndex : Nat) (server : RawCtxServerRouting.Identity) (program : OracleComp PqxdhDeploymentInterface.FullSpec X) :
    ∀ (ledger : PqxdhDeploymentSecrecy.Ledger) (copies : PqxdhDeploymentCompile.Local)
      (state : PqxdhRegistrationJointSchedule.State KemSK), Signed setup codec server ledger.transcript state →
      ∀ result ∈ support (execution setup codec checks route bounds seed identityIndex program ledger copies state),
        Signed setup codec server result.1.1.2.transcript result.2 := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      intro ledger copies state signed result member
      simp only [execution, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact signed
  | query_bind query next ih =>
      intro ledger copies state signed result member
      rw [execution_bind, mem_support_bind_iff] at member
      obtain ⟨middle, first, rest⟩ := member
      exact ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2
        (query_signed setup codec checks route bounds seed identityIndex server query ledger copies state signed middle
          first) result rest

/-- Server birth records at most one identity creation, so it keeps every signing history. -/
theorem install_messages (created : PqxdhLiveServerConstruction.Created Unit)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (index : Nat) :
    messagesAt index (PqxdhRegistrationJointServerBirth.install created pool).1.transcript =
      messagesAt index pool.1.transcript := by
  unfold PqxdhRegistrationJointServerBirth.install
  split
  · exact record_messages _ _ _ (by intro selected message; simp) index
  · rfl

/-- The signing-history invariant on every outcome of the annotated initialized source execution of the compiled program of a deployment adversary, in either mode, from empty private pools: the experiment's final transcript (the ledger the compiled program returns) and its final joint source state with the private identity pool and its signing log satisfy `Signed` for the Server's identity. -/
theorem signed_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local)) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : outcome ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (result : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local))
    (reached : outcome.1 = some result) :
    Signed setup codec result.2.2.shared.2.server.server.identity result.2.1.1.2.transcript result.2.2 := by
  simp only [PqxdhRegistrationJointInitializedSchedule.source, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, bornMember, supported⟩ := supported
  rcases born with ⟨_ | created, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    simp only [Option.some.injEq] at reached
    subst reached
    have pool : after.1 = PqxdhRegistrationJointServerBirth.install created
        (PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty) := by
      simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, support_map, Set.mem_image] at bornMember
      obtain ⟨constructed, _, same⟩ := bornMember
      simp only [Prod.mk.injEq] at same
      obtain ⟨first, second⟩ := same
      rw [first] at second
      rw [← second]
    have initial : Signed setup codec
        (PqxdhDeploymentNative.initial (KemSK := KemSK) created).native.shared.2.server.server.identity []
        (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared) := by
      refine ⟨PqxdhDeploymentEligibility.agree_initial setup codec created,
        PqxdhRegistrationJointSchedule.initial_owned _ _, ?_, ?_, ?_, ?_⟩
      · intro first second firstEntry _ firstFound
        simp [PqxdhRegistrationJointSchedule.initial] at firstFound
      · intro index _
        change messagesAt index after.1.1.transcript = []
        rw [pool, install_messages]
        rfl
      · intro owner _
        exact ⟨rfl, rfl⟩
      · intro owner entry found
        simp [PqxdhRegistrationJointSchedule.initial] at found
    have final := execution_signed setup codec checks route bounds created.seed
      created.server.server.metadata.identityIndex _ (PqxdhDeploymentInterface.asModeO mode adversary)
      PqxdhDeploymentSecrecy.Ledger.empty PqxdhDeploymentCompile.Local.empty _ initial executed executedMember
    rw [← final.agree.identity] at final
    exact final

/-- The `NoBundleFailure` signing-history lemma (CE-7). On every outcome of the annotated initialized source execution of the compiled program of a deployment adversary, every owner without a rejected bundle call made in Fresh either published no bundle and signed nothing, or published exactly the Phase 1 writer output of the candidate it signed with its own identity key over one key tuple, and its whole chronological signing history is the three messages of that tuple. -/
theorem signing_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local)) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : outcome ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (result : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local))
    (reached : outcome.1 = some result) (owner : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK)
    (found : result.2.2.owners[owner]? = some entry)
    (clean : PqxdhDeploymentTranscript.NoBundleFailureAt result.2.1.1.2.transcript owner) :
    (PqxdhDeploymentTranscript.bundleOf result.2.1.1.2.transcript owner = none ∧
        messagesAt entry.identityIndex result.2.2.pool.1.transcript = []) ∨
      ∃ bytes keys, PqxdhDeploymentTranscript.bundleOf result.2.1.1.2.transcript owner = some bytes ∧
        codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint entry.owner.beacon.identity
          (setup.joint.publicKeys entry.owner.beacon.identity).ed25519 keys) = some bytes ∧
        messagesAt entry.identityIndex result.2.2.pool.1.transcript = PqxdhRegistrationJointIssuedAttempts.messages keys := by
  have signed := signed_source setup codec checks route ensureInit bounds mode adversary runtime outcome supported result
    reached
  rcases signed.history owner entry found clean with ⟨_, none, empty⟩ | ⟨_, bytes, keys, published, written, history⟩
  · exact Or.inl ⟨none, empty⟩
  · exact Or.inr ⟨bytes, keys, published, written, history⟩

end BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.kept_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.kept_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.kept_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.kept_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.record_messages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.record_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.accept_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.accept_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.finish_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.finish_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.read_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.read_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.quiet_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.quiet_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.ownerCommand_kind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.ownerCommand_kind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.quiet_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.quiet_program

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.execution_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.execution_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.bundleOf_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.bundleOf_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signed_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signed_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.trace_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.trace_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.program_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.program_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.joint_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.joint_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.agree_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.agree_request

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.forwarded_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.forwarded_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.kept_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.kept_alike

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signed_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signed_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.forwarded_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.forwarded_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.create_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.create_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.finish_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.finish_summary

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.finish_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.finish_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.bundleOf_bundle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.bundleOf_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signed_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signed_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.bundle_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.bundle_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.native_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.native_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.secrecy_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.secrecy_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.query_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.query_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.execution_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.execution_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.install_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.install_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signed_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signing_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory.signing_history
