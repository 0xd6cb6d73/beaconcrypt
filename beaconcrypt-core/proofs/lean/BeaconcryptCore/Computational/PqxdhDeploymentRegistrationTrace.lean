-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentReplay

/-! Registration trace of a source14 program (CE-9, first part). `traceFrom program log` runs any source14 program unchanged and logs the reply of every raw accept and every bundle call: the logging interpreter forwards each query once, so forgetting the log gives back the program (`traceFrom_erase`) and tagging commutes with the forgetful map (`tag_map`). The tag of a traced program at raw-accept ordinal `i` records exactly the `i`-th logged accept, with its bytes and reply (`tag_traceFrom`); these are facts of the program alone, for every reply. On the annotated initialized source execution that the KEM theorems are stated for, started from an empty KEM pool, every traced program ends with the invariant `Traced` (`traced_source`): the Server's session counter equals the number of logged raw accepts; a logged accept that returned a session handle returned its own raw-accept ordinal and its bytes pass the native verification prefix `RawSignatures.verified`; every logged successful bundle of owner `k` is a Phase 1 writer output whose key tuple carries the public key at KEM creation index `k` of the pool (`Pooled`), which holds when the bundle is produced, because the owner signs its live KEM pair, which ownership places at its creation index and the positional invariant `PqxdhDeploymentKemIndex.Positional` places at index `k`, and persists because the pool only appends; and positional KEM indices and slot ownership hold. `source_map` and `source_support` relate the initialized execution of a mapped program to that of the program. Only native semantics are used: no codec law, no assumption and no advantage term. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut scan)
open PqxdhRegistrationJointAcceptCutTag (Tag tag tagFinish)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result Next : Type}

/-- A registration reply of a source14 program: a raw accept with its bytes and public reply, or a bundle call with its owner handle and reply. -/
inductive Logged where
  | accept (raw : Pqxdh.Bytes) (reply : Option Nat)
  | bundle (owner : Nat) (reply : Option Pqxdh.Bytes)

/-- Append the registration reply of one source14 query to a log; every other query leaves the log unchanged. -/
def record : (query : (Spec KemSK).Domain) → (Spec KemSK).Range query → List Logged → List Logged
  | .inl (.inr (.accept raw)), reply, log => log ++ [.accept raw reply]
  | .inl (.inr (.bundle owner)), reply, log => log ++ [.bundle owner reply]
  | _, _, log => log

/-- The logging interpreter: every query is forwarded once and unchanged, and its registration reply is appended to the log. -/
def logImpl : QueryImpl (Spec KemSK) (StateT (List Logged) (OracleComp (Spec KemSK))) := fun query log =>
  (fun reply => (reply, record query reply log)) <$> ((Spec KemSK).query query : OracleComp (Spec KemSK) _)

/-- A source14 program run under the logging interpreter from a starting log. It issues exactly the program's queries. -/
def traceFrom (program : OracleComp (Spec KemSK) Result) (log : List Logged) :
    OracleComp (Spec KemSK) (Result × List Logged) :=
  (simulateQ logImpl program).run log

/-- The logged raw accepts with their bytes and replies, in raw-accept order. -/
def acceptsOf (log : List Logged) : List (Pqxdh.Bytes × Option Nat) :=
  log.filterMap fun event => match event with
    | .accept raw reply => some (raw, reply)
    | .bundle _ _ => none

/-- A traced query is the query itself followed by the traced continuation from the extended log. -/
theorem traceFrom_query_bind (query : (Spec KemSK).Domain) (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result)
    (log : List Logged) :
    traceFrom (((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= next) log =
      ((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= fun reply => traceFrom (next reply) (record query reply log) := by
  simp only [traceFrom, simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    StateT.run]
  rfl

/-- Forgetting the log gives back the program. -/
theorem traceFrom_erase (program : OracleComp (Spec KemSK) Result) (log : List Logged) :
    Prod.fst <$> traceFrom program log = program := by
  induction program using OracleComp.inductionOn generalizing log with
  | pure value => simp [traceFrom]
  | query_bind query next ih =>
      rw [traceFrom_query_bind, map_bind]
      simp only [ih]

/-- The raw-accept scan stops at an accept when the remaining ordinal is zero. -/
theorem scan_accept_zero (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result) :
    scan (((Spec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (Spec KemSK) _) >>= next) 0 =
      pure (.pending raw next) := rfl

/-- The raw-accept scan forwards an accept and decreases the remaining ordinal. -/
theorem scan_accept_succ (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result) (index : Nat) :
    scan (((Spec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (Spec KemSK) _) >>= next) (index + 1) =
      ((Spec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (Spec KemSK) _) >>= fun answer =>
        scan (next answer) index := rfl


/-- A query other than a raw accept is forwarded by the scan without moving the cut. -/
theorem scan_other (query : (Spec KemSK).Domain) (other : ∀ raw, query ≠ .inl (.inr (.accept raw)))
    (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result) (index : Nat) :
    scan (((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= next) index =
      ((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= fun answer => scan (next answer) index := by
  rcases query with (coin | request) | read
  · rfl
  · cases request with
    | accept raw => exact absurd rfl (other raw)
    | _ => rfl
  · rfl

/-- A query other than a raw accept adds no accept to the log. -/
theorem acceptsOf_record_other (query : (Spec KemSK).Domain) (other : ∀ raw, query ≠ .inl (.inr (.accept raw)))
    (reply : (Spec KemSK).Range query) (log : List Logged) :
    acceptsOf (record query reply log) = acceptsOf log := by
  rcases query with (coin | request) | read
  · rfl
  · cases request with
    | accept raw => exact absurd rfl (other raw)
    | bundle owner => simp [record, acceptsOf]
    | _ => rfl
  · rfl

/-- The log of a traced run extends its starting log. -/
theorem traceFrom_prefix (program : OracleComp (Spec KemSK) Result) (log : List Logged)
    (outcome : Result × List Logged) (reached : outcome ∈ support (traceFrom program log)) : log <+: outcome.2 := by
  induction program using OracleComp.inductionOn generalizing log with
  | pure value =>
      simp only [traceFrom, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact List.prefix_refl _
  | query_bind query next ih =>
      rw [traceFrom_query_bind, mem_support_bind_iff] at reached
      obtain ⟨reply, _, reached⟩ := reached
      have later := ih reply (record query reply log) reached
      refine List.IsPrefix.trans ?_ later
      rcases query with (coin | request) | read
      · exact List.prefix_refl _
      · cases request with
        | accept raw => exact List.prefix_append _ _
        | bundle owner => exact List.prefix_append _ _
        | _ => exact List.prefix_refl _
      · exact List.prefix_refl _

/-- The scan of a finished program is complete. -/
theorem scan_pure (value : Result) (index : Nat) :
    scan (pure value : OracleComp (Spec KemSK) Result) index = pure (.complete value) := rfl

/-- The tag of a finished program records nothing. -/
theorem tag_pure (value : Result) (index : Nat) :
    tag (pure value : OracleComp (Spec KemSK) Result) index = pure (value, none) := by
  simp only [tag, scan_pure, pure_bind, tagFinish]

/-- At the selected ordinal the tag issues the accept and records its bytes and reply. -/
theorem tag_accept_zero (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result) :
    tag (((Spec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (Spec KemSK) _) >>= next) 0 =
      ((Spec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (Spec KemSK) _) >>= fun answer =>
        (fun result => (result, some (raw, answer))) <$> next answer := by
  simp only [tag, scan_accept_zero, pure_bind, tagFinish]

/-- Before the selected ordinal an accept is forwarded and the ordinal decreases. -/
theorem tag_accept_succ (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result) (index : Nat) :
    tag (((Spec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (Spec KemSK) _) >>= next) (index + 1) =
      ((Spec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (Spec KemSK) _) >>= fun answer =>
        tag (next answer) index := by
  simp only [tag, scan_accept_succ, bind_assoc]

/-- A query other than a raw accept is forwarded by the tag without moving the ordinal. -/
theorem tag_other (query : (Spec KemSK).Domain) (other : ∀ raw, query ≠ .inl (.inr (.accept raw)))
    (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result) (index : Nat) :
    tag (((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= next) index =
      ((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= fun answer => tag (next answer) index := by
  simp only [tag, scan_other query other, bind_assoc]

/-- Tagging commutes with a map of the program's result. -/
theorem tag_map (f : Result → Next) (program : OracleComp (Spec KemSK) Result) (index : Nat) :
    tag (f <$> program) index = (fun outcome => (f outcome.1, outcome.2)) <$> tag program index := by
  induction program using OracleComp.inductionOn generalizing index with
  | pure value => simp only [map_pure, tag_pure]
  | query_bind query next ih =>
      rw [map_bind]
      by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
      · obtain ⟨raw, rfl⟩ := accept
        cases index with
        | zero => simp only [tag_accept_zero, map_bind, Functor.map_map]
        | succ index => simp only [tag_accept_succ, map_bind, ih]
      · have other : ∀ raw, query ≠ .inl (.inr (.accept raw)) := fun raw same => accept ⟨raw, same⟩
        simp only [tag_other query other, map_bind, ih]

/-- The tag of a traced run records the accept at the selected raw-accept ordinal of the log. -/
theorem tag_traceFrom (program : OracleComp (Spec KemSK) Result) (log : List Logged) (index : Nat)
    (outcome : (Result × List Logged) × Tag) (reached : outcome ∈ support (tag (traceFrom program log) index)) :
    outcome.2 = (acceptsOf outcome.1.2)[(acceptsOf log).length + index]? := by
  induction program using OracleComp.inductionOn generalizing log index with
  | pure value =>
      simp only [traceFrom, simulateQ_pure, StateT.run_pure, tag_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      simp
  | query_bind query next ih =>
      rw [traceFrom_query_bind] at reached
      by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
      · obtain ⟨raw, rfl⟩ := accept
        cases index with
        | zero =>
            rw [tag_accept_zero, mem_support_bind_iff] at reached
            obtain ⟨answer, _, reached⟩ := reached
            rw [support_map] at reached
            obtain ⟨result, member, rfl⟩ := reached
            have extended := traceFrom_prefix _ _ result member
            obtain ⟨rest, same⟩ := extended
            simp only [record] at same
            simp only [← same, acceptsOf, List.filterMap_append, List.append_assoc, Nat.add_zero]
            simp
        | succ index =>
            rw [tag_accept_succ, mem_support_bind_iff] at reached
            obtain ⟨answer, _, reached⟩ := reached
            have later := ih answer (record _ answer log) index reached
            rw [later]
            congr 1
            simp only [record, acceptsOf, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
              List.length_append, List.length_singleton]
            omega
      · have other : ∀ raw, query ≠ .inl (.inr (.accept raw)) := fun raw same => accept ⟨raw, same⟩
        rw [tag_other query other, mem_support_bind_iff] at reached
        obtain ⟨answer, _, reached⟩ := reached
        rw [ih answer (record query answer log) index reached, acceptsOf_record_other query other]


/-- A result of a traced program, without its log, is a result of the program. -/
theorem traceFrom_support (program : OracleComp (Spec KemSK) Result) (log : List Logged)
    (outcome : Result × List Logged) (reached : outcome ∈ support (traceFrom program log)) : outcome.1 ∈ support program := by
  rw [← traceFrom_erase program log, support_map]
  exact ⟨outcome, reached, rfl⟩

/-- The tag of a program traced from the empty log records its logged accept at the selected raw-accept ordinal. -/
theorem tag_traced (program : OracleComp (Spec KemSK) Result) (index : Nat) (outcome : (Result × List Logged) × Tag)
    (reached : outcome ∈ support (tag (traceFrom program []) index)) :
    outcome.2 = (acceptsOf outcome.1.2)[index]? := by
  simpa [acceptsOf] using tag_traceFrom program [] index outcome reached

/-- Every annotated source step keeps the KEM key list as a prefix: only a Beacon creation appends a key. -/
theorem keys_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (result : (Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      query).run state)) :
    state.pool.2.keys <+: result.2.pool.2.keys := by
  have sharedKept : ∀ {Value : Type} (work : NativeGame KemSK Value)
      (reached : Value × PqxdhRegistrationJointSchedule.State KemSK),
      reached ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state) →
        state.pool.2.keys <+: reached.2.pool.2.keys := by
    intro Value work reached member
    simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact List.prefix_refl _
  rcases query with (coin | request) | ⟨index, field⟩
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      PqxdhRegistrationJointSchedule.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact List.prefix_refl _
  · cases request with
    | create pin keyId =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create, StateT.run, support_map,
          Set.mem_image] at supported
        obtain ⟨material, _, rfl⟩ := supported
        simp [PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointCreation.serviceView,
          PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record]
    | bundle address =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle, StateT.run] at supported
        split at supported
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact List.prefix_refl _
        · simp only [support_map, Set.mem_image] at supported
          obtain ⟨_, _, rfl⟩ := supported
          exact List.prefix_refl _
    | accept raw =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointServerSchedule.onBackend,
          StateT.run, support_map, Set.mem_image] at supported
        obtain ⟨accepted, acceptedMember, rfl⟩ := supported
        have keys := PqxdhDeploymentKemIndex.accept_keys setup codec checks seed identityIndex raw (state.pool, state.shared)
          accepted acceptedMember
        simp only [keys]
        exact List.prefix_refl _
    | build session payload => exact sharedKept _ result supported
    | finish address raw =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish, StateT.run] at supported
        split at supported
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact List.prefix_refl _
        · rename_i entry found
          simp only [support_map, Set.mem_image] at supported
          obtain ⟨finished, finishedMember, rfl⟩ := supported
          have keys := PqxdhDeploymentKemIndex.finish_keys setup codec entry.identityIndex entry.kemIndex raw entry.owner
            (state.pool, state.shared) finished finishedMember
          simp only [keys]
          exact List.prefix_refl _
    | hmac key message => exact sharedKept _ result supported
    | hash bytes => exact sharedKept _ result supported
    | reveal keyId => exact sharedKept _ result supported
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source, StateT.run,
      support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp only [PqxdhRegistrationJointLiveRead.sourceStep]
    split
    · exact List.prefix_refl _
    · cases field with
      | kem =>
          simp only [PqxdhRegistrationJointLiveRead.entrySource]
          split
          · exact List.prefix_refl _
          · exact List.prefix_refl _
      | _ => exact List.prefix_refl _


/-- A native raw accept advances the session counter by one; a successful one returns the counter before the call, and its bytes pass the native verification prefix `RawSignatures.verified`. -/
theorem nativeAccept_session (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (state : NativeState KemSK) (result : Option Nat × NativeState KemSK)
    (supported : result ∈ support ((nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar
      raw).run state)) :
    result.2.2.sessions = state.2.sessions + 1 ∧ ∀ session, result.1 = some session →
      session = state.2.sessions ∧ ∃ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value := by
  have original := evaluate_support setup seed PqxdhRegistrationSchedule.observationScalar _ state result (by
    rw [accept_native]
    exact supported)
  obtain ⟨_, _, sessions, _, _, accepted⟩ := PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks _ raw
    state.2 (result.1, result.2.2) original
  refine ⟨sessions, fun session returned => ⟨(accepted session returned).1, ?_⟩⟩
  obtain ⟨input, consumed, collected⟩ := PqxdhRegistrationJointRawSignatures.accept_prefix setup codec checks seed raw
    state result.2 session (by rw [← returned]; exact supported)
  simp only [PqxdhServerAuthNative.nativePrefix, PqxdhServerRootPreparation.collect, simulateQ_bind,
    StateT.run_bind] at collected
  rw [PqxdhRegistrationJointRawSignatures.verifyInput_source] at collected
  simp only [pure_bind] at collected
  cases checked : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
  | none =>
      simp only [checked, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        Option.some_ne_none, false_and] at collected
  | some value => exact ⟨value, rfl⟩

/-- A native source14 command other than a raw accept keeps the session counter. -/
theorem native_sessions (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (Spec KemSK).Domain) (other : ∀ raw, query ≠ .inl (.inr (.accept raw)))
    (state : PqxdhRegistrationSchedule.State KemSK)
    (result : (Spec KemSK).Range query × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query).run
      state)) :
    result.2.shared.2.sessions = state.shared.2.sessions := by
  rcases query with request | read
  · have upper := PqxdhRegistrationSchedule.handler_sessions setup codec checks seed request state result supported
    have lower := PqxdhRegistrationSchedule.server_relation setup codec checks seed
      (fun before after => before.sessions ≤ after.sessions) (fun _ _ => le_refl _)
      (fun original before after member =>
        (authHandler_step (Reader := Reader) (Response := Response) codec checks seed original before after member).2.1.sessions)
      request state result supported
    have notAccept : ¬PqxdhRegistrationSchedule.IsAccept request := by
      rcases request with coin | command
      · simp [PqxdhRegistrationSchedule.IsAccept, PqxdhRegistrationSchedule.serverLabel]
      · cases command with
        | accept raw => exact absurd rfl (other raw)
        | _ => simp [PqxdhRegistrationSchedule.IsAccept, PqxdhRegistrationSchedule.serverLabel, IsAcceptQuery]
    simp only [notAccept, ite_false, Nat.add_zero] at upper
    exact le_antisymm upper lower
  · simp only [PqxdhRegistrationJointRevealSchedule.native, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl


/-- An annotated source step projects to the native step on the same shared state. -/
theorem source_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (result : (Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      query).run state)) :
    (result.1, PqxdhRegistrationJointSchedule.source result.2) ∈ support
      ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query).run
        (PqxdhRegistrationJointSchedule.source state)) := by
  rw [← PqxdhRegistrationJointServerSchedule.query_native setup codec checks seed identityIndex query state, support_map]
  exact ⟨result, supported, rfl⟩

/-- The KEM pool's key at creation index `k` is the PQ key of the key tuple of a Phase 1 writer output `bytes`. -/
def Pooled (codec : Codec Reader Response) (k : Nat) (bytes : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointSchedule.State KemSK) : Prop :=
  ∃ (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (keys : PqxdhEd25519EufCma.Phase1KeyTuple)
    (preSignature oneSignature pqSignature : PqxdhEd25519EufCma.Ed25519Signature),
    codec.write1 (PqxdhJointPhase1SourceWriter.candidate identity keys preSignature oneSignature pqSignature) = some bytes ∧
      (state.pool.2.keys[k]?).map Prod.fst = some keys.pqKey

/-- A published bundle trace signs the owner's live KEM public key. -/
theorem trace_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhDynamicIdentityPool.SourceState)
    (supported : result ∈ support (PqxdhRegistrationJointBundle.trace setup codec identityIndex owner pool))
    (bytes : Pqxdh.Bytes) (published : result.1.1 = some bytes) :
    ∃ (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (keys : PqxdhEd25519EufCma.Phase1KeyTuple), PqxdhRegistrationJointOwnership.activeKey owner = some kem ∧
      keys.pqKey = kem.1 ∧ codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint owner.beacon.identity
        (setup.joint.publicKeys owner.beacon.identity).ed25519 keys) = some bytes := by
  have after : ∀ generated, (PqxdhRegistrationJointBundle.after setup codec identityIndex owner generated pool).1.1 =
      some bytes → ∃ (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (keys : PqxdhEd25519EufCma.Phase1KeyTuple),
        PqxdhRegistrationJointOwnership.activeKey owner = some kem ∧ keys.pqKey = kem.1 ∧
        codec.write1 (PqxdhJointPhase1SourceWriter.signedCandidate setup.joint owner.beacon.identity
          (setup.joint.publicKeys owner.beacon.identity).ed25519 keys) = some bytes := by
    intro generated returned
    unfold PqxdhRegistrationJointBundle.after at returned
    cases prepared : PqxdhBeaconPhase1Publication.prepare owner generated with
    | none => simp only [prepared] at returned; cases returned
    | some ready =>
        simp only [prepared] at returned
        have active : PqxdhRegistrationJointOwnership.activeKey owner = some ready.kem := by
          unfold PqxdhBeaconPhase1Publication.prepare at prepared
          unfold PqxdhRegistrationJointOwnership.activeKey
          cases phase : owner.beacon.phase with
          | fresh control prekey kem =>
              simp only [phase] at prepared
              cases generated with
              | none => cases prepared
              | some oneTime =>
                  simp only [Option.map_some, Option.some.injEq] at prepared
                  subst prepared
                  rfl
          | freshWithCoins control prekey oneTime kem =>
              simp only [phase, Option.some.injEq] at prepared
              subst prepared
              rfl
          | _ => simp only [phase] at prepared; cases prepared
        refine ⟨ready.kem, ⟨setup.dh.publicKey ready.prekey, setup.dh.publicKey ready.oneTime, ready.kem.1⟩, active,
          rfl, ?_⟩
        split at returned
        · cases returned
        · rename_i written writtenEq
          simp only [Option.some.injEq] at returned
          rw [writtenEq, returned]
  unfold PqxdhRegistrationJointBundle.trace at supported
  split at supported
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨scalar, _, rfl⟩ := supported
    exact after (some scalar) published
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact after none published
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases published

/-- A successful annotated bundle call of owner `address` returns a Phase 1 writer output whose PQ key is the pool key at creation index `address`, under ownership and positional KEM indices. -/
theorem bundle_pooled (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (address : Nat) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (owned : PqxdhRegistrationJointSchedule.Invariant state) (positional : PqxdhDeploymentKemIndex.Positional state)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      (.inl (.inr (.bundle address)))).run state)) (bytes : Pqxdh.Bytes) (published : result.1 = some bytes) :
    Pooled codec address bytes result.2 := by
  simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
    PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle, StateT.run] at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases published
  · rename_i entry found
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨traced, member, rfl⟩ := supported
    obtain ⟨kem, keys, active, pq, written⟩ := trace_published setup codec entry.identityIndex entry.owner state.pool.1
      traced member bytes published
    have pool := (owned entry (List.mem_of_getElem? found)).2 kem active
    rw [positional.2 address entry found] at pool
    refine ⟨_, keys, _, _, _, written, ?_⟩
    simp only [pool, Option.map_some, pq]


/-- `Pooled` survives any extension of the KEM key list. -/
theorem pooled_extend (codec : Codec Reader Response) (k : Nat) (bytes : Pqxdh.Bytes)
    (before after : PqxdhRegistrationJointSchedule.State KemSK) (pooled : Pooled codec k bytes before)
    (extended : before.pool.2.keys <+: after.pool.2.keys) : Pooled codec k bytes after := by
  obtain ⟨identity, keys, s1, s2, s3, written, found⟩ := pooled
  obtain ⟨pair, pairFound, same⟩ := Option.map_eq_some_iff.mp found
  refine ⟨identity, keys, s1, s2, s3, written, ?_⟩
  rw [PqxdhRegistrationJointKemRawBridge.prefix_lookup extended pairFound, Option.map_some, same]

/-- A query that is neither a raw accept nor a bundle call leaves the log unchanged. -/
theorem record_other (query : (Spec KemSK).Domain) (notAccept : ∀ raw, query ≠ .inl (.inr (.accept raw)))
    (notBundle : ∀ owner, query ≠ .inl (.inr (.bundle owner))) (reply : (Spec KemSK).Range query) (log : List Logged) :
    record query reply log = log := by
  rcases query with (coin | request) | read
  · rfl
  · cases request with
    | accept raw => exact absurd rfl (notAccept raw)
    | bundle owner => exact absurd rfl (notBundle owner)
    | _ => rfl
  · rfl

/-- The run invariant between the registration log of a traced program and the annotated source state: the Server's session counter counts the logged raw accepts, a logged accept that returned a session handle returned its own raw-accept ordinal and has bytes that pass the native verification prefix, every logged successful bundle of owner `k` carries the PQ key at KEM creation index `k` of the pool, and the positional KEM indices and slot ownership hold. -/
structure Traced (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (log : List Logged) (state : PqxdhRegistrationJointSchedule.State KemSK) : Prop where
  sessions : state.shared.2.sessions = (acceptsOf log).length
  positional : ∀ (position : Nat) (raw : Pqxdh.Bytes) (session : Nat),
    (acceptsOf log)[position]? = some (raw, some session) → session = position
  verified : ∀ (raw : Pqxdh.Bytes) (session : Nat), (raw, some session) ∈ acceptsOf log →
    ∃ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value
  bundles : ∀ (k : Nat) (bytes : Pqxdh.Bytes), Logged.bundle k (some bytes) ∈ log → Pooled codec k bytes state
  kem : PqxdhDeploymentKemIndex.Positional state
  owned : PqxdhRegistrationJointSchedule.Invariant state

/-- One annotated source step keeps the invariant, with its registration reply appended to the log. -/
theorem traced_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain) (log : List Logged)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (traced : Traced setup codec checks log state)
    (result : (Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      query).run state)) :
    Traced setup codec checks (record query result.1 log) result.2 := by
  have keys := keys_step setup codec checks seed identityIndex query state result supported
  have kem := PqxdhDeploymentKemIndex.positional_step setup codec checks seed identityIndex query state traced.kem result
    supported
  have owned := PqxdhRegistrationJointServerSchedule.query_owned setup codec checks seed identityIndex query state result
    traced.owned supported
  have native := source_native setup codec checks seed identityIndex query state result supported
  have oldBundles : ∀ k bytes, Logged.bundle k (some bytes) ∈ log → Pooled codec k bytes result.2 :=
    fun k bytes member => pooled_extend codec k bytes state result.2 (traced.bundles k bytes member) keys
  by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
  · obtain ⟨raw, rfl⟩ := accept
    change (result.1, PqxdhRegistrationJointSchedule.source result.2) ∈ support
      ((PqxdhRegistrationSchedule.onShared (nativeAccept setup codec checks seed
        PqxdhRegistrationSchedule.observationScalar raw)).run (PqxdhRegistrationJointSchedule.source state)) at native
    rw [PqxdhRegistrationSchedule.onShared_run, support_map] at native
    obtain ⟨reached, member, same⟩ := native
    simp only [Prod.mk.injEq] at same
    obtain ⟨replyEq, stateEq⟩ := same
    have sharedEq : result.2.shared = reached.2 := by
      have := congrArg PqxdhRegistrationSchedule.State.shared stateEq
      exact this.symm
    obtain ⟨sessions, returned⟩ := nativeAccept_session setup codec checks seed raw _ reached member
    have accepts : acceptsOf (record (.inl (.inr (.accept raw))) result.1 log) =
        acceptsOf log ++ ([(raw, result.1)] : List (Pqxdh.Bytes × Option Nat)) := by
      simp [record, acceptsOf]
    refine ⟨?_, ?_, ?_, ?_, kem, owned⟩
    · rw [accepts, List.length_append, List.length_singleton, sharedEq, sessions, ← traced.sessions]
      rfl
    · intro position raw' session found
      rw [accepts, List.getElem?_append] at found
      split at found
      · exact traced.positional position raw' session found
      · rename_i outside
        rw [List.getElem?_singleton] at found
        split at found
        · rename_i zero
          simp only [Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨_, returnedEq⟩ := found
          have := (returned session (by rw [← replyEq] at returnedEq; exact returnedEq)).1
          rw [this]
          change state.shared.2.sessions = position
          rw [traced.sessions]
          omega
        · cases found
    · intro raw' session member
      rw [accepts, List.mem_append, List.mem_singleton] at member
      rcases member with old | new
      · exact traced.verified raw' session old
      · simp only [Prod.mk.injEq] at new
        obtain ⟨rfl, returnedEq⟩ := new
        exact (returned session (by rw [← replyEq] at returnedEq; exact returnedEq.symm)).2
    · intro k bytes member
      simp only [record, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at member
      exact oldBundles k bytes member
  · have notAccept : ∀ raw, query ≠ .inl (.inr (.accept raw)) := fun raw same => accept ⟨raw, same⟩
    have sessions := native_sessions setup codec checks seed query notAccept _ _ native
    have accepts := acceptsOf_record_other query notAccept result.1 log
    refine ⟨?_, ?_, ?_, ?_, kem, owned⟩
    · rw [accepts, ← traced.sessions]
      exact sessions
    · rw [accepts]
      exact traced.positional
    · rw [accepts]
      exact traced.verified
    · by_cases bundle : ∃ address, query = .inl (.inr (.bundle address))
      · obtain ⟨address, rfl⟩ := bundle
        intro k bytes member
        simp only [record, List.mem_append, List.mem_singleton, Logged.bundle.injEq] at member
        rcases member with old | ⟨rfl, returned⟩
        · exact oldBundles k bytes old
        · exact bundle_pooled setup codec checks seed identityIndex k state traced.owned traced.kem result supported
            bytes returned.symm
      · have notBundle : ∀ owner, query ≠ .inl (.inr (.bundle owner)) := fun owner same => bundle ⟨owner, same⟩
        rw [record_other query notAccept notBundle]
        exact oldBundles


/-- The annotated source execution of a traced program keeps the invariant from any start. -/
theorem traced_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result) (log : List Logged)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (traced : Traced setup codec checks log state)
    (result : (Result × List Logged) × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex) (traceFrom program log)).run state)) :
    Traced setup codec checks result.1.2 result.2 := by
  induction program using OracleComp.inductionOn generalizing log state with
  | pure value =>
      simp only [traceFrom, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact traced
  | query_bind query next ih =>
      rw [traceFrom_query_bind] at supported
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
      exact ih reply (record query reply log) middle
        (traced_step setup codec checks seed identityIndex query log state traced (reply, middle) first) second

/-- Every completed initialized annotated execution of a traced program from an empty KEM pool ends with the invariant on its final log and final source state, whose pool is the execution's final pool. -/
theorem traced_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (empty : state.1.2.keys = [])
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK (Result × List Logged))
    (supported : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks
      ensureInit supplied (traceFrom program [])).run state)) :
    Traced setup codec checks outcome.2.1.2 outcome.2.2 ∧ after.1 = outcome.2.2.pool := by
  simp only [PqxdhRegistrationJointInitializedSchedule.source, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨_ | created, bornState⟩, born, reached⟩ := supported
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at reached
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at reached
    obtain ⟨finished, member, rfl, rfl⟩ := reached
    have bornKeys : bornState.1.2.keys = [] := by
      simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, support_map, Set.mem_image] at born
      obtain ⟨constructed, _, same⟩ := born
      simp only [Prod.mk.injEq] at same
      obtain ⟨wasCreated, rfl⟩ := same
      rw [wasCreated]
      simp only [PqxdhRegistrationJointServerBirth.install]
      exact empty
    have start : Traced setup codec checks [] (PqxdhRegistrationJointSchedule.initial bornState.1
        (PqxdhRegistrationSchedule.initial created).shared) :=
      ⟨rfl, fun _ _ _ found => by simp [acceptsOf] at found, fun _ _ member => by simp [acceptsOf] at member,
        fun _ _ member => by simp at member,
        ⟨by simp [PqxdhRegistrationJointSchedule.initial, bornKeys], fun _ _ found => by
          simp [PqxdhRegistrationJointSchedule.initial] at found⟩,
        PqxdhRegistrationJointSchedule.initial_owned _ _⟩
    exact ⟨traced_run setup codec checks created.seed _ program [] _ start finished member, rfl⟩


/-- The initialized annotated execution of a mapped program is the execution of the program with its result mapped. -/
theorem source_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (f : Result → Next)
    (program : OracleComp (Spec KemSK) Result) (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (f <$> program)).run state =
      (fun result => (result.1.map fun outcome => (outcome.1, f outcome.2.1, outcome.2.2), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run state := by
  simp only [PqxdhRegistrationJointInitializedSchedule.source, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp
  · simp only [simulateQ_map]
    change _ <$> (f <$> _ : StateT _ ProbComp _).run _ = _
    rw [StateT.run_map, Functor.map_map, Functor.map_map]
    rfl

/-- The result of a completed initialized annotated execution is a result of the program. -/
theorem source_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result)
    (supported : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks
      ensureInit supplied program).run state)) :
    outcome.2.1 ∈ support program := by
  simp only [PqxdhRegistrationJointInitializedSchedule.source, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨_ | created, born⟩, _, reached⟩ := supported
  · simp at reached
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at reached
    obtain ⟨finished, member, rfl, _⟩ := reached
    apply support_simulateQ_run'_subset (PqxdhRegistrationJointServerSchedule.source setup codec checks created.seed
      created.server.server.metadata.identityIndex) program _
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ member

end BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traceFrom_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traceFrom_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traceFrom_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traceFrom_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.scan_accept_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.scan_accept_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.scan_accept_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.scan_accept_succ

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.scan_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.scan_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.acceptsOf_record_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.acceptsOf_record_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traceFrom_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traceFrom_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.scan_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.scan_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_accept_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_accept_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_accept_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_accept_succ

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_traceFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_traceFrom

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traceFrom_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traceFrom_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_traced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.tag_traced

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.keys_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.keys_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.nativeAccept_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.nativeAccept_session

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.native_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.native_sessions

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.source_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.source_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.trace_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.trace_published

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.bundle_pooled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.bundle_pooled

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.pooled_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.pooled_extend

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.record_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.record_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traced_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traced_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traced_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traced_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traced_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.traced_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.source_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.source_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.source_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace.source_support
