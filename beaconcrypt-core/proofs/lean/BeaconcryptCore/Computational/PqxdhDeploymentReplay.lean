-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentKemIndex
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleLedger

/-! Registration replay in the common deployment experiment (CE-6, CE-R1). The experiment has one live Server object. Its consumed list grows only at successful accepts, and `accept_registration` shows, from the native accept code, that a successful accept appends the registration ID of its raw bytes, which was absent before, while a rejected accept leaves the list unchanged. The registration ID is read from public bytes: the identity key followed by the one-time key that the codec reader and the source attached verification of the setup's crypto yield from the raw candidate (`registrationOf`), which is the exact identity/one-time pair the native code consumes. Every other registration, record and secrecy command leaves the list unchanged (`handler_other`, `coinSend_consumed`). Hence `registered_game`: on every outcome of the experiment, in either mode, the consumed list is exactly the duplicate-free list of registration IDs of the successful accepts in the transcript, and `replay_game` (CE-R1): every registration ID is carried by at most one successful accept. The statements are deterministic, hold for every adversary with no budget, and use no codec law and no security assumption. Replay across several Server objects is outside this experiment, which has one. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentReplay
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerRootPreparation (Inputs registrationId collect)
open PqxdhDeploymentInterface (Spec Command FullSpec ModeSpec Mode Entry FreshBounds parsePin asModeO)
open PqxdhDeploymentTranscript (candidateOf acceptedKeys)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The registration ID of raw accept bytes, read from public bytes only: the identity key followed by the one-time key that the source attached verification of `crypto` yields from the raw candidate. -/
def registrationOf (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (raw : Pqxdh.Bytes) : Option Pqxdh.Bytes :=
  ((candidateOf codec raw).bind (acceptedKeys crypto)).map fun keys => keys.1.toList ++ keys.2.oneTime.toList

/-- The registration ID of a transcript entry: that of a successful accept, and none for every other entry. -/
def entryRegistration (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) : Entry → Option Pqxdh.Bytes
  | ⟨.inl (.inr (.accept raw)), some _⟩ => registrationOf crypto codec raw
  | _ => none

/-- The registration IDs of the successful accepts of a transcript, oldest first. -/
def acceptIds (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (transcript : List Entry) : List Pqxdh.Bytes :=
  transcript.filterMap (entryRegistration crypto codec)

/-- Every successful ServerAuth-level raw admission appends the registration ID of a verified input of its own native preparation, which was absent before; a rejected admission leaves the consumed list unchanged. -/
theorem accept_oracle_registration (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (state : GameState KemSK) (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    (result.1 = none ∧ result.2.server.consumed = state.server.consumed) ∨
      ∃ index input after, (some input, after) ∈ support ((serverPrefix setup codec checks raw).run state.server.consumed) ∧
        result.1 = some index ∧ registrationId input.verified ∉ state.server.consumed ∧
        result.2.server.consumed = state.server.consumed ++ [registrationId input.verified] := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨collectedMember, same⟩ := liftCoins_mem _ _ _ lifted
  have preserved := PqxdhRegistrationAdmission.prefix_program_preserves setup codec checks (collect raw)
    state.server.consumed collected.1 collectedMember
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact Or.inl ⟨rfl, preserved⟩
  | some input =>
      have reached : (some input, collected.1.2) ∈ support ((serverPrefix setup codec checks raw).run state.server.consumed) := by
        simpa only [← hc] using collectedMember
      have fresh := PqxdhRegistrationAdmission.prefix_fresh setup codec checks raw state.server.consumed collected.1.2 input
        reached
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      have changed := PqxdhRegistrationAdmission.client_consumed state.sessions (binding setup publicValue) input _ returned
        derived
      obtain ⟨_, _, _, _, tokenFields⟩ := client_run state.sessions (binding setup publicValue) input _ returned derived
      rcases returned with ⟨outcome, after⟩
      dsimp only at changed tokenFields
      rcases outcome with (_ | token) | error | _
      all_goals simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      all_goals subst supported
      · exact Or.inl ⟨rfl, changed.trans preserved⟩
      · have fields := (tokenFields token rfl).2.2
        have bytes := (congrArg (fun pending => PqxdhRefinement.absBytes pending.registration_id.bytes) fields).trans
          (PqxdhRegistrationAdmission.pending_registration_bytes (binding setup publicValue) input)
        refine Or.inr ⟨state.sessions, input, collected.1.2, reached, rfl, fresh, ?_⟩
        rw [changed, preserved]
        dsimp only
        rw [bytes]
      · exact Or.inl ⟨rfl, changed.trans preserved⟩
      · exact Or.inl ⟨rfl, changed.trans preserved⟩

/-- Every successful native raw accept appends the public registration ID of its raw bytes, which was absent from the live Server object's consumed list before; a rejected accept leaves the list unchanged. The registration ID is computed from the raw bytes by the codec reader and the source attached verification only. -/
theorem accept_registration (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (state : NativeState KemSK) (result : Option Nat × NativeState KemSK)
    (supported : result ∈ support ((nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar
      raw).run state)) :
    (result.1 = none ∧ result.2.2.server.consumed = state.2.server.consumed) ∨
      ∃ index rid, result.1 = some index ∧ registrationOf setup.source.crypto codec raw = some rid ∧
        rid ∉ state.2.server.consumed ∧ result.2.2.server.consumed = state.2.server.consumed ++ [rid] := by
  have original := accept_oracle_registration setup codec checks
    (challenge setup.joint setup.dh seed PqxdhRegistrationSchedule.observationScalar) raw state.2 (result.1, result.2.2)
    (evaluate_support setup seed PqxdhRegistrationSchedule.observationScalar _ state result (by
      rw [accept_native]
      exact supported))
  rcases original with ⟨rejected, same⟩ | ⟨index, input, after, reached, returned, fresh, changed⟩
  · exact Or.inl ⟨rejected, same⟩
  · refine Or.inr ⟨index, registrationId input.verified, returned, ?_, fresh, changed⟩
    have native : (some (PqxdhServerStaticDhSource.concreteInputs setup.joint seed input), after) ∈
        support ((nativePrefix setup codec checks seed raw).run state.2.server.consumed) := by
      rw [native_prefix, StateT.run_map, support_map]
      exact ⟨_, reached, rfl⟩
    obtain ⟨candidate, accepted⟩ := PqxdhRegistrationJointRawSignatures.prefix_candidate setup codec checks seed raw
      state.2.server.consumed after _ native
    simp only [PqxdhServerStaticDhSource.concreteInputs] at candidate accepted
    simp only [registrationOf, candidateOf, acceptedKeys, candidate, accepted, Option.bind_some, Option.map_some,
      registrationId]

/-- A source14 command other than an accept leaves the live Server object's consumed list unchanged. -/
theorem handler_other (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (query : PqxdhRegistrationSchedule.Spec.Domain)
    (notAccept : ¬PqxdhRegistrationSchedule.IsAccept query) (state : PqxdhRegistrationSchedule.State KemSK)
    (result : PqxdhRegistrationSchedule.Spec.Range query × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed query).run state)) :
    result.2.shared.2.server.consumed = state.shared.2.server.consumed := by
  have count := PqxdhRegistrationSchedule.handler_consumed_count setup codec checks serverSeed query state result supported
  rcases PqxdhRegistrationSchedule.handler_admission setup codec checks serverSeed query state result supported with
    same | ⟨rid, _, appended⟩
  · exact same
  · rw [appended, List.length_append] at count
    simp only [notAccept, ite_false, List.length_singleton] at count
    omega

/-- The registration IDs of a transcript extended by one entry. -/
theorem acceptIds_append (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (transcript : List Entry) (entry : Entry) :
    acceptIds crypto codec (transcript ++ [entry]) = acceptIds crypto codec transcript ++ (entryRegistration crypto codec entry).toList := by
  simp only [acceptIds, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases entryRegistration crypto codec entry <;> rfl

/-- The CE-R1 run invariant: the live Server object's consumed list is exactly the list of registration IDs of the successful accepts in the transcript, in order, and that list has no duplicate. -/
structure Registered (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (transcript : List Entry)
    (native : PqxdhRegistrationSchedule.State KemSK) : Prop where
  consumed : native.shared.2.server.consumed = acceptIds crypto codec transcript
  unique : (acceptIds crypto codec transcript).Nodup

/-- An entry without a registration ID and a step that keeps the consumed list keep the invariant. -/
theorem registered_other (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (transcript : List Entry)
    (before after : PqxdhRegistrationSchedule.State KemSK) (entry : Entry)
    (registered : Registered crypto codec transcript before)
    (same : after.shared.2.server.consumed = before.shared.2.server.consumed)
    (none : entryRegistration crypto codec entry = none) :
    Registered crypto codec (transcript ++ [entry]) after := by
  have ids : acceptIds crypto codec (transcript ++ [entry]) = acceptIds crypto codec transcript := by
    rw [acceptIds_append, none, Option.toList_none, List.append_nil]
  exact ⟨by rw [ids, same]; exact registered.consumed, by rw [ids]; exact registered.unique⟩

/-- One coin or command of the native deployment handler keeps the CE-R1 invariant, with the command and its reply appended to the transcript. A successful accept appends the registration ID of its raw bytes, absent before; nothing else changes the consumed list. -/
theorem command_registered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK)
    (registered : Registered setup.source.crypto codec transcript state.native)
    (result : Spec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state)) :
    Registered setup.source.crypto codec (transcript ++ [⟨.inl query, result.1⟩]) result.2.native := by
  have source : ∀ (request : PqxdhRegistrationSchedule.Request) (notAccept : ¬PqxdhRegistrationSchedule.IsAccept (.inr request))
      (result : PqxdhRegistrationSchedule.QuerySpec request × PqxdhDeploymentNative.State KemSK),
      result ∈ support ((PqxdhDeploymentNative.onNative
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request))).run state) →
      result.2.native.shared.2.server.consumed = state.native.shared.2.server.consumed := by
    intro request notAccept result member
    obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state result member
    exact handler_other setup codec checks serverSeed (.inr request) notAccept state.native inner innerMember
  have quiet : ∀ (request : PqxdhRegistrationSchedule.Request), ¬PqxdhRegistrationSchedule.IsAccept (.inr request) ↔
      ∀ raw, request ≠ .accept raw := by
    intro request
    cases request <;> simp [PqxdhRegistrationSchedule.IsAccept, PqxdhRegistrationSchedule.serverLabel, IsAcceptQuery]
  rcases query with coin | command
  · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact registered_other _ codec transcript _ _ _ registered rfl rfl
  · cases command with
    | create pin keyId =>
        cases parsed : parsePin pin with
        | none =>
            simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            subst supported
            exact registered_other _ codec transcript _ _ _ registered rfl rfl
        | some word =>
            simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_map, support_map, Set.mem_image] at supported
            obtain ⟨inner, member, rfl⟩ := supported
            exact registered_other _ codec transcript _ _ _ registered
              (source (.create word keyId) ((quiet _).mpr fun _ => by simp) inner member) rfl
    | bundle owner =>
        exact registered_other _ codec transcript _ _ _ registered
          (source (.bundle owner) ((quiet _).mpr fun _ => by simp) result supported) rfl
    | accept raw =>
        obtain ⟨inner, member, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state result supported
        simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.onShared_run, support_map,
          Set.mem_image] at member
        obtain ⟨reached, reachedMember, rfl⟩ := member
        rcases accept_registration setup codec checks serverSeed raw state.native.shared reached reachedMember with
          ⟨rejected, same⟩ | ⟨index, rid, returned, registration, fresh, changed⟩
        · apply registered_other _ codec transcript _ _ _ registered same
          change entryRegistration setup.source.crypto codec ⟨.inl (.inr (.accept raw)), reached.1⟩ = none
          rw [rejected]
          rfl
        · have entry : entryRegistration setup.source.crypto codec ⟨.inl (.inr (.accept raw)), reached.1⟩ = some rid := by
            rw [returned]
            exact registration
          refine ⟨?_, ?_⟩
          · rw [acceptIds_append, entry, Option.toList_some, ← registered.consumed]
            exact changed
          · rw [acceptIds_append, entry, Option.toList_some, List.nodup_append]
            refine ⟨registered.unique, List.nodup_singleton rid, ?_⟩
            intro left leftMember right rightMember equal
            rw [List.mem_singleton] at rightMember
            subst rightMember
            rw [← registered.consumed] at leftMember
            exact fresh (equal ▸ leftMember)
    | build session payload =>
        exact registered_other _ codec transcript _ _ _ registered
          (source (.build session payload) ((quiet _).mpr fun _ => by simp) result supported) rfl
    | finish owner raw =>
        exact registered_other _ codec transcript _ _ _ registered
          (source (.finish owner raw) ((quiet _).mpr fun _ => by simp) result supported) rfl
    | hmac key message =>
        exact registered_other _ codec transcript _ _ _ registered
          (source (.hmac key message) ((quiet _).mpr fun _ => by simp) result supported) rfl
    | hash bytes =>
        exact registered_other _ codec transcript _ _ _ registered
          (source (.hash bytes) ((quiet _).mpr fun _ => by simp) result supported) rfl
    | serverSend kid plaintext =>
        exact registered_other _ codec transcript _ _ _ registered
          (PqxdhDeploymentNative.serverStep_fields setup codec route (.inl (plaintext, kid)) state result
            supported).2.2.2.2.2.2.2.1 rfl
    | serverRaw raw =>
        exact registered_other _ codec transcript _ _ _ registered
          (PqxdhDeploymentNative.serverStep_fields setup codec route (.inr raw) state result
            supported).2.2.2.2.2.2.2.1 rfl
    | beaconSend owner plaintext =>
        have fields := PqxdhDeploymentNative.beaconStep_fields setup codec owner (.inl plaintext) state result supported
        exact registered_other _ codec transcript _ _ _ registered (by rw [fields.2.2.1]) rfl
    | beaconRaw owner raw =>
        have fields := PqxdhDeploymentNative.beaconStep_fields setup codec owner (.inr raw) state result supported
        exact registered_other _ codec transcript _ _ _ registered (by rw [fields.2.2.1]) rfl

/-- A native-interface program that issues only coins and sends keeps the consumed list of the live Server object. -/
theorem coinSend_consumed {Value : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (program : OracleComp Spec Value)
    (bounded : program.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (state : PqxdhDeploymentNative.State KemSK) (result : Value × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
      program).run state)) :
    result.2.native.shared.2.server.consumed = state.native.shared.2.server.consumed := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have kind : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases allowed with free | impossible
        · simpa using free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
      have firstSame : middle.native.shared.2.server.consumed = state.native.shared.2.server.consumed := by
        rcases query with coin | command
        · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at first
          obtain ⟨_, _, same⟩ := first
          cases same
          rfl
        · cases command with
          | serverSend kid plaintext =>
              exact (PqxdhDeploymentNative.serverStep_fields setup codec route (.inl (plaintext, kid)) state _
                first).2.2.2.2.2.2.2.1
          | beaconSend index plaintext =>
              have fields := PqxdhDeploymentNative.beaconStep_fields setup codec index (.inl plaintext) state _ first
              rw [fields.2.2.1]
          | _ => simp [PqxdhDeploymentSecrecy.coinOrSend] at kind
      have restBound := rest reply
      simp only [kind, Bool.true_eq_false, ite_false] at restBound
      exact (ih reply restBound middle second).trans firstSame

/-- Every query of the complete experiment, including the secrecy commands, keeps the CE-R1 invariant. -/
theorem experiment_registered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (query : PqxdhDeploymentInterface.Query) (state : PqxdhDeploymentSecrecy.State KemSK)
    (registered : Registered setup.source.crypto codec state.1.transcript state.2.native)
    (result : FullSpec.Range query × PqxdhDeploymentSecrecy.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run
      state)) :
    Registered setup.source.crypto codec result.2.1.transcript result.2.2.native := by
  rcases state with ⟨ledger, native⟩
  rw [PqxdhDeploymentEligibility.handler_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at member
    obtain ⟨answer, answerMember, rfl⟩ := member
    exact command_registered setup codec checks route serverSeed request ledger.transcript native registered answer
      answerMember
  · have value : reached.1 ∈ support ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds (.inr secrecy)).run
        ledger) := by
      apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
        _ native
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, member, rfl⟩
    have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
      ledger reached.1 value
    have same := coinSend_consumed setup codec checks route serverSeed _
      (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy ledger) native
      reached member
    simp only [recorded]
    exact registered_other _ codec ledger.transcript native.native reached.2.native _ registered same rfl

/-- The Server constructor starts with an empty consumed list. -/
theorem construct_consumed (primitives : Primitives) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (sender : Std.U64) (runtime : A) (created : PqxdhLiveServerConstruction.Created Unit) (after : A)
    (supported : (some created, after) ∈ support
      ((PqxdhLiveServerConstruction.construct primitives ensureInit identityIndex sender none).run runtime)) :
    created.consumed = [] := by
  simp only [PqxdhLiveServerConstruction.construct, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨ready, _, supported⟩ := supported
  split at supported
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at supported
    obtain ⟨seed, _, rfl, _⟩ := supported
    rfl
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported

/-- The CE-R1 invariant along the whole experiment: in either mode, every outcome of the common deployment experiment has the live Server object's consumed list equal to the duplicate-free list of registration IDs of the successful accepts in its transcript. -/
theorem registered_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) :
    Registered setup.source.crypto codec final.1.transcript final.2.native := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, bornMember, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    have empty := construct_consumed setup.joint ensureInit identityIndex setup.serverKeyId runtime constructed after
      bornMember
    exact OracleComp.simulateQ_run_preserves_inv_of_query
      (PqxdhDeploymentSecrecy.handler setup codec checks route constructed.seed bounds)
      (fun state => Registered setup.source.crypto codec state.1.transcript state.2.native)
      (fun query state registered result member => experiment_registered setup codec checks route constructed.seed
        bounds query state registered result member)
      (asModeO mode adversary) (Ledger.empty, PqxdhDeploymentNative.initial constructed)
      ⟨by simpa [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial, acceptIds, Ledger.empty] using empty,
        by simp [acceptIds, Ledger.empty]⟩ _ executedMember

/-- If a partial map of a list has no duplicate, at most one entry of the list is sent to any given value. -/
theorem countP_le_one {α β : Type} [DecidableEq β] (f : α → Option β) (value : β) (list : List α)
    (unique : (list.filterMap f).Nodup) : list.countP (fun item => f item = some value) ≤ 1 := by
  induction list with
  | nil => simp
  | cons head tail ih =>
      cases found : f head with
      | none =>
          rw [List.filterMap_cons, found] at unique
          simpa [List.countP_cons, found] using ih unique
      | some image =>
          rw [List.filterMap_cons, found, List.nodup_cons] at unique
          by_cases same : image = value
          · subst same
            have zero : tail.countP (fun item => f item = some image) = 0 := by
              rw [List.countP_eq_zero]
              intro item member mapped
              exact unique.1 (List.mem_filterMap.mpr ⟨item, member, by simpa using mapped⟩)
            simp [found, zero]
          · simpa [List.countP_cons, found, same] using ih unique.2

/-- Theorem CE-R1 (per live Server object, deterministic, zero loss): in either mode, on every outcome of the common deployment experiment, every registration ID (identity key and one-time key of the verified candidate, read from public bytes) is carried by at most one successful accept of the transcript, and the live Server object's consumed list is exactly the list of these registration IDs in order. -/
theorem replay_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) (rid : Pqxdh.Bytes) :
    final.1.transcript.countP (fun entry => entryRegistration setup.source.crypto codec entry = some rid) ≤ 1 ∧
      final.2.native.shared.2.server.consumed = acceptIds setup.source.crypto codec final.1.transcript := by
  have registered := registered_game setup codec checks route ensureInit identityIndex bounds mode adversary runtime
    outcome supported created output final reached
  refine ⟨?_, registered.consumed⟩
  exact countP_le_one _ rid _ registered.unique

end BeaconcryptCore.Computational.PqxdhDeploymentReplay

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.accept_oracle_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.accept_oracle_registration

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.accept_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.accept_registration

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.handler_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.handler_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.acceptIds_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.acceptIds_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.registered_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.registered_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.command_registered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.command_registered

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.coinSend_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.coinSend_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.experiment_registered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.experiment_registered

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.construct_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.construct_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.registered_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.registered_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.countP_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.countP_le_one

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReplay.replay_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReplay.replay_game
