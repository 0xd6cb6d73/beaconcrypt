-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal

/-! The embedding's own ServerAuth journal tracks the registration view of the frozen source14 journal (CE-8). `saReg c` reads an accept, build or finish of a ServerAuth journal as a registration entry, with the finish attributed to owner `c`; coin, HMAC, BLAKE2b and reveal queries are `Quiet`, and so are all queries of local Beacons (`coins_quiet`, `localCallbacks_quiet`). `Track` relates the registration view of the frozen journal, the embedding state and `R_c`'s own ServerAuth journal: one embedding entry per created owner, the target's placeholder exactly at `c` when the `c`-th create carried the input's binding, the slot of `c` that the summary determines (`slotOf`), no phase, failure or bundle for owners not yet created, no first bundle of the Fresh target and the input's published Phase 1 as its first bundle afterwards, every accept, build and finish of the ServerAuth journal in the view, every finish the target's and successful only once the target accepted or left InitSent, and, once the target accepted, a ServerAuth journal that ends with that acceptance, preceded only by entries of the view before it and by no successful finish. Each embedding step before the stop keeps `Track` (`track_step`, from `track_quiet`, `track_silent`, `track_create`, `track_targetBundle`, `track_targetFinish` and `track_local`), so every outcome of `R_c` is tracked (`adversary_track`). On a tracked outcome, the A1 failure of `c` under the input's binding gives a successful ServerAuth finish and no session with both an earlier publication of the accepted decoded record and an accept carrying the input's published keys (`track_unmatched`, `adversary_unmatched`); this holds on every outcome of `R_c` as a program, for every reply of every query. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentTranscript (PublicPhase Summary candidateOf acceptedKeys)
open PqxdhDeploymentServerAuthEvent (Reg SourceEntry regOfSource regsOfSource summarizeReg stepReg accepted acceptCheck
  bundleOfReg keysOfBundle publishedKeys Matched MatchedAt Unmatched Stop)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Owner Slot Emb embed freezeImpl dflt stopAt inputBinding coins forward
  localCallbacks localRoot embedded adversary)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- One entry of a ServerAuth journal. -/
abbrev SaEntry := (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query

/-- The registration entry of a ServerAuth journal entry, with its finish attributed to owner `c`. -/
def saReg (c : Nat) : SaEntry → Option Reg
  | ⟨.inr (.accept raw), reply⟩ => some (.accept raw reply)
  | ⟨.inr (.build session payload), reply⟩ => some (.build session payload reply)
  | ⟨.inr (.finish raw), reply⟩ => some (.finish c raw reply)
  | _ => none

/-- A ServerAuth query other than an accept, build or finish. -/
def Quiet : ServerAuthSpec.Domain → Prop
  | .inr (.accept _) => False
  | .inr (.build _ _) => False
  | .inr (.finish _) => False
  | _ => True

/-- A quiet entry has no registration entry. -/
theorem saReg_quiet (c : Nat) (entry : SaEntry) (quiet : Quiet entry.1) : saReg c entry = none := by
  rcases entry with ⟨coin | query, reply⟩
  · rfl
  · cases query <;> first | rfl | exact absurd quiet id

/-- Every query of a simulation is quiet when every query of the simulating implementation is. -/
theorem simulateQ_quiet {κ : Type} {spec : OracleSpec κ} {α : Type} (impl : QueryImpl spec (OracleComp ServerAuthSpec))
    (quiet : ∀ query, AllQueriesSatisfy (impl query) Quiet) (program : OracleComp spec α) :
    AllQueriesSatisfy (simulateQ impl program) Quiet := by
  induction program using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact allQueriesSatisfy_bind (quiet query) ih

/-- Coin queries are quiet. -/
theorem coins_quiet {α : Type} (work : ProbComp α) : AllQueriesSatisfy (coins work) Quiet :=
  simulateQ_quiet _ (fun query => (allQueriesSatisfy_query_iff (spec := ServerAuthSpec) (.inl query) Quiet).mpr trivial)
    work

/-- A mapped computation has the same queries. -/
theorem map_quiet {α β : Type} (f : α → β) (work : OracleComp ServerAuthSpec α) (quiet : AllQueriesSatisfy work Quiet) :
    AllQueriesSatisfy (f <$> work) Quiet :=
  (isQueryBound_map_iff work f () _ _).mpr quiet

/-- The callbacks of a local Beacon's finish issue only coin, HMAC and BLAKE2b queries. -/
theorem localCallbacks_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Domain) :
    AllQueriesSatisfy (localCallbacks setup codec query) Quiet := by
  rcases query with query | ((request | (bytes | input)) | (input | request | response))
  · exact coins_quiet _
  · exact allQueriesSatisfy_pure _ _
  · exact map_quiet _ _ ((allQueriesSatisfy_query_iff (spec := ServerAuthSpec) (.inr (.hash bytes)) Quiet).mpr trivial)
  · exact allQueriesSatisfy_pure _ _
  · exact map_quiet _ _ ((allQueriesSatisfy_query_iff (spec := ServerAuthSpec) (.inr (.hmac _ _)) Quiet).mpr trivial)
  · exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _

/-! ## Journals of steps -/

/-- Journaling distributes over sequencing. -/
theorem record_bind {α β : Type} (first : OracleComp ServerAuthSpec α) (next : α → OracleComp ServerAuthSpec β) :
    PqxdhServerAuthApiJournal.record (first >>= next) =
      PqxdhServerAuthApiJournal.record first >>= fun step =>
        Prod.map id (step.2 ++ ·) <$> PqxdhServerAuthApiJournal.record (next step.1) :=
  OracleComp.withQueryLog_bind first next

/-- Every journal entry of a quiet computation is quiet. -/
theorem record_quiet {α : Type} (work : OracleComp ServerAuthSpec α) (quiet : AllQueriesSatisfy work Quiet)
    (outcome : α × QueryLog ServerAuthSpec) (member : outcome ∈ support (PqxdhServerAuthApiJournal.record work)) :
    ∀ entry ∈ outcome.2, Quiet entry.1 :=
  OracleComp.holds_of_mem_log_of_mem_support_run_simulateQ quiet member

/-- The journal of a pure computation is empty. -/
theorem record_pure {α : Type} (value : α) (outcome : α × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (PqxdhServerAuthApiJournal.record (pure value : OracleComp ServerAuthSpec α))) :
    outcome = (value, []) := by
  simpa [PqxdhServerAuthApiJournal.record] using member

/-- The journal of one query is that query with its reply. -/
theorem record_query {α : Type} (query : ServerAuthSpec.Domain) (f : ServerAuthSpec.Range query → α)
    (outcome : α × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (PqxdhServerAuthApiJournal.record
      (f <$> (ServerAuthSpec.query query : OracleComp ServerAuthSpec _)))) :
    ∃ reply, outcome = (f reply, [⟨query, reply⟩]) := by
  rw [map_eq_bind_pure_comp] at member
  unfold PqxdhServerAuthApiJournal.record at member
  rw [run_simulateQ_loggingOracle_query_bind] at member
  simp only [Function.comp_apply, simulateQ_pure, mem_support_bind_iff, support_map] at member
  obtain ⟨reply, _, inner, innerMember, rfl⟩ := member
  have same : inner = (f reply, []) := by simpa using innerMember
  exact ⟨reply, by rw [same]⟩

/-! ## The embedded run -/

/-- The frozen program under the embedding from a journal and an embedding state. -/
noncomputable def run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat) (input : AuthInput)
    (program : OracleComp (SourceSpec KemSK) Result) (journal : List (SourceEntry KemSK)) (emb : Emb KemSK) :
    OracleComp ServerAuthSpec ((Result × List (SourceEntry KemSK)) × Emb KemSK) :=
  (simulateQ (embed setup codec c input) ((simulateQ (freezeImpl dflt (stopAt c)) program).run journal)).run emb

/-- One query of the embedded run: frozen after the stop, otherwise one embedding step journaled. -/
theorem run_query_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat) (input : AuthInput)
    (query : (SourceSpec KemSK).Domain) (next : (SourceSpec KemSK).Range query → OracleComp (SourceSpec KemSK) Result)
    (journal : List (SourceEntry KemSK)) (emb : Emb KemSK) :
    run setup codec c input ((SourceSpec KemSK).query query >>= next) journal emb =
      if stopAt c journal then run setup codec c input (next (dflt query)) journal emb
      else (embed setup codec c input query).run emb >>= fun step =>
        run setup codec c input (next step.1) (journal ++ [⟨query, step.1⟩]) step.2 := by
  unfold run
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
    PqxdhDeploymentServerAuthLocalize.freezeImpl_run]
  by_cases stopped : stopAt c journal
  · simp only [stopped, ite_true, simulateQ_pure, StateT.run_pure, pure_bind]
  · simp only [stopped, ite_false, simulateQ_map, simulateQ_spec_query, StateT.run_map, bind_map_left]

/-! ## The tracking invariant -/

open Classical in
/-- The slot of `c` that the registration summary determines: waiting before the `c`-th create, released when that create carried another binding, and otherwise failed after a rejected bundle in Fresh, fresh while Fresh, bundled after the first bundle. -/
noncomputable def slotOf (c : Nat) (input : AuthInput) (summary : Summary) : Slot :=
  if summary.owners.length ≤ c then .waiting
  else if summary.owners[c]? = some (inputBinding input) then
    (if summary.failures c = true then .failed else if summary.phases c = .fresh then .fresh else .bundled)
  else .released

/-- The embedding's state and its own ServerAuth journal track a registration view: the embedding holds one entry per created owner, the target's placeholder exactly at `c` when the `c`-th create carried the input's binding, and the slot the summary determines; owners not yet created have no phase, failure or bundle; while the target is Fresh it has no bundle, and after its first bundle that bundle is the input's published Phase 1; every accept, build and finish of the ServerAuth journal is in the view, every finish is the target's and is successful only once the target accepted or left InitSent; and once the target accepted, the ServerAuth journal ends with that acceptance, preceded only by entries of the view before it and by no successful finish. -/
structure Track (c : Nat) (input : AuthInput) (regs : List Reg) (emb : Emb KemSK) (log : QueryLog ServerAuthSpec) :
    Prop where
  count : emb.owners.length = (summarizeReg regs).owners.length
  target : ∀ index, emb.owners[index]? = some none ↔
    index = c ∧ (summarizeReg regs).owners[c]? = some (inputBinding input)
  slot : emb.slot = slotOf c input (summarizeReg regs)
  beyond : ∀ index, (summarizeReg regs).owners.length ≤ index →
    (summarizeReg regs).phases index = .absent ∧ (summarizeReg regs).failures index = false ∧
      bundleOfReg regs index = none
  created : ∀ index, index < (summarizeReg regs).owners.length → (summarizeReg regs).phases index ≠ .absent
  fresh : (summarizeReg regs).owners[c]? = some (inputBinding input) → (summarizeReg regs).phases c = .fresh →
    bundleOfReg regs c = none
  sent : (summarizeReg regs).owners[c]? = some (inputBinding input) → (summarizeReg regs).failures c = false →
    (summarizeReg regs).phases c ≠ .fresh → bundleOfReg regs c = input.phase1 ∧ input.phase1.isSome = true
  logged : ∀ entry ∈ log, ∀ reg, saReg c entry = some reg → reg ∈ regs
  finished : ∀ entry ∈ log, ∀ raw reply, saReg c entry = some (.finish c raw reply) →
    (summarizeReg regs).owners[c]? = some (inputBinding input) ∧
      (reply.isSome = true → (accepted c regs).isSome = true ∨ (summarizeReg regs).phases c = .aborted ∨
        (summarizeReg regs).phases c = .established)
  accepted : ∀ before raw, accepted c regs = some (before, raw) →
    (summarizeReg before).owners[c]? = some (inputBinding input) →
    ∃ prior payload, log = prior ++ [⟨.inr (.finish raw), some payload⟩] ∧
      (∀ entry ∈ prior, ∀ reg, saReg c entry = some reg → reg ∈ before) ∧
      (∀ entry ∈ prior, ∀ raw' payload', saReg c entry ≠ some (.finish c raw' (some payload'))) ∧
      bundleOfReg before c = input.phase1

/-- The empty view, the empty embedding state and the empty journal agree. -/
theorem track_empty (c : Nat) (input : AuthInput) : Track (KemSK := KemSK) c input [] Emb.empty [] where
  count := rfl
  target index := by simp [Emb.empty, summarizeReg, Summary.empty]
  slot := by simp [Emb.empty, slotOf, summarizeReg, Summary.empty]
  beyond index _ := by simp [summarizeReg, Summary.empty, bundleOfReg]
  created index short := by simp [summarizeReg, Summary.empty] at short
  fresh bound := by simp [summarizeReg, Summary.empty] at bound
  sent bound := by simp [summarizeReg, Summary.empty] at bound
  logged entry member := by simp at member
  finished entry member := by simp at member
  accepted before raw found := by simp [accepted, PqxdhDeploymentServerAuthEvent.acceptedFrom] at found

/-- Before a successful finish, the public calls preceding the first successful finish are the calls before it. -/
theorem beforeAcceptance_last (c : Nat) (prior : QueryLog ServerAuthSpec) (raw payload : Pqxdh.Bytes)
    (quiet : ∀ entry ∈ prior, ∀ raw' payload', saReg c entry ≠ some (.finish c raw' (some payload'))) :
    PqxdhServerAuthPublicationOccurrence.beforeAcceptance (prior ++ [⟨.inr (.finish raw), some payload⟩]) = prior ∧
      PqxdhServerAuthRecordPublicationEvent.acceptedRaw (prior ++ [⟨.inr (.finish raw), some payload⟩]) = some raw := by
  have notReturned : ∀ entry ∈ prior, PqxdhServerAuthPublicationOccurrence.finishReturned entry = false := by
    intro entry member
    rcases entry with ⟨coin | query, reply⟩
    · rfl
    · cases query with
      | finish phase2 =>
          cases reply with
          | none => rfl
          | some bytes => exact absurd rfl (quiet _ member phase2 bytes)
      | _ => rfl
  have noRaw : ∀ entry ∈ prior, PqxdhServerAuthRecordPublicationEvent.finishRaw entry = none := by
    intro entry member
    rcases entry with ⟨coin | query, reply⟩
    · rfl
    · cases query with
      | finish phase2 =>
          cases reply with
          | none => rfl
          | some bytes => exact absurd rfl (quiet _ member phase2 bytes)
      | _ => rfl
  constructor
  · unfold PqxdhServerAuthPublicationOccurrence.beforeAcceptance
    rw [List.takeWhile_append_of_pos (fun entry member => by simp [notReturned entry member])]
    simp [PqxdhServerAuthPublicationOccurrence.finishReturned]
  · unfold PqxdhServerAuthRecordPublicationEvent.acceptedRaw
    rw [List.findSome?_append, List.findSome?_eq_none_iff.mpr noRaw]
    rfl

/-- On a tracked state, the A1 failure of `c` under the input's binding gives a successful ServerAuth finish and no session with both an earlier publication of the accepted decoded record and an accept carrying the input's published keys. -/
theorem track_unmatched (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (c : Nat) (input : AuthInput)
    (regs : List Reg) (emb : Emb KemSK) (log : QueryLog ServerAuthSpec) (track : Track c input regs emb log)
    (failure : Unmatched crypto codec (inputBinding input) c regs) :
    (∃ raw payload, (⟨.inr (.finish raw), some payload⟩ : SaEntry) ∈ log) ∧
    ∀ index, PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index log →
      ∀ acceptRaw candidate keys, (⟨.inr (.accept acceptRaw), some index⟩ : SaEntry) ∈ log →
        candidateOf codec acceptRaw = some candidate → acceptedKeys crypto candidate = some keys →
        keysOfBundle codec input.phase1 ≠ some keys := by
  obtain ⟨before, raw, found, bound, _, unmatched⟩ := failure
  obtain ⟨prior, payload, logEq, priorLogged, priorQuiet, bundleEq⟩ := track.accepted before raw found bound
  obtain ⟨beforeEq, rawEq⟩ := beforeAcceptance_last c prior raw payload priorQuiet
  refine ⟨⟨raw, payload, by rw [logEq]; simp⟩, ?_⟩
  intro index published acceptRaw candidate keys acceptMember candidateEq keysEq bundleKeys
  obtain ⟨buildPayload, reply, raw', record, buildMember, rawFound, frameRaw, frameReply⟩ := published
  rw [logEq, beforeEq] at buildMember
  rw [logEq, rawEq, Option.some.injEq] at rawFound
  subst rawFound
  have acceptPrior : (⟨.inr (.accept acceptRaw), some index⟩ : SaEntry) ∈ prior := by
    rw [logEq, List.mem_append, List.mem_singleton] at acceptMember
    rcases acceptMember with member | impossible
    · exact member
    · simp at impossible
  apply unmatched
  refine ⟨index, acceptRaw, candidate, keys, buildPayload, reply, record,
    priorLogged _ acceptPrior _ rfl, candidateEq, keysEq, ?_, priorLogged _ buildMember _ rfl, frameRaw, frameReply⟩
  simp only [publishedKeys, bundleEq, bundleKeys]


/-! ## Steps of the tracking invariant -/

/-- Before the stop of `c`, owner `c` has not accepted and has no rejected bundle in Fresh. -/
theorem stop_open (c : Nat) (regs : List Reg) (open_ : ¬ Stop c regs) :
    accepted c regs = none ∧ (summarizeReg regs).failures c = false := by
  simp only [Stop, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at open_
  exact open_

/-- The first successful bundle of an owner in a view extended by one entry. -/
theorem bundleOfReg_snoc (regs : List Reg) (reg : Reg) (owner : Nat) :
    bundleOfReg (regs ++ [reg]) owner = (bundleOfReg regs owner).or (bundleOfReg [reg] owner) := by
  simp only [bundleOfReg, List.findSome?_append]

/-- A journal extension with no registration entry keeps the tracking before the stop. -/
theorem track_quiet (c : Nat) (input : AuthInput) (regs : List Reg) (emb : Emb KemSK) (log : QueryLog ServerAuthSpec)
    (track : Track c input regs emb log) (open_ : ¬ Stop c regs) (extra : QueryLog ServerAuthSpec)
    (quiet : ∀ entry ∈ extra, saReg c entry = none) : Track c input regs emb (log ++ extra) := by
  obtain ⟨notAccepted, _⟩ := stop_open c regs open_
  refine ⟨track.count, track.target, track.slot, track.beyond, track.created, track.fresh, track.sent, ?_, ?_, ?_⟩
  · intro entry member reg found
    rcases List.mem_append.mp member with old | new
    · exact track.logged entry old reg found
    · rw [quiet entry new] at found
      cases found
  · intro entry member raw reply found
    rcases List.mem_append.mp member with old | new
    · exact track.finished entry old raw reply found
    · rw [quiet entry new] at found
      cases found
  · intro before raw found
    rw [notAccepted] at found
    cases found

/-- One registration entry that changes neither the summary, nor the acceptance, nor any first bundle, with ServerAuth entries that are this entry or quiet and are no finish, keeps the tracking before the stop. -/
theorem track_silent (c : Nat) (input : AuthInput) (regs : List Reg) (emb : Emb KemSK) (log : QueryLog ServerAuthSpec)
    (track : Track c input regs emb log) (open_ : ¬ Stop c regs) (reg : Reg)
    (summary : stepReg (summarizeReg regs) reg = summarizeReg regs)
    (check : acceptCheck c (summarizeReg regs) regs reg = none)
    (bundles : ∀ owner, bundleOfReg [reg] owner = none) (extra : QueryLog ServerAuthSpec)
    (entries : ∀ entry ∈ extra, ∀ other, saReg c entry = some other → other = reg)
    (notFinish : ∀ entry ∈ extra, ∀ raw reply, saReg c entry ≠ some (.finish c raw reply)) :
    Track c input (regs ++ [reg]) emb (log ++ extra) := by
  obtain ⟨notAccepted, _⟩ := stop_open c regs open_
  have sumEq : summarizeReg (regs ++ [reg]) = summarizeReg regs := by
    rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, summary]
  have acceptedEq : accepted c (regs ++ [reg]) = none := by
    rw [PqxdhDeploymentServerAuthEvent.accepted_snoc, notAccepted, check]
    rfl
  have bundleEq : ∀ owner, bundleOfReg (regs ++ [reg]) owner = bundleOfReg regs owner := by
    intro owner
    rw [bundleOfReg_snoc, bundles owner, Option.or_none]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sumEq]; exact track.count
  · rw [sumEq]; exact track.target
  · rw [sumEq]; exact track.slot
  · intro index beyond
    rw [sumEq, bundleEq] at *
    exact track.beyond index beyond
  · rw [sumEq]; exact track.created
  · rw [sumEq, bundleEq]; exact track.fresh
  · rw [sumEq, bundleEq]; exact track.sent
  · intro entry member other found
    rcases List.mem_append.mp member with old | new
    · exact List.mem_append_left _ (track.logged entry old other found)
    · rw [entries entry new other found]
      simp
  · intro entry member raw reply found
    rw [sumEq]
    rcases List.mem_append.mp member with old | new
    · obtain ⟨bound, success⟩ := track.finished entry old raw reply found
      refine ⟨bound, fun isSome => ?_⟩
      rcases success isSome with accepted | rest
      · rw [notAccepted] at accepted
        cases accepted
      · exact Or.inr rest
    · exact absurd found (notFinish entry new raw reply)
  · intro before raw found
    rw [acceptedEq] at found
    cases found


open Classical PqxdhDeploymentServerAuthLocalize in
/-- A create, answered with the next handle, that places the target's placeholder exactly when it is the `c`-th create with the input's binding and sets the slot of `c` accordingly, with quiet ServerAuth entries, keeps the tracking before the stop. -/
theorem track_create (c : Nat) (input : AuthInput) (regs : List Reg) (emb : Emb KemSK) (log : QueryLog ServerAuthSpec)
    (track : Track c input regs emb log) (open_ : ¬ Stop c regs) (pin : Word32) (keyId : Std.U64)
    (entry : Option (Owner KemSK)) (after : Emb KemSK) (owners : after.owners = emb.owners ++ [entry])
    (placed : entry = none ↔ emb.owners.length = c ∧ (pin, keyId) = inputBinding input)
    (slot : after.slot = if emb.owners.length = c then (if (pin, keyId) = inputBinding input then .fresh else .released)
      else emb.slot)
    (extra : QueryLog ServerAuthSpec) (quiet : ∀ entry ∈ extra, saReg c entry = none) :
    Track c input (regs ++ [.create pin keyId emb.owners.length]) after (log ++ extra) := by
  obtain ⟨notAccepted, _⟩ := stop_open c regs open_
  have count : emb.owners.length = (summarizeReg regs).owners.length := track.count
  have sumOwners : (summarizeReg (regs ++ [.create pin keyId emb.owners.length])).owners = (summarizeReg regs).owners ++ [(pin, keyId)] := by
    rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
    rfl
  have sumPhases : (summarizeReg (regs ++ [.create pin keyId emb.owners.length])).phases = Function.update (summarizeReg regs).phases emb.owners.length .fresh := by
    rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
    rfl
  have sumFailures : (summarizeReg (regs ++ [.create pin keyId emb.owners.length])).failures = (summarizeReg regs).failures := by
    rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
    rfl
  have acceptedEq : accepted c (regs ++ [.create pin keyId emb.owners.length]) = none := by
    rw [PqxdhDeploymentServerAuthEvent.accepted_snoc, notAccepted]
    rfl
  have bundleEq : ∀ owner, bundleOfReg (regs ++ [.create pin keyId emb.owners.length]) owner = bundleOfReg regs owner := by
    intro owner
    rw [bundleOfReg_snoc]
    simp [bundleOfReg]
  have targetOld : (summarizeReg regs).owners[c]? = some (inputBinding input) → c < emb.owners.length := by
    intro found
    rw [count]
    exact (List.getElem?_eq_some_iff.mp found).1
  have ownersBelow : c < emb.owners.length → ((summarizeReg regs).owners ++ [(pin, keyId)])[c]? = (summarizeReg regs).owners[c]? :=
    fun below => lookup_snoc_ne (summarizeReg regs).owners (pin, keyId) c (by omega)
  have ownersAt : ((summarizeReg regs).owners ++ [(pin, keyId)])[emb.owners.length]? = some (pin, keyId) := by
    rw [count]
    exact lookup_snoc_self _ _
  have ownersAbove : emb.owners.length < c → ((summarizeReg regs).owners ++ [(pin, keyId)])[c]? = none :=
    fun above => List.getElem?_eq_none (by simp; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [owners, sumOwners]
    simp only [List.length_append, List.length_singleton]
    rw [count]
  · intro index
    rw [owners, sumOwners]
    rcases lt_trichotomy index emb.owners.length with below | same | above
    · rw [lookup_snoc_ne emb.owners entry index (by omega), track.target index]
      constructor
      · rintro ⟨rfl, found⟩
        exact ⟨rfl, by rw [ownersBelow below]; exact found⟩
      · rintro ⟨rfl, found⟩
        exact ⟨rfl, by rw [← ownersBelow below]; exact found⟩
    · rw [same, lookup_snoc_self, Option.some.injEq, placed]
      constructor
      · rintro ⟨atC, bound⟩
        exact ⟨atC, by rw [← atC, ownersAt, bound]⟩
      · rintro ⟨atC, found⟩
        rw [← atC, ownersAt, Option.some.injEq] at found
        exact ⟨atC, found⟩
    · rw [List.getElem?_eq_none (by simp; omega)]
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨rfl, found⟩
        rw [ownersAbove above] at found
        cases found
  · rw [slot]
    have old := track.slot
    unfold slotOf at old ⊢
    rw [sumOwners, sumPhases, sumFailures]
    rcases lt_trichotomy emb.owners.length c with below | same | above
    · have notC : emb.owners.length ≠ c := by omega
      have short : (summarizeReg regs).owners.length ≤ c := by omega
      have short' : ((summarizeReg regs).owners ++ [(pin, keyId)]).length ≤ c := by simp; omega
      simp only [notC, ite_false, old, short, short', ite_true]
    · rw [← same]
      have long : ¬ ((summarizeReg regs).owners ++ [(pin, keyId)]).length ≤ emb.owners.length := by simp; omega
      have fresh : (summarizeReg regs).failures emb.owners.length = false := (track.beyond emb.owners.length (by omega)).2.1
      by_cases bound : (pin, keyId) = inputBinding input
      · simp only [ite_true, long, ite_false, ownersAt]
        simp [bound, fresh]
      · have other : (some (pin, keyId) : Option (Word32 × Std.U64)) ≠ some (inputBinding input) := by
          simpa using bound
        simp only [ite_true, bound, ite_false, long, ownersAt, other]
    · have notC : emb.owners.length ≠ c := by omega
      have long : ¬ (summarizeReg regs).owners.length ≤ c := by omega
      have long' : ¬ ((summarizeReg regs).owners ++ [(pin, keyId)]).length ≤ c := by simp; omega
      simp only [notC, ite_false, old, long, long', ownersBelow above, Function.update_of_ne (Ne.symm notC)]
  · intro index beyond
    rw [sumOwners] at beyond
    simp only [List.length_append, List.length_singleton] at beyond
    have old := track.beyond index (by omega)
    rw [sumPhases, sumFailures, bundleEq, Function.update_of_ne (by omega)]
    exact old
  · intro index below
    rw [sumOwners] at below
    simp only [List.length_append, List.length_singleton] at below
    rw [sumPhases]
    rcases Nat.lt_or_ge index emb.owners.length with older | newest
    · rw [Function.update_of_ne (by omega)]
      exact track.created index (by omega)
    · have same : index = emb.owners.length := by omega
      subst same
      rw [Function.update_self]
      simp
  · intro found phase
    rw [sumOwners] at found
    rw [sumPhases] at phase
    rw [bundleEq]
    rcases lt_trichotomy c emb.owners.length with below | same | above
    · rw [ownersBelow below] at found
      rw [Function.update_of_ne (by omega)] at phase
      exact track.fresh found phase
    · rw [same]
      exact (track.beyond emb.owners.length (by omega)).2.2
    · rw [ownersAbove above] at found
      cases found
  · intro found failed phase
    rw [sumOwners] at found
    rw [sumPhases] at phase
    rw [sumFailures] at failed
    rw [bundleEq]
    rcases lt_trichotomy c emb.owners.length with below | same | above
    · rw [ownersBelow below] at found
      rw [Function.update_of_ne (by omega)] at phase
      exact track.sent found failed phase
    · subst same
      rw [Function.update_self] at phase
      exact absurd rfl phase
    · rw [ownersAbove above] at found
      cases found
  · intro entry member reg found
    rcases List.mem_append.mp member with old | new
    · exact List.mem_append_left _ (track.logged entry old reg found)
    · rw [quiet entry new] at found
      cases found
  · intro entry member raw reply found
    rcases List.mem_append.mp member with old | new
    · obtain ⟨bound, success⟩ := track.finished entry old raw reply found
      have below := targetOld bound
      rw [sumOwners, ownersBelow below, sumPhases, Function.update_of_ne (by omega), acceptedEq]
      refine ⟨bound, fun isSome => ?_⟩
      rcases success isSome with accepted | rest
      · rw [notAccepted] at accepted
        cases accepted
      · exact Or.inr rest
    · rw [quiet entry new] at found
      cases found
  · intro before raw found
    rw [acceptedEq] at found
    cases found


/-- A Fresh slot of `c` is the target's, Fresh in the summary without a rejected bundle. -/
theorem slotOf_fresh (c : Nat) (input : AuthInput) (summary : Summary) (fresh : slotOf c input summary = .fresh) :
    c < summary.owners.length ∧ summary.owners[c]? = some (inputBinding input) ∧ summary.failures c = false ∧
      summary.phases c = .fresh := by
  unfold slotOf at fresh
  split_ifs at fresh with short bound failed phase
  exact ⟨by omega, bound, by simpa using failed, phase⟩

/-- A bundled slot of `c` is the target's, past Fresh in the summary without a rejected bundle. -/
theorem slotOf_bundled (c : Nat) (input : AuthInput) (summary : Summary) (bundled : slotOf c input summary = .bundled) :
    c < summary.owners.length ∧ summary.owners[c]? = some (inputBinding input) ∧ summary.failures c = false ∧
      summary.phases c ≠ .fresh := by
  unfold slotOf at bundled
  split_ifs at bundled with short bound failed phase
  exact ⟨by omega, bound, by simpa using failed, phase⟩

/-- The slot of `c` depends only on the owner bindings and on the failure and phase of `c`. -/
theorem slotOf_congr (c : Nat) (input : AuthInput) (first second : Summary) (owners : first.owners = second.owners)
    (failures : first.failures c = second.failures c) (phases : first.phases c = second.phases c) :
    slotOf c input first = slotOf c input second := by
  unfold slotOf
  rw [owners, failures, phases]

/-- The first bundle of `c` in the target's Fresh slot answers the input's published Phase 1 and keeps the tracking before the stop. -/
theorem track_targetBundle (c : Nat) (input : AuthInput) (regs : List Reg) (emb : Emb KemSK)
    (log : QueryLog ServerAuthSpec) (track : Track c input regs emb log) (open_ : ¬ Stop c regs)
    (fresh : emb.slot = .fresh) :
    Track c input (regs ++ [.bundle c input.phase1])
      { emb with slot := if input.phase1.isSome then .bundled else .failed } log := by
  obtain ⟨notAccepted, _⟩ := stop_open c regs open_
  have slotFresh := slotOf_fresh c input _ (track.slot ▸ fresh)
  obtain ⟨below, bound, notFailed, phase⟩ := slotFresh
  have acceptedEq : accepted c (regs ++ [.bundle c input.phase1]) = none := by
    rw [PqxdhDeploymentServerAuthEvent.accepted_snoc, notAccepted]
    rfl
  have noFinishReply : ∀ entry ∈ log, ∀ raw reply, saReg c entry = some (.finish c raw reply) → reply.isSome = false := by
    intro entry member raw reply found
    obtain ⟨_, success⟩ := track.finished entry member raw reply found
    cases reply with
    | none => rfl
    | some payload =>
        rcases success rfl with accepted | aborted | established
        · rw [notAccepted] at accepted
          cases accepted
        · rw [phase] at aborted
          cases aborted
        · rw [phase] at established
          cases established
  have logged : ∀ entry ∈ log, ∀ reg, saReg c entry = some reg → reg ∈ regs ++ [.bundle c input.phase1] :=
    fun entry member reg found => List.mem_append_left _ (track.logged entry member reg found)
  cases published : input.phase1 with
  | none =>
      have sumOwners : (summarizeReg (regs ++ [.bundle c none])).owners = (summarizeReg regs).owners := by
        rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
        simp [stepReg, phase]
      have sumPhases : (summarizeReg (regs ++ [.bundle c none])).phases = (summarizeReg regs).phases := by
        rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
        simp [stepReg, phase]
      have sumFailures : (summarizeReg (regs ++ [.bundle c none])).failures =
          Function.update (summarizeReg regs).failures c true := by
        rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
        simp [stepReg, phase]
      have bundleEq : ∀ owner, bundleOfReg (regs ++ [.bundle c none]) owner = bundleOfReg regs owner := by
        intro owner
        rw [bundleOfReg_snoc]
        simp [bundleOfReg]
      rw [published] at logged acceptedEq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, logged, ?_, ?_⟩
      · rw [sumOwners]; exact track.count
      · rw [sumOwners]; exact track.target
      · unfold slotOf
        rw [sumOwners, sumFailures]
        have long : ¬ (summarizeReg regs).owners.length ≤ c := by omega
        simp [long, bound]
      · intro index beyond
        rw [sumOwners] at beyond
        rw [sumPhases, sumFailures, bundleEq, Function.update_of_ne (by omega)]
        exact track.beyond index beyond
      · rw [sumOwners, sumPhases]; exact track.created
      · rw [sumOwners, sumPhases, bundleEq]; exact track.fresh
      · intro _ failed
        rw [sumFailures] at failed
        simp at failed
      · intro entry member raw reply found
        rw [sumOwners]
        refine ⟨bound, fun isSome => ?_⟩
        rw [noFinishReply entry member raw reply found] at isSome
        cases isSome
      · intro before raw found
        rw [acceptedEq] at found
        cases found
  | some bytes =>
      have sumOwners : (summarizeReg (regs ++ [.bundle c (some bytes)])).owners = (summarizeReg regs).owners := by
        rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
        simp [stepReg, phase]
      have sumPhases : (summarizeReg (regs ++ [.bundle c (some bytes)])).phases =
          Function.update (summarizeReg regs).phases c .initSent := by
        rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
        simp [stepReg, phase]
      have sumFailures : (summarizeReg (regs ++ [.bundle c (some bytes)])).failures = (summarizeReg regs).failures := by
        rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
        simp [stepReg, phase]
      have bundleOther : ∀ owner, owner ≠ c → bundleOfReg (regs ++ [.bundle c (some bytes)]) owner =
          bundleOfReg regs owner := by
        intro owner other
        rw [bundleOfReg_snoc]
        simp [bundleOfReg, Ne.symm other]
      have bundleSelf : bundleOfReg (regs ++ [.bundle c (some bytes)]) c = some bytes := by
        rw [bundleOfReg_snoc, track.fresh bound phase]
        simp [bundleOfReg]
      rw [published] at logged acceptedEq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, logged, ?_, ?_⟩
      · rw [sumOwners]; exact track.count
      · rw [sumOwners]; exact track.target
      · unfold slotOf
        rw [sumOwners, sumFailures, sumPhases]
        have long : ¬ (summarizeReg regs).owners.length ≤ c := by omega
        simp [long, bound, notFailed]
      · intro index beyond
        rw [sumOwners] at beyond
        rw [sumPhases, sumFailures, bundleOther index (by omega), Function.update_of_ne (by omega)]
        exact track.beyond index beyond
      · intro index short
        rw [sumOwners] at short
        rw [sumPhases]
        by_cases same : index = c
        · rw [same, Function.update_self]
          simp
        · rw [Function.update_of_ne same]
          exact track.created index short
      · intro _ phaseNow
        rw [sumPhases, Function.update_self] at phaseNow
        cases phaseNow
      · intro _ _ _
        rw [published]
        exact ⟨bundleSelf, rfl⟩
      · intro entry member raw reply found
        rw [sumOwners]
        refine ⟨bound, fun isSome => ?_⟩
        rw [noFinishReply entry member raw reply found] at isSome
        cases isSome
      · intro before raw found
        rw [acceptedEq] at found
        cases found


/-- A finish of `c` in the target's bundled slot, forwarded as the ServerAuth finish with its reply, keeps the tracking before the stop. -/
theorem track_targetFinish (c : Nat) (input : AuthInput) (regs : List Reg) (emb : Emb KemSK)
    (log : QueryLog ServerAuthSpec) (track : Track c input regs emb log) (open_ : ¬ Stop c regs)
    (bundled : emb.slot = .bundled) (raw : Pqxdh.Bytes) (reply : Option Pqxdh.Bytes) :
    Track c input (regs ++ [.finish c raw reply]) emb (log ++ [⟨.inr (.finish raw), reply⟩]) := by
  obtain ⟨notAccepted, _⟩ := stop_open c regs open_
  obtain ⟨below, bound, notFailed, notFresh⟩ := slotOf_bundled c input _ (track.slot ▸ bundled)
  have notAbsent := track.created c below
  have stepEq := PqxdhDeploymentServerAuthEvent.summarizeReg_snoc regs (.finish c raw reply)
  have sumOwners : (summarizeReg (regs ++ [.finish c raw reply])).owners = (summarizeReg regs).owners := by
    rw [stepEq]
    cases reply <;> simp only [stepReg] <;> split_ifs <;> rfl
  have sumFailures : (summarizeReg (regs ++ [.finish c raw reply])).failures = (summarizeReg regs).failures := by
    rw [stepEq]
    cases reply <;> simp only [stepReg] <;> split_ifs <;> rfl
  have phaseOther : ∀ owner, owner ≠ c →
      (summarizeReg (regs ++ [.finish c raw reply])).phases owner = (summarizeReg regs).phases owner := by
    intro owner other
    rw [stepEq]
    cases reply <;> simp only [stepReg] <;> split_ifs <;> simp [Function.update_of_ne other]
  have phaseSelf : (summarizeReg (regs ++ [.finish c raw reply])).phases c =
      if (summarizeReg regs).phases c = .initSent then (if reply.isSome then .established else .aborted)
      else (summarizeReg regs).phases c := by
    rw [stepEq]
    cases reply <;> simp only [stepReg] <;> split_ifs <;> simp_all
  have bundleEq : ∀ owner, bundleOfReg (regs ++ [.finish c raw reply]) owner = bundleOfReg regs owner := by
    intro owner
    rw [bundleOfReg_snoc]
    simp [bundleOfReg]
  have acceptedEq : accepted c (regs ++ [.finish c raw reply]) =
      acceptCheck c (summarizeReg regs) regs (.finish c raw reply) := by
    rw [PqxdhDeploymentServerAuthEvent.accepted_snoc, notAccepted]
    rfl
  have newNotFresh : (summarizeReg (regs ++ [.finish c raw reply])).phases c ≠ .fresh := by
    rw [phaseSelf]
    split_ifs <;> simp_all
  have terminal : (summarizeReg regs).phases c = .aborted ∨ (summarizeReg regs).phases c = .established →
      (summarizeReg (regs ++ [.finish c raw reply])).phases c = (summarizeReg regs).phases c := by
    intro done
    rw [phaseSelf]
    rcases done with done | done <;> simp [done]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sumOwners]; exact track.count
  · rw [sumOwners]; exact track.target
  · rw [bundled]
    unfold slotOf
    rw [sumOwners, sumFailures]
    have long : ¬ (summarizeReg regs).owners.length ≤ c := by omega
    simp [long, bound, notFailed, newNotFresh]
  · intro index beyond
    rw [sumOwners] at beyond
    rw [phaseOther index (by omega), sumFailures, bundleEq]
    exact track.beyond index beyond
  · intro index short
    rw [sumOwners] at short
    by_cases same : index = c
    · rw [same, phaseSelf]
      split_ifs <;> simp_all
    · rw [phaseOther index same]
      exact track.created index short
  · intro _ phase
    exact absurd phase newNotFresh
  · intro _ _ _
    rw [bundleEq]
    exact track.sent bound notFailed notFresh
  · intro entry member reg found
    rcases List.mem_append.mp member with old | new
    · exact List.mem_append_left _ (track.logged entry old reg found)
    · rw [List.mem_singleton] at new
      subst new
      simp only [saReg, Option.some.injEq] at found
      rw [← found]
      simp
  · intro entry member raw' reply' found
    rw [sumOwners]
    refine ⟨bound, fun isSome => ?_⟩
    rcases List.mem_append.mp member with old | new
    · obtain ⟨_, success⟩ := track.finished entry old raw' reply' found
      rcases success isSome with accepted | done
      · rw [notAccepted] at accepted
        cases accepted
      · rw [terminal done]
        exact Or.inr done
    · rw [List.mem_singleton] at new
      subst new
      simp only [saReg, Option.some.injEq, Reg.finish.injEq] at found
      obtain ⟨_, rfl, rfl⟩ := found
      by_cases sent : (summarizeReg regs).phases c = .initSent
      · left
        rw [acceptedEq]
        cases reply with
        | none => cases isSome
        | some payload => simp [acceptCheck, sent]
      · right
        rw [phaseSelf]
        cases phase : (summarizeReg regs).phases c <;> simp_all
  · intro before raw' found _
    rw [acceptedEq] at found
    cases reply with
    | none => simp [acceptCheck] at found
    | some payload =>
        simp only [acceptCheck, true_and] at found
        split_ifs at found with sent
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        refine ⟨log, payload, rfl, track.logged, ?_, ?_⟩
        · intro entry member raw'' payload'' found
          obtain ⟨_, success⟩ := track.finished entry member raw'' (some payload'') found
          rcases success rfl with accepted | aborted | established
          · rw [notAccepted] at accepted
            cases accepted
          · rw [sent] at aborted
            cases aborted
          · rw [sent] at established
            cases established
        · exact (track.sent bound notFailed notFresh).1

/-- A bundle or finish of a local owner, which changes only that owner's summary entry, keeps its phase created, adds no first bundle of another owner and can accept only at `c`, with quiet ServerAuth entries, keeps the tracking before the stop. -/
theorem track_local (c : Nat) (input : AuthInput) (regs : List Reg) (emb : Emb KemSK)
    (log : QueryLog ServerAuthSpec) (track : Track c input regs emb log) (open_ : ¬ Stop c regs) (index : Nat)
    (owner : Owner KemSK) (placed : emb.owners[index]? = some (some owner)) (updated : Owner KemSK) (reg : Reg)
    (owners : (stepReg (summarizeReg regs) reg).owners = (summarizeReg regs).owners)
    (others : ∀ other, other ≠ index → (stepReg (summarizeReg regs) reg).phases other = (summarizeReg regs).phases other ∧
      (stepReg (summarizeReg regs) reg).failures other = (summarizeReg regs).failures other)
    (stays : (summarizeReg regs).phases index ≠ .absent → (stepReg (summarizeReg regs) reg).phases index ≠ .absent)
    (bundles : ∀ other, other ≠ index → bundleOfReg [reg] other = none)
    (check : ∀ before raw, acceptCheck c (summarizeReg regs) regs reg = some (before, raw) → index = c ∧ before = regs)
    (extra : QueryLog ServerAuthSpec) (quiet : ∀ entry ∈ extra, saReg c entry = none) :
    Track c input (regs ++ [reg]) { emb with owners := emb.owners.set index (some updated) } (log ++ extra) := by
  obtain ⟨notAccepted, _⟩ := stop_open c regs open_
  have below : index < (summarizeReg regs).owners.length := by
    rw [← track.count]
    exact (List.getElem?_eq_some_iff.mp placed).1
  have notTarget : index = c → (summarizeReg regs).owners[c]? ≠ some (inputBinding input) := by
    intro same bound
    have := (track.target c).mpr ⟨rfl, bound⟩
    rw [← same, placed] at this
    simp at this
  have stepEq := PqxdhDeploymentServerAuthEvent.summarizeReg_snoc regs reg
  have bundleEq : ∀ other, other ≠ index → bundleOfReg (regs ++ [reg]) other = bundleOfReg regs other := by
    intro other different
    rw [bundleOfReg_snoc, bundles other different, Option.or_none]
  have targetOther : (summarizeReg regs).owners[c]? = some (inputBinding input) → c ≠ index :=
    fun bound same => notTarget same.symm bound
  have acceptedEq : ∀ before raw, accepted c (regs ++ [reg]) = some (before, raw) → index = c ∧ before = regs := by
    intro before raw found
    rw [PqxdhDeploymentServerAuthEvent.accepted_snoc, notAccepted, Option.none_or] at found
    exact check before raw found
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stepEq, owners, List.length_set]; exact track.count
  · intro other
    rw [stepEq, owners]
    by_cases same : other = index
    · subst same
      rw [List.getElem?_set_self (by rw [track.count]; exact below)]
      constructor
      · intro impossible
        simp at impossible
      · rintro ⟨rfl, bound⟩
        exact absurd bound (notTarget rfl)
    · rw [List.getElem?_set_ne (Ne.symm same)]
      exact track.target other
  · show emb.slot = _
    rw [track.slot, stepEq]
    by_cases same : index = c
    · subst same
      unfold slotOf
      rw [owners]
      have long : ¬ (summarizeReg regs).owners.length ≤ index := by omega
      simp [long, notTarget rfl]
    · exact (slotOf_congr c input _ _ owners (others c (Ne.symm same)).2 (others c (Ne.symm same)).1).symm
  · intro other beyond
    rw [stepEq, owners] at beyond
    rw [stepEq, (others other (by omega)).1, (others other (by omega)).2, bundleEq other (by omega)]
    exact track.beyond other beyond
  · intro other short
    rw [stepEq, owners] at short
    rw [stepEq]
    by_cases same : other = index
    · subst same
      exact stays (track.created other short)
    · rw [(others other same).1]
      exact track.created other short
  · intro bound phase
    rw [stepEq, owners] at bound
    rw [stepEq, (others c (targetOther bound)).1] at phase
    rw [bundleEq c (targetOther bound)]
    exact track.fresh bound phase
  · intro bound failed phase
    rw [stepEq, owners] at bound
    rw [stepEq, (others c (targetOther bound)).2] at failed
    rw [stepEq, (others c (targetOther bound)).1] at phase
    rw [bundleEq c (targetOther bound)]
    exact track.sent bound failed phase
  · intro entry member other found
    rcases List.mem_append.mp member with old | new
    · exact List.mem_append_left _ (track.logged entry old other found)
    · rw [quiet entry new] at found
      cases found
  · intro entry member raw reply found
    rcases List.mem_append.mp member with old | new
    · obtain ⟨bound, success⟩ := track.finished entry old raw reply found
      rw [stepEq, owners, (others c (targetOther bound)).1]
      refine ⟨bound, fun isSome => ?_⟩
      rcases success isSome with accepted | rest
      · rw [notAccepted] at accepted
        cases accepted
      · exact Or.inr rest
    · rw [quiet entry new] at found
      cases found
  · intro before raw found bound
    obtain ⟨same, rfl⟩ := acceptedEq before raw found
    exact absurd bound (notTarget same)


/-- The journal of a mapped computation is the journal of the computation. -/
theorem record_map_mem {α β : Type} (f : α → β) (work : OracleComp ServerAuthSpec α) (outcome : β × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (PqxdhServerAuthApiJournal.record (f <$> work))) :
    ∃ value, outcome.1 = f value ∧ (value, outcome.2) ∈ support (PqxdhServerAuthApiJournal.record work) := by
  rw [map_eq_bind_pure_comp, record_bind] at member
  simp only [mem_support_bind_iff, support_map, Set.mem_image] at member
  obtain ⟨step, stepMember, inner, innerMember, rfl⟩ := member
  rw [record_pure _ inner innerMember]
  exact ⟨step.1, rfl, by simpa using stepMember⟩

/-- The journal of a lifted query is that query with its reply, and the state is kept. -/
theorem record_lift {σ : Type} (query : ServerAuthSpec.Domain) (state : σ)
    (outcome : (ServerAuthSpec.Range query × σ) × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (PqxdhServerAuthApiJournal.record
      ((StateT.lift (ServerAuthSpec.query query : OracleComp ServerAuthSpec _) : StateT σ (OracleComp ServerAuthSpec) _).run
        state))) :
    ∃ reply, outcome = ((reply, state), [⟨query, reply⟩]) := by
  simp only [StateT.run_lift, bind_pure_comp] at member
  exact record_query query _ outcome member

/-- A forwarded registration query keeps the state and journals the query. -/
theorem forward_lift {σ : Type} (query : ServerAuthQuery) (state : σ)
    (outcome : (QuerySpec query × σ) × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (PqxdhServerAuthApiJournal.record
      ((StateT.lift (forward query) : StateT σ (OracleComp ServerAuthSpec) _).run state))) :
    ∃ reply, outcome = ((reply, state), [⟨.inr query, reply⟩]) :=
  record_lift (.inr query) state outcome member


/-- The summary facts of a local owner's bundle. -/
theorem local_bundle (c : Nat) (regs : List Reg) (index : Nat) (reply : Option Pqxdh.Bytes) :
    (stepReg (summarizeReg regs) (.bundle index reply)).owners = (summarizeReg regs).owners ∧
    (∀ other, other ≠ index → (stepReg (summarizeReg regs) (.bundle index reply)).phases other =
      (summarizeReg regs).phases other ∧
      (stepReg (summarizeReg regs) (.bundle index reply)).failures other = (summarizeReg regs).failures other) ∧
    ((summarizeReg regs).phases index ≠ .absent →
      (stepReg (summarizeReg regs) (.bundle index reply)).phases index ≠ .absent) ∧
    (∀ other, other ≠ index → bundleOfReg [.bundle index reply] other = none) ∧
    (∀ before raw, acceptCheck c (summarizeReg regs) regs (.bundle index reply) = some (before, raw) →
      index = c ∧ before = regs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases reply <;> simp only [stepReg] <;> split_ifs <;> rfl
  · intro other different
    cases reply <;> simp only [stepReg] <;> split_ifs <;> simp [Function.update_of_ne different]
  · intro created
    cases reply <;> simp only [stepReg] <;> split_ifs <;> simp_all
  · intro other different
    cases reply <;> simp [bundleOfReg, Ne.symm different]
  · intro before raw found
    simp [acceptCheck] at found

/-- The summary facts of a local owner's finish. -/
theorem local_finish (c : Nat) (regs : List Reg) (index : Nat) (raw : Pqxdh.Bytes) (reply : Option Pqxdh.Bytes) :
    (stepReg (summarizeReg regs) (.finish index raw reply)).owners = (summarizeReg regs).owners ∧
    (∀ other, other ≠ index → (stepReg (summarizeReg regs) (.finish index raw reply)).phases other =
      (summarizeReg regs).phases other ∧
      (stepReg (summarizeReg regs) (.finish index raw reply)).failures other = (summarizeReg regs).failures other) ∧
    ((summarizeReg regs).phases index ≠ .absent →
      (stepReg (summarizeReg regs) (.finish index raw reply)).phases index ≠ .absent) ∧
    (∀ other, other ≠ index → bundleOfReg [.finish index raw reply] other = none) ∧
    (∀ before raw', acceptCheck c (summarizeReg regs) regs (.finish index raw reply) = some (before, raw') →
      index = c ∧ before = regs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases reply <;> simp only [stepReg] <;> split_ifs <;> rfl
  · intro other different
    cases reply <;> simp only [stepReg] <;> split_ifs <;> simp [Function.update_of_ne different]
  · intro created
    cases reply <;> simp only [stepReg] <;> split_ifs <;> simp_all
  · intro other _
    simp [bundleOfReg]
  · intro before raw' found
    cases reply with
    | none => simp [acceptCheck] at found
    | some payload =>
        simp only [acceptCheck] at found
        split_ifs at found with accepting
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        exact ⟨accepting.1, found.1.symm⟩

open Classical in
/-- One step of the frozen program under the embedding, before the stop, keeps the tracking. -/
theorem track_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat) (input : AuthInput)
    (journal : List (SourceEntry KemSK)) (emb : Emb KemSK) (log : QueryLog ServerAuthSpec)
    (track : Track c input (regsOfSource journal) emb log) (open_ : ¬ stopAt c journal)
    (query : (SourceSpec KemSK).Domain)
    (outcome : ((SourceSpec KemSK).Range query × Emb KemSK) × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (PqxdhServerAuthApiJournal.record ((embed setup codec c input query).run emb))) :
    Track c input (regsOfSource (journal ++ [⟨query, outcome.1.1⟩])) outcome.1.2 (log ++ outcome.2) := by
  have open' : ¬ Stop c (regsOfSource journal) := open_
  obtain ⟨_, notFailed⟩ := stop_open c _ open'
  rw [PqxdhDeploymentServerAuthEvent.regsOfSource_append]
  rcases query with (coin | request) | ⟨index, field⟩
  · obtain ⟨reply, rfl⟩ := record_lift (.inl coin) emb outcome member
    simpa [regOfSource] using track_quiet c input _ emb log track open' _ (by simp [saReg])
  · cases request with
    | create pin keyId =>
        rw [PqxdhDeploymentServerAuthLocal.embed_create] at member
        by_cases chosen : emb.owners.length = c ∧ emb.slot = .waiting ∧ (pin, keyId) = inputBinding input
        · rw [ite_eq_left chosen] at member
          obtain rfl := record_pure _ outcome member
          have stepped := track_create c input _ emb log track open' pin keyId none
            { emb with owners := emb.owners ++ [none], slot := .fresh } rfl (iff_of_true rfl ⟨chosen.1, chosen.2.2⟩)
            (by simp [chosen.1, chosen.2.2]) [] (by simp)
          rw [chosen.1] at stepped
          simpa [regOfSource] using stepped
        · rw [ite_eq_right chosen] at member
          obtain ⟨owner, outcomeEq, created⟩ := record_map_mem _ _ outcome member
          have quiet := record_quiet _ (coins_quiet _) _ created
          have waiting : emb.owners.length = c → emb.slot = .waiting := by
            intro atC
            rw [track.slot]
            unfold slotOf
            rw [← track.count, atC]
            simp
          have notChosen : ¬ (emb.owners.length = c ∧ (pin, keyId) = inputBinding input) :=
            fun both => chosen ⟨both.1, waiting both.1, both.2⟩
          have stepped := track_create c input _ emb log track open' pin keyId (some owner) outcome.1.2
            (by rw [outcomeEq]) (iff_of_false (by simp) notChosen)
            (by
              rw [outcomeEq]
              by_cases atC : emb.owners.length = c
              · have other : (pin, keyId) ≠ inputBinding input := fun bound => notChosen ⟨atC, bound⟩
                simp [atC, waiting atC, other]
              · simp [atC])
            outcome.2 (fun entry member => saReg_quiet c entry (quiet entry member))
          have handle : outcome.1.1 = emb.owners.length := by rw [outcomeEq]
          simpa [regOfSource, handle] using stepped
    | bundle index =>
        rw [PqxdhDeploymentServerAuthLocal.embed_bundle] at member
        cases found : emb.owners[index]? with
        | none =>
            simp only [found] at member
            obtain rfl := record_pure _ outcome member
            have beyond : (summarizeReg (regsOfSource journal)).owners.length ≤ index := by
              rw [← track.count]
              exact List.getElem?_eq_none_iff.mp found
            have absent := (track.beyond index beyond).1
            have stepped := track_silent c input _ emb log track open' (.bundle index none)
              (by simp [stepReg, absent]) rfl (fun _ => by simp [bundleOfReg]) [] (by simp) (by simp)
            simpa [regOfSource] using stepped
        | some entry =>
            cases entry with
            | none =>
                obtain ⟨atC, bound⟩ := (track.target index).mp found
                subst atC
                simp only [found] at member
                by_cases fresh : emb.slot = .fresh
                · rw [ite_eq_left fresh] at member
                  obtain rfl := record_pure _ outcome member
                  simpa [regOfSource] using track_targetBundle index input _ emb log track open' fresh
                · rw [ite_eq_right fresh] at member
                  obtain rfl := record_pure _ outcome member
                  have notFresh : (summarizeReg (regsOfSource journal)).phases index ≠ .fresh := by
                    intro phase
                    apply fresh
                    rw [track.slot]
                    unfold slotOf
                    have long : ¬ (summarizeReg (regsOfSource journal)).owners.length ≤ index := by
                      rw [← track.count]
                      have := (List.getElem?_eq_some_iff.mp found).1
                      omega
                    simp [long, bound, notFailed, phase]
                  have stepped := track_silent index input _ emb log track open' (.bundle index none)
                    (by simp [stepReg, notFresh]) rfl (fun _ => by simp [bundleOfReg]) [] (by simp) (by simp)
                  simpa [regOfSource] using stepped
            | some owner =>
                simp only [found] at member
                obtain ⟨result, outcomeEq, bundled⟩ := record_map_mem _ _ outcome member
                have quiet := record_quiet _ (coins_quiet _) _ bundled
                obtain ⟨owners, others, stays, bundles, check⟩ :=
                  local_bundle c (regsOfSource journal) index result.1
                have stepped := track_local c input _ emb log track open' index owner found result.2
                  (.bundle index result.1) owners others stays bundles check outcome.2
                  (fun entry member => saReg_quiet c entry (quiet entry member))
                rw [outcomeEq]
                simpa [regOfSource] using stepped
    | accept raw =>
        obtain ⟨reply, rfl⟩ := forward_lift (.accept raw) emb outcome member
        have stepped := track_silent c input _ emb log track open' (.accept raw reply) rfl rfl
          (fun _ => by simp [bundleOfReg]) [⟨.inr (.accept raw), reply⟩]
          (by simp [saReg]) (by simp [saReg])
        simpa [regOfSource] using stepped
    | build session payload =>
        obtain ⟨reply, rfl⟩ := forward_lift (.build session payload) emb outcome member
        have stepped := track_silent c input _ emb log track open' (.build session payload reply) rfl rfl
          (fun _ => by simp [bundleOfReg]) [⟨.inr (.build session payload), reply⟩]
          (by simp [saReg]) (by simp [saReg])
        simpa [regOfSource] using stepped
    | finish index raw =>
        rw [PqxdhDeploymentServerAuthLocal.embed_finish] at member
        cases found : emb.owners[index]? with
        | none =>
            simp only [found] at member
            obtain rfl := record_pure _ outcome member
            have beyond : (summarizeReg (regsOfSource journal)).owners.length ≤ index := by
              rw [← track.count]
              exact List.getElem?_eq_none_iff.mp found
            have absent := (track.beyond index beyond).1
            have stepped := track_silent c input _ emb log track open' (.finish index raw none)
              (by simp [stepReg, absent]) rfl (fun _ => by simp [bundleOfReg]) [] (by simp) (by simp)
            simpa [regOfSource] using stepped
        | some entry =>
            cases entry with
            | none =>
                obtain ⟨atC, bound⟩ := (track.target index).mp found
                subst atC
                simp only [found] at member
                by_cases bundled : emb.slot = .bundled
                · rw [ite_eq_left bundled] at member
                  obtain ⟨reply, rfl⟩ := record_query (.inr (.finish raw)) _ outcome member
                  simpa [regOfSource] using track_targetFinish index input _ emb log track open' bundled raw reply
                · rw [ite_eq_right bundled] at member
                  obtain rfl := record_pure _ outcome member
                  have notSent : (summarizeReg (regsOfSource journal)).phases index ≠ .initSent := by
                    intro phase
                    apply bundled
                    rw [track.slot]
                    unfold slotOf
                    have long : ¬ (summarizeReg (regsOfSource journal)).owners.length ≤ index := by
                      rw [← track.count]
                      have := (List.getElem?_eq_some_iff.mp found).1
                      omega
                    simp [long, bound, notFailed, phase]
                  have stepped := track_silent index input _ emb log track open' (.finish index raw none)
                    (by simp [stepReg, notSent]) rfl (fun _ => by simp [bundleOfReg]) [] (by simp) (by simp)
                  simpa [regOfSource] using stepped
            | some owner =>
                simp only [found] at member
                obtain ⟨result, outcomeEq, finished⟩ := record_map_mem _ _ outcome member
                have quiet := record_quiet _ (simulateQ_quiet _ (localCallbacks_quiet setup codec) _) _ finished
                obtain ⟨owners, others, stays, bundles, check⟩ :=
                  local_finish c (regsOfSource journal) index raw result.1
                have stepped := track_local c input _ emb log track open' index owner found result.2
                  (.finish index raw result.1) owners others stays bundles check outcome.2
                  (fun entry member => saReg_quiet c entry (quiet entry member))
                rw [outcomeEq]
                simpa [regOfSource] using stepped
    | hmac key message =>
        obtain ⟨reply, rfl⟩ := forward_lift (.hmac key message) emb outcome member
        simpa [regOfSource] using track_quiet c input _ emb log track open' _ (by simp [saReg])
    | hash bytes =>
        obtain ⟨reply, rfl⟩ := forward_lift (.hash bytes) emb outcome member
        simpa [regOfSource] using track_quiet c input _ emb log track open' _ (by simp [saReg])
    | reveal keyId =>
        obtain ⟨reply, rfl⟩ := forward_lift (.reveal keyId) emb outcome member
        simpa [regOfSource] using track_quiet c input _ emb log track open' _ (by simp [saReg])
  · obtain rfl := record_pure _ outcome member
    simpa [regOfSource] using track_quiet c input _ emb log track open' [] (by simp)


/-- The frozen program under the embedding keeps the tracking from every tracked state: on every outcome, the final journal's registration view, the final embedding state and the ServerAuth journal extended by the run's own journal are tracked. -/
theorem track_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat) (input : AuthInput)
    (program : OracleComp (SourceSpec KemSK) Result) (journal : List (SourceEntry KemSK)) (emb : Emb KemSK)
    (log : QueryLog ServerAuthSpec) (track : Track c input (regsOfSource journal) emb log)
    (outcome : ((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (PqxdhServerAuthApiJournal.record (run setup codec c input program journal emb))) :
    Track c input (regsOfSource outcome.1.1.2) outcome.1.2 (log ++ outcome.2) := by
  induction program using OracleComp.inductionOn generalizing journal emb log outcome with
  | pure value =>
      have pureEq : run setup codec c input (pure value : OracleComp (SourceSpec KemSK) Result) journal emb =
          pure ((value, journal), emb) := by
        simp [run]
      rw [pureEq] at member
      obtain rfl := record_pure _ outcome member
      simpa using track
  | query_bind query next ih =>
      rw [run_query_bind] at member
      by_cases stopped : stopAt c journal
      · rw [ite_eq_left stopped] at member
        exact ih (dflt query) journal emb log track outcome member
      · rw [ite_eq_right stopped, record_bind] at member
        simp only [mem_support_bind_iff, support_map, Set.mem_image] at member
        obtain ⟨step, stepMember, inner, innerMember, rfl⟩ := member
        have stepped := track_step setup codec c input journal emb log track stopped query step stepMember
        have final := ih step.1.1 _ _ _ stepped inner innerMember
        simpa [List.append_assoc] using final

/-- On every outcome of `R_c`, the registration view of its frozen journal, its final embedding state and its own ServerAuth journal are tracked. -/
theorem adversary_track (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (program : OracleComp (SourceSpec KemSK) Result) (input : AuthInput)
    (outcome : ((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (adversary setup codec c program input)) :
    Track c input (regsOfSource outcome.1.1.2) outcome.1.2 outcome.2 := by
  simpa using track_run setup codec c input program [] Emb.empty [] (track_empty c input) outcome member

/-- On every outcome of `R_c` whose frozen journal has the A1 failure of `c` under the input's binding, `R_c`'s own ServerAuth journal has a successful finish and no session with both an earlier publication of the accepted decoded record and an accept carrying the input's published keys. -/
theorem adversary_unmatched (crypto : Pqxdh.Crypto) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (c : Nat) (program : OracleComp (SourceSpec KemSK) Result) (input : AuthInput)
    (outcome : ((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec)
    (member : outcome ∈ support (adversary setup codec c program input))
    (failure : Unmatched crypto codec (inputBinding input) c (regsOfSource outcome.1.1.2)) :
    (∃ raw payload, (⟨.inr (.finish raw), some payload⟩ : SaEntry) ∈ outcome.2) ∧
    ∀ index, PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index outcome.2 →
      ∀ acceptRaw candidate keys, (⟨.inr (.accept acceptRaw), some index⟩ : SaEntry) ∈ outcome.2 →
        candidateOf codec acceptRaw = some candidate → acceptedKeys crypto candidate = some keys →
        keysOfBundle codec input.phase1 ≠ some keys :=
  track_unmatched crypto codec c input _ _ _ (adversary_track setup codec c program input outcome member) failure


end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.saReg_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.saReg_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.simulateQ_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.simulateQ_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.coins_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.coins_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.map_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.map_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.localCallbacks_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.localCallbacks_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_query

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.run_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.run_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.beforeAcceptance_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.beforeAcceptance_last

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_unmatched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_unmatched

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.stop_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.stop_open

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.bundleOfReg_snoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.bundleOfReg_snoc

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_silent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_silent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.slotOf_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.slotOf_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.slotOf_bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.slotOf_bundled

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.slotOf_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.slotOf_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_targetBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_targetBundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_targetFinish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_targetFinish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_local

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_map_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_map_mem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.record_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.forward_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.forward_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.local_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.local_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.local_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.local_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.track_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.adversary_track' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.adversary_track

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.adversary_unmatched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack.adversary_unmatched
