-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld

/-! Private installation provenance is recorded only from actual successful world replies. Erasing these annotations restores the complete executable world; equal key bytes never determine a slot. This is not yet the logical-kernel selected-input compiler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftOrigins
open PqxdhRecordLiftInterface
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- None records no hidden installation origin; ordinary world lookup still distinguishes an absent handle from a caller-known kernel. -/
structure Origins (n : Nat) where
  peers : Std.U64 → Option (Slot n)
  owners : Nat → Option (Slot n)

def empty : Origins n := ⟨fun _ => none, fun _ => none⟩

def origin : KernelRef n → Option (Slot n)
  | .known _ => none
  | .hidden slot => some slot

/-- The original request and its actual success reply determine provenance. Refusals do not change it, and append starts without a hidden origin. -/
def annotate : (query : (WorldSpec n).Domain) → (WorldSpec n).Range query → Origins n → Origins n
  | .inr (.inl (.inr (.installServer keyId _ ref))), success, state =>
      if @Eq Bool success true then { state with peers := Function.update state.peers keyId (origin ref) } else state
  | .inr (.inl (.inr (.installBeacon owner _ ref))), success, state =>
      if @Eq Bool success true then { state with owners := Function.update state.owners owner (origin ref) } else state
  | .inr (.inl (.inr (.appendOwner _ _ _))), owner, state =>
      { state with owners := Function.update state.owners owner none }
  | _, _, state => state

abbrev State (n : Nat) := PqxdhRecordLiftWorld.State n × Origins n

def initial : State n := (PqxdhRecordLiftWorld.initial, empty)

/-- Run the literal world request first, then annotate its returned success or append handle. No primitive, sampler, log or caller-visible result is replaced. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (WorldSpec n) (StateT (State n) ProbComp) := fun query state => do
  let result ← (PqxdhRecordLiftWorld.handler setup codec route query).run state.1
  pure (result.1, (result.2, annotate query result.1 state.2))

/-- Removing the private annotation restores the entire original query reply and world poststate. -/
theorem handler_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (state : State n) :
    Prod.map id Prod.fst <$> (handler setup codec route query).run state =
      (PqxdhRecordLiftWorld.handler setup codec route query).run state.1 := by
  simp [handler, StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def]

/-- Every adaptive continuation has the same complete execution after provenance erasure. -/
theorem schedule_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) {Result : Type}
    (client : OracleComp (WorldSpec n) Result) (state : State n) :
    Prod.map id Prod.fst <$> (simulateQ (handler setup codec route) client).run state =
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) client).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (handler_erase setup codec route) client state

/-- Every recorded hidden origin has already consumed precisely its installed role. -/
def Marked (state : State n) : Prop :=
  (∀ keyId slot, state.2.peers keyId = some slot → state.1.used slot .server = true) ∧
    (∀ owner slot, state.2.owners owner = some slot → state.1.used slot .beacon = true)

/-- Distinct handles cannot be annotated with the same hidden slot in the same role. -/
def Unique (state : Origins n) : Prop :=
  (∀ left right slot, state.peers left = some slot → state.peers right = some slot → left = right) ∧
    (∀ left right slot, state.owners left = some slot → state.owners right = some slot → left = right)

/-- The actual successful installation reply implies the world consumed the requested hidden role. -/
def MarkedReply (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query)
    (after : PqxdhRecordLiftWorld.State n) : Prop :=
  match query with
  | .inr (.inl (.inr (.installServer _ _ (.hidden slot)))) => reply = true → after.used slot .server = true
  | .inr (.inl (.inr (.installBeacon _ _ (.hidden slot)))) => reply = true → after.used slot .beacon = true
  | _ => True

/-- Successful hidden installations began with their role unused; this is derived from the executable world, not a frame hypothesis. -/
def UnusedReply (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query)
    (before : PqxdhRecordLiftWorld.State n) : Prop :=
  match query with
  | .inr (.inl (.inr (.installServer _ _ (.hidden slot)))) => reply = true → before.used slot .server = false
  | .inr (.inl (.inr (.installBeacon _ _ (.hidden slot)))) => reply = true → before.used slot .beacon = false
  | _ => True

/-- The provenance annotations start empty, including any caller-supplied initial known peers. -/
theorem initial_facts : Marked (initial : State n) ∧ Unique (empty : Origins n) := by
  simp [Marked, Unique, initial, empty]

/-- Successful replies carry the world-derived admission and marker facts, including the exact charged state used by capability dispatch. -/
theorem reply_facts (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : PqxdhRecordLiftWorld.State n) (result : (WorldSpec n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.handler setup codec route query).run state)) :
    MarkedReply query result.1 result.2 ∧ UnusedReply query result.1 state := by
  rcases query with created | ((coin | query) | record)
  all_goals try exact ⟨trivial, trivial⟩
  cases query
  all_goals try exact ⟨trivial, trivial⟩
  all_goals rename_i target shell ref
  all_goals cases ref
  all_goals try exact ⟨trivial, trivial⟩
  all_goals rename_i slot
  all_goals rcases result with ⟨reply, after⟩
  all_goals simp only [MarkedReply, UnusedReply]
  all_goals constructor
  all_goals intro success
  all_goals subst reply
  all_goals simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.effects,
    PqxdhRecordLiftWorld.capability, StateT.run] at supported
  · exact PqxdhRecordLiftWorld.installServer_marks target shell slot _ after supported
  · exact (PqxdhRecordLiftWorld.installServer_admitted target shell (.hidden slot) _ after supported).2
  · exact PqxdhRecordLiftWorld.installBeacon_marks target shell slot _ after supported
  · exact (PqxdhRecordLiftWorld.installBeacon_admitted target shell (.hidden slot) _ after supported).2

/-- Updating one optional origin preserves a property when the new origin has it. -/
theorem update_property {Handle : Type} [DecidableEq Handle]
    (table : Handle → Option (Slot n)) (property : Slot n → Prop)
    (target : Handle) (value : Option (Slot n))
    (prior : ∀ handle slot, table handle = some slot → property slot)
    (fresh : ∀ slot, value = some slot → property slot) :
    ∀ handle slot, Function.update table target value handle = some slot → property slot := by
  intro handle slot found
  by_cases same : handle = target
  · exact fresh slot (by simpa [same] using found)
  · exact prior handle slot (by simpa [Function.update_of_ne same] using found)

/-- Updating to an absent hidden slot, or clearing an origin, preserves uniqueness. -/
theorem update_unique {Handle : Type} [DecidableEq Handle]
    (table : Handle → Option (Slot n)) (target : Handle) (value : Option (Slot n))
    (prior : ∀ left right slot, table left = some slot → table right = some slot → left = right)
    (fresh : ∀ handle slot, value = some slot → table handle ≠ some slot) :
    ∀ left right slot, Function.update table target value left = some slot →
      Function.update table target value right = some slot → left = right := by
  intro left right slot hl hr
  by_cases l : left = target <;> by_cases r : right = target
  · exact l.trans r.symm
  · exact False.elim (fresh right slot (by simpa [l] using hl)
      (by simpa [Function.update_of_ne r] using hr))
  · exact False.elim (fresh left slot (by simpa [r] using hr)
      (by simpa [Function.update_of_ne l] using hl))
  · exact prior left right slot (by simpa [Function.update_of_ne l] using hl)
      (by simpa [Function.update_of_ne r] using hr)

/-- Persistent world markers retain every existing annotation's marker fact. -/
theorem marked_persists (before after : PqxdhRecordLiftWorld.State n) (origins : Origins n)
    (marked : Marked (before, origins)) (persistent : PqxdhRecordLiftWorld.UsesPersist before after) :
    Marked (after, origins) :=
  ⟨fun handle slot found => persistent slot .server (marked.1 handle slot found),
    fun handle slot found => persistent slot .beacon (marked.2 handle slot found)⟩

/-- Annotation consumes only already-proved successful-reply marker facts; it introduces no world effect. -/
theorem annotate_marked (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query)
    (before after : PqxdhRecordLiftWorld.State n) (origins : Origins n)
    (marked : Marked (before, origins)) (persistent : PqxdhRecordLiftWorld.UsesPersist before after)
    (installed : MarkedReply query reply after) : Marked (after, annotate query reply origins) := by
  have stable := marked_persists before after origins marked persistent
  rcases query with created | ((coin | query) | record)
  all_goals try exact stable
  cases query
  all_goals try exact stable
  case appendOwner sender pin phase =>
    exact ⟨stable.1, update_property (Handle := Nat) _ _ reply none stable.2 (by simp)⟩
  case installServer keyId identity ref =>
    cases reply with
    | false => exact stable
    | true =>
        refine ⟨update_property _ _ keyId (origin ref) stable.1 ?_, stable.2⟩
        cases ref with
        | known kernel => simp [origin]
        | hidden slot =>
            intro other same
            cases Option.some.inj same
            exact installed rfl
  case installBeacon owner shell ref =>
    cases reply with
    | false => exact stable
    | true =>
        refine ⟨stable.1, update_property _ _ owner (origin ref) stable.2 ?_⟩
        cases ref with
        | known kernel => simp [origin]
        | hidden slot =>
            intro other same
            cases Option.some.inj same
            exact installed rfl

/-- The world's unused-role admission rule prevents a newly installed origin from aliasing another handle's hidden slot. -/
theorem annotate_unique (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query)
    (before : PqxdhRecordLiftWorld.State n) (origins : Origins n)
    (marked : Marked (before, origins)) (unique : Unique origins)
    (unused : UnusedReply query reply before) : Unique (annotate query reply origins) := by
  rcases query with created | ((coin | query) | record)
  all_goals try exact unique
  cases query
  all_goals try exact unique
  case appendOwner sender pin phase =>
    exact ⟨unique.1, update_unique (Handle := Nat) _ reply none unique.2 (by simp)⟩
  case installServer keyId identity ref =>
    cases reply with
    | false => exact unique
    | true =>
        refine ⟨update_unique _ keyId (origin ref) unique.1 ?_, unique.2⟩
        cases ref with
        | known kernel => simp [origin]
        | hidden slot =>
            intro handle other same found
            cases Option.some.inj same
            exact Bool.noConfusion ((marked.1 handle slot found).symm.trans (unused rfl))
  case installBeacon owner shell ref =>
    cases reply with
    | false => exact unique
    | true =>
        refine ⟨unique.1, update_unique _ owner (origin ref) unique.2 ?_⟩
        cases ref with
        | known kernel => simp [origin]
        | hidden slot =>
            intro handle other same found
            cases Option.some.inj same
            exact Bool.noConfusion ((marked.2 handle slot found).symm.trans (unused rfl))
/-- Every supported result retains the actual world result and exactly the reply-derived annotation. -/
theorem handler_result (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler setup codec route query).run state)) :
    (result.1, result.2.1) ∈ support ((PqxdhRecordLiftWorld.handler setup codec route query).run state.1) ∧
      result.2.2 = annotate query result.1 state.2 := by
  simp only [handler, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact ⟨member, rfl⟩

/-- Consumed-role attribution and per-role uniqueness are preserved by every actual world operation. -/
theorem handler_facts (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : State n) (result : (WorldSpec n).Range query × State n)
    (marked : Marked state) (unique : Unique state.2)
    (supported : result ∈ support ((handler setup codec route query).run state)) :
    Marked result.2 ∧ Unique result.2.2 := by
  obtain ⟨member, annotation⟩ := handler_result setup codec route query state result supported
  have replies := reply_facts setup codec route query state.1 (result.1, result.2.1) member
  have persistent := PqxdhRecordLiftWorld.handler_persists setup codec route query state.1
    (result.1, result.2.1) member
  have markedAfter := annotate_marked query result.1 state.1 result.2.1 state.2 marked persistent.2 replies.1
  have uniqueAfter := annotate_unique query result.1 state.1 state.2 marked unique replies.2
  simpa only [← annotation] using And.intro markedAfter uniqueAfter

/-- The properties hold throughout every adaptive schedule and are derived from the executable installation checks. -/
theorem schedule_facts {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (state : State n) (marked : Marked state) (unique : Unique state.2)
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route) client).run state)) :
    Marked result.2 ∧ Unique result.2.2 :=
  simulateQ_run_preservesInv (handler setup codec route) (fun state => Marked state ∧ Unique state.2)
    (fun query current facts after member => handler_facts setup codec route query current after facts.1 facts.2 member)
    client state ⟨marked, unique⟩ result supported

/-- The initialized wrapper needs no provenance hypothesis for any adaptive execution. -/
theorem initial_schedule_facts {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route) client).run initial)) :
    Marked result.2 ∧ Unique result.2.2 :=
  schedule_facts setup codec route client initial initial_facts.1 initial_facts.2 result supported

/-- A successful Server reply records the requested provenance at exactly its assigned handle. -/
theorem server_success (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (keyId : Std.U64)
    (identity : RawCtxServerRouting.Identity) (ref : KernelRef n) (before after : State n)
    (supported : (true, after) ∈ support ((handler setup codec route
      (.inr (.inl (.inr (.installServer keyId identity ref))))).run before)) :
    after.2.peers = Function.update before.2.peers keyId (origin ref) ∧
      after.2.owners = before.2.owners := by
  have same := (handler_result setup codec route (.inr (.inl (.inr (.installServer keyId identity ref)))) before (true, after) supported).2
  simp only [annotate, ↓reduceIte] at same
  exact ⟨by simpa only [annotate] using congrArg Origins.peers same,
    by simpa only [annotate] using congrArg Origins.owners same⟩

/-- A successful Beacon reply records the requested provenance at exactly its owner handle. -/
theorem beacon_success (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (owner : Nat)
    (shell : BeaconShell) (ref : KernelRef n) (before after : State n)
    (supported : (true, after) ∈ support ((handler setup codec route
      (.inr (.inl (.inr (.installBeacon owner shell ref))))).run before)) :
    after.2.peers = before.2.peers ∧
      after.2.owners = Function.update before.2.owners owner (origin ref) := by
  have same := (handler_result setup codec route (.inr (.inl (.inr (.installBeacon owner shell ref)))) before (true, after) supported).2
  simp only [annotate, ↓reduceIte] at same
  exact ⟨by simpa only [annotate] using congrArg Origins.peers same,
    by simpa only [annotate] using congrArg Origins.owners same⟩

/-- A refused Server request cannot create or erase any provenance annotation. -/
theorem server_refused (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (keyId : Std.U64)
    (identity : RawCtxServerRouting.Identity) (ref : KernelRef n) (before after : State n)
    (supported : (false, after) ∈ support ((handler setup codec route
      (.inr (.inl (.inr (.installServer keyId identity ref))))).run before)) :
    after.2 = before.2 :=
  (handler_result setup codec route (.inr (.inl (.inr (.installServer keyId identity ref)))) before (false, after) supported).2

/-- A refused Beacon request cannot create or erase any provenance annotation. -/
theorem beacon_refused (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (owner : Nat)
    (shell : BeaconShell) (ref : KernelRef n) (before after : State n)
    (supported : (false, after) ∈ support ((handler setup codec route
      (.inr (.inl (.inr (.installBeacon owner shell ref))))).run before)) :
    after.2 = before.2 :=
  (handler_result setup codec route (.inr (.inl (.inr (.installBeacon owner shell ref)))) before (false, after) supported).2

/-- The actual newly appended handle starts without a hidden installation origin. -/
theorem append_result (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (sender : Std.U64)
    (pin : RawCtxServerRouting.Identity) (phase : InactivePhase) (before after : State n) (owner : Nat)
    (supported : (owner, after) ∈ support ((handler setup codec route
      (.inr (.inl (.inr (.appendOwner sender pin phase))))).run before)) :
    after.2.peers = before.2.peers ∧
      after.2.owners = Function.update before.2.owners owner none := by
  have same := (handler_result setup codec route (.inr (.inl (.inr (.appendOwner sender pin phase)))) before (owner, after) supported).2
  exact ⟨by simpa only [annotate] using congrArg Origins.peers same,
    by simpa only [annotate] using congrArg Origins.owners same⟩

/-- Successful hidden Server installation creates an actual source peer whose initial kernel comes from the same cached seed named by its provenance. This is an installation fact, not a claim that later evolved kernels equal their initial value. -/
theorem server_hidden_installed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (keyId : Std.U64)
    (identity : RawCtxServerRouting.Identity) (slot : Slot n) (before after : State n)
    (supported : (true, after) ∈ support ((handler setup codec route
      (.inr (.inl (.inr (.installServer keyId identity (.hidden slot)))))).run before)) :
    ∃ seed server, after.1.server = some server ∧
      server.records.server.peers keyId = some ⟨identity, PqxdhRecordLiftWorld.kernel .server seed, ()⟩ ∧
      after.1.seeds.1 slot = some seed ∧ after.2.peers keyId = some slot := by
  have tagged := (server_success setup codec route keyId identity (.hidden slot) before after supported).1
  have actual := (handler_result setup codec route
    (.inr (.inl (.inr (.installServer keyId identity (.hidden slot))))) before (true, after) supported).1
  simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.effects,
    PqxdhRecordLiftWorld.capability, StateT.run] at actual
  obtain ⟨⟨server, found, vacant⟩, unused⟩ := PqxdhRecordLiftWorld.installServer_admitted
    keyId identity (.hidden slot) _ after.1 actual
  simp only [PqxdhRecordLiftWorld.installServer, StateT.run, found,
    ite_eq_left (And.intro vacant unused), bind_pure_comp, support_map] at actual
  obtain ⟨inner, member, equal⟩ := actual
  obtain ⟨seed, sameKernel, cached, _⟩ :=
    PqxdhRecordLiftWorld.resolve_hidden_facts .server slot _ inner member
  refine ⟨seed, { server with records := { server.records with server :=
    { server.records.server with peers := (Function.update server.records.server.peers keyId
      (some ⟨identity, inner.1, ()⟩)) } } }, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun result => result.2.server) equal).symm
  · simp [sameKernel]
  · simpa only [PqxdhRecordLiftWorld.markUsed] using
      (congrArg (fun result => result.2.seeds.1 slot) equal).symm.trans cached
  · simp [tagged, origin]

/-- Successful hidden Beacon installation publishes the supplied shell and the initial kernel of the same cached seed recorded by its provenance. -/
theorem beacon_hidden_installed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (owner : Nat)
    (shell : BeaconShell) (slot : Slot n) (before after : State n)
    (supported : (true, after) ∈ support ((handler setup codec route
      (.inr (.inl (.inr (.installBeacon owner shell (.hidden slot)))))).run before)) :
    ∃ seed, after.1.owners[owner]? =
        some (.established shell (PqxdhRecordLiftWorld.kernel .beacon seed)) ∧
      after.1.seeds.1 slot = some seed ∧ after.2.owners owner = some slot := by
  have tagged := (beacon_success setup codec route owner shell (.hidden slot) before after supported).2
  have actual := (handler_result setup codec route
    (.inr (.inl (.inr (.installBeacon owner shell (.hidden slot))))) before (true, after) supported).1
  simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.effects,
    PqxdhRecordLiftWorld.capability, StateT.run] at actual
  have admitted := PqxdhRecordLiftWorld.installBeacon_admitted owner shell (.hidden slot) _ after.1 actual
  have bound : owner < before.1.owners.length := (List.getElem?_eq_some_iff.mp admitted.1).1
  simp only [PqxdhRecordLiftWorld.installBeacon, StateT.run, ite_eq_left admitted,
    bind_pure_comp, support_map] at actual
  obtain ⟨inner, member, equal⟩ := actual
  obtain ⟨seed, sameKernel, cached, _⟩ :=
    PqxdhRecordLiftWorld.resolve_hidden_facts .beacon slot _ inner member
  refine ⟨seed, ?_, ?_, ?_⟩
  · have same := (congrArg (fun result => result.2.owners[owner]?) equal).symm
    simpa only [PqxdhRecordLiftWorld.chargeEffect, List.getElem?_set_self bound, sameKernel] using same
  · simpa only [PqxdhRecordLiftWorld.markUsed] using
      (congrArg (fun result => result.2.seeds.1 slot) equal).symm.trans cached
  · simp [tagged, origin]

end BeaconcryptCore.Computational.PqxdhRecordLiftOrigins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.handler_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.handler_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.schedule_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.schedule_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.initial_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.initial_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.reply_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.reply_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.update_property' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.update_property

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.update_unique' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.update_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.marked_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.marked_persists

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.annotate_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.annotate_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.annotate_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.annotate_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.handler_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.handler_result

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.handler_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.handler_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.schedule_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.schedule_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.initial_schedule_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.initial_schedule_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.server_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.server_success

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.beacon_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.beacon_success

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.server_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.server_refused

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.beacon_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.beacon_refused

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.append_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.append_result

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.server_hidden_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.server_hidden_installed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.beacon_hidden_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOrigins.beacon_hidden_installed
