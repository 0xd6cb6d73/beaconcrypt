-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal

/-! The localization of the frozen deployment program at creation index `c` (CE-8). `stack outer inner` is the handler of an inner stateful interpreter run under an outer one, on the product state (`stack_run`). The singleton side is the frozen program under the embedding under the routed source14 handler (`singleSide`); the eager side is the frozen program under `eager`. `localize` shows, for every program that issues no identity, KEM, prekey or one-time read and every drawn target material that the target's first bundle can produce, that the two runs have the same result and the same frozen journal, and the reassembled final state of the singleton side is the eager final state up to the analysis histories. Its run invariant `Inv` holds when the journal has stopped or the embedding is `Ready` and `Consistent` with the journal's registration summary: before the target's creation the summary has no phase at or above the embedding's owner count, while the target is Fresh the summary has it Fresh without a rejected bundle, and after its first bundle the summary has it in the phase class of the singleton's owner. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhSecretInputKdf
open PqxdhJointGapDh (ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentServerAuthEvent (SourceEntry regsOfSource summarizeReg Stop)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Owner Slot Emb embed freezeImpl dflt stopAt inputBinding)
open PqxdhDeploymentServerAuthLocal (State base Phase Pre eager singleStep multiOf phaseOf Bad Ready step_commute
  keep keep_run base_stable)
open PqxdhRegistrationR1Restriction (eraseShared route)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-! ## Stacked handlers -/

/-- An inner stateful interpreter run under an outer one, on the product state. -/
def stack {κ₀ κ₁ : Type} {spec₀ : OracleSpec κ₀} {spec₁ : OracleSpec κ₁} {σ τ : Type}
    (outer : QueryImpl spec₁ (StateT τ ProbComp)) (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁))) :
    QueryImpl spec₀ (StateT (σ × τ) ProbComp) :=
  (outer.mapStateTBase inner).flattenStateT

/-- One stacked step runs the inner step under the outer interpreter. -/
theorem stack_apply {κ₀ κ₁ : Type} {spec₀ : OracleSpec κ₀} {spec₁ : OracleSpec κ₁} {σ τ : Type}
    (outer : QueryImpl spec₁ (StateT τ ProbComp)) (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (query : spec₀.Domain) (state : σ × τ) :
    (stack outer inner query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ outer ((inner query).run state.1)).run state.2 :=
  rfl

/-- A whole program under an inner interpreter under an outer one is the stacked run, reassociated. -/
theorem stack_run {κ₀ κ₁ : Type} {spec₀ : OracleSpec κ₀} {spec₁ : OracleSpec κ₁} {σ τ α : Type}
    (outer : QueryImpl spec₁ (StateT τ ProbComp)) (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (program : OracleComp spec₀ α) (first : σ) (second : τ) :
    (simulateQ outer ((simulateQ inner program).run first)).run second =
      (fun result => ((result.1, result.2.1), result.2.2)) <$> (simulateQ (stack outer inner) program).run (first, second) :=
  OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT outer inner program first second

/-! ## Simulation under an invariant, avoiding bad queries -/

/-- A state projection commutes with a whole simulation from an invariant state when it commutes with every step that the program can issue, and the invariant is kept by those steps. -/
theorem map_run_inv_bound {κ : Type} {spec : OracleSpec κ} {σ₁ σ₂ α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂) (bad : spec.Domain → Prop) [DecidablePred bad]
    (kept : ∀ query state, ¬ bad query → inv state → ∀ result ∈ support ((impl₁ query).run state), inv result.2)
    (commute : ∀ query state, ¬ bad query → inv state →
      Prod.map id proj <$> (impl₁ query).run state = (impl₂ query).run (proj state))
    (program : OracleComp spec α) (bound : program.IsQueryBoundP bad 0) (state : σ₁) (holds : inv state) :
    Prod.map id proj <$> (simulateQ impl₁ program).run state = (simulateQ impl₂ program).run (proj state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bound
      obtain ⟨allowed, rest⟩ := bound
      have good : ¬ bad query := by
        rcases allowed with free | impossible
        · exact free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      rw [← commute query state good holds, bind_map_left]
      refine bind_congr_of_forall_mem_support _ fun result member => ?_
      have nextBound := rest result.1
      simp only [good, ite_false] at nextBound
      simpa using ih result.1 nextBound result.2 (kept query state good holds result member)

/-! ## The two sides -/

/-- One frozen step: the default after the stop, otherwise the query journaled. -/
theorem freezeImpl_run {κ : Type} {spec : OracleSpec κ} (dfl : (query : spec.Domain) → spec.Range query)
    (stop : List ((query : spec.Domain) × spec.Range query) → Prop) [DecidablePred stop] (query : spec.Domain)
    (journal : List ((query : spec.Domain) × spec.Range query)) :
    (freezeImpl dfl stop query).run journal =
      if stop journal then pure (dfl query, journal)
      else (fun reply => (reply, journal ++ [⟨query, reply⟩])) <$> (spec.query query : OracleComp spec _) := rfl

/-- The routed source14 handler as an interpreter of ServerAuth queries. -/
noncomputable def routed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) : QueryImpl ServerAuthSpec (StateT (State KemSK) ProbComp) :=
  PqxdhRegistrationSchedule.handler setup codec checks seed ∘ₛ route

/-- The journal state. -/
abbrev Journal (KemSK : Type) := List (SourceEntry KemSK)

/-- The singleton side: the frozen program under the embedding under the routed source14 handler, stacked. -/
noncomputable def singleSide (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) :
    QueryImpl (SourceSpec KemSK) (StateT (Journal KemSK × (Emb KemSK × State KemSK)) ProbComp) :=
  stack (stack (routed setup codec checks seed) (embed setup codec c input)) (freezeImpl dflt (stopAt c))

/-- The eager side: the frozen program under the eager handler, stacked. -/
noncomputable def eagerSide (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) :
    QueryImpl (SourceSpec KemSK) (StateT (Journal KemSK × (State KemSK × Phase)) ProbComp) :=
  stack (eager setup codec checks seed c binding pre) (freezeImpl dflt (stopAt c))

/-- A step of the singleton side: frozen after the stop, otherwise one embedding step journaled. -/
theorem singleSide_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (query : (SourceSpec KemSK).Domain)
    (journal : Journal KemSK) (emb : Emb KemSK) (single : State KemSK) :
    (singleSide setup codec checks seed c input query).run (journal, (emb, single)) =
      if stopAt c journal then pure (dflt query, (journal, (emb, single)))
      else (fun result => (result.1.1, (journal ++ [⟨query, result.1.1⟩], (result.1.2, result.2)))) <$>
        singleStep setup codec checks seed c input query emb single := by
  rw [singleSide, stack_apply, freezeImpl_run]
  split
  · simp
  · simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_map, stack_apply, routed, QueryImpl.simulateQ_compose, singleStep, Functor.map_map]

/-- A step of the eager side: frozen after the stop, otherwise one eager step journaled. -/
theorem eagerSide_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) (query : (SourceSpec KemSK).Domain)
    (journal : Journal KemSK) (state : State KemSK × Phase) :
    (eagerSide setup codec checks seed c binding pre query).run (journal, state) =
      if stopAt c journal then pure (dflt query, (journal, state))
      else (fun result => (result.1, (journal ++ [⟨query, result.1⟩], result.2))) <$>
        (eager setup codec checks seed c binding pre query).run state := by
  rw [eagerSide, stack_apply, freezeImpl_run]
  split
  · simp
  · simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_map, Functor.map_map]

/-- Erase the analysis histories of the eager state. -/
def eraseEager (state : Journal KemSK × (State KemSK × Phase)) : Journal KemSK × (State KemSK × Phase) :=
  (state.1, (eraseShared state.2.1, state.2.2))

/-- Reassemble the eager state from the singleton side's state. -/
def reassemble (pre : Pre KemSK) (state : Journal KemSK × (Emb KemSK × State KemSK)) :
    Journal KemSK × (State KemSK × Phase) :=
  (state.1, (eraseShared (multiOf pre state.2.1 state.2.2), phaseOf state.2.1.slot))

/-- The eager side with the histories erased after each step. -/
noncomputable def erasedSide (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) :
    QueryImpl (SourceSpec KemSK) (StateT (Journal KemSK × (State KemSK × Phase)) ProbComp) := fun query =>
  StateT.mk fun state => Prod.map id eraseEager <$> (eagerSide setup codec checks seed c binding pre query).run state

/-- One singleton-side step, reassembled, is one erased eager-side step on the reassembled state. -/
theorem side_commute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (binding : Word32 × Std.U64) (pre : Pre KemSK)
    (bound : inputBinding input = binding) (published : input.phase1 = pre.reply)
    (query : (SourceSpec KemSK).Domain) (good : ¬ Bad query) (state : Journal KemSK × (Emb KemSK × State KemSK))
    (ready : stopAt c state.1 ∨ Ready c pre state.2.1 state.2.2) :
    Prod.map id (reassemble pre) <$> (singleSide setup codec checks seed c input query).run state =
      (erasedSide setup codec checks seed c binding pre query).run (reassemble pre state) := by
  obtain ⟨journal, emb, single⟩ := state
  simp only [erasedSide, StateT.run_mk, reassemble, singleSide_step, eagerSide_step]
  by_cases stopped : stopAt c journal
  · simp only [stopped, ite_true, map_pure]
    rfl
  · simp only [stopped, ite_false, Functor.map_map]
    have ready' : Ready c pre emb single := ready.resolve_left stopped
    have step := congrArg (fun computation => (fun result => (result.1, (journal ++ [⟨query, result.1⟩],
      result.2))) <$> computation)
      (step_commute setup codec checks seed c input binding pre bound published query good emb single ready')
    simp only [Functor.map_map] at step
    exact step

/-! ## The run invariant -/

/-- The embedding is consistent with the journal's registration summary: before the target's creation the embedding holds at most `c` owners, no summary phase exists at or above the embedding's owner count, the Fresh target is Fresh in the summary, and after its first bundle the target's summary phase is the phase class of the singleton's owner. -/
structure Consistent (c : Nat) (journal : Journal KemSK) (emb : Emb KemSK) (single : State KemSK) : Prop where
  waiting : emb.slot = .waiting → emb.owners.length ≤ c
  absent : ∀ index, emb.owners.length ≤ index → (summarizeReg (regsOfSource journal)).phases index = .absent
  fresh : emb.slot = .fresh → (summarizeReg (regsOfSource journal)).phases c = .fresh
  sent : emb.slot = .bundled → ∀ owner, single.owners = [owner] →
    (summarizeReg (regsOfSource journal)).phases c = PqxdhDeploymentEligibility.phaseClass owner.beacon.phase

/-- The run invariant of the singleton side: the journal has stopped, or the embedding is ready and consistent with it. -/
def Inv (c : Nat) (pre : Pre KemSK) (state : Journal KemSK × (Emb KemSK × State KemSK)) : Prop :=
  stopAt c state.1 ∨ (Ready c pre state.2.1 state.2.2 ∧ Consistent c state.1 state.2.1 state.2.2)

/-- Readiness reads only the embedding and the singleton's owners. -/
theorem ready_owners (c : Nat) (pre : Pre KemSK) (emb : Emb KemSK) (single other : State KemSK)
    (ready : Ready c pre emb single) (same : other.owners = single.owners) : Ready c pre emb other :=
  ⟨ready.target, ready.noTarget, ready.placed, by rw [same]; exact ready.singleton, ready.notFailed, ready.createdFresh⟩

/-- Consistency reads only the embedding, the singleton's owners and the journal's summary. -/
theorem consistent_transfer (c : Nat) (journal other : Journal KemSK) (emb : Emb KemSK) (single next : State KemSK)
    (consistent : Consistent c journal emb single) (same : next.owners = single.owners)
    (summary : summarizeReg (regsOfSource other) = summarizeReg (regsOfSource journal)) :
    Consistent c other emb next :=
  ⟨consistent.waiting, fun index above => by rw [summary]; exact consistent.absent index above,
    fun fresh => by rw [summary]; exact consistent.fresh fresh,
    fun bundled owner owned => by rw [summary]; exact consistent.sent bundled owner (same ▸ owned)⟩

/-- An entry that adds no registration entry keeps the summary and the stop. -/
theorem quiet_entry (c : Nat) (journal : Journal KemSK) (entry : SourceEntry KemSK)
    (quiet : PqxdhDeploymentServerAuthEvent.regOfSource entry = none) :
    summarizeReg (regsOfSource (journal ++ [entry])) = summarizeReg (regsOfSource journal) ∧
      (stopAt c (journal ++ [entry]) ↔ stopAt c journal) := by
  simp only [stopAt, PqxdhDeploymentServerAuthEvent.regsOfSource_append, quiet, Option.toList_none, List.append_nil,
    and_self, iff_self]

/-- An accept or build entry keeps the summary and the stop. -/
theorem server_entry (c : Nat) (journal : Journal KemSK) (entry : SourceEntry KemSK)
    (server : (∃ raw reply, PqxdhDeploymentServerAuthEvent.regOfSource entry = some (.accept raw reply)) ∨
      ∃ session payload reply, PqxdhDeploymentServerAuthEvent.regOfSource entry = some (.build session payload reply)) :
    summarizeReg (regsOfSource (journal ++ [entry])) = summarizeReg (regsOfSource journal) ∧
      (stopAt c (journal ++ [entry]) ↔ stopAt c journal) := by
  rcases server with ⟨raw, reply, found⟩ | ⟨session, payload, reply, found⟩
  all_goals simp only [stopAt, Stop, PqxdhDeploymentServerAuthEvent.regsOfSource_append, found, Option.toList_some,
    PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, PqxdhDeploymentServerAuthEvent.accepted_snoc,
    PqxdhDeploymentServerAuthEvent.acceptCheck, PqxdhDeploymentServerAuthEvent.stepReg, Option.or_none, and_self,
    iff_self]

/-- A shared-state operation keeps the owners. -/
theorem onShared_owners {α : Type} (op : NativeGame KemSK α) (state : State KemSK) (result : α × State KemSK)
    (member : result ∈ support ((PqxdhRegistrationSchedule.onShared op).run state)) : result.2.owners = state.owners := by
  rw [PqxdhRegistrationSchedule.onShared_run, support_map] at member
  obtain ⟨inner, _, rfl⟩ := member
  rfl

/-- A step that keeps the embedding and the singleton's owners and adds no phase-changing registration entry keeps the invariant. -/
theorem kept_shared (c : Nat) (pre : Pre KemSK) (journal : Journal KemSK) (emb : Emb KemSK) (single next : State KemSK)
    (entry : SourceEntry KemSK) (ready : Ready c pre emb single)
    (consistent : Consistent c journal emb single) (owners : next.owners = single.owners)
    (keeps : summarizeReg (regsOfSource (journal ++ [entry])) = summarizeReg (regsOfSource journal) ∧
      (stopAt c (journal ++ [entry]) ↔ stopAt c journal)) :
    Inv c pre (journal ++ [entry], (emb, next)) :=
  Or.inr ⟨ready_owners c pre emb single next ready owners,
    consistent_transfer c journal _ emb single next consistent owners keeps.1⟩

/-- A accept keeps the embedding and the singleton's owners. -/
theorem accept_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (raw : Pqxdh.Bytes) (emb : Emb KemSK) (single : State KemSK)
    (result : (((SourceSpec KemSK).Range (.inl (.inr (.accept raw))) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inr (.accept raw))) emb single)) :
    result.1.2 = emb ∧ result.2.owners = single.owners := by
  rw [PqxdhDeploymentServerAuthLocal.singleStep_lift setup codec checks seed c input _ emb single _ rfl] at member
  simp only [route, PqxdhDeploymentServerAuthEmbed.forward, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, PqxdhRegistrationSchedule.handler, support_map, Set.mem_image] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨rfl, onShared_owners _ single inner innerMember⟩

/-- A build keeps the embedding and the singleton's owners. -/
theorem build_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (session : Nat) (payload : Option Pqxdh.Bytes) (emb : Emb KemSK) (single : State KemSK)
    (result : (((SourceSpec KemSK).Range (.inl (.inr (.build session payload))) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inr (.build session payload))) emb single)) :
    result.1.2 = emb ∧ result.2.owners = single.owners := by
  rw [PqxdhDeploymentServerAuthLocal.singleStep_lift setup codec checks seed c input _ emb single _ rfl] at member
  simp only [route, PqxdhDeploymentServerAuthEmbed.forward, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, PqxdhRegistrationSchedule.handler, support_map, Set.mem_image] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨rfl, onShared_owners _ single inner innerMember⟩

/-- A hmac keeps the embedding and the singleton's owners. -/
theorem hmac_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (key : HmacBlock) (message : Pqxdh.Bytes) (emb : Emb KemSK) (single : State KemSK)
    (result : (((SourceSpec KemSK).Range (.inl (.inr (.hmac key message))) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inr (.hmac key message))) emb single)) :
    result.1.2 = emb ∧ result.2.owners = single.owners := by
  rw [PqxdhDeploymentServerAuthLocal.singleStep_lift setup codec checks seed c input _ emb single _ rfl] at member
  simp only [route, PqxdhDeploymentServerAuthEmbed.forward, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, PqxdhRegistrationSchedule.handler, support_map, Set.mem_image] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨rfl, onShared_owners _ single inner innerMember⟩

/-- A hash keeps the embedding and the singleton's owners. -/
theorem hash_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (bytes : Pqxdh.Bytes) (emb : Emb KemSK) (single : State KemSK)
    (result : (((SourceSpec KemSK).Range (.inl (.inr (.hash bytes))) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inr (.hash bytes))) emb single)) :
    result.1.2 = emb ∧ result.2.owners = single.owners := by
  rw [PqxdhDeploymentServerAuthLocal.singleStep_lift setup codec checks seed c input _ emb single _ rfl] at member
  simp only [route, PqxdhDeploymentServerAuthEmbed.forward, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, PqxdhRegistrationSchedule.handler, support_map, Set.mem_image] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨rfl, onShared_owners _ single inner innerMember⟩

/-- A reveal keeps the embedding and the singleton's owners. -/
theorem reveal_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (keyId : Std.U64) (emb : Emb KemSK) (single : State KemSK)
    (result : (((SourceSpec KemSK).Range (.inl (.inr (.reveal keyId))) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inr (.reveal keyId))) emb single)) :
    result.1.2 = emb ∧ result.2.owners = single.owners := by
  rw [PqxdhDeploymentServerAuthLocal.singleStep_lift setup codec checks seed c input _ emb single _ rfl] at member
  simp only [route, PqxdhDeploymentServerAuthEmbed.forward, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, PqxdhRegistrationSchedule.handler, support_map, Set.mem_image] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨rfl, onShared_owners _ single inner innerMember⟩

/-- A coin keeps the embedding and the singleton state. -/
theorem coin_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (coin : Nat) (emb : Emb KemSK) (single : State KemSK)
    (result : (((SourceSpec KemSK).Range (.inl (.inl coin)) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inl coin)) emb single)) :
    result.1.2 = emb ∧ result.2 = single := by
  rw [PqxdhDeploymentServerAuthLocal.singleStep_lift setup codec checks seed c input _ emb single _ rfl] at member
  simp only [route, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    PqxdhRegistrationSchedule.handler, StateT.run_lift, support_map, support_bind, support_pure, Set.mem_image,
    Set.mem_iUnion, Set.mem_singleton_iff] at member
  obtain ⟨inner, ⟨reply, _, rfl⟩, rfl⟩ := member
  exact ⟨rfl, rfl⟩

/-- A registration entry's own owner handle, if it has one. -/
def regOwner : PqxdhDeploymentServerAuthEvent.Reg → Option Nat
  | .create _ _ owner => some owner
  | .bundle owner _ => some owner
  | .finish owner _ _ => some owner
  | _ => none

/-- A registration entry changes the summary's phase and failure flag only at its own owner handle. -/
theorem stepReg_other (summary : PqxdhDeploymentTranscript.Summary) (reg : PqxdhDeploymentServerAuthEvent.Reg)
    (index : Nat) (other : regOwner reg ≠ some index) :
    (PqxdhDeploymentServerAuthEvent.stepReg summary reg).phases index = summary.phases index ∧
      (PqxdhDeploymentServerAuthEvent.stepReg summary reg).failures index = summary.failures index := by
  cases reg with
  | create pin keyId owner =>
      have different : index ≠ owner := fun same => other (by rw [same]; rfl)
      simp [PqxdhDeploymentServerAuthEvent.stepReg, Function.update_of_ne different]
  | bundle owner reply =>
      have different : index ≠ owner := fun same => other (by rw [same]; rfl)
      cases reply <;> simp only [PqxdhDeploymentServerAuthEvent.stepReg] <;> split_ifs <;>
        simp [Function.update_of_ne different]
  | finish owner raw reply =>
      have different : index ≠ owner := fun same => other (by rw [same]; rfl)
      cases reply <;> simp only [PqxdhDeploymentServerAuthEvent.stepReg] <;> split_ifs <;>
        simp [Function.update_of_ne different]
  | accept raw reply => exact ⟨rfl, rfl⟩
  | build session payload reply => exact ⟨rfl, rfl⟩

/-- Every owner entry of a list extended by one owner, other than at the new position, is the old one. -/
theorem lookup_snoc_ne {α : Type} (list : List α) (value : α) (index : Nat) (other : index ≠ list.length) :
    (list ++ [value])[index]? = list[index]? := by
  rcases Nat.lt_or_ge index list.length with below | above
  · exact List.getElem?_append_left below
  · have beyond : list.length < index := lt_of_le_of_ne above (Ne.symm other)
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- The entry at the new position of a list extended by one owner. -/
theorem lookup_snoc_self {α : Type} (list : List α) (value : α) : (list ++ [value])[list.length]? = some value := by
  simp

/-- A create step keeps the invariant. -/
theorem kept_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (pre : Pre KemSK) (pin : Word32) (keyId : Std.U64)
    (journal : Journal KemSK) (emb : Emb KemSK) (single : State KemSK) (stopped : ¬ stopAt c journal)
    (ready : Ready c pre emb single) (consistent : Consistent c journal emb single)
    (result : (((SourceSpec KemSK).Range (.inl (.inr (.create pin keyId))) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inr (.create pin keyId))) emb single)) :
    Inv c pre (journal ++ [⟨.inl (.inr (.create pin keyId)), result.1.1⟩], (result.1.2, result.2)) := by
  have regs : regsOfSource (journal ++ [⟨.inl (.inr (.create pin keyId)), result.1.1⟩]) =
      regsOfSource journal ++ [.create pin keyId result.1.1] := by
    rw [PqxdhDeploymentServerAuthEvent.regsOfSource_append]
    rfl
  have stop : stopAt c (journal ++ [⟨.inl (.inr (.create pin keyId)), result.1.1⟩]) ↔ stopAt c journal := by
    simp only [stopAt, Stop, regs, PqxdhDeploymentServerAuthEvent.accepted_snoc,
      PqxdhDeploymentServerAuthEvent.acceptCheck, Option.or_none, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc,
      PqxdhDeploymentServerAuthEvent.stepReg]
  refine Or.inr ?_
  simp only [singleStep] at member
  rw [PqxdhDeploymentServerAuthLocal.embed_create] at member
  split at member
  · rename_i target
    obtain ⟨atC, waiting, chosen⟩ := target
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    have free := PqxdhDeploymentServerAuthLocal.ready_noTarget c pre emb single ready (Or.inl waiting)
    obtain ⟨owner, single_eq, drawn, sent⟩ := ready.singleton
    have summary : summarizeReg (regsOfSource (journal ++ [⟨.inl (.inr (.create pin keyId)), c⟩])) =
        PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal)) (.create pin keyId c) := by
      rw [regs, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
    refine ⟨⟨fun index held => ?_, fun slot => by simp at slot, fun _ => ?_, ⟨owner, single_eq, fun _ => drawn (Or.inl waiting),
      fun slot => by simp at slot⟩, by simp, ready.createdFresh⟩, ⟨fun slot => by simp at slot, fun index above => ?_,
      fun _ => ?_, fun slot => by simp at slot⟩⟩
    · by_cases same : index = emb.owners.length
      · rw [same, atC]
      · rw [lookup_snoc_ne _ _ _ same] at held
        exact absurd held (free index)
    · rw [← atC]
      exact lookup_snoc_self _ _
    · simp only [List.length_append, List.length_singleton] at above
      rw [summary]
      have other : regOwner (.create pin keyId c) ≠ some index := by
        simp only [regOwner, ne_eq, Option.some.injEq]
        omega
      rw [(stepReg_other _ _ index other).1]
      exact consistent.absent index (by omega)
    · rw [summary]
      simp [PqxdhDeploymentServerAuthEvent.stepReg]
  · rename_i target
    simp only [simulateQ_map, StateT.run_map, PqxdhDeploymentServerAuthEmbed.coins_route, Functor.map_map, support_map,
      Set.mem_image] at member
    obtain ⟨owner, _, rfl⟩ := member
    obtain ⟨single_owner, single_eq, drawn, sent⟩ := ready.singleton
    have summary : summarizeReg (regsOfSource (journal ++ [⟨.inl (.inr (.create pin keyId)), emb.owners.length⟩])) =
        PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal)) (.create pin keyId emb.owners.length) := by
      rw [PqxdhDeploymentServerAuthEvent.regsOfSource_append]
      exact PqxdhDeploymentServerAuthEvent.summarizeReg_snoc _ _
    have phaseAt : ∀ index, index ≠ emb.owners.length →
        (summarizeReg (regsOfSource (journal ++ [⟨.inl (.inr (.create pin keyId)), emb.owners.length⟩]))).phases index =
          (summarizeReg (regsOfSource journal)).phases index := by
      intro index different
      rw [summary]
      exact (stepReg_other _ _ index (by simp only [regOwner, ne_eq, Option.some.injEq]; omega)).1
    have below : (emb.slot = .fresh ∨ emb.slot = .bundled) → c < emb.owners.length := by
      intro taken
      exact (List.getElem?_eq_some_iff.mp (ready.placed taken)).1
    simp only
    refine ⟨⟨fun index held => ?_, fun free => ?_, fun taken => ?_, ⟨single_owner, single_eq, fun slot => ?_,
      fun slot => ?_⟩, ?_, ready.createdFresh⟩, ⟨fun slot => ?_, fun index above => ?_, fun slot => ?_,
      fun slot owner owned => ?_⟩⟩
    · by_cases same : index = emb.owners.length
      · subst same
        simp at held
      · rw [lookup_snoc_ne _ _ _ same] at held
        exact ready.target index held
    · by_cases same : c = emb.owners.length
      · rw [same, lookup_snoc_self]
        simp
      · rw [lookup_snoc_ne _ _ _ same]
        split at free
        · rename_i opened
          exact absurd opened.1.symm same
        · exact ready.noTarget free
    · split at taken
      · simp at taken
      · have stays := below taken
        rw [lookup_snoc_ne _ _ _ (by omega)]
        exact ready.placed taken
    · split at slot
      · exact drawn (Or.inl (by tauto))
      · exact drawn slot
    · split at slot
      · simp at slot
      · exact sent slot
    · split
      · simp
      · exact ready.notFailed
    · split at slot
      · simp at slot
      · rename_i opened
        have atMost := consistent.waiting slot
        simp only [List.length_append, List.length_singleton]
        by_contra exceeded
        exact opened ⟨by omega, slot⟩
    · simp only [List.length_append, List.length_singleton] at above
      rw [phaseAt index (by omega)]
      exact consistent.absent index (by omega)
    · split at slot
      · simp at slot
      · have stays := below (Or.inl slot)
        rw [phaseAt c (by omega)]
        exact consistent.fresh slot
    · split at slot
      · simp at slot
      · have stays := below (Or.inr slot)
        rw [phaseAt c (by omega)]
        exact consistent.sent slot owner owned

/-- A step at a local owner keeps the invariant: the owner's entry stays local, the singleton's owners are kept, and the new registration entry concerns only that owner's handle. -/
theorem kept_local (c : Nat) (pre : Pre KemSK) (journal : Journal KemSK) (emb : Emb KemSK) (single next : State KemSK)
    (index : Nat) (owner updated : Owner KemSK) (entry : SourceEntry KemSK) (reg : PqxdhDeploymentServerAuthEvent.Reg)
    (found : emb.owners[index]? = some (some owner)) (ready : Ready c pre emb single)
    (consistent : Consistent c journal emb single) (owners : next.owners = single.owners)
    (registered : regsOfSource (journal ++ [entry]) = regsOfSource journal ++ [reg]) (atOwner : regOwner reg = some index) :
    Inv c pre (journal ++ [entry], ({ emb with owners := emb.owners.set index (some updated) }, next)) := by
  have bound : index < emb.owners.length := (List.getElem?_eq_some_iff.mp found).1
  have phaseAt : ∀ other, other ≠ index →
      (summarizeReg (regsOfSource (journal ++ [entry]))).phases other = (summarizeReg (regsOfSource journal)).phases other := by
    intro other different
    rw [registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
    exact (stepReg_other _ reg other (by rw [atOwner]; simp only [ne_eq, Option.some.injEq]; omega)).1
  have notC : (emb.slot = .fresh ∨ emb.slot = .bundled) → c ≠ index := by
    rintro taken rfl
    rw [ready.placed taken] at found
    cases found
  obtain ⟨single_owner, single_eq, drawn, sent⟩ := ready.singleton
  refine Or.inr ⟨⟨fun other held => ?_, fun free => ?_, fun taken => ?_, ⟨single_owner, owners ▸ single_eq, drawn, sent⟩,
    ready.notFailed, ready.createdFresh⟩, ⟨fun slot => ?_, fun other above => ?_, fun slot => ?_,
    fun slot candidate owned => ?_⟩⟩
  · by_cases same : other = index
    · subst same
      simp [List.getElem?_set_self bound] at held
    · rw [List.getElem?_set_ne (Ne.symm same)] at held
      exact ready.target other held
  · by_cases same : c = index
    · subst same
      simp [List.getElem?_set_self bound]
    · rw [List.getElem?_set_ne (Ne.symm same)]
      exact ready.noTarget free
  · rw [List.getElem?_set_ne (Ne.symm (notC taken))]
    exact ready.placed taken
  · simpa using consistent.waiting slot
  · simp only [List.length_set] at above
    rw [phaseAt other (by omega)]
    exact consistent.absent other above
  · rw [phaseAt c (notC (Or.inl slot))]
    exact consistent.fresh slot
  · rw [phaseAt c (notC (Or.inr slot))]
    exact consistent.sent slot candidate (owners ▸ owned)

/-- A local finish through the route keeps the singleton's owners. -/
theorem localFinish_owners {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed)
    (program : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) α)
    (single : State KemSK) (result : α × State KemSK)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
      (simulateQ route (simulateQ (PqxdhDeploymentServerAuthEmbed.localCallbacks setup codec) program))).run single)) :
    result.2.owners = single.owners := by
  have mapped : Prod.map id eraseShared result ∈ support (Prod.map id eraseShared <$>
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ route (simulateQ (PqxdhDeploymentServerAuthEmbed.localCallbacks setup codec) program))).run single) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ member
  rw [PqxdhDeploymentServerAuthStable.localFinish_route, support_map] at mapped
  obtain ⟨inner, _, same⟩ := mapped
  have owners := congrArg (fun value => value.2.owners) same
  simpa [eraseShared] using owners.symm

/-- A bundle or finish entry at a handle without a summary phase changes nothing. -/
theorem absent_entry (c : Nat) (journal : Journal KemSK) (entry : SourceEntry KemSK) (reg : PqxdhDeploymentServerAuthEvent.Reg)
    (index : Nat) (registered : regsOfSource (journal ++ [entry]) = regsOfSource journal ++ [reg])
    (shape : (∃ reply, reg = .bundle index reply) ∨ ∃ raw reply, reg = .finish index raw reply)
    (absent : (summarizeReg (regsOfSource journal)).phases index = .absent) :
    summarizeReg (regsOfSource (journal ++ [entry])) = summarizeReg (regsOfSource journal) ∧
      (stopAt c (journal ++ [entry]) ↔ stopAt c journal) := by
  rcases shape with ⟨reply, rfl⟩ | ⟨raw, reply, rfl⟩
  · have same : PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal)) (.bundle index reply) =
        summarizeReg (regsOfSource journal) := by
      cases reply <;> simp [PqxdhDeploymentServerAuthEvent.stepReg, absent]
    simp only [stopAt, Stop, registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, same,
      PqxdhDeploymentServerAuthEvent.accepted_snoc, PqxdhDeploymentServerAuthEvent.acceptCheck, Option.or_none, and_self,
      iff_self]
  · have same : PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal)) (.finish index raw reply) =
        summarizeReg (regsOfSource journal) := by
      cases reply <;> simp [PqxdhDeploymentServerAuthEvent.stepReg, absent]
    have check : PqxdhDeploymentServerAuthEvent.acceptCheck c (summarizeReg (regsOfSource journal)) (regsOfSource journal)
        (.finish index raw reply) = none := by
      cases reply with
      | none => rfl
      | some payload =>
          simp only [PqxdhDeploymentServerAuthEvent.acceptCheck]
          split_ifs with accepting
          · obtain ⟨rfl, initSent⟩ := accepting
            rw [absent] at initSent
            cases initSent
          · rfl
    simp only [stopAt, Stop, registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, same,
      PqxdhDeploymentServerAuthEvent.accepted_snoc, check, Option.or_none, and_self, iff_self]

/-- A missing owner handle has no summary phase. -/
theorem absent_missing (c : Nat) (journal : Journal KemSK) (emb : Emb KemSK) (single : State KemSK)
    (consistent : Consistent c journal emb single) (index : Nat) (missing : emb.owners[index]? = none) :
    (summarizeReg (regsOfSource journal)).phases index = .absent :=
  consistent.absent index (List.getElem?_eq_none_iff.mp missing)

/-- A bundle step keeps the invariant. -/
theorem kept_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (pre : Pre KemSK) (published : input.phase1 = pre.reply)
    (bundledSent : ∀ bytes, pre.reply = some bytes →
      PqxdhDeploymentEligibility.phaseClass pre.bundled.beacon.phase = .initSent)
    (index : Nat) (journal : Journal KemSK) (emb : Emb KemSK) (single : State KemSK)
    (ready : Ready c pre emb single) (consistent : Consistent c journal emb single)
    (result : (((SourceSpec KemSK).Range (.inl (.inr (.bundle index))) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inr (.bundle index))) emb single)) :
    Inv c pre (journal ++ [⟨.inl (.inr (.bundle index)), result.1.1⟩], (result.1.2, result.2)) := by
  have registered : ∀ reply, regsOfSource (journal ++ [⟨.inl (.inr (.bundle index)), reply⟩]) =
      regsOfSource journal ++ [.bundle index reply] := fun reply => by
    rw [PqxdhDeploymentServerAuthEvent.regsOfSource_append]
    rfl
  simp only [singleStep] at member
  rw [PqxdhDeploymentServerAuthLocal.embed_bundle] at member
  cases found : emb.owners[index]? with
  | none =>
      rw [found] at member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact kept_shared c pre journal emb single single _ ready consistent rfl
        (absent_entry c journal _ _ index (registered none) (Or.inl ⟨none, rfl⟩)
          (absent_missing c journal emb single consistent index found))
  | some slot =>
      cases slot with
      | none =>
          have atC := ready.target index found
          subst atC
          rw [found] at member
          obtain ⟨single_owner, single_eq, drawn, sent⟩ := ready.singleton
          by_cases fresh : emb.slot = .fresh
          · rw [ite_eq_left fresh] at member
            simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
            subst member
            have phaseC := consistent.fresh fresh
            cases phase1 : input.phase1 with
            | none =>
                left
                simp only [stopAt, Stop, registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc,
                  PqxdhDeploymentServerAuthEvent.stepReg, phaseC, ite_true, Function.update_self, or_true]
            | some bytes =>
                have isSent := bundledSent bytes (published ▸ phase1)
                have owner_eq : single_owner = pre.bundled := drawn (Or.inr (Or.inl fresh))
                have summary : summarizeReg (regsOfSource (journal ++ [⟨.inl (.inr (.bundle index)), some bytes⟩])) =
                    PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal)) (.bundle index (some bytes)) := by
                  rw [registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
                have bound : index < emb.owners.length := (List.getElem?_eq_some_iff.mp found).1
                right
                simp only [Option.isSome_some, ite_true]
                refine ⟨⟨ready.target, fun free => by simp at free, fun _ => found,
                  ⟨single_owner, single_eq, fun slot => by simp at slot, fun _ => Or.inl (owner_eq ▸ isSent)⟩,
                  by simp, ready.createdFresh⟩, ⟨fun slot => by simp at slot, fun other above => ?_,
                  fun slot => by simp at slot, fun _ owner owned => ?_⟩⟩
                · dsimp only at above
                  rw [summary, (stepReg_other _ _ other (by simp only [regOwner, ne_eq, Option.some.injEq]; omega)).1]
                  exact consistent.absent other above
                · rw [single_eq, List.cons.injEq] at owned
                  rw [← owned.1, owner_eq, isSent, summary]
                  simp [PqxdhDeploymentServerAuthEvent.stepReg, phaseC]
          · rw [ite_eq_right fresh] at member
            simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
            subst member
            have bundled : emb.slot = .bundled := by
              cases slot : emb.slot with
              | waiting => exact absurd found (ready.noTarget (Or.inl slot))
              | released => exact absurd found (ready.noTarget (Or.inr slot))
              | fresh => exact absurd slot fresh
              | failed => exact absurd slot ready.notFailed
              | bundled => rfl
            have phaseC := consistent.sent bundled single_owner single_eq
            have notFreshPhase : (summarizeReg (regsOfSource journal)).phases index ≠ .fresh := by
              rw [phaseC]
              rcases sent bundled with initSent | aborted
              · rw [initSent]
                decide
              · rw [aborted]
                decide
            have same : PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal)) (.bundle index none) =
                summarizeReg (regsOfSource journal) := by
              simp [PqxdhDeploymentServerAuthEvent.stepReg, notFreshPhase]
            exact kept_shared index pre journal emb single single _ ready consistent rfl
              ⟨by rw [registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, same], by
                simp only [stopAt, Stop, registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, same,
                  PqxdhDeploymentServerAuthEvent.accepted_snoc, PqxdhDeploymentServerAuthEvent.acceptCheck,
                  Option.or_none]⟩
      | some owner =>
          rw [found] at member
          simp only [simulateQ_map, StateT.run_map, PqxdhDeploymentServerAuthEmbed.coins_route, Functor.map_map,
            support_map, Set.mem_image] at member
          obtain ⟨bundled, _, rfl⟩ := member
          exact kept_local c pre journal emb single single index owner bundled.2 _ _ found ready consistent rfl
            (registered bundled.1) rfl

/-- A finish step keeps the invariant. -/
theorem kept_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (pre : Pre KemSK) (index : Nat) (raw : Pqxdh.Bytes)
    (journal : Journal KemSK) (emb : Emb KemSK) (single : State KemSK)
    (ready : Ready c pre emb single) (consistent : Consistent c journal emb single)
    (result : (((SourceSpec KemSK).Range (.inl (.inr (.finish index raw))) × Emb KemSK) × State KemSK))
    (member : result ∈ support (singleStep setup codec checks seed c input (.inl (.inr (.finish index raw))) emb single)) :
    Inv c pre (journal ++ [⟨.inl (.inr (.finish index raw)), result.1.1⟩], (result.1.2, result.2)) := by
  have registered : ∀ reply, regsOfSource (journal ++ [⟨.inl (.inr (.finish index raw)), reply⟩]) =
      regsOfSource journal ++ [.finish index raw reply] := fun reply => by
    rw [PqxdhDeploymentServerAuthEvent.regsOfSource_append]
    rfl
  simp only [singleStep] at member
  rw [PqxdhDeploymentServerAuthLocal.embed_finish] at member
  cases found : emb.owners[index]? with
  | none =>
      rw [found] at member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact kept_shared c pre journal emb single single _ ready consistent rfl
        (absent_entry c journal _ _ index (registered none) (Or.inr ⟨raw, none, rfl⟩)
          (absent_missing c journal emb single consistent index found))
  | some slot =>
      cases slot with
      | none =>
          have atC := ready.target index found
          subst atC
          rw [found] at member
          obtain ⟨single_owner, single_eq, drawn, sent⟩ := ready.singleton
          by_cases bundled : emb.slot = .bundled
          · rw [ite_eq_left bundled] at member
            have zero : single.owners[0]? = some single_owner := by simp [single_eq]
            simp only [PqxdhDeploymentServerAuthEmbed.forward, simulateQ_map, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, route, StateT.run_map, PqxdhRegistrationSchedule.handler] at member
            rw [PqxdhDeploymentServerAuthLocal.finish_found setup codec 0 raw single single_owner zero] at member
            simp only [Functor.map_map, support_map, Set.mem_image] at member
            obtain ⟨finished, finishedMember, rfl⟩ := member
            have phaseC := consistent.sent bundled single_owner single_eq
            rcases sent bundled with initSent | aborted
            · cases reply : finished.1.1 with
              | some payload =>
                  left
                  simp only [stopAt, Stop, registered, PqxdhDeploymentServerAuthEvent.accepted_snoc,
                    PqxdhDeploymentServerAuthEvent.acceptCheck, phaseC, initSent, and_self, ite_true, Option.isSome_or,
                    Option.isSome_some, Bool.or_true, true_or]
              | none =>
                  have failed := PqxdhDeploymentEligibility.finish_failure setup codec raw single_owner single.shared
                    finished.1.2 finished.2 (by rw [← reply]; exact finishedMember)
                  have abortedNext : PqxdhDeploymentEligibility.phaseClass finished.1.2.beacon.phase = .aborted := by
                    cases phase : single_owner.beacon.phase with
                    | initSent control prekey oneTime kem =>
                        simp only [phase] at failed
                        rw [failed]
                        rfl
                    | _ =>
                        rw [phase] at initSent
                        cases initSent
                  have summary : summarizeReg (regsOfSource (journal ++ [⟨.inl (.inr (.finish index raw)), none⟩])) =
                      PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal)) (.finish index raw none) := by
                    rw [registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc]
                  have bound : index < emb.owners.length := (List.getElem?_eq_some_iff.mp found).1
                  right
                  simp only [single_eq, List.set_cons_zero]
                  refine ⟨⟨ready.target, ready.noTarget, ready.placed,
                    ⟨finished.1.2, rfl, fun slot => by rw [bundled] at slot; simp at slot, fun _ => Or.inr abortedNext⟩,
                    ready.notFailed, ready.createdFresh⟩, ⟨consistent.waiting, fun other above => ?_,
                    fun slot => (by rw [bundled] at slot; cases slot), fun _ owner owned => ?_⟩⟩
                  · rw [summary, (stepReg_other _ _ other (by simp only [regOwner, ne_eq, Option.some.injEq]; omega)).1]
                    exact consistent.absent other above
                  · rw [List.cons.injEq] at owned
                    rw [← owned.1, abortedNext, summary]
                    simp [PqxdhDeploymentServerAuthEvent.stepReg, phaseC, initSent]
            · have open_ : PqxdhDeploymentEligibility.phaseClass single_owner.beacon.phase ≠ .initSent := by
                rw [aborted]
                decide
              rw [PqxdhDeploymentServerAuthLocal.nativeOwner_open codec.frameRead raw single_owner open_] at finishedMember
              simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at finishedMember
              subst finishedMember
              have same : PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal))
                  (.finish index raw none) = summarizeReg (regsOfSource journal) := by
                simp [PqxdhDeploymentServerAuthEvent.stepReg, phaseC, aborted]
              exact kept_shared index pre journal emb single _ _ ready consistent (by simp [single_eq])
                ⟨by rw [registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, same], by
                  simp only [stopAt, Stop, registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, same,
                    PqxdhDeploymentServerAuthEvent.accepted_snoc, PqxdhDeploymentServerAuthEvent.acceptCheck,
                    Option.or_none]⟩
          · rw [ite_eq_right bundled] at member
            simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
            subst member
            have fresh : emb.slot = .fresh := by
              cases slot : emb.slot with
              | waiting => exact absurd found (ready.noTarget (Or.inl slot))
              | released => exact absurd found (ready.noTarget (Or.inr slot))
              | bundled => exact absurd slot bundled
              | failed => exact absurd slot ready.notFailed
              | fresh => rfl
            have phaseC := consistent.fresh fresh
            have same : PqxdhDeploymentServerAuthEvent.stepReg (summarizeReg (regsOfSource journal))
                (.finish index raw none) = summarizeReg (regsOfSource journal) := by
              simp [PqxdhDeploymentServerAuthEvent.stepReg, phaseC]
            exact kept_shared index pre journal emb single single _ ready consistent rfl
              ⟨by rw [registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, same], by
                simp only [stopAt, Stop, registered, PqxdhDeploymentServerAuthEvent.summarizeReg_snoc, same,
                  PqxdhDeploymentServerAuthEvent.accepted_snoc, PqxdhDeploymentServerAuthEvent.acceptCheck,
                  Option.or_none]⟩
      | some owner =>
          rw [found] at member
          simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at member
          obtain ⟨finished, finishedMember, rfl⟩ := member
          exact kept_local c pre journal emb single finished.2 index owner finished.1.2 _ _ found ready consistent
            (localFinish_owners setup codec checks seed _ single finished finishedMember) (registered finished.1.1) rfl

/-- Every step of the singleton side keeps the invariant. -/
theorem kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (pre : Pre KemSK) (published : input.phase1 = pre.reply)
    (bundledSent : ∀ bytes, pre.reply = some bytes →
      PqxdhDeploymentEligibility.phaseClass pre.bundled.beacon.phase = .initSent)
    (query : (SourceSpec KemSK).Domain) (good : ¬ Bad query) (state : Journal KemSK × (Emb KemSK × State KemSK))
    (holds : Inv c pre state)
    (result : (SourceSpec KemSK).Range query × (Journal KemSK × (Emb KemSK × State KemSK)))
    (member : result ∈ support ((singleSide setup codec checks seed c input query).run state)) :
    Inv c pre result.2 := by
  obtain ⟨journal, emb, single⟩ := state
  rw [singleSide_step] at member
  by_cases stopped : stopAt c journal
  · rw [ite_eq_left stopped, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact Or.inl stopped
  · rw [ite_eq_right stopped, support_map] at member
    obtain ⟨step, stepMember, rfl⟩ := member
    obtain ⟨ready, consistent⟩ := holds.resolve_left stopped
    dsimp only
    rcases query with (coin | request) | ⟨index, field⟩
    · obtain ⟨sameEmb, sameSingle⟩ := coin_support setup codec checks seed c input coin emb single step stepMember
      rw [sameEmb, sameSingle]
      exact kept_shared c pre journal emb single single _ ready consistent rfl (quiet_entry c journal _ rfl)
    · cases request with
      | create pin keyId =>
          exact kept_create setup codec checks seed c input pre pin keyId journal emb single stopped ready
            consistent step stepMember
      | bundle index =>
          exact kept_bundle setup codec checks seed c input pre published bundledSent index journal emb single
            ready consistent step stepMember
      | accept raw =>
          obtain ⟨sameEmb, owners⟩ := accept_support setup codec checks seed c input raw emb single step stepMember
          rw [sameEmb]
          exact kept_shared c pre journal emb single step.2 _ ready consistent owners
            (server_entry c journal _ (Or.inl ⟨raw, step.1.1, rfl⟩))
      | build session payload =>
          obtain ⟨sameEmb, owners⟩ := build_support setup codec checks seed c input session payload emb single step
            stepMember
          rw [sameEmb]
          exact kept_shared c pre journal emb single step.2 _ ready consistent owners
            (server_entry c journal _ (Or.inr ⟨session, payload, step.1.1, rfl⟩))
      | finish index raw =>
          exact kept_finish setup codec checks seed c input pre index raw journal emb single ready
            consistent step stepMember
      | hmac key message =>
          obtain ⟨sameEmb, owners⟩ := hmac_support setup codec checks seed c input key message emb single step stepMember
          rw [sameEmb]
          exact kept_shared c pre journal emb single step.2 _ ready consistent owners (quiet_entry c journal _ rfl)
      | hash bytes =>
          obtain ⟨sameEmb, owners⟩ := hash_support setup codec checks seed c input bytes emb single step stepMember
          rw [sameEmb]
          exact kept_shared c pre journal emb single step.2 _ ready consistent owners (quiet_entry c journal _ rfl)
      | reveal keyId =>
          obtain ⟨sameEmb, owners⟩ := reveal_support setup codec checks seed c input keyId emb single step stepMember
          rw [sameEmb]
          exact kept_shared c pre journal emb single step.2 _ ready consistent owners (quiet_entry c journal _ rfl)
    · rw [PqxdhDeploymentServerAuthLocal.singleStep_read, support_pure, Set.mem_singleton_iff] at stepMember
      subst stepMember
      exact kept_shared c pre journal emb single single _ ready consistent rfl (quiet_entry c journal _ rfl)

/-- The eager handler reads neither analysis history. -/
theorem eager_stable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) (query : (SourceSpec KemSK).Domain)
    (state : State KemSK × Phase) :
    Prod.map id (fun next : State KemSK × Phase => (eraseShared next.1, next.2)) <$>
        (eager setup codec checks seed c binding pre query).run state =
      Prod.map id (fun next : State KemSK × Phase => (eraseShared next.1, next.2)) <$>
        (eager setup codec checks seed c binding pre query).run (eraseShared state.1, state.2) := by
  have kept : ∀ request : (SourceSpec KemSK).Domain,
      Prod.map id (fun next : State KemSK × Phase => (eraseShared next.1, next.2)) <$>
          (keep setup codec checks seed request).run state =
        Prod.map id (fun next : State KemSK × Phase => (eraseShared next.1, next.2)) <$>
          (keep setup codec checks seed request).run (eraseShared state.1, state.2) := fun request => by
    rw [keep_run, keep_run]
    have same := congrArg (fun computation => (fun result => (result.1, (result.2, state.2))) <$> computation)
      (base_stable setup codec checks seed request state.1)
    simp only [Functor.map_map] at same ⊢
    exact same
  rcases query with (coin | request) | ⟨index, field⟩
  · exact kept _
  · cases request with
    | create pin keyId =>
        rw [PqxdhDeploymentServerAuthLocal.eager_create, PqxdhDeploymentServerAuthLocal.eager_create]
        have length : (eraseShared state.1).owners.length = state.1.owners.length := rfl
        simp only [length]
        split
        · split
          · simp only [map_pure]
            rfl
          · have same := congrArg (fun computation => (fun result => (result.1, (result.2, Phase.done))) <$> computation)
              (base_stable setup codec checks seed (.inl (.inr (.create pin keyId))) state.1)
            simp only [Functor.map_map] at same ⊢
            exact same
        · exact kept _
    | bundle index =>
        rw [PqxdhDeploymentServerAuthLocal.eager_bundle, PqxdhDeploymentServerAuthLocal.eager_bundle]
        split
        · simp only [map_pure]
          rfl
        · exact kept _
    | _ => exact kept _
  · exact kept _

/-- The eager side reads neither analysis history. -/
theorem eagerSide_stable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) (query : (SourceSpec KemSK).Domain)
    (state : Journal KemSK × (State KemSK × Phase)) :
    Prod.map id eraseEager <$> (eagerSide setup codec checks seed c binding pre query).run state =
      (erasedSide setup codec checks seed c binding pre query).run (eraseEager state) := by
  rw [erasedSide, StateT.run_mk]
  obtain ⟨journal, inner⟩ := state
  simp only [eraseEager, eagerSide_step]
  split
  · simp only [map_pure]
    rfl
  · have same := congrArg (fun computation => (fun result => (result.1, (journal ++ [⟨query, result.1⟩], result.2))) <$>
      computation) (eager_stable setup codec checks seed c binding pre query inner)
    simp only [Functor.map_map] at same ⊢
    exact same

/-- The initial state of the singleton side satisfies the invariant when the singleton's only owner is the drawn bundled owner. -/
theorem inv_initial (c : Nat) (pre : Pre KemSK) (single : State KemSK) (owner : single.owners = [pre.bundled])
    (createdFresh : PqxdhDeploymentEligibility.phaseClass pre.created.beacon.phase = .fresh) :
    Inv c pre ([], (Emb.empty, single)) :=
  Or.inr ⟨⟨fun index held => by simp [Emb.empty] at held, fun _ => by simp [Emb.empty], fun taken => by
      simp [Emb.empty] at taken, ⟨pre.bundled, owner, fun _ => rfl, fun slot => by simp [Emb.empty] at slot⟩,
      by simp [Emb.empty], createdFresh⟩,
    ⟨fun _ => by simp [Emb.empty], fun index _ => rfl, fun slot => by simp [Emb.empty] at slot,
      fun slot => by simp [Emb.empty] at slot⟩⟩

/-- Localization at creation index `c`: for a program that issues no identity, KEM, prekey or one-time read and target material whose created owner is Fresh and whose bundled owner is in InitSent when the bundle succeeded, the singleton side, reassembled, is the eager side, up to the analysis histories, jointly over the program's result, the frozen journal and the final state. -/
theorem localize (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (binding : Word32 × Std.U64) (pre : Pre KemSK)
    (bound : inputBinding input = binding) (published : input.phase1 = pre.reply)
    (createdFresh : PqxdhDeploymentEligibility.phaseClass pre.created.beacon.phase = .fresh)
    (bundledSent : ∀ bytes, pre.reply = some bytes →
      PqxdhDeploymentEligibility.phaseClass pre.bundled.beacon.phase = .initSent)
    (program : OracleComp (SourceSpec KemSK) Result) (unread : program.IsQueryBoundP (Bad (KemSK := KemSK)) 0)
    (single : State KemSK) (owner : single.owners = [pre.bundled]) :
    Prod.map id (reassemble pre) <$>
        (simulateQ (singleSide setup codec checks seed c input) program).run ([], (Emb.empty, single)) =
      Prod.map id eraseEager <$>
        (simulateQ (eagerSide setup codec checks seed c binding pre) program).run ([], (⟨single.shared, []⟩, .waiting)) := by
  rw [OracleComp.map_run_simulateQ_eq_of_query_map_eq (eagerSide setup codec checks seed c binding pre)
    (erasedSide setup codec checks seed c binding pre) eraseEager
    (eagerSide_stable setup codec checks seed c binding pre) program _]
  exact map_run_inv_bound (singleSide setup codec checks seed c input) (erasedSide setup codec checks seed c binding pre)
    (Inv c pre) (reassemble pre) Bad
    (fun query state good holds => kept setup codec checks seed c input pre published bundledSent query good state holds)
    (fun query state good holds => side_commute setup codec checks seed c input binding pre bound published query good
      state (holds.imp id And.left)) program unread _ (inv_initial c pre single owner createdFresh)

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.stack_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.stack_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.stack_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.stack_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.map_run_inv_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.map_run_inv_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.freezeImpl_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.freezeImpl_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.singleSide_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.singleSide_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.eagerSide_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.eagerSide_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.side_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.side_commute

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.ready_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.ready_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.consistent_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.consistent_transfer

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.quiet_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.quiet_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.server_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.server_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.onShared_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.onShared_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.accept_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.accept_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.build_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.build_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.hmac_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.hmac_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.hash_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.hash_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.reveal_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.reveal_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.coin_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.coin_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.stepReg_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.stepReg_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.lookup_snoc_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.lookup_snoc_ne

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.lookup_snoc_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.lookup_snoc_self

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_local

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.localFinish_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.localFinish_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.absent_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.absent_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.absent_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.absent_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.kept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.eager_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.eager_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.eagerSide_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.eagerSide_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.inv_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.inv_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.localize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize.localize
