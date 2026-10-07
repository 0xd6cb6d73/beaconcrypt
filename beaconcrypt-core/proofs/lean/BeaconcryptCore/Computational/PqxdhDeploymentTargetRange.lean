-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! Range of the public designation in the common deployment experiment (CE-9, open point of unit A). For a budget-respecting adversary, every designation `(session, k)` of any handle on any outcome of the experiment has `session < qAccept` and `k < qCreate + 1` (`range_game`), so the budgeted designation `designateIn` agrees with `designate` (`designateIn_range`) and a claim is designated exactly when it is designated inside the target domain `Fin qAccept × Fin (qCreate + 1)` (`eligible_designated`). The session bound combines the positional accept replies of the trace invariant (an accept that returned session `i` is the `i`-th accept attempt) with a transcript count: the secrecy layer appends exactly one entry per query (`ledger_step`), so the transcript has at most `qAccept` accept entries (`ledger_count`), and these are exactly the logged accepts (`accepts_count`). The owner bound uses that a designated owner was created (`designate_created`) and that only create entries add created owners (`owners_count`). `kem_transfer_eligible` restates the exact-sum headline `PqxdhDeploymentKemTransfer.kem_transfer_sum` with this unbudgeted eligibility. Premises: the approved Phase 1 and Phase 2 read-back contracts (through CE-COMPILE) and the adversary budget; no assumption and no advantage term is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentTargetRange
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Entry Handle FullSpec ModeSpec Mode Budget FreshBounds asModeO queryClass)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentCompile (Local compileImpl)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhDeploymentRegistrationTrace (Logged traceFrom acceptsOf)
open PqxdhDeploymentKemTransfer (registrations regOf)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result : Type}

/-- The number of transcript entries of one query class. -/
def classCount (kind : Fin 14) (transcript : List Entry) : Nat :=
  transcript.countP fun entry => decide (queryClass entry.query = kind)

/-- One secrecy-layer step appends exactly the query with its reply to the transcript. -/
theorem ledger_step (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (query : PqxdhDeploymentInterface.Query) (ledger : Ledger) (result : FullSpec.Range query × Ledger)
    (reached : result ∈ support ((ledgerImpl crypto codec serverKid bounds query).run ledger)) :
    result.2.transcript = ledger.transcript ++ [⟨query, result.1⟩] := by
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at reached
    obtain ⟨reply, _, rfl⟩ := reached
    rfl
  · exact PqxdhDeploymentEligibility.ledger_secrecy crypto codec serverKid bounds secrecy ledger result reached

/-- A program with at most `cap` queries of a class adds at most `cap` transcript entries of that class through the secrecy layer. -/
theorem ledger_count (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (kind : Fin 14) (program : OracleComp FullSpec Result) (cap : Nat)
    (bounded : program.IsQueryBoundP (fun query => queryClass query = kind) cap) (ledger : Ledger)
    (result : Result × Ledger)
    (reached : result ∈ support ((simulateQ (ledgerImpl crypto codec serverKid bounds) program).run ledger)) :
    classCount kind result.2.transcript ≤ classCount kind ledger.transcript + cap := by
  induction program using OracleComp.inductionOn generalizing cap ledger with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact Nat.le_add_right _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, second⟩ := reached
      have appended := ledger_step crypto codec serverKid bounds query ledger middle first
      have later := ih middle.1 _ (rest middle.1) middle.2 second
      rw [appended] at later
      simp only [classCount, List.countP_append, List.countP_singleton] at later ⊢
      by_cases same : queryClass query = kind
      · have positive := allowed.resolve_left (fun absurd => absurd same)
        simp only [same, decide_true, ite_true] at later
        omega
      · simp only [same, decide_false, Bool.false_eq_true, ite_false] at later
        omega


/-- The registration reply of one entry is a logged accept exactly for an accept entry. -/
theorem entry_accepts (entry : Entry) :
    (acceptsOf (regOf entry).toList).length = if queryClass entry.query = 3 then 1 else 0 := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · rfl
  · cases command <;> rfl
  · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> rfl

/-- The logged raw accepts of a transcript's registrations are exactly its accept entries. -/
theorem accepts_count (transcript : List Entry) :
    (acceptsOf (registrations transcript)).length = classCount 3 transcript := by
  induction transcript using List.reverseRecOn with
  | nil => rfl
  | append_singleton rest entry ih =>
      rw [PqxdhDeploymentKemTransfer.registrations_append]
      simp only [acceptsOf, List.filterMap_append, List.length_append] at ih ⊢
      have single := entry_accepts entry
      simp only [acceptsOf] at single
      rw [ih, single]
      simp only [classCount, List.countP_append, List.countP_singleton, decide_eq_true_eq]

/-- Only a create entry adds a created owner to the transcript summary, and at most one. -/
theorem step_owners (summary : PqxdhDeploymentTranscript.Summary) (entry : Entry) :
    (PqxdhDeploymentTranscript.step summary entry).owners.length ≤
      summary.owners.length + if queryClass entry.query = 1 then 1 else 0 := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · simp [PqxdhDeploymentTranscript.step]
  · cases command with
    | create pin keyId =>
        cases reply with
        | none => simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand]
        | some index =>
            simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand]
            split <;> simp [queryClass]
    | bundle owner =>
        cases reply <;> simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand] <;>
          split <;> simp
    | finish owner raw =>
        cases reply <;> simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand] <;>
          split <;> simp
    | _ => simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand]
  · simp [PqxdhDeploymentTranscript.step]

/-- The created owners of a transcript summary are at most its create entries. -/
theorem owners_count (transcript : List Entry) :
    (PqxdhDeploymentTranscript.summarize transcript).owners.length ≤ classCount 1 transcript := by
  induction transcript using List.reverseRecOn with
  | nil => simp [PqxdhDeploymentTranscript.summarize, PqxdhDeploymentTranscript.Summary.empty]
  | append_singleton rest entry ih =>
      rw [PqxdhDeploymentTranscript.summarize_append]
      have stepped := step_owners (PqxdhDeploymentTranscript.summarize rest) entry
      simp only [classCount, List.countP_append, List.countP_singleton] at ih ⊢
      split at stepped <;> simp_all <;> omega


/-- A designated owner of either side was created in the transcript. -/
theorem designate_created (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (transcript : List Entry) (handle : Handle) (session k : Nat)
    (designated : PqxdhDeploymentTranscript.designate crypto codec serverKid transcript handle = some (session, k)) :
    k < (PqxdhDeploymentTranscript.summarize transcript).owners.length := by
  cases handle with
  | peer keyId =>
      obtain ⟨_, _, _, _, _, _, _, _, created, _⟩ :=
        PqxdhDeploymentTranscript.designate_peer crypto codec serverKid keyId transcript session k designated
      exact created
  | owner index =>
      obtain ⟨rfl, _, _, _, _, _, _, binding, _⟩ :=
        PqxdhDeploymentTranscript.designate_owner crypto codec serverKid transcript index session k designated
      exact (List.getElem?_eq_some_iff.mp binding).1

/-- Range of the designation in the traced annotated execution of the compiled program of a budget-respecting adversary: every designated session is below the accept budget and every designated KEM creation index below the create budget plus one. -/
theorem traced_range (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (runtime : A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK (((X × Ledger) × Local) × List Logged))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (reached : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks
      ensureInit none (traceFrom (compileFull setup codec route bounds mode adversary) [])).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (handle : Handle) (session k : Nat)
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
      outcome.2.1.1.1.2.transcript handle = some (session, k)) :
    session < budget.accept ∧ k < budget.capacity := by
  have result := PqxdhDeploymentRegistrationTrace.source_support setup codec checks ensureInit none _ _ _ outcome reached
  have logEq := PqxdhDeploymentKemTransfer.compiled_trace setup codec route bounds mode adversary outcome.2.1 result
  obtain ⟨traced, _⟩ := PqxdhDeploymentRegistrationTrace.traced_source setup codec checks ensureInit none _ _ rfl after
    outcome reached
  have compiled := PqxdhDeploymentRegistrationTrace.traceFrom_support _ [] outcome.2.1 result
  have wrapped : outcome.2.1.1.1 ∈ support (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId
      bounds (asModeO mode adversary)) := by
    apply support_simulateQ_run'_subset (compileImpl setup codec route) _ Local.empty
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ compiled
  have accepts := ledger_count setup.source.crypto codec setup.serverKeyId bounds 3 (asModeO mode adversary)
    (budget.cap 3) (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects 3) Ledger.empty _ wrapped
  have creates := ledger_count setup.source.crypto codec setup.serverKeyId bounds 1 (asModeO mode adversary)
    (budget.cap 1) (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects 1) Ledger.empty _ wrapped
  simp only [Ledger.empty, classCount, List.countP_nil, Nat.zero_add] at accepts creates
  obtain ⟨raw, _, _, _, rawFound, _, _, _, _⟩ := PqxdhDeploymentKemTransfer.designate_keys _ codec _ _ handle session k
    designated
  have acceptLogged : (raw, some session) ∈ acceptsOf outcome.2.1.2 := by
    rw [logEq]
    simp only [acceptsOf, registrations, List.mem_filterMap]
    exact ⟨.accept raw (some session), ⟨_, PqxdhDeploymentKemTransfer.acceptOf_mem _ _ raw rawFound, rfl⟩, rfl⟩
  obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp acceptLogged
  have samePosition := traced.positional position raw session positionFound
  have bound := (List.getElem?_eq_some_iff.mp positionFound).1
  rw [logEq, accepts_count] at bound
  have created := designate_created _ codec _ _ handle session k designated
  have owners := owners_count outcome.2.1.1.1.2.transcript
  simp only [classCount] at owners bound
  refine ⟨?_, ?_⟩
  · rw [samePosition]
    exact lt_of_lt_of_le bound accepts
  · exact Nat.lt_succ_of_lt (lt_of_lt_of_le created (le_trans owners creates))


/-- Range of the designation in the deployment experiment (the open point of unit A): on every outcome of the experiment of a budget-respecting adversary, every designation `(session, k)` of any handle has `session < qAccept` and `k < qCreate + 1`. Under the approved Phase 1 and Phase 2 read-back contracts, through CE-COMPILE. -/
theorem range_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (reached : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (observed : PqxdhDeploymentKemTransfer.Observed X) (found : PqxdhDeploymentKemTransfer.observeGame outcome.1 = some observed)
    (handle : Handle) (session k : Nat)
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
      observed.2.1.transcript handle = some (session, k)) :
    session < budget.accept ∧ k < budget.capacity := by
  have game := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2 bounds
    mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  change _ = (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime at game
  have traced := PqxdhDeploymentRegistrationTrace.source_map setup codec checks ensureInit none Prod.fst
    (traceFrom (compileFull setup codec route bounds mode adversary) [])
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at traced
  rw [← game, traced, Functor.map_map, support_map] at reached
  obtain ⟨⟨_ | source, after⟩, member, rfl⟩ := reached
  · cases found
  · have same : some (source.2.1.1.1.1, source.2.1.1.1.2, source.2.1.1.2.produced) = some observed := found
    obtain rfl := Option.some.inj same
    exact traced_range setup codec checks route ensureInit bounds mode adversary budget respects runtime source after
      member handle session k designated

/-- A designation inside the budgeted domain is its budgeted designation. -/
theorem designateIn_range (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (budget : Budget)
    (transcript : List Entry) (handle : Handle) (session k : Nat)
    (designated : PqxdhDeploymentTranscript.designate crypto codec serverKid transcript handle = some (session, k))
    (sessionBound : session < budget.accept) (kBound : k < budget.capacity) :
    PqxdhDeploymentTranscript.designateIn crypto codec serverKid budget transcript handle =
      some (⟨session, sessionBound⟩, ⟨k, kBound⟩) := by
  simp only [PqxdhDeploymentTranscript.designateIn, designated, Option.bind_some, sessionBound, kBound, _root_.dite_true]


/-- The unbudgeted designation of a claim on an outcome of the experiment: `designate` on the transcript, applied to the handle the claim names. -/
noncomputable def eligible (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (claim : PqxdhDeploymentKemTransfer.Observed X → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Option (Nat × Nat) :=
  (PqxdhDeploymentKemTransfer.observeGame outcome.1).bind fun observed =>
    (claim observed).bind (PqxdhDeploymentTranscript.designate crypto codec serverKid observed.2.1.transcript)

/-- On every outcome of the experiment of a budget-respecting adversary, a claim is designated exactly when it is designated inside the budgeted target domain, so the budgeted eligibility of the headline loses no outcome. -/
theorem eligible_designated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (claim : PqxdhDeploymentKemTransfer.Observed X → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (reached : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime)) :
    (eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome =
      (PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome := by
  unfold eligible PqxdhDeploymentKemTransfer.designated PqxdhDeploymentKemTransfer.target
  cases found : PqxdhDeploymentKemTransfer.observeGame outcome.1 with
  | none => rfl
  | some observed =>
      simp only [Option.bind_some]
      cases named : claim observed with
      | none => rfl
      | some handle =>
          simp only [Option.bind_some]
          cases chosen : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
              observed.2.1.transcript handle with
          | none => simp [PqxdhDeploymentTranscript.designateIn, chosen]
          | some pair =>
              obtain ⟨sessionBound, kBound⟩ := range_game setup codec checks route ensureInit phase1 phase2 bounds mode
                adversary budget respects runtime outcome reached observed found handle pair.1 pair.2 chosen
              rw [designateIn_range _ codec _ budget _ handle pair.1 pair.2 chosen sessionBound kBound]
              rfl

/-- Exact-sum headline with unbudgeted eligibility: the probability that the deployment experiment ends with the event and the claim designated at all is at most the sum over all targets `g` in `Fin qAccept × Fin (qCreate + 1)` of the opaque KEM-ideal branch of `g`'s decision plus one IND-CCA advantage and one correctness error, each with coefficient one. -/
theorem kem_transfer_eligible (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : PqxdhDeploymentKemTransfer.Observed X → Bool)
    (claim : PqxdhDeploymentKemTransfer.Observed X → Option Handle) (runtime : A) :
    𝒟[(fun outcome => decide (PqxdhDeploymentKemTransfer.happens event outcome = true ∧
        (eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.capacity,
        (𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
          (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileFull setup codec route bounds mode adversary) runtime budget.create
          (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val false] {true} +
        ENNReal.ofReal (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
            (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
          (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
            (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
            (compileFull setup codec route bounds mode adversary) runtime budget.create
            (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val).toINDCCA +
          PqxdhRegistrationJointKemRawGame.correctnessError setup)) := by
  rw [PqxdhDeploymentKemTransfer.map_support_congr _ _
    (fun outcome => decide (PqxdhDeploymentKemTransfer.happens event outcome = true ∧
      (PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome))
    (fun outcome reached => by
      rw [eligible_designated setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects
        runtime claim outcome reached])]
  exact PqxdhDeploymentKemTransfer.kem_transfer_sum setup functional codec checks route ensureInit phase1 phase2 bounds
    mode adversary budget respects event claim runtime

end BeaconcryptCore.Computational.PqxdhDeploymentTargetRange

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.ledger_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.ledger_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.ledger_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.ledger_count

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.entry_accepts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.entry_accepts

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.accepts_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.accepts_count

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.step_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.step_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.owners_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.owners_count

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.designate_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.designate_created

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.traced_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.traced_range

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.range_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.range_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.designateIn_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.designateIn_range

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.eligible_designated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.eligible_designated

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.kem_transfer_eligible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTargetRange.kem_transfer_eligible
