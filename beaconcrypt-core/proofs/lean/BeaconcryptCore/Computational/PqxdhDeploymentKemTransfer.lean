-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentRegistrationTrace
import BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps
import BeaconcryptCore.Computational.UniformTargetSelection
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills

/-! Per-target KEM transfer of the common deployment experiment (CE-9, plan section 9 steps 9.1-9.4). A deployment event reads the adversary's output, the secrecy ledger and the produced frames (`Observed`); a claim names a record handle, and its target is the budgeted public designation `designateIn` of that handle on the transcript, a pair `g = (i, k)` of raw-accept ordinal and KEM creation index in `Fin qAccept × Fin (qCreate + 1)`. The per-target decision of the compiled program (`decision`) is the event together with the designation of `g`; it reads only the program's result. Step 9.1 (`eligible_actual`) is an equality: the experiment's probability of the event with target `g` equals the probability of T4's event in the literal annotated initialized execution of the tagged compiled program at ordinal `i`, namely `Decided` (the selected accept returned a session and the decision holds), `GoodKem k` and `KeyMatchFinal k`. Its proof traces the compiled program (`PqxdhDeploymentRegistrationTrace`): the log of the traced compiled program is the registration part of its transcript (`compiled_trace`, a fact of the program for every reply), the tag at ordinal `i` is the `i`-th logged accept, and on the annotated execution the run invariant `Traced` gives that an accept that returned session `i` is the `i`-th accept attempt and passed the native verification prefix, and that every published bundle of owner `k` carries the pool key at KEM creation index `k` (the bundle-to-pool invariant). The designation then gives, on both the Server and the Beacon side, accept bytes of session `i` whose verified PQ key is owner `k`'s published key (`designate_keys`), hence `KeyMatchFinal k` under `Phase1ReadBack` (`keymatch_point`); `GoodKem` is `PqxdhDeploymentQuiet.approved_goodkem_unbudgeted`. Steps 9.2-9.4 (`kem_transfer`) chain T4 `actual_le_real` at the transported caps (`compile_full_certified`, `transported_room`), the certified KEM hop `KemRawCertified.real_le_ideal` and T6 `branchRaw_opaque`: per target, one ordinary one-key ML-KEM IND-CCA advantage of the exact proof-carrying raw-ordinal adversary and one ML-KEM correctness error, each with coefficient one, and the opaque KEM-ideal branch of the per-target decision remains. `kem_transfer_bills` instantiates `KemRawBills.adversary_bound` at the transported caps, `transported_total` gives its uniform allowance in closed form, `kem_hop_close` is the two-sided KEM hop at one target, and `kem_transfer_sum` is the exact-sum headline over all targets through `UniformTargetSelection.split`. T5 and T8 are not used per target, so no EUF term is charged. Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack`, `FunctionalDecapsulation` (the premise of the KEM hop) and the adversary budget; the bills (`kem_transfer_bills`, `kem_transfer_billed`) also take the existing cost premises `KemBound setup caps` and `initBound`, a total query bound `qInit` of the runtime initializer. T4 is one-sided, so a two-sided transfer needs CE-9b. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhDeploymentInterface (Entry Handle FullSpec ModeSpec Mode Budget FreshBounds FrameTag asModeO queryClass)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentCompile (Local compileImpl)
open PqxdhDeploymentCompileSecrecy (compileFull wrapCost)
open PqxdhDeploymentCompileBudget (commandKind cost unit)
open PqxdhDeploymentRegistrationTrace (Logged record logImpl traceFrom acceptsOf)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result Next : Type}

/-- The registration reply recorded by a transcript entry: a raw accept or a bundle call with its reply. -/
def regOf : Entry → Option Logged
  | ⟨.inl (.inr (.accept raw)), reply⟩ => some (.accept raw reply)
  | ⟨.inl (.inr (.bundle owner)), reply⟩ => some (.bundle owner reply)
  | _ => none

/-- The registration replies of a transcript, oldest first. -/
def registrations (transcript : List Entry) : List Logged := transcript.filterMap regOf

/-- A traced bind is the traced first program followed by the traced continuation from the reached log. -/
theorem traceFrom_bind (program : OracleComp (Spec KemSK) Result) (next : Result → OracleComp (Spec KemSK) Next)
    (log : List Logged) :
    traceFrom (program >>= next) log = traceFrom program log >>= fun reached => traceFrom (next reached.1) reached.2 := by
  simp only [traceFrom, simulateQ_bind, StateT.run_bind]

/-- A traced program that issues no bundle call and no raw accept keeps its log. -/
theorem traceFrom_quiet (program : OracleComp (Spec KemSK) Result)
    (noBundle : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 2) 0)
    (noAccept : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 3) 0) (log : List Logged)
    (outcome : Result × List Logged) (reached : outcome ∈ support (traceFrom program log)) : outcome.2 = log := by
  induction program using OracleComp.inductionOn generalizing log with
  | pure value =>
      simp only [traceFrom, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at noBundle noAccept
      obtain ⟨bundleAllowed, bundleRest⟩ := noBundle
      obtain ⟨acceptAllowed, acceptRest⟩ := noAccept
      have notBundle : sourceKind (KemSK := KemSK) query ≠ .inl 2 := by
        rcases bundleAllowed with free | impossible
        · exact free
        · omega
      have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := by
        rcases acceptAllowed with free | impossible
        · exact free
        · omega
      rw [PqxdhDeploymentRegistrationTrace.traceFrom_query_bind, mem_support_bind_iff] at reached
      obtain ⟨reply, _, reached⟩ := reached
      rw [PqxdhDeploymentRegistrationTrace.record_other query (fun raw same => notAccept (by rw [same]; rfl))
        (fun owner same => notBundle (by rw [same]; rfl))] at reached
      have bundleNext := bundleRest reply
      have acceptNext := acceptRest reply
      simp only [notBundle, notAccept, ite_false] at bundleNext acceptNext
      exact ih reply bundleNext acceptNext log reached

/-- Source bundle calls of the compiled secrecy-layer step of a query: none unless the query is a bundle command. -/
theorem bundle_cost (bounds : FreshBounds) (kind : Fin 14) (other : kind ≠ 2) :
    (∑ core, cost (.inl 2) core * wrapCost bounds core kind) = 0 := by
  fin_cases kind <;> simp_all [Fin.sum_univ_succ, cost, unit, wrapCost]

/-- Source raw accepts of the compiled secrecy-layer step of a query: none unless the query is an accept command. -/
theorem accept_cost (bounds : FreshBounds) (kind : Fin 14) (other : kind ≠ 3) :
    (∑ core, cost (.inl 3) core * wrapCost bounds core kind) = 0 := by
  fin_cases kind <;> simp_all [Fin.sum_univ_succ, cost, unit, wrapCost]


/-- Tracing commutes with a map of the program's result. -/
theorem traceFrom_map (f : Result → Next) (program : OracleComp (Spec KemSK) Result) (log : List Logged) :
    traceFrom (f <$> program) log = (fun outcome => (f outcome.1, outcome.2)) <$> traceFrom program log := by
  simp only [traceFrom, simulateQ_map, StateT.run_map]

/-- A traced single query logs its own registration reply. -/
theorem traceFrom_query (query : (Spec KemSK).Domain) (log : List Logged) :
    traceFrom ((Spec KemSK).query query : OracleComp (Spec KemSK) _) log =
      (fun reply => (reply, record query reply log)) <$> ((Spec KemSK).query query : OracleComp (Spec KemSK) _) := by
  have single := PqxdhDeploymentRegistrationTrace.traceFrom_query_bind query
    (fun reply => (pure reply : OracleComp (Spec KemSK) _)) log
  simp only [bind_pure] at single
  rw [single]
  simp only [traceFrom, simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- A forwarded registration command whose reply is logged by the compiler is one source query. -/
theorem forwardLogged_run (request : PqxdhRegistrationSchedule.Request) (command : PqxdhDeploymentInterface.Command)
    (reply : PqxdhRegistrationSchedule.QuerySpec request → PqxdhDeploymentInterface.CommandSpec command) (copies : Local) :
    (PqxdhDeploymentCompile.forwardLogged (KemSK := KemSK) request command reply).run copies =
      (fun answer => (reply answer, { copies with log := PqxdhDeploymentCompile.logReply copies.log command (reply answer) })) <$>
        PqxdhDeploymentCompile.forward (KemSK := KemSK) request := by
  simp only [PqxdhDeploymentCompile.forwardLogged, StateT.run, bind_pure_comp]

/-- One complete-interface query through the secrecy layer and the compiler, traced: the transcript gains exactly the query with its reply, and the log gains exactly that entry's registration reply. -/
theorem step_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Query)
    (ledger : Ledger) (copies : Local) (log : List Logged)
    (outcome : ((FullSpec.Range query × Ledger) × Local) × List Logged)
    (reached : outcome ∈ support (traceFrom ((simulateQ (compileImpl setup codec route)
      ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)).run copies) log)) :
    outcome.1.1.2.transcript = ledger.transcript ++ [⟨query, outcome.1.1.1⟩] ∧
      outcome.2 = log ++ (regOf ⟨query, outcome.1.1.1⟩).toList := by
  have compiled := PqxdhDeploymentRegistrationTrace.traceFrom_support _ log outcome reached
  have layered : outcome.1.1 ∈ support ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger) := by
    apply support_simulateQ_run'_subset (compileImpl setup codec route) _ copies
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ compiled
  have transcript : outcome.1.1.2.transcript = ledger.transcript ++ [⟨query, outcome.1.1.1⟩] := by
    rcases query with request | secrecy
    · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at layered
      obtain ⟨reply, _, same⟩ := layered
      rw [← same]
      rfl
    · exact PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy ledger
        outcome.1.1 layered
  refine ⟨transcript, ?_⟩
  by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
  · obtain ⟨raw, rfl⟩ := accept
    rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
    simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_map, compileImpl, traceFrom_map, support_map, Set.mem_image] at reached
    obtain ⟨answer, member, rfl⟩ := reached
    rw [forwardLogged_run, PqxdhDeploymentCompile.forward, traceFrom_map, traceFrom_query, Functor.map_map,
      support_map] at member
    obtain ⟨reply, _, rfl⟩ := member
    rfl
  · by_cases bundle : ∃ owner, query = .inl (.inr (.bundle owner))
    · obtain ⟨owner, rfl⟩ := bundle
      rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
      simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_map, compileImpl, traceFrom_map, support_map, Set.mem_image] at reached
      obtain ⟨answer, member, rfl⟩ := reached
      rw [forwardLogged_run, PqxdhDeploymentCompile.forward, traceFrom_map, traceFrom_query, Functor.map_map,
        support_map] at member
      obtain ⟨reply, _, rfl⟩ := member
      rfl
    · have notAccept : queryClass query ≠ 3 := by
        intro same
        rcases query with ((coin | command) | secrecy)
        · cases same
        · cases command <;> first | exact accept ⟨_, rfl⟩ | cases same
        · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> cases same
      have notBundle : queryClass query ≠ 2 := by
        intro same
        rcases query with ((coin | command) | secrecy)
        · cases same
        · cases command <;> first | exact bundle ⟨_, rfl⟩ | cases same
        · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> cases same
      have quietBundle := FinitePartitionQueryBounds.weighted_bound commandKind (cost (.inl 2))
        (fun core => wrapCost bounds core (queryClass query)) (compileImpl setup codec route)
        (fun request => sourceKind (KemSK := KemSK) request = .inl 2)
        ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)
        (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto codec setup.serverKeyId bounds core query
          ledger)
        (fun request state => PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 2) request state) copies
      have quietAccept := FinitePartitionQueryBounds.weighted_bound commandKind (cost (.inl 3))
        (fun core => wrapCost bounds core (queryClass query)) (compileImpl setup codec route)
        (fun request => sourceKind (KemSK := KemSK) request = .inl 3)
        ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)
        (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto codec setup.serverKeyId bounds core query
          ledger)
        (fun request state => PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 3) request state) copies
      rw [bundle_cost bounds _ notBundle] at quietBundle
      rw [accept_cost bounds _ notAccept] at quietAccept
      have kept := traceFrom_quiet _ quietBundle quietAccept log outcome reached
      have none : regOf ⟨query, outcome.1.1.1⟩ = none := by
        rcases query with ((coin | command) | secrecy)
        · rfl
        · cases command with
          | accept raw => exact absurd ⟨raw, rfl⟩ accept
          | bundle owner => exact absurd ⟨owner, rfl⟩ bundle
          | _ => rfl
        · rfl
      rw [kept, none, Option.toList_none, List.append_nil]


/-- The registrations of a transcript extended by one entry. -/
theorem registrations_append (transcript : List Entry) (entry : Entry) :
    registrations (transcript ++ [entry]) = registrations transcript ++ (regOf entry).toList := by
  simp only [registrations, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases regOf entry <;> rfl

/-- In every outcome of the traced compiled secrecy-layer run of a complete-interface program, started from a log equal to the registrations of the starting transcript, the final log is the registrations of the final transcript. -/
theorem compiled_traceFrom (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (program : OracleComp FullSpec Result)
    (ledger : Ledger) (copies : Local) (log : List Logged) (synced : log = registrations ledger.transcript)
    (outcome : ((Result × Ledger) × Local) × List Logged)
    (reached : outcome ∈ support (traceFrom ((simulateQ (compileImpl setup codec route)
      ((simulateQ (ledgerImpl setup.source.crypto codec setup.serverKeyId bounds) program).run ledger)).run copies) log)) :
    outcome.2 = registrations outcome.1.1.2.transcript := by
  induction program using OracleComp.inductionOn generalizing ledger copies log with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, traceFrom, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact synced
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, traceFrom_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, second⟩ := reached
      obtain ⟨transcript, logged⟩ := step_trace setup codec route bounds query ledger copies log middle first
      exact ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2
        (by rw [logged, transcript, registrations_append, synced]) second

/-- The log of the traced compiled program of a complete-interface adversary is the registrations of its final transcript. -/
theorem compiled_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (outcome : ((X × Ledger) × Local) × List Logged)
    (reached : outcome ∈ support (traceFrom (compileFull setup codec route bounds mode adversary) [])) :
    outcome.2 = registrations outcome.1.1.2.transcript :=
  compiled_traceFrom setup codec route bounds (asModeO mode adversary) Ledger.empty Local.empty [] rfl outcome reached


/-- What a deployment event may read: the adversary's output, the secrecy ledger (transcript, test session and fresh messages) and the produced record frames. -/
abbrev Observed (X : Type) := X × Ledger × List (FrameTag × PqxdhDeploymentNative.Frame)

/-- The observation of a result of the compiled program. -/
def observeCompiled (result : (X × Ledger) × Local) : Observed X := (result.1.1, result.1.2, result.2.produced)

/-- The observation of an outcome of the experiment, when the Server was constructed. -/
def observeGame (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
    PqxdhDeploymentSecrecy.State KemSK)) : Option (Observed X) :=
  outcome.map fun result => (result.2.1, result.2.2.1, result.2.2.2.produced)

/-- The target of a claim: the budgeted public designation, on the transcript, of the handle the claim names. -/
noncomputable def target (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (budget : Budget)
    (claim : Observed X → Option Handle) (observed : Observed X) : Option (Fin budget.accept × Fin budget.capacity) :=
  (claim observed).bind (PqxdhDeploymentTranscript.designateIn crypto codec serverKid budget observed.2.1.transcript)

/-- The per-target decision of the compiled program: the event holds and the claim designates `g`. It reads only the program's result. -/
noncomputable def decision (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (budget : Budget)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (result : (X × Ledger) × Local) : Bool :=
  event (observeCompiled result) && decide (target crypto codec serverKid budget claim (observeCompiled result) = some g)

/-- The event on an outcome of the experiment: false when no Server was constructed. -/
def happens (event : Observed X → Bool) (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
    PqxdhDeploymentSecrecy.State KemSK) × A) : Bool :=
  (observeGame outcome.1).any event

/-- The target designated on an outcome of the experiment. -/
noncomputable def designated (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (budget : Budget)
    (claim : Observed X → Option Handle) (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.State KemSK) × A) : Option (Fin budget.accept × Fin budget.capacity) :=
  (observeGame outcome.1).bind (target crypto codec serverKid budget claim)

/-- The accept bytes of a session come from a successful accept entry that returned that session handle. -/
theorem acceptOf_mem (transcript : List Entry) (session : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.acceptOf transcript session = some raw) :
    (⟨.inl (.inr (.accept raw)), some session⟩ : Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · cases value
  · cases command with
    | accept other =>
        cases reply with
        | none => cases value
        | some handle =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact member
            · cases value
    | _ => cases value
  · cases value

/-- A budgeted designation is a designation of the same pair. -/
theorem designateIn_some (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (budget : Budget)
    (transcript : List Entry) (handle : Handle) (g : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn crypto codec serverKid budget transcript handle = some g) :
    PqxdhDeploymentTranscript.designate crypto codec serverKid transcript handle = some (g.1.val, g.2.val) := by
  unfold PqxdhDeploymentTranscript.designateIn at designated
  obtain ⟨pair, found, rest⟩ := Option.bind_eq_some_iff.mp designated
  rw [found]
  split at rest
  · split at rest
    · simp only [Option.some.injEq] at rest
      subst rest
      rfl
    · cases rest
  · cases rest

/-- A designation `(session, k)` on either side names accept bytes of `session` whose candidate verifies, under the source attached verification of `crypto`, to keys whose PQ key is the one read from owner `k`'s published bundle. -/
theorem designate_keys (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (transcript : List Entry) (handle : Handle) (session k : Nat)
    (designated : PqxdhDeploymentTranscript.designate crypto codec serverKid transcript handle = some (session, k)) :
    ∃ raw accepted keys published, PqxdhDeploymentTranscript.acceptOf transcript session = some raw ∧
      PqxdhDeploymentTranscript.candidateOf codec raw = some accepted ∧
      PqxdhDeploymentTranscript.acceptedKeys crypto accepted = some keys ∧
      (PqxdhDeploymentTranscript.bundleOf transcript k).bind (PqxdhDeploymentTranscript.candidateOf codec) =
        some published ∧ PqxdhDeploymentTranscript.publishedPq published = some keys.2.pqKey := by
  cases handle with
  | peer keyId =>
      obtain ⟨_, raw, accepted, keys, _, rawFound, acceptedFound, keysFound, _, published, publishedFound, _, pq⟩ :=
        PqxdhDeploymentTranscript.designate_peer crypto codec serverKid keyId transcript session k designated
      exact ⟨raw, accepted, keys, published, rawFound, acceptedFound, keysFound, publishedFound, pq⟩
  | owner index =>
      obtain ⟨rfl, _, _, _, _, published, pqKey, _, _, _, publishedFound, pqFound, _, linked⟩ :=
        PqxdhDeploymentTranscript.designate_owner crypto codec serverKid transcript index session k designated
      obtain ⟨_, accepted, keys, _, _, _, acceptedFound, keysFound, same⟩ := linked
      obtain ⟨raw, rawFound, candidateFound⟩ := Option.bind_eq_some_iff.mp acceptedFound
      exact ⟨raw, accepted, keys, published, rawFound, candidateFound, keysFound, publishedFound, by rw [same]; exact pqFound⟩


/-- A result of a tagged program, without its tag, is a result of the program. -/
theorem tag_support (program : OracleComp (Spec KemSK) Result) (index : Nat) (outcome : Result × PqxdhRegistrationJointAcceptCutTag.Tag)
    (reached : outcome ∈ support (PqxdhRegistrationJointAcceptCutTag.tag program index)) : outcome.1 ∈ support program := by
  rw [← PqxdhRegistrationJointAcceptCutTag.tag_erase program index, support_map]
  exact ⟨outcome, reached, rfl⟩

/-- Step 9.1, pointwise: in the annotated initialized execution of the tagged traced compiled program at raw-accept ordinal `i`, from empty pools, every outcome whose per-target decision for `g = (i, k)` holds recorded, at the selected raw accept, bytes that returned session `i`, pass the native verification prefix, and verify to the public key at KEM creation index `k` of the final pool. -/
theorem keymatch_point (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      ((((X × Ledger) × Local) × List Logged) × PqxdhRegistrationJointAcceptCutTag.Tag))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (reached : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks
      ensureInit none (PqxdhRegistrationJointAcceptCutTag.tag (traceFrom (compileFull setup codec route bounds mode adversary)
        []) g.1.val)).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (decided : decision setup.source.crypto codec setup.serverKeyId budget event claim g outcome.2.1.1.1 = true) :
    ∃ raw value, outcome.2.1.2 = some (raw, some g.1.val) ∧
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
      (after.1.2.keys[g.2.val]?).map Prod.fst = some value.keys.pqKey := by
  have tagged := PqxdhDeploymentRegistrationTrace.source_support setup codec checks ensureInit none _ _ _ outcome
    reached
  have tagEq := PqxdhDeploymentRegistrationTrace.tag_traced _ g.1.val outcome.2.1 tagged
  have logEq := compiled_trace setup codec route bounds mode adversary outcome.2.1.1
    (tag_support _ g.1.val outcome.2.1 tagged)
  have projected : (some (outcome.1, outcome.2.1.1, outcome.2.2), after) ∈ support
      ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
        (traceFrom (compileFull setup codec route bounds mode adversary) [])).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
    rw [← PqxdhRegistrationJointAcceptCutTag.tag_erase (traceFrom (compileFull setup codec route bounds mode adversary) [])
      g.1.val, PqxdhDeploymentRegistrationTrace.source_map, support_map]
    exact ⟨_, reached, rfl⟩
  obtain ⟨traced, poolEq⟩ := PqxdhDeploymentRegistrationTrace.traced_source setup codec checks ensureInit none _ _ rfl
    after (outcome.1, outcome.2.1.1, outcome.2.2) projected
  simp only at traced poolEq
  simp only [decision, Bool.and_eq_true, decide_eq_true_eq] at decided
  obtain ⟨_, targeted⟩ := decided
  obtain ⟨handle, _, designatedIn⟩ := Option.bind_eq_some_iff.mp targeted
  obtain ⟨raw, accepted, keys, published, rawFound, candidateFound, keysFound, publishedFound, pqFound⟩ :=
    designate_keys _ codec setup.serverKeyId _ handle _ _ (designateIn_some _ codec setup.serverKeyId budget _ handle g
      designatedIn)
  have acceptLogged : (raw, some g.1.val) ∈ acceptsOf outcome.2.1.1.2 := by
    rw [logEq]
    simp only [acceptsOf, registrations, List.mem_filterMap]
    exact ⟨.accept raw (some g.1.val), ⟨_, acceptOf_mem _ _ raw rawFound, rfl⟩, rfl⟩
  obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp acceptLogged
  have samePosition := traced.positional position raw g.1.val positionFound
  rw [← samePosition] at positionFound
  obtain ⟨value, checked⟩ := traced.verified raw g.1.val acceptLogged
  obtain ⟨candidateEq, keysEq⟩ := PqxdhDeploymentKeyMatch.verified_keys setup codec checks raw value checked
  rw [candidateFound, Option.some.injEq] at candidateEq
  subst candidateEq
  rw [keysFound, Option.some.injEq] at keysEq
  subst keysEq
  obtain ⟨bytes, bytesFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  have bundleLogged : Logged.bundle g.2.val (some bytes) ∈ outcome.2.1.1.2 := by
    rw [logEq]
    simp only [registrations, List.mem_filterMap]
    exact ⟨_, PqxdhDeploymentKeyMatch.bundleOf_mem _ _ bytes bytesFound, rfl⟩
  obtain ⟨identity, tuple, s1, s2, s3, written, pooled⟩ := traced.bundles g.2.val bytes bundleLogged
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at publishedRead
  subst publishedRead
  rw [PqxdhDeploymentKeyMatch.publishedPq_candidate, Option.some.injEq] at pqFound
  refine ⟨raw, value, by rw [tagEq, positionFound], checked, ?_⟩
  rw [poolEq, pooled, pqFound]


/-- The KEM creation index of a target, in the form of T4's `selected` with `count = qCreate`. -/
def selectedKem (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) : Fin (budget.create + 1) :=
  ⟨g.2.val, g.2.isLt⟩

/-- Two maps that agree on the support of a run give the same run. -/
theorem map_support_congr {α β : Type} (run : ProbComp α) (first second : α → β)
    (same : ∀ value ∈ support run, first value = second value) : first <$> run = second <$> run := by
  simp only [map_eq_bind_pure_comp]
  exact bind_congr_of_forall_mem_support run fun value member => by simp only [Function.comp, same value member]

/-- Step 9.1 (plan section 9): for a target `g = (i, k)`, the probability that the deployment experiment ends with the event and the claim designating `g` equals the probability of T4's event in the literal annotated initialized execution of the tagged compiled program at raw-accept ordinal `i`: the selected accept returned a session and the per-target decision holds (`Decided`), KEM key `k` was never disclosed (`GoodKem`), and the selected raw bytes verify to the public key at KEM creation index `k` of the final pool (`KeyMatchFinal`). The approved Phase 1 and Phase 2 read-back contracts are the only premises; no budget is needed. -/
theorem eligible_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} =
    (letI := Classical.propDecidable
    𝒟[(fun final => decide (PqxdhRegistrationJointKemRawBridge.Decided
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g) final ∧
        PqxdhRegistrationJointKemRawBridge.GoodKem (selectedKem budget g) final ∧
        PqxdhRegistrationJointKemRawBridge.KeyMatchFinal setup codec checks (selectedKem budget g) final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
          (PqxdhRegistrationJointAcceptCutTag.tag (compileFull setup codec route bounds mode adversary) g.1.val)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true}) := by
  set work := compileFull setup codec route bounds mode adversary with workEq
  set tagged := PqxdhRegistrationJointAcceptCutTag.tag (traceFrom work []) g.1.val with taggedEq
  set start : PqxdhRegistrationJointServerPrefix.State KemSK A :=
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) with startEq
  have erased : work = (fun outcome => outcome.1.1) <$> tagged := by
    calc work = Prod.fst <$> traceFrom work [] := (PqxdhDeploymentRegistrationTrace.traceFrom_erase work []).symm
      _ = Prod.fst <$> (Prod.fst <$> tagged) := by rw [taggedEq, PqxdhRegistrationJointAcceptCutTag.tag_erase]
      _ = (fun outcome => outcome.1.1) <$> tagged := by rw [Functor.map_map]
  have retagged : PqxdhRegistrationJointAcceptCutTag.tag work g.1.val =
      (fun outcome => (outcome.1.1, outcome.2)) <$> tagged := by
    have mapped := PqxdhDeploymentRegistrationTrace.tag_map Prod.fst (traceFrom work []) g.1.val
    rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at mapped
    exact mapped
  have leftRun : (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none work).run start =
      (fun result => (result.1.map fun outcome => (outcome.1, outcome.2.1.1.1, outcome.2.2), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none tagged).run start := by
    have mapped := PqxdhDeploymentRegistrationTrace.source_map setup codec checks ensureInit none
      (fun outcome : (((X × Ledger) × Local) × List Logged) × PqxdhRegistrationJointAcceptCutTag.Tag => outcome.1.1)
      tagged start
    rw [← erased] at mapped
    exact mapped
  have rightRun : (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
      (PqxdhRegistrationJointAcceptCutTag.tag work g.1.val)).run start =
      (fun result => (result.1.map fun outcome => (outcome.1, (outcome.2.1.1.1, outcome.2.1.2), outcome.2.2),
        result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none tagged).run
          start := by
    rw [retagged]
    exact PqxdhDeploymentRegistrationTrace.source_map setup codec checks ensureInit none _ tagged start
  have game := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2 bounds
    mode adversary start
  change _ = (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime at game
  rw [← game, leftRun, rightRun]
  simp only [Functor.map_map]
  congr 2
  apply map_support_congr
  rintro ⟨_ | outcome, after⟩ member
  · simp [happens, observeGame, PqxdhDeploymentCompileSecrecy.mergeFull, PqxdhRegistrationJointKemRawBridge.Decided]
  · have observed : observeGame (PqxdhDeploymentCompileSecrecy.mergeFull
        (some (PqxdhRegistrationJointInitializedSchedule.eraseOutcome (outcome.1, outcome.2.1.1.1, outcome.2.2)),
          after.2)).1 = some (observeCompiled outcome.2.1.1.1) := rfl
    have good : PqxdhRegistrationJointKemRawBridge.GoodKem (selectedKem budget g)
        ((some (outcome.1, (outcome.2.1.1.1, outcome.2.1.2), outcome.2.2)).map
          (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), after) := by
      apply PqxdhDeploymentQuiet.approved_goodkem_unbudgeted setup codec checks route ensureInit none bounds mode
        adversary g.1.val runtime
      rw [← workEq, ← startEq, rightRun, Functor.map_map, support_map]
      exact ⟨_, member, rfl⟩
    rw [decide_eq_decide]
    constructor
    · rintro ⟨happened, chosen⟩
      simp only [happens, Option.map_some] at happened
      rw [observed] at happened
      simp only [designated, Option.map_some] at chosen
      rw [observed] at chosen
      have decided : decision setup.source.crypto codec setup.serverKeyId budget event claim g outcome.2.1.1.1 = true := by
        simp only [decision, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by simpa using happened, by simpa using chosen⟩
      obtain ⟨raw, value, tagEq, checked, keys⟩ := keymatch_point setup codec checks route ensureInit phase1 bounds mode
        adversary budget event claim g runtime outcome after member decided
      refine ⟨⟨_, rfl, decided, by simp only [tagEq]; rfl⟩, good, _, raw, some g.1.val, value, rfl, tagEq, checked, keys⟩
    · rintro ⟨⟨reached, found, decided, _⟩, _⟩
      simp only [Option.map_some, Option.some.injEq] at found
      subst found
      simp only [decision, Bool.and_eq_true, decide_eq_true_eq] at decided
      refine ⟨?_, ?_⟩
      · simp only [happens, Option.map_some]
        rw [observed]
        exact decided.1
      · simp only [designated, Option.map_some]
        rw [observed, Option.bind_some]
        exact decided.2


/-- Steps 9.2-9.4 (plan section 9) for one target `g = (i, k)` of a budget-respecting adversary: the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability that the opaque KEM-ideal branch of the compiled program accepts the per-target decision, plus one ordinary one-key ML-KEM IND-CCA advantage of the exact proof-carrying raw-ordinal adversary and one ML-KEM correctness error, both with coefficient one. The chain is CE-COMPILE with the bundle-to-pool invariant (step 9.1, `eligible_actual`), T4 `actual_le_real` with the transported caps (`compile_full_certified`, `transported_room`), the certified KEM hop `KemRawCertified.real_le_ideal` and T6 `branchRaw_opaque`. Premises: the approved Phase 1 and Phase 2 read-back contracts, functional decapsulation (the premise of the KEM hop) and the budget. -/
theorem kem_transfer (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val
        false] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
          g.1.val).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  rw [eligible_actual setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget event claim g
    runtime, ← PqxdhRegistrationJointKemRawOpaque.branchRaw_opaque]
  exact (PqxdhRegistrationJointKemRawBridge.actual_le_real setup codec checks ensureInit none _
    (compileFull setup codec route bounds mode adversary) runtime (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects)
    budget.create (selectedKem budget g) g.1.val (PqxdhDeploymentCompileCaps.transported_room bounds budget)).trans
    (PqxdhRegistrationJointKemRawCertified.real_le_ideal setup functional codec checks ensureInit none _ _ runtime
      budget.create (selectedKem budget g) g.1.val)

/-- Bills of the per-target KEM reduction: `KemRawBills.adversary_bound` at the caps transported from the deployment budget. Prechallenge: `(qInit + 32) + (keygenCost · qCreate + V)` uniform queries, `decapsBase · qFinish` base queries and `qFinish` logical decapsulations; postchallenge: `V`, `decapsBase · qFinish` and `qFinish`; where `V = uniformCap caps qCreate qFinish (OpenUniform.total caps (transported bounds budget)) qAccept`. -/
theorem kem_transfer_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
        g.1.val).MakesAtMostQueries
      ((qInit + 32) + (caps.keygenCost * budget.create + PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create
        budget.finish (PqxdhRegistrationJointOpenUniform.total caps (PqxdhDeploymentCompileCaps.transported bounds budget))
        budget.accept))
      (caps.decapsBase * budget.finish) budget.finish
      (PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create budget.finish
        (PqxdhRegistrationJointOpenUniform.total caps (PqxdhDeploymentCompileCaps.transported bounds budget))
        budget.accept)
      (caps.decapsBase * budget.finish) budget.finish :=
  PqxdhRegistrationJointKemRawBills.adversary_bound setup codec checks caps bounded ensureInit qInit initBound none
    (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (compileFull setup codec route bounds mode adversary) (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects) runtime
    budget.create (selectedKem budget g) g.1.val


/-- The per-target bound together with its bills. -/
theorem kem_transfer_billed (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val
        false] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
          g.1.val).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) ∧
    (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
        g.1.val).MakesAtMostQueries
      ((qInit + 32) + (caps.keygenCost * budget.create + PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create
        budget.finish (PqxdhRegistrationJointOpenUniform.total caps (PqxdhDeploymentCompileCaps.transported bounds budget))
        budget.accept))
      (caps.decapsBase * budget.finish) budget.finish
      (PqxdhRegistrationJointKemPostBills.uniformCap caps budget.create budget.finish
        (PqxdhRegistrationJointOpenUniform.total caps (PqxdhDeploymentCompileCaps.transported bounds budget))
        budget.accept)
      (caps.decapsBase * budget.finish) budget.finish :=
  ⟨kem_transfer setup functional codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects event
    claim g runtime,
   kem_transfer_bills setup codec checks route caps bounded ensureInit qInit initBound bounds mode adversary budget
    respects event claim g runtime⟩

/-- The two-sided KEM hop for the compiled program at one target: the real raw-ordinal game and the opaque KEM-ideal branch of the per-target decision are within one IND-CCA advantage of the proof-carrying adversary plus the correctness error (`KemRawCertified.ideal_close` with T6). This is the form a later two-sided T4 (CE-9b) composes with; T4 itself is one-sided. -/
theorem kem_hop_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
        g.1.val] {true}).toReal -
      (𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val
        false] {true}).toReal| ≤
      (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
          g.1.val).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup := by
  rw [← PqxdhRegistrationJointKemRawOpaque.branchRaw_opaque]
  exact PqxdhRegistrationJointKemRawCertified.ideal_close setup functional codec checks ensureInit none _ _ runtime
    budget.create (selectedKem budget g) g.1.val

/-- Exact-sum headline of the key transfer (plan sections 7 and 9): the probability that the deployment experiment ends with the event and the claim designating some target in `Fin qAccept × Fin (qCreate + 1)` is at most the sum over all such targets `g` of the opaque KEM-ideal branch of `g`'s decision plus one IND-CCA advantage of `g`'s proof-carrying adversary plus one correctness error, each with coefficient one. The first step is the exact split `UniformTargetSelection.split`; no selection factor and no EUF term is charged. -/
theorem kem_transfer_sum (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        (designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.capacity,
        (𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val
          false] {true} +
        ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
            (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
          (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
            (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
            (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
            g.1.val).toINDCCA).toReal +
          PqxdhRegistrationJointKemRawGame.correctnessError setup)) := by
  rw [UniformTargetSelection.split]
  exact Finset.sum_le_sum fun g _ => kem_transfer setup functional codec checks route ensureInit phase1 phase2 bounds
    mode adversary budget respects event claim g runtime


/-- The native uniform allowance of the KEM bills at the transported caps, in closed form: experiment coins, 32 per create and per bundle, `96 + encapsCost` per accept, 64 per build, `64 · 56` per finish, 64 per HMAC and 64 per BLAKE2b query; Server kernel reveals and established-kernel reads add nothing. -/
theorem transported_total (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounds : FreshBounds) (budget : Budget) :
    PqxdhRegistrationJointOpenUniform.total caps (PqxdhDeploymentCompileCaps.transported bounds budget) =
      (budget.coin + budget.test + budget.freshBytes bounds) + 32 * budget.create + 32 * budget.bundle +
        (96 + caps.encapsCost) * budget.accept + 64 * budget.build + (64 * 56) * budget.finish + 64 * budget.hmac +
        64 * (budget.hash + budget.sends + budget.receives + budget.test + budget.fresh) := by
  simp [PqxdhRegistrationJointOpenUniform.total, PqxdhDeploymentCompileCaps.transported]

end BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.traceFrom_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.traceFrom_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.traceFrom_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.traceFrom_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.bundle_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.bundle_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.accept_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.accept_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.traceFrom_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.traceFrom_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.traceFrom_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.traceFrom_query

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.forwardLogged_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.forwardLogged_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.step_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.step_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.registrations_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.registrations_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.compiled_traceFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.compiled_traceFrom

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.compiled_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.compiled_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.acceptOf_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.acceptOf_mem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.designateIn_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.designateIn_some

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.designate_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.designate_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.tag_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.tag_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.keymatch_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.keymatch_point

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.map_support_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.map_support_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.eligible_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.eligible_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_transfer

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_transfer_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_transfer_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_transfer_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_transfer_billed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_hop_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_hop_close

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_transfer_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.kem_transfer_sum

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.transported_total' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer.transported_total
