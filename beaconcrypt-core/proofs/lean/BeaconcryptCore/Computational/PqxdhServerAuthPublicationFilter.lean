import BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure

/-! A private publication flag supplies an explicit stopped comparison before any changed public reply is used. The actual source branch and component refusal remain in the same program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhJointKdfGame PqxdhServerAuthCtxCalls
open PqxdhServerAuthCtxBuild (Outcome Log Response)
open PqxdhServerAuthPublicationFailure
variable {ι KemSK Reader WireResponse Result : Type} {baseSpec : OracleSpec ι}

/-- Actual component refusal produces the identical complete source settlement in both paired views, before any public response exists. -/
theorem post_refusal (session : Nat) (state : Local KemSK) (result : Option Outcome × Log)
    (refused : (PqxdhServerAuthCtxBuild.post session state result).1 = none) :
    (pair session state result).1 = (pair session state result).2 := by
  rcases result with ⟨_ | outcome, log⟩
  · rfl
  · cases refused

/-- The exact selected callback's component refusal is shared by both complete paired outcomes, with no native rejection or writer premise. -/
theorem selected_refusal (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK) (result : (Option (Option Response) × Local KemSK) × (Option (Option Response) × Local KemSK))
    (supported : result ∈ support (selected source codec checks rest session token payload state))
    (refused : result.1.1 = none) : result.1 = result.2 := by
  simp only [selected, support_map, Set.mem_image] at supported
  obtain ⟨actual, _, rfl⟩ := supported
  exact post_refusal session state actual refused

/-- The private stopping flag uses the actual marked build and its literal optional public reply. Ordinary successful builds do not set it. -/
def published (query : ServerAuthSpec.Domain) (state : Local KemSK)
    (reply : Option (ServerAuthSpec.Range query)) : Bool :=
  match query with
  | .inr (.build session _) => state.1.2.1 session && reply.join.isSome
  | _ => false

/-- Every supported paired build without selected publication has identical complete operational settlements, including component refusal and ordinary successful builds. -/
theorem build_unpublished (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK)
    (result : (Option (Option Response) × Local KemSK) × (Option (Option Response) × Local KemSK))
    (supported : result ∈ support (build source codec checks rest session payload state))
    (quiet : published (.inr (.build session payload)) state result.1.1 = false) :
    Prod.map id PqxdhServerAuthPublicationGhost.project result.1 =
      Prod.map id PqxdhServerAuthPublicationGhost.project result.2 := by
  unfold build at supported
  split at supported
  · simp_all only [mem_support_pure_iff]
  · split_ifs at supported with marked
    · cases answer : result.1.1 with
      | none =>
          exact congrArg (Prod.map id PqxdhServerAuthPublicationGhost.project)
            (selected_refusal source codec checks rest session _ payload state result supported answer)
      | some value =>
          cases value with
          | none => exact selected_rejection source codec checks rest session _ payload state result supported answer
          | some response => simp [published, marked, answer] at quiet
    · simp only [support_map, Set.mem_image] at supported
      rcases supported with ⟨actual, _, rfl⟩
      rfl

/-- Every original API route has equal projected settlements until actual selected publication, without suppressing ordinary successful source operations. -/
theorem route_unpublished (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (select : Bool)
    (query : ServerAuthSpec.Domain) (state : Local KemSK)
    (result : (Option (ServerAuthSpec.Range query) × Local KemSK) ×
      (Option (ServerAuthSpec.Range query) × Local KemSK))
    (supported : result ∈ support (route setup codec checks context rest select query state))
    (quiet : published query state result.1.1 = false) :
    Prod.map id PqxdhServerAuthPublicationGhost.project result.1 =
      Prod.map id PqxdhServerAuthPublicationGhost.project result.2 := by
  cases query with
  | inl coin =>
      simp only [route, support_map, Set.mem_image] at supported
      rcases supported with ⟨actual, _, rfl⟩
      rfl
  | inr query =>
      cases query
      case build session payload => exact build_unpublished setup.source codec checks rest session payload state result supported quiet
      all_goals simp only [route, support_map, Set.mem_image] at supported
      all_goals rcases supported with ⟨actual, _, rfl⟩
      all_goals rfl

/-- The complete original settlement preserves equality before selected publication, including the sticky refusal and designation fields. -/
theorem handler_unpublished (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK)
    (result : (Option (ServerAuthSpec.Range query) × Local KemSK) ×
      (Option (ServerAuthSpec.Range query) × Local KemSK))
    (supported : result ∈ support (handler setup codec checks context rest Q j query state))
    (quiet : published query state result.1.1 = false) :
    Prod.map id PqxdhServerAuthPublicationGhost.project result.1 =
      Prod.map id PqxdhServerAuthPublicationGhost.project result.2 := by
  simp only [handler, support_map, Set.mem_image] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  have same := route_unpublished setup codec checks context rest
    (!state.2 && hiddenDesignated Q j query state.1) query state actual reached
    (by simpa only [Prod.map_def, (PqxdhServerAuthCtxHandlerBounds.settle_fields Q j query state actual.1).1] using quiet)
  change Prod.map id PqxdhServerAuthPublicationGhost.project
    (PqxdhServerAuthCtxHandler.settle Q j query state actual.1) =
      Prod.map id PqxdhServerAuthPublicationGhost.project
        (PqxdhServerAuthCtxHandler.settle Q j query state actual.2)
  rw [PqxdhServerAuthPublicationGhost.settle_project, PqxdhServerAuthPublicationGhost.settle_project, same]

/-- The original second-session monitor never changes whether this actual callback published the selected build. -/
theorem published_observe (query : ServerAuthSpec.Domain) (before : Local KemSK × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × Local KemSK) :
    published query before.1
      (PqxdhServerAuthCtxStop.observe (fun current : Local KemSK => current.1.1.sessions)
        (fun current => current.1.2.1) query before result).1 =
      published query before.1 result.1 := by
  cases query with
  | inl coin => rfl
  | inr query =>
      cases query <;> simp [published, PqxdhServerAuthCtxStop.observe, PqxdhServerAuthCtxStop.checkpoint]
      cases result.1 <;> rfl

/-- Full monitored callbacks remain operationally equal until actual selected publication, with all refusal poststates and monitor coordinates preserved. -/
theorem stopped_unpublished (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat)
    (result : (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) ×
      (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)))
    (supported : result ∈ support (stopped setup codec checks context rest Q j query state))
    (quiet : published query state.1 result.1.1 = false) :
    Prod.map id PqxdhServerAuthPublicationGhost.tracked result.1 =
      Prod.map id PqxdhServerAuthPublicationGhost.tracked result.2 := by
  simp only [stopped, support_map, Set.mem_image] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  have same := handler_unpublished setup codec checks context rest Q j query state.1 actual reached
    (by simpa only [Prod.map_def, published_observe] using quiet)
  change Prod.map id PqxdhServerAuthPublicationGhost.tracked
    (PqxdhServerAuthCtxStop.observe (fun current : Local KemSK => current.1.1.sessions)
      (fun current => current.1.2.1) query state actual.1) =
      Prod.map id PqxdhServerAuthPublicationGhost.tracked
        (PqxdhServerAuthCtxStop.observe (fun current : Local KemSK => current.1.1.sessions)
          (fun current => current.1.2.1) query state actual.2)
  rw [PqxdhServerAuthPublicationGhost.observe_project, PqxdhServerAuthPublicationGhost.observe_project, same]

/-- The stopped comparison kills the selected publication branch after its entire callback. It returns the exact normal reply and ghost-erased operational state on every continuing branch. Underlying component effects are not discarded. -/
def gate (actual : Bool) (query : ServerAuthSpec.Domain) (before : Local KemSK × Option Nat)
    (result : (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) ×
      (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat))) :
    Option (ServerAuthSpec.Range query × (Local KemSK × Option Nat)) :=
  if published query before.1 result.1.1 then none
  else
    let chosen := if actual then result.1 else result.2
    chosen.1.map fun reply => (reply, PqxdhServerAuthPublicationGhost.tracked chosen.2)

/-- Killing only actual selected publication makes the two complete callback views identical after private ghost erasure, including component refusal. -/
theorem gate_equal (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat)
    (result : (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) ×
      (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)))
    (supported : result ∈ support (stopped setup codec checks context rest Q j query state)) :
    gate true query state result = gate false query state result := by
  cases flag : published query state.1 result.1.1 with
  | true => simp only [gate, flag, ite_true]
  | false =>
      simpa only [gate, flag, Bool.false_eq_true, ite_false, ite_true, Prod.map_def, id_eq] using
        congrArg (fun outcome : Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat) =>
          outcome.1.map fun reply => (reply, outcome.2))
          (stopped_unpublished setup codec checks context rest Q j query state result supported flag)

/-- A complete adaptive comparison callback runs the original paired component work before the private stop and projection. The outer option marks paths excluded from this comparison. -/
noncomputable def filtered (actual : Bool) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader WireResponse) (checks : Checks) (context : Context KemSK)
    (rest : Residual) (Q : Nat) (j : Fin (Q + 1)) :
    QueryImpl ServerAuthSpec (StateT (Local KemSK × Option Nat)
      (OptionT (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))) :=
  fun query before => OptionT.mk <|
    gate actual query before <$> stopped setup codec checks context rest Q j query before

/-- The two complete killed callback programs are identical before selecting any cryptographic interpreter. -/
theorem filtered_equal (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    (filtered true setup codec checks context rest Q j query state).run =
      (filtered false setup codec checks context rest Q j query state).run := by
  change gate true query state <$> stopped setup codec checks context rest Q j query state =
    gate false query state <$> stopped setup codec checks context rest Q j query state
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact bind_congr_of_forall_mem_support _ fun result supported =>
    congrArg pure (gate_equal setup codec checks context rest Q j query state result supported)

/-- Arbitrary adaptive continuations have exactly the same killed oracle program in the actual and reference views. This includes all callback work before each private stop and every permitted query before termination. -/
theorem program_equal (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    ((simulateQ (filtered true setup codec checks context rest Q j) work).run state).run =
      ((simulateQ (filtered false setup codec checks context rest Q j) work).run state).run := by
  have same : filtered true setup codec checks context rest Q j =
      filtered false setup codec checks context rest Q j := by
    funext query before
    exact congrArg OptionT.mk (filtered_equal setup codec checks context rest Q j query before)
  rw [same]

/-- The actual stopped view can test the private kill directly on the original optional reply. -/
def actualGate (query : ServerAuthSpec.Domain) (before : Local KemSK × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) :
    Option (ServerAuthSpec.Range query × (Local KemSK × Option Nat)) :=
  if published query before.1 result.1 then none
  else result.1.map fun reply => (reply, PqxdhServerAuthPublicationGhost.tracked result.2)

/-- The actual killed callback is literally the original complete source callback followed by the private test and ghost projection. No paired computation is inserted into the actual source side. -/
theorem filtered_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    (filtered true setup codec checks context rest Q j query state).run =
      actualGate query state <$>
        (PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state := by
  change (fun result => actualGate query state result.1) <$>
    stopped setup codec checks context rest Q j query state = _
  simpa only [Functor.map_map] using congrArg (Functor.map (actualGate query state))
    (stopped_actual setup codec checks context rest Q j query state)

/-- The private kill examines only the actual public reply and the source mark, never the analysis ghost. -/
theorem published_project (query : ServerAuthSpec.Domain) (before : Local KemSK)
    (reply : Option (ServerAuthSpec.Range query)) :
    published query (PqxdhServerAuthPublicationGhost.project before) reply =
      published query before reply := by
  cases query with
  | inl coin => rfl
  | inr query => cases query <;> rfl

/-- Kill selected publication without erasing any source field on continuing paths. All terminal component effects remain outside this local option. -/
def sourceGate (query : ServerAuthSpec.Domain) (before : Local KemSK × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) :
    Option (ServerAuthSpec.Range query × (Local KemSK × Option Nat)) :=
  if published query before.1 result.1 then none
  else result.1.map fun reply => (reply, result.2)

/-- Source ghost projection commutes with the actual private kill, preserving exact public replies. -/
theorem sourceGate_project (query : ServerAuthSpec.Domain) (before : Local KemSK × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) :
    (sourceGate query before result).map (Prod.map id PqxdhServerAuthPublicationGhost.tracked) =
      sourceGate query (PqxdhServerAuthPublicationGhost.tracked before)
        (Prod.map id PqxdhServerAuthPublicationGhost.tracked result) := by
  simp only [sourceGate, PqxdhServerAuthPublicationGhost.tracked, Prod.map_def, id_eq,
    published_project]
  split <;> simp_all only [Option.map_none, Option.map_map, Function.comp_def]

/-- The original source handler keeps its complete private history until an actual selected publication or component stop ends the comparison. -/
noncomputable def sourceFiltered (setup : Setup baseSpec KemSK)
    (codec : Codec Reader WireResponse) (checks : Checks) (context : Context KemSK)
    (rest : Residual) (Q : Nat) (j : Fin (Q + 1)) :
    QueryImpl ServerAuthSpec (StateT (Local KemSK × Option Nat)
      (OptionT (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))) :=
  fun query before => OptionT.mk <|
    sourceGate query before <$>
      (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run before

/-- Projecting the original complete killed callback gives the checked actual comparison callback from the same operational state. -/
theorem source_filtered_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    Option.map (Prod.map id PqxdhServerAuthPublicationGhost.tracked) <$>
      (sourceFiltered setup codec checks context rest Q j query state).run =
        (filtered true setup codec checks context rest Q j query
          (PqxdhServerAuthPublicationGhost.tracked state)).run := by
  rw [filtered_actual]
  simp only [sourceFiltered, OptionT.run_mk, Functor.map_map, sourceGate_project]
  rw [show actualGate query (PqxdhServerAuthPublicationGhost.tracked state) =
    (fun result => sourceGate query (PqxdhServerAuthPublicationGhost.tracked state)
      (Prod.map id PqxdhServerAuthPublicationGhost.tracked result)) from rfl]
  simpa only [Functor.map_map] using
    congrArg (Functor.map (sourceGate query (PqxdhServerAuthPublicationGhost.tracked state)))
      (PqxdhServerAuthPublicationGhost.stopped_project setup codec checks context rest Q j query state)

/-- The original adaptive source retains its complete ghost between callbacks; erasing it only at the result boundary yields the exact reference-side killed comparison. All component programs, caches and instrumentation are preserved by this equality. -/
theorem source_program (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    Option.map (Prod.map id PqxdhServerAuthPublicationGhost.tracked) <$>
      ((simulateQ (sourceFiltered setup codec checks context rest Q j) work).run state).run =
        ((simulateQ (filtered false setup codec checks context rest Q j) work).run
          (PqxdhServerAuthPublicationGhost.tracked state)).run := by
  rw [← program_equal setup codec checks context rest Q j work]
  have projected := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (sourceFiltered setup codec checks context rest Q j)
    (filtered true setup codec checks context rest Q j)
    PqxdhServerAuthPublicationGhost.tracked
    (fun query before => by
      apply OptionT.ext
      simpa only [OptionT.run_map, StateT.run] using
        source_filtered_project setup codec checks context rest Q j query before) work state
  simpa only [OptionT.run_map] using congrArg OptionT.run projected

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.post_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.post_refusal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.selected_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.selected_refusal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.build_unpublished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.build_unpublished

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.route_unpublished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.route_unpublished

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.handler_unpublished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.handler_unpublished

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.published_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.published_observe

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.stopped_unpublished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.stopped_unpublished

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.gate_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.gate_equal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.filtered_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.filtered_equal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.program_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.program_equal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.filtered_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.filtered_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.published_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.published_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.sourceGate_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.sourceGate_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.source_filtered_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.source_filtered_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter.source_program
