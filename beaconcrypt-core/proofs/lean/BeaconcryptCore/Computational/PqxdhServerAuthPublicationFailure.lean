import BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost

/-! Couple the actual and selected-writer reference callbacks using one complete component execution. Failure is a retained event, never a condition imposed on component randomness. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhJointKdfGame PqxdhServerAuthCtxCalls
open PqxdhServerAuthCtxBuild (Outcome Log Response)
open PqxdhServerAuthPublicationGhost (project)
variable {ι KemSK Reader WireResponse Result : Type} {baseSpec : OracleSpec ι}

/-- The unannotated actual builder's optional native rejection keeps the entire old Server. This follows from the reached writer trace, without a total-writer premise. -/
theorem native_rejection (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (payload : Option Pqxdh.Bytes) (server rejected : ServerState) (before after : Log)
    (supported : (some (.ok (none, rejected)), after) ∈ support
      ((PqxdhServerAuthBuildProgram.compiled source codec checks rest pending payload () server).run.run before)) :
    rejected = server := by
  rw [← PqxdhServerAuthPublicationTrace.compiled_erase source codec checks rest pending payload () server (before, [])] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨⟨reply, log, trace⟩, actual, equal⟩ := supported
  cases (congrArg Prod.fst equal : reply = some (.ok (none, rejected)))
  exact PqxdhServerAuthPublicationWriter.compiled_rejection source codec checks rest pending payload () server rejected (before, []) (log, trace) actual

/-- The reference changes only the native result and the local source log. Every component query is run in the shared program before this pure map. -/
def mask (state : Local KemSK) (result : Option Outcome × Log) : Option Outcome × Log :=
  (PqxdhServerAuthPublicationForcedFrame.suppressNative state.1.1.server result.1, [])

/-- Keep both complete settlements of a single component execution as private analysis output. The actual public reply is still the first component. -/
def pair (session : Nat) (state : Local KemSK) (result : Option Outcome × Log) :=
  (PqxdhServerAuthCtxBuild.post session state result,
   PqxdhServerAuthCtxBuild.post session state (mask state result))

/-- On actual native rejection the reference has exactly the same operational reply and full poststate; only the private source ghost can differ. Component refusal is retained separately. -/
theorem post_rejection (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (payload : Option Pqxdh.Bytes) (session : Nat) (state : Local KemSK)
    (result : Option Outcome × Log)
    (supported : result ∈ support
      ((PqxdhServerAuthBuildProgram.compiled source codec checks rest pending payload () state.1.1.server).run.run []))
    (rejected : (PqxdhServerAuthCtxBuild.post session state result).1 = some none) :
    Prod.map id PqxdhServerAuthPublicationGhost.project (pair session state result).1 =
      Prod.map id PqxdhServerAuthPublicationGhost.project (pair session state result).2 := by
  rcases result with ⟨_ | outcome, log⟩
  · rfl
  · cases outcome with
    | fail error => rfl
    | div => rfl
    | ok value =>
      rcases value with ⟨_ | response, server⟩
      · rw [native_rejection source codec checks rest pending payload state.1.1.server server [] log supported]
        rfl
      · change some (some response) = some none at rejected
        cases Option.some.inj rejected

/-- Both complete callback outcomes come from one unchanged actual selected component execution, before any public continuation branches on either result. -/
noncomputable def selected (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK) :=
  pair session state <$>
    (PqxdhServerAuthBuildProgram.compiled source codec checks rest token.pending payload () state.1.1.server).run.run []

/-- The first projection is the entire original selected callback, including actual optional reply and complete source settlement. -/
theorem selected_actual (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK) :
    Prod.fst <$> selected source codec checks rest session token payload state =
      (PqxdhServerAuthCtxBuild.selected source codec checks rest session token payload state.1.1.server).run.run state := by
  simp only [selected, Functor.map_map, pair, PqxdhServerAuthCtxBuild.selected,
    PqxdhServerAuthCtxBuild.after, OptionT.run_mk, StateT.run]

/-- The second projection is exactly the selected reference callback. Both projections retain the same oracle requests, so every interpreter's private effects are preserved. -/
theorem selected_reference (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK) :
    Prod.snd <$> selected source codec checks rest session token payload state =
      (PqxdhServerAuthCtxBuild.selected source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec)
        checks rest session token payload state.1.1.server).run.run state := by
  simp only [selected, PqxdhServerAuthCtxBuild.selected, PqxdhServerAuthCtxBuild.after,
    OptionT.run_mk, Functor.map_map]
  rw [PqxdhServerAuthPublicationForcedFrame.compiled_mask]
  simp only [StateT.run, Functor.map_map, pair, mask]

/-- Every supported paired execution with an actual rejected response has equal complete projected settlements. The enclosing component execution is not conditioned or resampled. -/
theorem selected_rejection (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK) (result : (Option (Option Response) × Local KemSK) × (Option (Option Response) × Local KemSK))
    (supported : result ∈ support (selected source codec checks rest session token payload state))
    (rejected : result.1.1 = some none) :
    Prod.map id PqxdhServerAuthPublicationGhost.project result.1 =
      Prod.map id PqxdhServerAuthPublicationGhost.project result.2 := by
  simp only [selected, support_map, Set.mem_image] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  exact post_rejection source codec checks rest token.pending payload session state actual reached rejected

/-- One execution of the original lookup and complete callback supplies both public-result views. Ordinary builders and missing tokens use identical settlements. -/
noncomputable def build (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      ((Option (Option Response) × Local KemSK) × (Option (Option Response) × Local KemSK)) :=
  match state.1.1.pending session with
  | none => pure ((some none, state), (some none, state))
  | some token => if state.1.2.1 session then selected source codec checks rest session token payload state
      else (fun result => (result, result)) <$>
        (PqxdhServerAuthCtxBuild.known source codec checks session token payload state.1.1.server).run.run state

/-- The full paired build's first projection is the original actual source callback. -/
theorem build_actual (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK) :
    Prod.fst <$> build source codec checks rest session payload state =
      (PqxdhServerAuthCtxBuild.build source codec checks rest session payload).run.run state := by
  simp only [build, PqxdhServerAuthCtxBuild.build, OptionT.run_mk, StateT.run]
  cases state.1.1.pending session <;> simp only [map_pure]
  split_ifs
  · exact selected_actual source codec checks rest session _ payload state
  · simp only [Functor.map_map, id_map']

/-- The other complete build projection is the mixed reference, retaining the original ordinary codec and absent-token behavior. -/
theorem build_reference (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK) :
    Prod.snd <$> build source codec checks rest session payload state =
      (PqxdhServerAuthPublicationReference.build source codec checks rest session payload).run.run state := by
  simp only [build, PqxdhServerAuthPublicationReference.build, OptionT.run_mk, StateT.run]
  cases state.1.1.pending session <;> simp only [map_pure]
  split_ifs
  · exact selected_reference source codec checks rest session _ payload state
  · simp only [Functor.map_map, id_map']

/-- Actual optional rejection in the full lookup/selected/ordinary dispatch preserves identical projected poststates in the coupled run. -/
theorem build_rejection (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK)
    (result : (Option (Option Response) × Local KemSK) × (Option (Option Response) × Local KemSK))
    (supported : result ∈ support (build source codec checks rest session payload state))
    (rejected : result.1.1 = some none) :
    Prod.map id PqxdhServerAuthPublicationGhost.project result.1 =
      Prod.map id PqxdhServerAuthPublicationGhost.project result.2 := by
  unfold build at supported
  split at supported
  · simp_all only [mem_support_pure_iff]
  · split_ifs at supported
    · exact selected_rejection source codec checks rest session _ payload state result supported rejected
    · simp only [support_map, Set.mem_image] at supported
      obtain ⟨actual, _, rfl⟩ := supported
      rfl

/-- Both API views share the identical query and complete source callback; only the selected native result is mapped differently. -/
noncomputable def route (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (select : Bool)
    (query : ServerAuthSpec.Domain) (state : Local KemSK) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      ((Option (ServerAuthSpec.Range query) × Local KemSK) × (Option (ServerAuthSpec.Range query) × Local KemSK)) :=
  match query with
  | .inr (.build session payload) => build setup.source codec checks rest session payload state
  | query => (fun result => (result, result)) <$>
      (PqxdhServerAuthCtxHandler.route setup codec checks context rest select query).run.run state

/-- The original entire API is the first projection of the concrete paired callback. -/
theorem route_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (select : Bool)
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    Prod.fst <$> route setup codec checks context rest select query state =
      (PqxdhServerAuthCtxHandler.route setup codec checks context rest select query).run.run state := by
  cases query with
  | inl coin => simp only [route, Functor.map_map, id_map']
  | inr query =>
      cases query
      case build session payload => exact build_actual setup.source codec checks rest session payload state
      all_goals simp only [route, Functor.map_map, id_map']

/-- The mixed reference's entire original API is the second projection of the same paired callback. -/
theorem route_reference (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (select : Bool)
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    Prod.snd <$> route setup codec checks context rest select query state =
      (PqxdhServerAuthPublicationReference.route setup codec checks context rest select query).run.run state := by
  cases query with
  | inl coin => simp only [route, PqxdhServerAuthPublicationReference.route, Functor.map_map, id_map']
  | inr query =>
      cases query
      case build session payload => exact build_reference setup.source codec checks rest session payload state
      all_goals simp only [route, PqxdhServerAuthPublicationReference.route, Functor.map_map, id_map']

/-- Each paired route is followed by the original designation and refusal settlement on both complete outcomes. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :=
  Prod.map (PqxdhServerAuthCtxHandler.settle Q j query state) (PqxdhServerAuthCtxHandler.settle Q j query state) <$>
    route setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state

/-- The first complete handler projection is the original API including designation and sticky refusal. -/
theorem handler_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    Prod.fst <$> handler setup codec checks context rest Q j query state =
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state := by
  simpa only [handler, PqxdhServerAuthCtxHandler.handler, OptionT.run_mk, StateT.run,
    Functor.map_map, Prod.map_def] using congrArg
      (Functor.map (PqxdhServerAuthCtxHandler.settle Q j query state))
      (route_actual setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state)

/-- The second complete handler projection is exactly the reference with the same designation and sticky-refusal mechanism. -/
theorem handler_reference (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    Prod.snd <$> handler setup codec checks context rest Q j query state =
      (PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j query).run.run state := by
  simpa only [handler, PqxdhServerAuthPublicationReference.handler, OptionT.run_mk, StateT.run,
    Functor.map_map, Prod.map_def] using congrArg
      (Functor.map (PqxdhServerAuthCtxHandler.settle Q j query state))
      (route_reference setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state)

/-- Keep the entire original second-session checkpoint on each complete paired handler result, including refusal poststates. -/
noncomputable def stopped (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :=
  let monitor := PqxdhServerAuthCtxStop.observe
    (fun current : Local KemSK => current.1.1.sessions) (fun current => current.1.2.1) query state
  Prod.map monitor monitor <$> handler setup codec checks context rest Q j query state.1

/-- The first monitored callback is exactly the full original source stop wrapper. -/
theorem stopped_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    Prod.fst <$> stopped setup codec checks context rest Q j query state =
      (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state := by
  simpa only [stopped, PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped,
    OptionT.run_mk, StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def] using congrArg
      (Functor.map (PqxdhServerAuthCtxStop.observe
        (fun current : Local KemSK => current.1.1.sessions) (fun current => current.1.2.1) query state))
      (handler_actual setup codec checks context rest Q j query state.1)

/-- The second monitored callback is exactly the complete reference stop wrapper. -/
theorem stopped_reference (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    Prod.snd <$> stopped setup codec checks context rest Q j query state =
      (PqxdhServerAuthPublicationReference.stopped setup codec checks context rest Q j query).run.run state := by
  simpa only [stopped, PqxdhServerAuthPublicationReference.stopped,
    PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped,
    OptionT.run_mk, StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def] using congrArg
      (Functor.map (PqxdhServerAuthCtxStop.observe
        (fun current : Local KemSK => current.1.1.sessions) (fun current => current.1.2.1) query state))
      (handler_reference setup codec checks context rest Q j query state.1)

/-- A rejected actual build has the same complete projected handler settlement in the coupled reference, including the pending token, designation and sticky refusal fields. -/
theorem handler_build_rejection (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK)
    (result : (Option (Option Response) × Local KemSK) × (Option (Option Response) × Local KemSK))
    (supported : result ∈ support (handler setup codec checks context rest Q j (.inr (.build session payload)) state))
    (rejected : result.1.1 = some none) :
    Prod.map id PqxdhServerAuthPublicationGhost.project result.1 =
      Prod.map id PqxdhServerAuthPublicationGhost.project result.2 := by
  simp only [handler, route, support_map, Set.mem_image] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  have same := build_rejection setup.source codec checks rest session payload state actual reached
    (by simpa only [Prod.map_def,
      (PqxdhServerAuthCtxHandlerBounds.settle_fields Q j (.inr (.build session payload)) state actual.1).1] using rejected)
  change Prod.map id PqxdhServerAuthPublicationGhost.project
    (PqxdhServerAuthCtxHandler.settle Q j (.inr (.build session payload)) state actual.1) =
      Prod.map id PqxdhServerAuthPublicationGhost.project
        (PqxdhServerAuthCtxHandler.settle Q j (.inr (.build session payload)) state actual.2)
  rw [PqxdhServerAuthPublicationGhost.settle_project, PqxdhServerAuthPublicationGhost.settle_project, same]

/-- The literal second-session monitor preserves the same complete projected rejected-build state and checkpoint in both coupled views. -/
theorem stopped_build_rejection (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK × Option Nat)
    (result : (Option (Option Response) × (Local KemSK × Option Nat)) ×
      (Option (Option Response) × (Local KemSK × Option Nat)))
    (supported : result ∈ support (stopped setup codec checks context rest Q j (.inr (.build session payload)) state))
    (rejected : result.1.1 = some none) :
    Prod.map id PqxdhServerAuthPublicationGhost.tracked result.1 =
      Prod.map id PqxdhServerAuthPublicationGhost.tracked result.2 := by
  simp only [stopped, support_map, Set.mem_image] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  have normal : actual.1.1 = some none := by
    cases answer : actual.1.1 <;> simp_all only [Prod.map_def, PqxdhServerAuthCtxStop.observe,
      PqxdhServerAuthCtxStop.checkpoint]
  have same := handler_build_rejection setup codec checks context rest Q j session payload state.1 actual reached normal
  change Prod.map id PqxdhServerAuthPublicationGhost.tracked
    (PqxdhServerAuthCtxStop.observe (fun current : Local KemSK => current.1.1.sessions)
      (fun current => current.1.2.1) (.inr (.build session payload)) state actual.1) =
      Prod.map id PqxdhServerAuthPublicationGhost.tracked
        (PqxdhServerAuthCtxStop.observe (fun current : Local KemSK => current.1.1.sessions)
          (fun current => current.1.2.1) (.inr (.build session payload)) state actual.2)
  rw [PqxdhServerAuthPublicationGhost.observe_project, PqxdhServerAuthPublicationGhost.observe_project, same]

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.native_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.native_rejection
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.post_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.post_rejection
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.selected_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.selected_actual
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.selected_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.selected_reference
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.selected_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.selected_rejection
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.build_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.build_actual
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.build_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.build_reference
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.build_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.build_rejection
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.route_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.route_actual
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.route_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.route_reference
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.handler_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.handler_actual
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.handler_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.handler_reference
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.stopped_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.stopped_actual
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.stopped_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.stopped_reference
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.handler_build_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.handler_build_rejection
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.stopped_build_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationFailure.stopped_build_rejection
