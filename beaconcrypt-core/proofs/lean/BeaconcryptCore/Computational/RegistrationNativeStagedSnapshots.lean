-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage
import BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts
import BeaconcryptCore.Computational.RegistrationNativePublicObservation

/-! One finite map captures the actual first successful public Server-acceptance or Beacon-completion callback at each named native endpoint. The mandatory-ML experiment and complete original secrecy ledger keep running after every capture. These are actual native staged snapshots and finite union bounds, not a completed partner/root agreement claim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots
open RegistrationNativeInterface (Entry FullSpec ModeSpec asModeO)
open PqxdhDeploymentInterface (FreshBounds Mode)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentSessionSnapshots (Journal)
variable {n : Nat} {ι KemSK Value Index : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

abbrev Endpoints (sessions owners : Nat) := Fin sessions ⊕ Fin owners
abbrev Native := RegistrationNativeLedger.State × RegistrationNativeExperiment.State n KemSK source
abbrev Snapshots (Index : Type) := PqxdhDeploymentSessionSnapshots.State Index FullSpec (Native (n := n) (KemSK := KemSK) (source := source))

def entries (journal : Journal FullSpec) : List Entry := journal.map fun entry => ⟨entry.1, entry.2⟩

/-- The endpoint test uses only original public command operands and their permitted mode-P reply. -/
def hit {sessions owners : Nat} : Endpoints sessions owners → RegistrationNativeLedgerHiding.PublicEntry → Bool
  | .inl session, entry => (RegistrationNativePublicObservation.acceptPublic session.val entry).isSome
  | .inr owner, ⟨.inl (.inr (.finish index _)), some _⟩ => index == owner.val
  | .inr _, _ => false

def stop {sessions owners : Nat} (endpoint : Endpoints sessions owners) (journal : Journal FullSpec) : Prop :=
  ((entries journal).map RegistrationNativeLedgerHiding.view).any (hit endpoint) = true

instance {sessions owners : Nat} (endpoint : Endpoints sessions owners) : DecidablePred (stop endpoint) := fun journal => by unfold stop; infer_instance

theorem stop_empty {sessions owners : Nat} (endpoint : Endpoints sessions owners) : ¬ stop endpoint [] := by
  simp only [stop, entries, List.map_nil, List.any_nil, Bool.false_eq_true, not_false_eq_true]

/-- The stopping point depends only on the permitted original public transcript, never on hidden origin ownership. -/
theorem stop_public {sessions owners : Nat} (endpoint : Endpoints sessions owners) (first second : Journal FullSpec)
    (same : (entries first).map RegistrationNativeLedgerHiding.view = (entries second).map RegistrationNativeLedgerHiding.view) :
    stop endpoint first ↔ stop endpoint second := by rw [stop, stop, same]

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (bounds : FreshBounds)

noncomputable def handler := RegistrationNativeFullCompiler.handler setup.source.crypto wire
  created.server.server.metadata.sender bounds
  (RegistrationNativeExperiment.handler (n := n) setup checks wire route representation created source credential)

noncomputable def run {sessions owners : Nat} (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ProbComp (Value × Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners)) :=
  PqxdhDeploymentSessionSnapshots.run (handler setup checks wire route representation created credential bounds)
    stop (asModeO mode work) (RegistrationNativeLedger.empty, before)

/-- Erasing the whole receipt map preserves the original full joint native distribution, including ledger, live state, primitive cache, counters, pools and later callback replies. -/
theorem erase {sessions owners : Nat} (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (fun result => (result.1, result.2.native)) <$>
      run (sessions := sessions) (owners := owners) setup checks wire route representation created credential bounds mode work before =
      RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before :=
  PqxdhDeploymentSessionSnapshots.erase _ _ _ _

/-- Every endpoint is the marginal of this same run, jointly with the original result and live final native state. -/
theorem project {sessions owners : Nat} (endpoint : Endpoints sessions owners)
    (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (before : RegistrationNativeExperiment.State n KemSK source) :
    (fun result => (result.1, PqxdhDeploymentSessionSnapshots.project endpoint result.2)) <$>
      run setup checks wire route representation created credential bounds mode work before =
      PqxdhDeploymentSessionSnapshot.run (handler setup checks wire route representation created credential bounds)
        (stop endpoint) (asModeO mode work) (RegistrationNativeLedger.empty, before) :=
  PqxdhDeploymentSessionSnapshots.project_run _ _ _ _ _

/-- All eligible endpoint failures concern snapshots from one actual native execution; no independence is assumed. -/
theorem all_endpoint_bound {sessions owners : Nat} (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (failure : Endpoints sessions owners → Value × PqxdhDeploymentSessionSnapshot.State FullSpec
      (Native (n := n) (KemSK := KemSK) (source := source)) → Prop) :
    Pr{let result ← run setup checks wire route representation created credential bounds mode work before}[
      ∃ endpoint, failure endpoint (result.1, PqxdhDeploymentSessionSnapshots.project endpoint result.2)] ≤
      ∑ endpoint, Pr{let result ← (PqxdhDeploymentSessionSnapshot.run
        (handler setup checks wire route representation created credential bounds)
        (stop endpoint) (asModeO mode work) (RegistrationNativeLedger.empty, before))}[failure endpoint result] :=
  PqxdhDeploymentSessionSnapshots.all_owner_bound _ _ _ _ _

/-- Actual original typed dispatch logs the same mode-O public entry as the observer's journal. -/
theorem handler_records (query : FullSpec.Domain) (before : Native (n := n) (KemSK := KemSK) (source := source))
    (result : FullSpec.Range query × Native (n := n) (KemSK := KemSK) (source := source))
    (supported : result ∈ support ((handler setup checks wire route representation created credential bounds query).run before)) :
    result.2.1.transcript = before.1.transcript ++ [⟨query, result.1⟩] :=
  RegistrationNativeParsedCounterLedger.step_trace setup checks wire route representation created credential bounds query before result supported

/-- Current and saved native ledgers are exactly their own original public callback journals. -/
def Consistent (state : Snapshots (n := n) (KemSK := KemSK) (source := source) Index) : Prop :=
  state.native.1.transcript = entries state.journal ∧
    ∀ index snapshot, state.captured index = some snapshot → snapshot.2.1.transcript = entries snapshot.1

private theorem advance_consistent
    (stops : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stops index)]
    (state : Snapshots (n := n) (KemSK := KemSK) (source := source) Index) (query : FullSpec.Domain) (reply : FullSpec.Range query)
    (native : Native (n := n) (KemSK := KemSK) (source := source)) (consistent : Consistent state)
    (recorded : native.1.transcript = state.native.1.transcript ++ [⟨query, reply⟩]) :
    Consistent (PqxdhDeploymentSessionSnapshots.advance stops state query reply native) := by
  have current : native.1.transcript = entries (state.journal ++ [⟨query, reply⟩]) := by
    simpa [entries] using recorded.trans (congrArg (fun transcript => transcript ++ [⟨query, reply⟩]) consistent.1)
  refine ⟨current, ?_⟩
  intro index snapshot saved
  cases previous : state.captured index with
  | none =>
      simp [PqxdhDeploymentSessionSnapshots.advance, previous] at saved
      rcases saved with ⟨_, rfl⟩
      exact current
  | some retained =>
      have same : retained = snapshot := by simpa [PqxdhDeploymentSessionSnapshots.advance, previous] using saved
      exact same ▸ consistent.2 index retained previous

private theorem program_consistent
    (stops : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stops index)]
    (work : OracleComp FullSpec Value) (state : Snapshots (n := n) (KemSK := KemSK) (source := source) Index)
    (consistent : Consistent state) (result : Value × Snapshots (n := n) (KemSK := KemSK) (source := source) Index)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentSessionSnapshots.handler
      (handler setup checks wire route representation created credential bounds) stops) work).run state)) : Consistent result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simpa only [supported] using consistent
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PqxdhDeploymentSessionSnapshots.handler_run,
        bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨step, reached, continued⟩ := supported
      exact ih step.1 _ (advance_consistent stops state query step.1 step.2 consistent
        (handler_records setup checks wire route representation created credential bounds query state.native step reached)) continued

/-- Complete native execution derives journal linkage and receipt coverage for every eligible endpoint, including every later suffix. -/
theorem run_facts {sessions owners : Nat} (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners))
    (supported : result ∈ support (run setup checks wire route representation created credential bounds mode work before)) :
    Consistent result.2 ∧ PqxdhDeploymentSessionSnapshotCoverage.Covered stop result.2 :=
  ⟨program_consistent setup checks wire route representation created credential bounds stop (asModeO mode work)
    (⟨[], fun _ => none, (RegistrationNativeLedger.empty, before)⟩ : Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners))
    ⟨rfl, fun _ _ impossible => nomatch impossible⟩ result supported,
    PqxdhDeploymentSessionSnapshotCoverage.run_covered _ _ _ _ stop_empty result supported⟩

/-- The native simultaneous map stores the actual cached signing and public-prefix call receipts at every captured state. -/
def PrefixHistories (offset : Nat) (state : Snapshots (n := n) (KemSK := KemSK) (source := source) Index) : Prop :=
  RegistrationNativeMldsaPrefixReceipts.Holds
    (RegistrationNativeParsedCounterLedger.native setup checks wire route representation created credential) wire offset state.native ∧
    ∀ index snapshot, state.captured index = some snapshot → RegistrationNativeMldsaPrefixReceipts.Holds
      (RegistrationNativeParsedCounterLedger.native setup checks wire route representation created credential) wire offset snapshot.2

private theorem advance_histories (offset : Nat)
    (stops : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stops index)]
    (state : Snapshots (n := n) (KemSK := KemSK) (source := source) Index) (query : FullSpec.Domain) (reply : FullSpec.Range query)
    (native : Native (n := n) (KemSK := KemSK) (source := source))
    (prior : PrefixHistories setup checks wire route representation created credential offset state)
    (current : RegistrationNativeMldsaPrefixReceipts.Holds
      (RegistrationNativeParsedCounterLedger.native setup checks wire route representation created credential) wire offset native) :
    PrefixHistories setup checks wire route representation created credential offset
      (PqxdhDeploymentSessionSnapshots.advance stops state query reply native) := by
  refine ⟨current, ?_⟩
  intro index snapshot saved
  cases previous : state.captured index with
  | none =>
      simp [PqxdhDeploymentSessionSnapshots.advance, previous] at saved
      rcases saved with ⟨_, rfl⟩
      exact current
  | some retained =>
      have same : retained = snapshot := by simpa [PqxdhDeploymentSessionSnapshots.advance, previous] using saved
      exact same ▸ prior.2 index retained previous

private theorem program_histories (offset : Nat)
    (stops : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stops index)]
    (work : OracleComp FullSpec Value) (state : Snapshots (n := n) (KemSK := KemSK) (source := source) Index)
    (prior : PrefixHistories setup checks wire route representation created credential offset state)
    (result : Value × Snapshots (n := n) (KemSK := KemSK) (source := source) Index)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentSessionSnapshots.handler
      (handler setup checks wire route representation created credential bounds) stops) work).run state)) :
    PrefixHistories setup checks wire route representation created credential offset result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simpa only [supported] using prior
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PqxdhDeploymentSessionSnapshots.handler_run,
        bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨step, reached, continued⟩ := supported
      exact ih step.1 _ (advance_histories setup checks wire route representation created credential offset stops state query step.1 step.2 prior
        (RegistrationNativeMldsaPrefixReceipts.step_holds setup checks wire route representation created credential bounds query
          offset state.native prior.1 step reached)) continued

/-- Every saved native endpoint state carries its actual historical ML receipts; later callbacks cannot replace them with future signing or final ratchet state. -/
theorem run_histories {sessions owners : Nat} (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (valid : RegistrationNativeMldsaInvariant.Valid before)
    (result : Value × Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners))
    (supported : result ∈ support (run setup checks wire route representation created credential bounds mode work before)) :
    PrefixHistories setup checks wire route representation created credential before.parsedAccepts result.2 := by
  apply program_histories setup checks wire route representation created credential bounds before.parsedAccepts stop (asModeO mode work)
    (⟨[], fun _ => none, (RegistrationNativeLedger.empty, before)⟩ : Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners))
    ?_ result supported
  refine ⟨⟨rfl, valid, ?_⟩, fun _ _ impossible => nomatch impossible⟩
  intro pre entry post impossible
  have sizes := congrArg List.length impossible
  simp only [RegistrationNativeLedger.empty, List.length_nil, List.length_append, List.length_cons] at sizes
  omega

/-- Successful original source startup supplies the simultaneous cached-prefix invariant without a caller history premise. -/
theorem initialized_histories {sessions owners : Nat} (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (result : Value × Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners))
    (supported : result ∈ support (run setup checks wire route representation initial.created initial.credential bounds mode work initial.state)) :
    PrefixHistories setup checks wire route representation initial.created initial.credential initial.state.parsedAccepts result.2 :=
  run_histories setup checks wire route representation initial.created initial.credential bounds mode work initial.state
    (RegistrationNativeMldsaInvariant.start setup ensureInit identityIndex serverKeyId initial startup) result supported

noncomputable def profile {sessions owners : Nat} (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (ModeSpec mode) Value) :
    ProbComp (Option (Value × Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners))) := do
  match ← RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId with
  | none => pure none
  | some initial => some <$> (run setup checks wire route representation initial.created initial.credential bounds mode
      (adversary initial.public) initial.state)

/-- The initialized mandatory-ML profile, original hidden bit and every complete event retain their exact distribution when all endpoint snapshots are erased. -/
theorem profile_erase {sessions owners : Nat} (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    (fun outcome => (outcome.map fun result => event (result.1, result.2.native)).getD false) <$>
      profile (sessions := sessions) (owners := owners) setup checks wire route representation bounds
        ensureInit identityIndex serverKeyId mode adversary =
      RegistrationNativeExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary event := by
  simp only [profile, RegistrationNativeExperiment.profile, map_bind]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => simp only [map_pure, Option.map_none, Option.getD_none]
  | some initial =>
      simp only [Functor.map_map, Option.map_some, Option.getD_some]
      have same := congrArg (fun work => event <$> work)
        (erase (sessions := sessions) (owners := owners) setup checks wire route representation initial.created initial.credential bounds
          mode (adversary initial.public) initial.state)
      simpa only [Functor.map_map, Function.comp_apply] using same

end BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.stop_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.stop_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.stop_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.stop_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.all_endpoint_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.all_endpoint_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.handler_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.handler_records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.run_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.run_facts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.run_histories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.run_histories

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.initialized_histories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.initialized_histories

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.profile_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots.profile_erase
