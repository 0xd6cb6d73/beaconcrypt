-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhDeploymentPublicationSuppression
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry EncodedState encodeEntry encodeState)
open PqxdhRegistrationJointOwnership (Entry Owned)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Next : Type}

abbrev State (KemSK : Type) := PqxdhRegistrationJointSchedule.State KemSK × Selection
abbrev Client (KemSK Response Result : Type) := StateT (List EncodedEntry × Selection)
  (OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response)) Result

def bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat) :
    StateT (State KemSK) ProbComp (Option Pqxdh.Bytes) := fun state =>
  match state.1.owners[address]? with
  | none => pure (none, (state.1, state.2.next none))
  | some entry =>
    (fun result => (result.1.1.1, ({ state.1 with
      pool := (result.1.2, state.1.pool.2),
      owners := state.1.owners.set address { entry with owner := result.1.1.2 } }, result.2))) <$>
        trace setup codec entry.identityIndex entry.owner state.1.pool.1 state.2

def onSource (work : StateT (PqxdhRegistrationJointSchedule.State KemSK) ProbComp Result) :
    StateT (State KemSK) ProbComp Result := fun state =>
  (fun result => (result.1, (result.2, state.2))) <$> work.run state.1

/-- All commands retain the actual initialized Server's indexed private-service interpretation. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (StateT (State KemSK) ProbComp)
  | .inl (.inr (.bundle address)) => bundle setup codec address
  | query => onSource (PqxdhRegistrationJointServerSchedule.source setup codec checks seed index query)

def carry (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response Result) : Client KemSK Response Result :=
  fun state => (fun result => (result.1, (result.2, state.2))) <$> work.run state.1

/-- The selected role is a handle owner; no generated identity secret enters this dispatcher. -/
def bundleClient (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat) :
    Client KemSK Response (Option Pqxdh.Bytes) := fun state =>
  match state.1[address]? with
  | none => pure (none, (state.1, state.2.next none))
  | some entry =>
    (fun result => (result.1.1, (state.1.set address (entry.1, entry.2.1, result.1.2), result.2))) <$>
      simulateQ PqxdhRegistrationJointServiceSchedule.poolLift
        (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler codec)
          (PqxdhDeploymentPublicationSuppression.client (PqxdhRegistrationJointBundle.projection setup) entry.2.2 state.2))

noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (Client KemSK Response)
  | .inl (.inr (.bundle address)) => bundleClient setup codec address
  | query => carry (PqxdhRegistrationJointRevealSchedule.client setup codec query)

/-- Only representation bookkeeping is added beside the actual complete indexed backend execution. -/
noncomputable def execute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (publicIdentity : PublicIdentity) (work : Client KemSK Response Result)
    (state : EncodedState KemSK × Selection) : ProbComp (Result × (EncodedState KemSK × Selection)) :=
  (fun result => (result.1.1, (⟨result.2.1, result.2.2, result.1.2.1⟩, result.1.2.2))) <$>
    (simulateQ (PqxdhRegistrationJointServerClient.impl setup codec checks index publicIdentity)
      (work.run (state.1.owners, state.2))).run (state.1.pool, state.1.shared)

/-- Every unmodified source operation retains its complete result and exact suppression bookkeeping. -/
theorem carry_execute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (publicIdentity : PublicIdentity)
    (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response Result)
    (state : EncodedState KemSK) (selection : Selection) :
    execute setup codec checks index publicIdentity (carry work) (state, selection) =
      (fun result => (result.1, (result.2, selection))) <$>
        PqxdhRegistrationJointServerClient.execute setup codec checks index publicIdentity work state := by
  have carried : (carry work).run (state.owners, selection) =
      (fun result => (result.1, (result.2, selection))) <$> work.run state.owners := rfl
  simp only [execute, PqxdhRegistrationJointServerClient.execute, Functor.map_map]
  rw [carried, simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]

/-- Source-backed whole-block suppression preserves the actual handle/native correspondence at every present or absent owner. -/
theorem bundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (publicIdentity : PublicIdentity) (address : Nat) (state : State KemSK)
    (owned : PqxdhRegistrationJointSchedule.Invariant state.1) :
    execute setup codec checks index publicIdentity (bundleClient setup codec address) (encodeState setup state.1, state.2) =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (bundle setup codec address).run state := by
  cases found : state.1.owners[address]? with
  | none =>
      simp [execute, StateT.run, bundleClient, encodeState, List.getElem?_map, found, bundle]
      rfl
  | some entry =>
      simp only [execute, StateT.run, bundleClient, encodeState, List.getElem?_map, found,
        Option.map_some, encodeEntry, simulateQ_map]
      change _ <$> StateT.run (_ <$> _) _ = _
      rw [StateT.run_map, PqxdhRegistrationJointServerClient.pool_program,
        compiled_source setup codec entry.identityIndex entry.kemIndex entry.owner state.1.pool state.2
          (owned entry (List.mem_of_getElem? found)).1]
      simp [bundle, found, Functor.map_map, encodeEntry]

/-- Skipping a block cannot change any private seed slot or the selected owner's key ownership. -/
theorem after_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (entry : Entry KemSK) (generated : Option ScalarBytes) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (selection : Selection) (owned : Owned pool entry) :
    (after setup codec entry.identityIndex entry.owner generated pool.1 selection).1.2.seeds = pool.1.seeds ∧
      Owned ((after setup codec entry.identityIndex entry.owner generated pool.1 selection).1.2, pool.2)
        { entry with owner := (after setup codec entry.identityIndex entry.owner generated pool.1 selection).1.1.2 } := by
  by_cases blocked : (selection.next (nativeCurrent setup entry.identityIndex entry.owner generated)).blocks
      (nativeCurrent setup entry.identityIndex entry.owner generated) = true
  · rw [after_blocked setup codec entry.identityIndex entry.owner generated pool.1 selection blocked]
    exact ⟨rfl, owned⟩
  · simp only [after, blocked, Bool.false_eq_true, ite_false]
    exact ⟨PqxdhRegistrationJointBundle.after_seeds setup codec entry.identityIndex entry.owner generated pool.1,
      PqxdhRegistrationJointOwnership.bundle_owned setup codec entry generated pool owned⟩

/-- Every supported modified local trace retains ownership and all private seed slots. -/
theorem trace_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (entry : Entry KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (selection : Selection)
    (result : NativeResult KemSK × Selection) (owned : Owned pool entry)
    (supported : result ∈ support (trace setup codec entry.identityIndex entry.owner pool.1 selection)) :
    result.1.2.seeds = pool.1.seeds ∧ Owned (result.1.2, pool.2) { entry with owner := result.1.1.2 } := by
  cases phase : entry.owner.beacon.phase <;>
    simp only [trace, phase, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case fresh =>
    obtain ⟨scalar, _, rfl⟩ := supported
    exact after_owned setup codec entry (some scalar) pool selection owned
  all_goals subst result
  all_goals exact after_owned setup codec entry none pool selection owned

/-- Source representation invariants survive every modified bundle outcome. -/
theorem bundle_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (index address : Nat) (state : State KemSK)
    (result : Option Pqxdh.Bytes × State KemSK)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed index state.1)
    (supported : result ∈ support ((bundle setup codec address).run state)) :
    PqxdhRegistrationJointServerSchedule.Owned seed index result.2.1 := by
  cases found : state.1.owners[address]? <;>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case none => simpa only [supported] using owned
  case some entry =>
    obtain ⟨reached, member, rfl⟩ := supported
    have preserved := trace_owned setup codec entry state.1.pool state.2 reached
      (owned.1 entry (List.mem_of_getElem? found)) member
    exact ⟨PqxdhRegistrationJointSchedule.updated_owned state.1 (reached.1.2, state.1.pool.2) state.1.shared address
      { entry with owner := reached.1.1.2 } owned.1 preserved.1 rfl preserved.2,
      by simpa only [preserved.1] using owned.2⟩

/-- Reassociation keeps the complete adaptive continuation on the same source/backend state. -/
theorem execute_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (publicIdentity : PublicIdentity) (work : Client KemSK Response Result)
    (next : Result → Client KemSK Response Next) (state : EncodedState KemSK × Selection) :
    execute setup codec checks index publicIdentity (work >>= next) state =
      (execute setup codec checks index publicIdentity work state >>= fun result =>
        execute setup codec checks index publicIdentity (next result.1) result.2) := by
  simp only [execute, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]

/-- Existing nonsuppressed command compilers preserve the complete source correspondence with the added selection coordinate. -/
theorem carried_query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (owned : PqxdhRegistrationJointServerSchedule.Owned seed index state.1) :
    execute setup codec checks index (setup.joint.publicKeys seed)
      (carry (PqxdhRegistrationJointRevealSchedule.client setup codec query)) (encodeState setup state.1, state.2) =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (onSource (PqxdhRegistrationJointServerSchedule.source setup codec checks seed index query)).run state := by
  rw [carry_execute, PqxdhRegistrationJointServerClient.query_source setup codec checks seed index query state.1 owned]
  simp only [onSource, StateT.run, Functor.map_map]

/-- Every literal command runs the genuine handle client against the same full native/source poststate. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (owned : PqxdhRegistrationJointServerSchedule.Owned seed index state.1) :
    execute setup codec checks index (setup.joint.publicKeys seed) (handler setup codec query)
      (encodeState setup state.1, state.2) =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (source setup codec checks seed index query).run state := by
  rcases query with (coin | command) | read
  · exact carried_query_source setup codec checks seed index _ state owned
  · cases command
    case bundle address => exact bundle_source setup codec checks index (setup.joint.publicKeys seed) address state owned.1
    all_goals exact carried_query_source setup codec checks seed index _ state owned
  · exact carried_query_source setup codec checks seed index _ state owned

/-- Forwarded commands retain the initialized Server slot and all live-owner slot invariants. -/
theorem carried_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed index state.1)
    (supported : result ∈ support ((onSource
      (PqxdhRegistrationJointServerSchedule.source setup codec checks seed index query)).run state)) :
    PqxdhRegistrationJointServerSchedule.Owned seed index result.2.1 := by
  simp only [onSource, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨actual, member, rfl⟩ := supported
  exact PqxdhRegistrationJointServerSchedule.query_invariant setup codec checks seed index query state.1 actual owned member

/-- The representation invariant propagates through every actual modified source command. -/
theorem query_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed index state.1)
    (supported : result ∈ support ((source setup codec checks seed index query).run state)) :
    PqxdhRegistrationJointServerSchedule.Owned seed index result.2.1 := by
  rcases query with (coin | command) | read
  · exact carried_owned setup codec checks seed index _ state result owned supported
  · cases command
    case bundle address => exact bundle_owned setup codec seed index address state result owned supported
    all_goals exact carried_owned setup codec checks seed index _ state result owned supported
  · exact carried_owned setup codec checks seed index _ state result owned supported

/-- Full adaptive suppression is the exact interpreted handle client on all source coordinates; no seed or codec-law premise is introduced. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (owned : PqxdhRegistrationJointServerSchedule.Owned seed index state.1) :
    execute setup codec checks index (setup.joint.publicKeys seed) (simulateQ (handler setup codec) program)
      (encodeState setup state.1, state.2) =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (simulateQ (source setup codec checks seed index) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [execute, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, execute_bind,
        query_source setup codec checks seed index query state owned,
        bind_map_left, StateT.run_bind, map_bind]
      apply bind_congr_of_forall_mem_support
      intro result member
      exact ih result.1 result.2 (query_owned setup codec checks seed index query state result owned member)

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.carry_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.carry_execute

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.bundle_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.after_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.after_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.trace_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.trace_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.bundle_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.bundle_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.execute_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.execute_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.carried_query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.carried_query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.carried_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.carried_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.query_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.query_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule.program_source
