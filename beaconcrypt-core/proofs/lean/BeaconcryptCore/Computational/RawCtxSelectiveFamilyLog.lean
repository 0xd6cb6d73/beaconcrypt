import BeaconcryptCore.Computational.RawCtxPendingParentPrefix

/-!
The selective source execution records the chronological input of every actual private receive/send callback, including repeated cache hits. Logging changes only a private list: the same primitive work, full table, selected cursor, original family and live history remain present. The log is recorded after each executed callback, so a saved unexecuted predecessor request is not silently included in its prior-input list.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxPendingSelectiveFamily

abbrev LoggedState (Auxiliary : Type) := State Auxiliary × List JointKdfAddress

def inputs {serverCount beaconCount : Nat} (query : (Spec serverCount beaconCount).Domain)
    (past : List JointKdfAddress) : List JointKdfAddress :=
  match RawCtxSelectedFamilyContext.queryAddress query with
  | none => past
  | some address => past ++ [address]

noncomputable def handler {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat) :
    QueryImpl (Spec serverCount beaconCount) (StateT (LoggedState Auxiliary) ProbComp) :=
  fun query state => do
    let result ← (RawCtxPendingSelectiveFamily.handler source writer stage query).run state.1
    pure (result.1, (result.2, inputs query state.2))

/-- Erasing only the chronological input log recovers the same complete actual selective execution. -/
theorem program_projection {Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (Spec serverCount beaconCount) Result) (state : State Auxiliary) (past : List JointKdfAddress) :
    (fun result => (result.1, result.2.1)) <$>
      ((simulateQ (handler source writer stage) client).run (state, past)) =
      (simulateQ (RawCtxPendingSelectiveFamily.handler source writer stage) client).run state := by
  induction client using OracleComp.inductionOn generalizing state past with
  | pure result => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [handler, StateT.run, map_bind, bind_assoc, pure_bind]
    exact bind_congr fun result => ih result.1 result.2 (inputs query past)

def Covered {Auxiliary : Type} (state : LoggedState Auxiliary) : Prop :=
  ∀ address output, state.1.2.1 address = some output → address ∈ state.2

/-- The actual empty private cache needs no assumed enumeration; any retained earlier input list covers it. -/
theorem empty_covered {Auxiliary : Type} (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (cursor : Cursor) (past : List JointKdfAddress) :
    Covered ((primitive, (∅, cursor)), past) := by
  intro address output found
  cases found

/-- Every actual cache binding remains represented by the chronological log after the same original callback, including hits, failures and non-KDF shared effects. -/
theorem step_covered {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (Spec serverCount beaconCount).Domain) (state : LoggedState Auxiliary) (covered : Covered state)
    (result : (Spec serverCount beaconCount).Range query × LoggedState Auxiliary)
    (supported : result ∈ support (((handler source writer stage) query).run state)) : Covered result.2 := by
  simp only [handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨reply, actual, rfl⟩ := supported
  intro address output cached
  cases found : RawCtxSelectedFamilyContext.queryAddress query with
  | none =>
    have same := RawCtxPendingNonKdfStore.callback_store source writer stage query found state.1 reply actual
    have previous : state.1.2.1 address = some output := by simpa only [same] using cached
    simpa only [inputs, found] using covered address output previous
  | some request =>
    obtain ⟨response, exactState⟩ := RawCtxPendingParentCallbacks.kdf_state source writer stage query request found state.1 reply actual
    rw [exactState] at cached
    by_cases same : address = request
    · subst address
      simp [inputs, found]
    · have previous : state.1.2.1 address = some output := by
        simpa only [QueryCache.cacheQuery_of_ne (spec := JointKdfRO) state.1.2.1 response same] using cached
      simp only [inputs, found, List.mem_append]
      exact Or.inl (covered address output previous)

/-- The complete original adaptive execution derives every private-cache input from its actual chronological log. -/
theorem program_covered {Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (Spec serverCount beaconCount) Result) (state : LoggedState Auxiliary) (covered : Covered state)
    (result : Result × LoggedState Auxiliary)
    (supported : result ∈ support ((simulateQ (handler source writer stage) client).run state)) : Covered result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact covered
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    exact ih reply.1 reply.2 (step_covered source writer stage query state covered reply head) result tail

/-- Every actual completed or pending source prefix derives the same cache-input provenance at its full reached state. -/
theorem scan_covered {Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec serverCount beaconCount).Domain → LoggedState Auxiliary → Bool)
    (client : OracleComp (Spec serverCount beaconCount) Result) (state : LoggedState Auxiliary) (covered : Covered state)
    (result : RawCtxPendingMixedPrefix.Prefix (Spec serverCount beaconCount) Result (LoggedState Auxiliary))
    (supported : result ∈ support (RawCtxStatefulPendingPrefix.scan selected (handler source writer stage) client state)) :
    Covered result.2 := by
  exact RawCtxStatefulPrefixInvariant.scan_valid selected (handler source writer stage) Covered
    (fun query before valid _ reply head => step_covered source writer stage query before valid reply head)
    client state covered result supported

noncomputable def family {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) (past : List JointKdfAddress) :=
  Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
    ((simulateQ (handler source writer stage) (program sender route decode client state)).run ((primitive, store), past))

/-- The original complete native family game is recovered by erasing only its private chronological log after execution. -/
theorem source_projection {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) (past : List JointKdfAddress) :
    (fun result => (result.1, result.2.1)) <$> family source writer stage sender route decode client state primitive store past =
      RawCtxSelectiveChainGame.family source writer stage serverCount beaconCount sender route decode client state primitive store := by
  rw [RawCtxPendingSelectiveFamily.source_program,
    ← program_projection source writer stage (program sender route decode client state) (primitive, store) past]
  simp only [family, Functor.map_map, Prod.map_def, id_eq]

/-- Erasing only the input log preserves the exact original state-dependent pending scan, including its complete dependent continuation and actual reached state. -/
theorem scan_projection {Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec serverCount beaconCount).Domain → State Auxiliary → Bool)
    (client : OracleComp (Spec serverCount beaconCount) Result) (state : State Auxiliary) (past : List JointKdfAddress) :
    (fun result => (result.1, result.2.1)) <$>
      RawCtxStatefulPendingPrefix.scan (fun query logged => selected query logged.1)
        (handler source writer stage) client (state, past) =
      RawCtxStatefulPendingPrefix.scan selected (RawCtxPendingSelectiveFamily.handler source writer stage) client state := by
  induction client using OracleComp.inductionOn generalizing state past with
  | pure value => rfl
  | query_bind query next ih =>
    cases chosen : selected query state with
    | true =>
      rw [RawCtxStatefulPendingPrefix.scan_cut (fun query logged => selected query logged.1)
        (handler source writer stage) query next (state, past) chosen,
        RawCtxStatefulPendingPrefix.scan_cut selected (RawCtxPendingSelectiveFamily.handler source writer stage)
          query next state chosen]
      rfl
    | false =>
      rw [RawCtxStatefulPendingPrefix.scan_other (fun query logged => selected query logged.1)
        (handler source writer stage) query next (state, past) chosen,
        RawCtxStatefulPendingPrefix.scan_other selected (RawCtxPendingSelectiveFamily.handler source writer stage)
          query next state chosen]
      simp only [handler, StateT.run, map_bind, bind_assoc, pure_bind]
      exact bind_congr fun result => ih result.1 result.2 (inputs query past)

end BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.program_projection

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.empty_covered' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.empty_covered

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.step_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.step_covered

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.program_covered

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.scan_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.scan_covered

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.source_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.source_projection

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.scan_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.scan_projection
