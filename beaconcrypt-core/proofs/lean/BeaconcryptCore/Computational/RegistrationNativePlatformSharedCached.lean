-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication
/-! The actual complete stateful Beacon and Server publication preserve cached ML receipts after projecting to their shared signing state. The same primitive signer is retained, Ed replies are the supplied pure source values, and the trusted source writer runs in arbitrary external platform state with all failure/divergence poststates. An exact auxiliary World projection supplies the invariant without a whole-publication Cached premise or an assumed signer law. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSharedCached
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {I Auxiliary Value Encoded : Type} {extra : OracleSpec I}
variable (primitive : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
abbrev SharedM (Auxiliary : Type) := StateT RegistrationSigningShared.State (StateT Auxiliary ProbComp)
abbrev WorldM (n : Nat) (Auxiliary : Type) := StateT (RegistrationWorldSigning.State n) (StateT Auxiliary ProbComp)

def signing : QueryImpl RegistrationSigningShared.Spec (SharedM Auxiliary) :=
  fun query => RegistrationNativePlatformInterpret.state coins (RegistrationSigningShared.implementation primitive query)

noncomputable def worldSigning : QueryImpl RegistrationSigningShared.Spec (WorldM n Auxiliary) :=
  fun query => RegistrationNativePlatformInterpret.state coins (RegistrationWorldSigning.outgoing primitive query)

noncomputable def worldHandler (side : QueryImpl extra (StateT Auxiliary ProbComp)) :
    QueryImpl (RegistrationNativePlatformJournalErasure.Spec extra) (WorldM n Auxiliary)
  | .inl query => worldSigning primitive query
  | .inr query => StateT.lift (side query)

def sharedHandler (side : QueryImpl extra (StateT Auxiliary ProbComp)) :
    QueryImpl (RegistrationNativePlatformJournalErasure.Spec extra) (SharedM Auxiliary)
  | .inl query => signing primitive query
  | .inr query => StateT.lift (side query)

private theorem query_project (side : QueryImpl extra (StateT Auxiliary ProbComp))
    (query : (RegistrationNativePlatformJournalErasure.Spec extra).Domain) (before : RegistrationWorldSigning.State n) :
    Prod.map id RegistrationWorldSigning.project <$> ((worldHandler primitive side) query).run before =
      ((sharedHandler primitive side) query).run (RegistrationWorldSigning.project before) := by
  cases query with
  | inl query =>
      change (Prod.map id RegistrationWorldSigning.project <$>
        simulateQ coins ((RegistrationWorldSigning.outgoing primitive query).run before)) =
        simulateQ coins ((RegistrationSigningShared.implementation primitive query).run (RegistrationWorldSigning.project before))
      rw [← simulateQ_map, RegistrationWorldSigning.outgoing_project]
  | inr query =>
      simp only [worldHandler, sharedHandler, StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map, id_eq]

theorem project (side : QueryImpl extra (StateT Auxiliary ProbComp))
    (work : OracleComp (RegistrationNativePlatformJournalErasure.Spec extra) Value) (before : RegistrationWorldSigning.State n) :
    Prod.map id RegistrationWorldSigning.project <$> (simulateQ (worldHandler primitive side) work).run before =
      (simulateQ (sharedHandler primitive side) work).run (RegistrationWorldSigning.project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ RegistrationWorldSigning.project (query_project primitive side) work before

private theorem lift_pure {S A : Type} (value : A) :
    (StateT.lift (pure value : StateT Auxiliary ProbComp A) : StateT S (StateT Auxiliary ProbComp) A) = pure value := by
  funext before
  change (StateT.lift (pure value : StateT Auxiliary ProbComp A) : StateT S (StateT Auxiliary ProbComp) A).run before =
    (pure value : StateT S (StateT Auxiliary ProbComp) A).run before
  simp only [StateT.run_lift, StateT.run_pure, pure_bind]

private theorem lift_frame {A : Type} (work : StateT Auxiliary ProbComp A)
    (before : RegistrationWorldSigning.State n) (previous : Auxiliary)
    (result : (A × RegistrationWorldSigning.State n) × Auxiliary)
    (supported : result ∈ support (((StateT.lift work : WorldM n Auxiliary A).run before).run previous)) :
    RegistrationNativePlatformJournalSafe.Frame before result.1.2 := by
  rw [StateT.run_lift, StateT.run_bind] at supported
  simp only [StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  exact ⟨rfl, le_refl _⟩

private def embed (state : RegistrationSigningShared.State) : RegistrationWorldSigning.State 0 :=
  ({ PqxdhRecordLiftWorld.initial with primitive := ((PqxdhRecordLiftWorld.initial (n := 0)).primitive.1, state.2) }, state.1)

private theorem embed_project (state : RegistrationSigningShared.State) : RegistrationWorldSigning.project (embed state) = state := by
  cases state
  rfl

private def side (ed : registration.Ed25519SigningRequest → RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT Auxiliary ProbComp (RustM (core.option.Option Encoded))) :
    QueryImpl (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded) (StateT Auxiliary ProbComp)
  | .inl request => pure (ed request)
  | .inr view => encode view

private def free : QueryImpl RegistrationBeaconInitExecutor.Spec
    (OracleComp (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)))
  | .inl query => (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)).query (.inl query)
  | .inr request => (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)).query (.inr (.inl request))

private def freeEncode (view : registration.SignedInitView) :
    OracleComp (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)) (RustM (core.option.Option Encoded)) :=
  (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)).query (.inr (.inr view))

def outgoing (ed : registration.Ed25519SigningRequest → RegistrationSigningShared.SignReply) : QueryImpl RegistrationBeaconInitExecutor.Spec (SharedM Auxiliary)
  | .inl query => signing primitive query
  | .inr request => pure (ed request)

private theorem beacon_project
    (ed : registration.Ed25519SigningRequest → RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT Auxiliary ProbComp (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) (before : RegistrationWorldSigning.State n) :
    Prod.map id RegistrationWorldSigning.project <$>
      (RegistrationNativePlatformBeaconPublication.begin (RegistrationNativePlatformJournalWorld.beaconOutgoing coins primitive (fun request => pure (ed request)))
        (fun view => StateT.lift (encode view)) control inputs scalar pin mldsa).run before =
      (RegistrationNativePlatformBeaconPublication.begin (outgoing primitive ed) (fun view => StateT.lift (encode view)) control inputs scalar pin mldsa).run
        (RegistrationWorldSigning.project before) := by
  have projected := project primitive (side ed encode)
    (RegistrationNativePlatformBeaconPublication.begin free freeEncode control inputs scalar pin mldsa) before
  rw [RegistrationNativePlatformBeaconPublication.begin_interpret,
    RegistrationNativePlatformBeaconPublication.begin_interpret] at projected
  have leftCallbacks : (fun query => simulateQ (worldHandler (n := n) primitive (side ed encode)) (free (Encoded := Encoded) query)) =
      RegistrationNativePlatformJournalWorld.beaconOutgoing (n := n) coins primitive (fun request => pure (ed request)) := by
    funext query
    cases query <;> simp only [free, simulateQ_spec_query, worldHandler, worldSigning, side, lift_pure, RegistrationNativePlatformJournalWorld.beaconOutgoing]
  have rightCallbacks : (fun query => simulateQ (sharedHandler primitive (side ed encode)) (free (Encoded := Encoded) query)) = outgoing primitive ed := by
    funext query
    cases query <;> simp only [free, simulateQ_spec_query, sharedHandler, side, lift_pure, outgoing]
  rw [leftCallbacks, rightCallbacks] at projected
  simpa only [freeEncode, simulateQ_spec_query, worldHandler, sharedHandler, side] using projected

theorem beacon
    (ed : registration.Ed25519SigningRequest → RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT Auxiliary ProbComp (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (before : RegistrationSigningShared.State) (cached : RegistrationSigningShared.Cached before) (previous : Auxiliary)
    (result : (RustM (RegistrationBeaconInitExecutor.Result Encoded) × RegistrationSigningShared.State) × Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformBeaconPublication.begin (outgoing primitive ed)
      (fun view => StateT.lift (encode view)) control inputs scalar pin mldsa).run before).run previous)) : RegistrationSigningShared.Cached result.1.2 := by
  have law := congrArg (fun work => (work : StateT Auxiliary ProbComp _).run previous)
    (beacon_project primitive ed encode control inputs scalar pin mldsa (embed before))
  rw [embed_project, StateT.run_map] at law
  rw [← law, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  have started : RegistrationSigningShared.Cached (RegistrationWorldSigning.project (embed before)) := by simpa only [embed_project] using cached
  have worldCached := RegistrationNativePlatformJournalCachedPublication.beacon primitive
    (fun request => pure (ed request)) (fun view => StateT.lift (encode view))
    (fun request before previous result supported => lift_frame (pure (ed request)) before previous result (by simpa only [lift_pure] using supported))
    (fun view => lift_frame (encode view)) control inputs scalar pin mldsa (embed before) started previous inner reached
  cases same
  exact worldCached

theorem server
    (encode : registration.SignedResponseView → StateT Auxiliary ProbComp (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) (before : RegistrationSigningShared.State)
    (cached : RegistrationSigningShared.Cached before) (previous : Auxiliary)
    (result : (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State) × Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformServerPublication.program (signing primitive)
      (fun view => StateT.lift (encode view)) pending).run before).run previous)) : RegistrationSigningShared.Cached result.1.2 := by
  let spec := RegistrationNativePlatformJournalErasure.Spec (registration.SignedResponseView →ₒ RustM (core.option.Option Encoded))
  have projected := project primitive encode
    (RegistrationNativePlatformServerPublication.program (fun query => spec.query (.inl query)) (fun view => spec.query (.inr view)) pending) (embed before)
  rw [RegistrationNativePlatformServerPublication.program_interpret,
    RegistrationNativePlatformServerPublication.program_interpret] at projected
  simp only [spec, simulateQ_spec_query, worldHandler, sharedHandler] at projected
  have law := congrArg (fun work => (work : StateT Auxiliary ProbComp _).run previous) projected
  rw [embed_project, StateT.run_map] at law
  rw [← law, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  have started : RegistrationSigningShared.Cached (RegistrationWorldSigning.project (embed before)) := by simpa only [embed_project] using cached
  have worldCached := RegistrationNativePlatformJournalCachedPublication.server primitive
    (fun view => StateT.lift (encode view)) (fun view => lift_frame (encode view)) pending (embed before) started previous inner reached
  cases same
  exact worldCached
end BeaconcryptCore.Computational.RegistrationNativePlatformSharedCached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSharedCached.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSharedCached.project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSharedCached.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSharedCached.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSharedCached.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSharedCached.server
