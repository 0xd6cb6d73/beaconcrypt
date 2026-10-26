import BeaconcryptCore.Computational.PqxdhProtocolSelector
import BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter

/-!
The Phase1 adapter retains the source Fresh/FreshWithCoins distinction. The three signatures precede this private serialization continuation. Only a successful writer publishes InitSent; a failed writer keeps all prior role fields. Fresh one-time material is a local argument until publication. Identity and key-pair representations are parameters, so the same operation also runs on interpreter handles. The unpacked writer is an explicit optional callback, not an injective constructor or a primitive security assumption.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication
open PqxdhEd25519EufCma PqxdhJointPhase1SourceWriter

variable {I D K : Type}

abbrev State := RawCtxBeaconLifecycle.State I D K

/-- The native match chooses existing prekey/KEM fields and either local or explicitly retained one-time material. -/
structure Prepared (D K : Type) where
  control : pqxdh.BeaconFresh
  prekey : D
  oneTime : D
  kem : K

def prepare (state : State (I := I) (D := D) (K := K)) (generated : Option D) :
    Option (Prepared D K) :=
  match state.beacon.phase with
  | .fresh control prekey kem => generated.map (fun oneTime => ⟨control, prekey, oneTime, kem⟩)
  | .freshWithCoins control prekey oneTime kem => some ⟨control, prekey, oneTime, kem⟩
  | _ => none

/-- This is the control installed by the extracted builder, independently of tagged-buffer allocation. -/
def control (fresh : pqxdh.BeaconFresh) (identity : Std.Array Std.U8 32#usize) :
    pqxdh.BeaconInitSent := ⟨fresh.expected_server_binding, identity⟩

theorem core_control (fresh : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) :
    ∃ started, pqxdh.beacon_start fresh inputs coins = ok started ∧
      started.state = control fresh inputs.identity_public_key := by
  obtain ⟨a, ha, _⟩ := PqxdhRefinement.tag_sign_key_abs inputs.identity_public_key
  obtain ⟨pre, hpre, _⟩ := PqxdhRefinement.tag_x25519_key_abs pqxdh.KEY_ROLE_PREKEY inputs.prekey_public_key
  obtain ⟨one, hone, _⟩ := PqxdhRefinement.tag_x25519_key_abs pqxdh.KEY_ROLE_ONE_TIME coins.one_time_public_key
  obtain ⟨pq, hpq, _⟩ := PqxdhRefinement.tag_mlkem768_key_abs inputs.pq_public_key
  refine ⟨_, by rw [pqxdh.beacon_start, ha, hpre, hone, hpq]; rfl, rfl⟩

/-- Native publication retains the complete identity, route and instrumentation fields. -/
def publish (identity : Std.Array Std.U8 32#usize) (prepared : Prepared D K)
    (state : State (I := I) (D := D) (K := K)) : State (I := I) (D := D) (K := K) :=
  { state with beacon := { state.beacon with phase := .initSent (control prepared.control identity) prepared.prekey prepared.oneTime prepared.kem } }

abbrev WriterSpec : OracleSpec Phase1Candidate := fun _ => Option Pqxdh.Bytes

/-- All three exact signing buffers have already been produced when the source writer is called. -/
def afterSigning (identity : Std.Array Std.U8 32#usize) (bundle : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    OracleComp WriterSpec (Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) := do
  match prepare state generated with
  | none => pure (none, state)
  | some prepared =>
      let serialized ← WriterSpec.query bundle
      match serialized with
      | none => pure (none, state)
      | some bytes => pure (some bytes, publish identity prepared state)

/-- Every optional writer reply and its complete callback poststate reach the unchanged continuation. -/
theorem afterSigning_complete {A Result : Type}
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (identity : Std.Array Std.U8 32#usize) (bundle : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) (auxiliary : A)
    (next : (Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) × A → ProbComp Result) :
    (simulateQ writer (afterSigning identity bundle generated state)).run auxiliary >>= next =
      match prepare state generated with
      | none => next ((none, state), auxiliary)
      | some prepared => (writer bundle).run auxiliary >>= fun result =>
          match result.1 with
          | none => next ((none, state), result.2)
          | some bytes => next ((some bytes, publish identity prepared state), result.2) := by
  unfold afterSigning
  split
  · simp
  · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    apply bind_congr
    intro result
    cases result.1 <;> simp

theorem publish_fields (identity : Std.Array Std.U8 32#usize) (prepared : Prepared D K)
    (state : State (I := I) (D := D) (K := K)) :
    (publish identity prepared state).beacon.identity = state.beacon.identity ∧
    (publish identity prepared state).beacon.identityKeyId = state.beacon.identityKeyId ∧
    (publish identity prepared state).beacon.serverIdentity = state.beacon.serverIdentity ∧
    (publish identity prepared state).rawAttempts = state.rawAttempts ∧
    (publish identity prepared state).beacon.phase =
      .initSent (control prepared.control identity) prepared.prekey prepared.oneTime prepared.kem := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One original serialization attempt is charged even when it returns failure. -/
theorem afterSigning_bound (identity : Std.Array Std.U8 32#usize) (bundle : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    (afterSigning identity bundle generated state).IsQueryBoundP (fun _ => True) 1 := by
  unfold afterSigning
  split
  · simp
  · rw [isQueryBoundP_query_bind_iff]
    exact ⟨by simp, fun reply => by cases reply <;> simp⟩

/-- Interpreter handles erase only the identity/KEM representation; private DH pairs and every native control/kernel remain unchanged. -/
def mapPhase {K' : Type} (kem : K → K') :
    RawCtxBeaconLifecycle.Phase D K ratchet.concrete.ConcreteRatchetKernel →
      RawCtxBeaconLifecycle.Phase D K' ratchet.concrete.ConcreteRatchetKernel
  | .fresh control prekey key => .fresh control prekey (kem key)
  | .freshWithCoins control prekey oneTime key => .freshWithCoins control prekey oneTime (kem key)
  | .initSent control prekey oneTime key => .initSent control prekey oneTime (kem key)
  | .established control ad kernel => .established control ad kernel
  | .aborted control => .aborted control

def mapState {I' K' : Type} (identity : I → I') (kem : K → K')
    (state : State (I := I) (D := D) (K := K)) : State (I := I') (D := D) (K := K') :=
  ⟨⟨identity state.beacon.identity, state.beacon.identityKeyId, state.beacon.serverIdentity,
    mapPhase kem state.beacon.phase⟩, state.rawAttempts⟩

/-- Complete Phase1 publication commutes with the actual handle erasure, including failure, full writer arguments and all optional replies. -/
theorem afterSigning_map {I' K' : Type} (identityMap : I → I') (kemMap : K → K')
    (identity : Std.Array Std.U8 32#usize) (bundle : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    (fun result => (result.1, mapState identityMap kemMap result.2)) <$>
      afterSigning identity bundle generated state =
      afterSigning identity bundle generated (mapState identityMap kemMap state) := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk owner kid pin phase =>
      cases phase <;> cases generated <;>
        simp [afterSigning, prepare, mapState, mapPhase, publish, map_bind]
      all_goals apply bind_congr; intro reply; cases reply <;> rfl

/-- The entire evaluated writer continuation preserves the same auxiliary/primitive poststate under handle erasure. -/
theorem afterSigning_map_run {I' K' A : Type} (identityMap : I → I') (kemMap : K → K')
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (identity : Std.Array Std.U8 32#usize) (bundle : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) (auxiliary : A) :
    (fun result => ((result.1.1, mapState identityMap kemMap result.1.2), result.2)) <$>
      (simulateQ writer (afterSigning identity bundle generated state)).run auxiliary =
      (simulateQ writer (afterSigning identity bundle generated (mapState identityMap kemMap state))).run auxiliary := by
  rw [← afterSigning_map identityMap kemMap identity bundle generated state]
  simp only [simulateQ_map, StateT.run_map]

end BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.core_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.core_control

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.afterSigning_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.afterSigning_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.publish_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.publish_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.afterSigning_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.afterSigning_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.afterSigning_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.afterSigning_map

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.afterSigning_map_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication.afterSigning_map_run
