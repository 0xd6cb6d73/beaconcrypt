import BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication

/-!
Live Phase1 compatibility operations retain the actual native phase and all unrelated fields. Generating a one-time key happens before phase admission, including inactive rejection. Deletion is a live API operation; no snapshot or persistence interface is modeled. Primitive generation is an explicit optional callback.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLivePhase1State

variable {I D K : Type}
abbrev State := RawCtxBeaconLifecycle.State I D K
abbrev Phase := RawCtxBeaconLifecycle.Phase D K ratchet.concrete.ConcreteRatchetKernel

def replacePhase (state : State (I := I) (D := D) (K := K))
    (phase : Phase (D := D) (K := K)) : State (I := I) (D := D) (K := K) :=
  { state with beacon := { state.beacon with phase := phase } }

/-- A generated one-time pair replaces earlier explicit coins only while the owner remains fresh. -/
def newCoins (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    Option Unit × State (I := I) (D := D) (K := K) :=
  match generated with
  | none => (none, state)
  | some oneTime => match state.beacon.phase with
    | .fresh control prekey kem | .freshWithCoins control prekey _ kem =>
        (some (), replacePhase state (.freshWithCoins control prekey oneTime kem))
    | _ => (none, state)

abbrev GenerateSpec (D : Type) := Unit →ₒ Option D

/-- The native helper always calls the generator before testing its phase. -/
def newOneTime (state : State (I := I) (D := D) (K := K)) :
    OracleComp (GenerateSpec D) (Option Unit × State (I := I) (D := D) (K := K)) := do
  let generated ← (GenerateSpec D).query ()
  pure (newCoins generated state)

def deleteOneTime (state : State (I := I) (D := D) (K := K)) :
    State (I := I) (D := D) (K := K) :=
  match state.beacon.phase with
  | .freshWithCoins control prekey _ kem => replacePhase state (.fresh control prekey kem)
  | .initSent control _ _ _ => replacePhase state (.aborted ⟨control.expected_server_binding.identity_key_id⟩)
  | _ => state

def deleteKem (state : State (I := I) (D := D) (K := K)) :
    State (I := I) (D := D) (K := K) :=
  match state.beacon.phase with
  | .fresh control _ _ | .freshWithCoins control _ _ _ =>
      replacePhase state (.aborted ⟨control.expected_server_binding.identity_key_id⟩)
  | .initSent control _ _ _ => replacePhase state (.aborted ⟨control.expected_server_binding.identity_key_id⟩)
  | _ => state

def privateKeys (state : State (I := I) (D := D) (K := K)) : Option (D × K) :=
  match state.beacon.phase with
  | .fresh _ prekey kem | .freshWithCoins _ prekey _ kem | .initSent _ prekey _ kem => some (prekey, kem)
  | _ => none

/-- The source abort controls are the exact extracted ones used on deletion. -/
theorem abort_controls (fresh : pqxdh.BeaconFresh) (sent : pqxdh.BeaconInitSent) :
    pqxdh.beacon_abort_fresh fresh = ok ⟨fresh.expected_server_binding.identity_key_id⟩ ∧
    pqxdh.beacon_abort_init sent = ok ⟨sent.expected_server_binding.identity_key_id⟩ := ⟨rfl, rfl⟩

/-- Every generated reply, including failure, precedes the complete private continuation; no inactive draw is erased. -/
theorem newOneTime_complete {A Result : Type}
    (generate : QueryImpl (GenerateSpec D) (StateT A ProbComp))
    (state : State (I := I) (D := D) (K := K)) (auxiliary : A)
    (next : ((Option Unit × State (I := I) (D := D) (K := K)) × A) → ProbComp Result) :
    (simulateQ generate (newOneTime state)).run auxiliary >>= next =
      ((generate ()).run auxiliary >>= fun result => next (newCoins result.1 state, result.2)) := by
  simp only [newOneTime, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]

/-- Regenerating explicit one-time coins never changes the existing prekey or KEM pair. -/
theorem newCoins_privateKeys (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    privateKeys (newCoins generated state).2 = privateKeys state := by
  cases generated with
  | none => rfl
  | some oneTime =>
    cases phase : state.beacon.phase <;>
      simp [newCoins, phase, privateKeys, replacePhase]

/-- The helper preserves identity, pinned route and instrumentation on every optional generation and phase branch. -/
theorem newCoins_fields (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    (newCoins generated state).2.beacon.identity = state.beacon.identity ∧
    (newCoins generated state).2.beacon.identityKeyId = state.beacon.identityKeyId ∧
    (newCoins generated state).2.beacon.serverIdentity = state.beacon.serverIdentity ∧
    (newCoins generated state).2.rawAttempts = state.rawAttempts := by
  cases generated with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some oneTime =>
    cases phase : state.beacon.phase <;> simp [newCoins, phase, replacePhase]

/-- Deleting the KEM pair removes the retained prekey, one-time and KEM fields, while inactive phases already have none. -/
theorem deleteKem_privateKeys (state : State (I := I) (D := D) (K := K)) :
    privateKeys (deleteKem state) = none := by
  cases phase : state.beacon.phase <;> simp [deleteKem, phase, privateKeys, replacePhase]

/-- Exactly the original generator callback is budgeted on every helper call, including inactive rejection. -/
theorem newOneTime_bound (state : State (I := I) (D := D) (K := K)) :
    (newOneTime state).IsTotalQueryBound 1 := by
  simp only [newOneTime, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
  exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩

/-- The live coin update uses neither the private identity nor KEM representation. -/
theorem newCoins_map {I' K' : Type} (identity : I → I') (kem : K → K')
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    (Prod.map id (PqxdhBeaconPhase1Publication.mapState identity kem) (newCoins generated state)) =
      newCoins generated (PqxdhBeaconPhase1Publication.mapState identity kem state) := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk owner kid pin phase =>
      cases phase <;> cases generated <;> rfl

/-- Live one-time deletion preserves the existing interpreter-handle correspondence through every phase. -/
theorem deleteOneTime_map {I' K' : Type} (identity : I → I') (kem : K → K')
    (state : State (I := I) (D := D) (K := K)) :
    PqxdhBeaconPhase1Publication.mapState identity kem (deleteOneTime state) =
      deleteOneTime (PqxdhBeaconPhase1Publication.mapState identity kem state) := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk owner kid pin phase => cases phase <;> rfl

/-- Live KEM deletion does not inspect the unavailable secret before removing its retained handle. -/
theorem deleteKem_map {I' K' : Type} (identity : I → I') (kem : K → K')
    (state : State (I := I) (D := D) (K := K)) :
    PqxdhBeaconPhase1Publication.mapState identity kem (deleteKem state) =
      deleteKem (PqxdhBeaconPhase1Publication.mapState identity kem state) := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk owner kid pin phase => cases phase <;> rfl

end BeaconcryptCore.Computational.PqxdhLivePhase1State

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.abort_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.abort_controls
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.newOneTime_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.newOneTime_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.newCoins_privateKeys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.newCoins_privateKeys
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.newCoins_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.newCoins_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.deleteKem_privateKeys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.deleteKem_privateKeys
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.newOneTime_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.newOneTime_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.newCoins_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.newCoins_map
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.deleteOneTime_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.deleteOneTime_map
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1State.deleteKem_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1State.deleteKem_map
