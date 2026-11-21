import BeaconcryptCore.Computational.PqxdhLiveJointSigning
import BeaconcryptCore.Computational.PqxdhServerRegistrationPublication

/-!
Actual serialization, identity validation, allocation and logical erasure callbacks do not access the CTX hash service. Their private local state is lifted over the same retained commitment cache. Complete program equations and random-query ledgers preserve all callback outcomes and costs. Native codec, validation, allocation and compiler contracts remain functional boundaries; no cache-preservation or cryptographic security conclusion is assumed of an arbitrary shared-state environment.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSourceAuxiliary

variable {ι : Type} {spec : OracleSpec ι} {A : Type}

/-- Lift only the actual non-hash local callback state; every existing shared commitment entry remains untouched. -/
def lift (callback : QueryImpl spec (StateT A ProbComp)) :
    QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) := fun query state =>
  (fun result => (result.1, (result.2, state.2))) <$> (callback query).run state.1

/-- These callbacks match the native non-hash boundary. Logical erasure is fixed below, not a caller-supplied observer of erased bytes. -/
structure Callbacks (A : Type) where
  phase1Write : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec (StateT A ProbComp)
  checkIdentity : PqxdhServerRegistrationPublication.Identity → Bool
  reservePeer : StateT A ProbComp Bool
  reservePlaintext : Nat → StateT A ProbComp Bool
  responseWrite : PqxdhServerRegistrationPublication.ResponseFields → StateT A ProbComp (Option Pqxdh.Bytes)

/-- Source request dispatch preserves the original parser/allocation/writer replies. Erasing a temporary buffer has no logical public or auxiliary observation. -/
def localServer (callbacks : Callbacks A) :
    QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT A ProbComp) := fun query =>
  match query with
  | .checkIdentity identity => pure (callbacks.checkIdentity identity)
  | .reservePeer => callbacks.reservePeer
  | .reservePlaintext size => callbacks.reservePlaintext size
  | .erase _ => pure ()
  | .write fields => callbacks.responseWrite fields

def phase1 (callbacks : Callbacks A) := lift callbacks.phase1Write

def server (callbacks : Callbacks A) := lift (localServer callbacks)

/-- One concrete local request retains the entire prior shared cache and the actual updated auxiliary state. -/
theorem lift_step (callback : QueryImpl spec (StateT A ProbComp)) (query : spec.Domain)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (lift callback query).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (callback query).run state.1 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive local program preserves the complete cache and evaluated continuation, including failed callbacks. -/
theorem lift_complete {Result : Type} (callback : QueryImpl spec (StateT A ProbComp))
    (work : OracleComp spec Result) (state : RawCtxSharedPrimitive.SharedState A) :
    (simulateQ (lift callback) work).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (simulateQ callback work).run state.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lift_step,
      bind_map_left, ih, map_bind]

/-- Lifting changes no uniform-query bill, including actual local callback randomness. -/
theorem lift_uniform {Result : Type} (callback : QueryImpl spec (StateT A ProbComp))
    (work : OracleComp spec Result) (state : RawCtxSharedPrimitive.SharedState A) (q : Nat) :
    ((simulateQ (lift callback) work).run state).IsTotalQueryBound q ↔
      ((simulateQ callback work).run state.1).IsTotalQueryBound q := by
  rw [lift_complete]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]

/-- Native Phase-1 serialization changes only its actual auxiliary state; every earlier CTX cache entry is retained. -/
theorem phase1_step (callbacks : Callbacks A) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (phase1 callbacks candidate).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (callbacks.phase1Write candidate).run state.1 := rfl

/-- Public-key validation returns the native functional parser's actual Boolean and changes no logical state. -/
theorem server_check (callbacks : Callbacks A) (identity : PqxdhServerRegistrationPublication.Identity)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (server callbacks (.checkIdentity identity)).run state = pure (callbacks.checkIdentity identity, state) := by
  rfl

/-- Peer reservation retains the native success/failure and allocation state, with no hash query or cache mutation. -/
theorem server_reservePeer (callbacks : Callbacks A) (state : RawCtxSharedPrimitive.SharedState A) :
    (server callbacks .reservePeer).run state =
      (fun result => (result.1, (result.2, state.2))) <$> callbacks.reservePeer.run state.1 := rfl

/-- Plaintext reservation receives the actual requested length and retains its whole optional allocation outcome. -/
theorem server_reservePlaintext (callbacks : Callbacks A) (size : Nat)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (server callbacks (.reservePlaintext size)).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (callbacks.reservePlaintext size).run state.1 := rfl

/-- Logical temporary erasure exposes no erased bytes through a callback and does not modify the shared oracle. This is not a physical-erasure theorem. -/
theorem server_erase (callbacks : Callbacks A) (bytes : Pqxdh.Bytes)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (server callbacks (.erase bytes)).run state = pure ((), state) := by
  rfl

/-- The packed response writer receives every exact source field and retains its actual optional result and auxiliary state. -/
theorem server_write (callbacks : Callbacks A) (fields : PqxdhServerRegistrationPublication.ResponseFields)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (server callbacks (.write fields)).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (callbacks.responseWrite fields).run state.1 := rfl

/-- An arbitrary complete native auxiliary continuation preserves the shared cache by construction, not by a premise about an opaque shared-state callback. -/
theorem server_complete {Result : Type} (callbacks : Callbacks A)
    (work : OracleComp PqxdhServerRegistrationPublication.AuxSpec Result)
    (state : RawCtxSharedPrimitive.SharedState A) :
    (simulateQ (server callbacks) work).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (simulateQ (localServer callbacks) work).run state.1 :=
  lift_complete (localServer callbacks) work state

/-- A Phase-1 writer keeps the full callback's actual random-query cap; no auxiliary work is omitted. -/
theorem phase1_uniform (callbacks : Callbacks A) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (state : RawCtxSharedPrimitive.SharedState A) (qWriter : Nat)
    (bounded : ((callbacks.phase1Write candidate).run state.1).IsTotalQueryBound qWriter) :
    ((phase1 callbacks candidate).run state).IsTotalQueryBound qWriter := by
  rw [phase1_step]
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bounded

set_option backward.isDefEq.respectTransparency false in
/-- The concrete dispatch charges the complete actual allocation and writer bills. Identity parsing and logical erasure make no uniform queries. -/
theorem server_uniform (callbacks : Callbacks A) (query : PqxdhServerRegistrationPublication.AuxSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState A) (qAux : Nat)
    (peerBound : ∀ auxiliary, (callbacks.reservePeer.run auxiliary).IsTotalQueryBound qAux)
    (plaintextBound : ∀ size auxiliary, ((callbacks.reservePlaintext size).run auxiliary).IsTotalQueryBound qAux)
    (writerBound : ∀ fields auxiliary, ((callbacks.responseWrite fields).run auxiliary).IsTotalQueryBound qAux) :
    ((server callbacks query).run state).IsTotalQueryBound qAux := by
  cases query with
  | checkIdentity identity =>
      change IsTotalQueryBound (pure (callbacks.checkIdentity identity, state)) qAux
      trivial
  | reservePeer =>
      rw [server_reservePeer]
      simpa only [IsTotalQueryBound, isQueryBound_map_iff] using peerBound state.1
  | reservePlaintext size =>
      rw [server_reservePlaintext]
      simpa only [IsTotalQueryBound, isQueryBound_map_iff] using plaintextBound size state.1
  | erase bytes =>
      change IsTotalQueryBound (pure ((), state)) qAux
      trivial
  | write fields =>
      rw [server_write]
      simpa only [IsTotalQueryBound, isQueryBound_map_iff] using writerBound fields state.1

end BeaconcryptCore.Computational.PqxdhSourceAuxiliary

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.lift_step' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.lift_step

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.lift_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.lift_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.lift_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.lift_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.phase1_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.phase1_step

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_check

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_reservePeer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_reservePeer

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_reservePlaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_reservePlaintext

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_write

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.phase1_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.phase1_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceAuxiliary.server_uniform
