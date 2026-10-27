import BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity

/-!
The actual fixed source record/public/reveal backend carries the complete joint identity state beside its original auxiliary value, retaining the same CTX cache. Full native roles, registration controls, consumed IDs and reveal history survive the state reassociation. No arbitrary source preservation premise is introduced.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2OldSource
open PqxdhJointKdfGame PqxdhPhase2SharedIdentity
variable {A J : Type}

private theorem state_pure {State Result : Type} (value : Result) (state : State) :
    (pure value : StateT State ProbComp Result) state = pure (value, state) := rfl

/-- Every actual backend callback preserves the additional identity state and the same original cache effects. -/
theorem backend_pack (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxServerServices.BackendSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState A) (identities : J) :
    (RawCtxProtocolBackend.backend (Auxiliary := A × J) source writer query).run (pack (state, identities)) =
      (fun result => (result.1, pack (result.2, identities))) <$>
        (RawCtxProtocolBackend.backend (Auxiliary := A) source writer query).run state := by
  rcases query with coin | (request | view)
  case inr.inl =>
    rcases request with kdf | (sealing | (opening | (bytes | frame)))
    all_goals simp [RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl,
      RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, QueryImpl.compose,
      OracleSpec.query, RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl,
      RawCtxSourceHkdf.kdfImpl, pack, StateT.run, bind_pure_comp, Functor.map_map, state_pure]
  all_goals simp [RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl,
    pack, StateT.run, bind_pure_comp, Functor.map_map]

/-- An arbitrary original backend program retains its complete result and every cache effect when the identity state is carried alongside it. -/
theorem backend_schedule {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (client : OracleComp RawCtxServerServices.BackendSpec Result)
    (state : RawCtxSharedPrimitive.SharedState A) (identities : J) :
    (simulateQ (RawCtxProtocolBackend.backend (Auxiliary := A × J) source writer) client).run (pack (state, identities)) =
      (fun result => (result.1, pack (result.2, identities))) <$>
        (simulateQ (RawCtxProtocolBackend.backend (Auxiliary := A) source writer) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq _ _ (fun state => pack (state, identities))
    (fun query before => (backend_pack source writer query before identities).symm) client state).symm

/-- The actual mixed role/public/reveal schedule retains every owner, timestamp and optional reply while carrying the same identity state and shared cache. -/
theorem reveals_schedule {M P I D K Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (roles : RawCtxProtocolReveals.State M P I D K S B)
    (primitive : RawCtxSharedPrimitive.SharedState A) (identities : J) :
    (simulateQ (RawCtxProtocolReveals.sourceImpl (Auxiliary := A × J)
      source writer S B senderId route decode) client).run (roles, pack (primitive, identities)) =
      (fun result => (result.1, (result.2.1, pack (result.2.2, identities)))) <$>
        (simulateQ (RawCtxProtocolReveals.sourceImpl (Auxiliary := A)
          source writer S B senderId route decode) client).run (roles, primitive) := by
  have equation := backend_schedule source writer
    ((simulateQ (RawCtxProtocolReveals.protocolImpl S B senderId route decode) client).run roles)
    primitive identities
  rw [RawCtxProtocolReveals.schedule_interpretation,
    RawCtxProtocolReveals.schedule_interpretation] at equation
  have projected := congrArg (fun work =>
    (fun result : (Result × RawCtxProtocolReveals.State M P I D K S B) ×
      RawCtxSharedPrimitive.SharedState (A × J) => (result.1.1, (result.1.2, result.2))) <$> work) equation
  simp only [Functor.map_map, Prod.mk.eta] at projected
  change id <$> _ = _ at projected
  simpa only [id_map] using projected

variable {M P I D K : Type} {S B : Nat}

/-- Move only the original auxiliary/identity association; every role, control and prior disclosure remains verbatim. -/
def packState (state : PqxdhRegistrationProtocolState.State M P I D K A S B) (identities : J) :
    PqxdhRegistrationProtocolState.State M P I D K (A × J) S B :=
  ⟨state.roles, state.controls, state.consumed, pack (state.primitive, identities)⟩

def unpackState (state : PqxdhRegistrationProtocolState.State M P I D K (A × J) S B) :
    PqxdhRegistrationProtocolState.State M P I D K A S B × J :=
  (⟨state.roles, state.controls, state.consumed, (state.primitive.1.1, state.primitive.2)⟩,
    state.primitive.1.2)

/-- Both the full native registration state and complete identity state are recovered literally. -/
theorem unpackState_packState (state : PqxdhRegistrationProtocolState.State M P I D K A S B)
    (identities : J) : unpackState (packState state identities) = (state, identities) := rfl

/-- The inverse loses no field of an arbitrary complete packed state. -/
theorem packState_unpackState (state : PqxdhRegistrationProtocolState.State M P I D K (A × J) S B) :
    packState (unpackState state).1 (unpackState state).2 = state := rfl

/-- Actual old-source execution commutes with complete registration/identity reassociation, retaining every owner, control, consumed list and primitive effect. -/
theorem registration_schedule {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) (identities : J) :
    (simulateQ (PqxdhRegistrationProtocolState.sourceImpl (A := A × J)
      source writer senderId route decode) client).run (packState state identities) =
      (fun result => (result.1, packState result.2 identities)) <$>
        (simulateQ (PqxdhRegistrationProtocolState.sourceImpl (A := A)
          source writer senderId route decode) client).run state := by
  rw [PqxdhRegistrationProtocolState.source_schedule, PqxdhRegistrationProtocolState.source_schedule]
  simp only [PqxdhRegistrationProtocolState.project, packState]
  rw [reveals_schedule]
  simp only [Functor.map_map, PqxdhRegistrationProtocolState.restore]

/-- Every selected underlying query bound is unchanged on the actual full-state source program. -/
theorem registration_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) (identities : J)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (PqxdhRegistrationProtocolState.sourceImpl (A := A × J)
      source writer senderId route decode) client).run (packState state identities)).IsQueryBoundP predicate budget ↔
      ((simulateQ (PqxdhRegistrationProtocolState.sourceImpl (A := A)
        source writer senderId route decode) client).run state).IsQueryBoundP predicate budget := by
  rw [registration_schedule, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.PqxdhPhase2OldSource

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2OldSource.backend_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2OldSource.backend_pack

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2OldSource.backend_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2OldSource.backend_schedule

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2OldSource.reveals_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2OldSource.reveals_schedule

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2OldSource.unpackState_packState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2OldSource.unpackState_packState

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2OldSource.packState_unpackState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2OldSource.packState_unpackState

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2OldSource.registration_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2OldSource.registration_schedule

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2OldSource.registration_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2OldSource.registration_bound
