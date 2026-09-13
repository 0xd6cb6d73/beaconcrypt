import BeaconcryptCore.Computational.PqxdhPhase2SourceAux
import BeaconcryptCore.Computational.PqxdhPhase2LiveFinish

/-!
The existing identity interpreter and source auxiliary/cache pair are reassociated into the live scheduler's one shared primitive state. Both maps retain every field. This supplies a concrete common-state layout, without adding a new storage or reveal capability.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity
variable {A Identity : Type}

abbrev Split (A Identity : Type) := RawCtxSharedPrimitive.SharedState A × Identity
abbrev Packed (A Identity : Type) := RawCtxSharedPrimitive.SharedState (A × Identity)

def pack (state : Split A Identity) : Packed A Identity := ((state.1.1, state.2), state.1.2)
def unpack (state : Packed A Identity) : Split A Identity := ((state.1.1, state.2), state.1.2)

/-- The live cache/identity layout retains every original private value. -/
theorem unpack_pack (state : Split A Identity) : unpack (pack state) = state := rfl

def packed {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    (handler : QueryImpl spec (StateT (Split A Identity) m)) :
    QueryImpl spec (StateT (Packed A Identity) m) :=
  fun query state => (fun result => (result.1, pack result.2)) <$> (handler query).run (unpack state)

/-- Reassociation preserves the complete original adaptive result, identity history, source auxiliary value and common cache. -/
theorem packed_run {ι Result : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl spec (StateT (Split A Identity) m))
    (client : OracleComp spec Result) (state : Split A Identity) :
    (fun result => (result.1, pack result.2)) <$> (simulateQ handler client).run state =
      (simulateQ (packed handler) client).run (pack state) := by
  exact map_run_simulateQ_eq_of_query_map_eq handler (packed handler) pack
    (fun query before => by rfl) client state

/-- The same ordinary interpreter commutes with complete private state reassociation. -/
theorem packed_interpretation {ι κ : Type} {spec : OracleSpec ι} {base : OracleSpec κ}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : QueryImpl base m) (handler : QueryImpl spec (StateT (Split A Identity) (OracleComp base))) :
    interpret.mapStateTBase (packed handler) = packed (interpret.mapStateTBase handler) := by
  funext query state
  simp only [QueryImpl.mapStateTBase, packed, simulateQ_map, StateT.run, StateT.mk]

/-- State reassociation preserves every selected ordinary query count on the exact program syntax. -/
theorem packed_bound {ι κ Result : Type} {spec : OracleSpec ι} {base : OracleSpec κ}
    (handler : QueryImpl spec (StateT (Split A Identity) (OracleComp base)))
    (client : OracleComp spec Result) (state : Packed A Identity)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (packed handler) client).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ handler client).run (unpack state)).IsQueryBoundP predicate budget := by
  have complete := packed_run handler client (unpack state)
  change (fun result => (result.1, pack result.2)) <$> (simulateQ handler client).run (unpack state) =
    (simulateQ (packed handler) client).run state at complete
  rw [← complete, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity.unpack_pack' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity.unpack_pack

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity.packed_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity.packed_run

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity.packed_interpretation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity.packed_interpretation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity.packed_bound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedIdentity.packed_bound
