import BeaconcryptCore.Computational.RawCtxProtocolBackend
import BeaconcryptCore.Computational.RawCtxBeaconLifecycle

/-!
Indexed routing selects an entire Server or Beacon instance while every instance uses the same primitive interpreter. Five statements preserve complete adaptive execution, original replies, all unselected role fields and one common primitive state. Supplied initial role states may be arbitrarily correlated; no key-independence or generator-order interchange premise is used. The per-step query bound transfers without an operational instance-selection factor.

Fin count identifies existing typed API instances; arbitrary raw-frame/machine identifiers remain inside the checked source handlers. This interface does not allocate or generate instances, and its fixed-state execution bound does not charge or declare free their earlier construction. Dynamic registration, imports, live reveal operations and global security require additional interfaces. Snapshots, persistence, restoration and their consequences are excluded from the active protocol proof. Private full-state equality does not grant the adversary a state-reveal service.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxRoleFamily

abbrev FamilySpec {ι : Type} (localSpec : OracleSpec ι) (count : Nat) :=
  OracleSpec.sigma (fun _ : Fin count => localSpec)

/-- Only the selected complete role state changes; every role uses the same primitive backend. -/
def familyImpl {ι κ LocalState : Type} {localSpec : OracleSpec ι} {backendSpec : OracleSpec κ}
    (count : Nat) (localImpl : QueryImpl localSpec (StateT LocalState (OracleComp backendSpec))) :
    QueryImpl (FamilySpec localSpec count)
      (StateT (Fin count → LocalState) (OracleComp backendSpec)) :=
  fun query state => do
    let result ← (localImpl query.2).run (state query.1)
    pure (result.1, Function.update state query.1 result.2)

/-- The source family invokes the actual selected source implementation with the same complete primitive state. -/
def sourceFamily {ι κ LocalState PrimitiveState : Type}
    {localSpec : OracleSpec ι} {base : OracleSpec κ}
    (count : Nat)
    (localSource : QueryImpl localSpec (StateT (LocalState × PrimitiveState) (OracleComp base))) :
    QueryImpl (FamilySpec localSpec count)
      (StateT ((Fin count → LocalState) × PrimitiveState) (OracleComp base)) :=
  fun query state => do
    let result ← (localSource query.2).run (state.1 query.1, state.2)
    pure (result.1, (Function.update state.1 query.1 result.2.1, result.2.2))

/-- Full primitive interpretation commutes with selected-role routing, without a key-independence assumption. -/
theorem family_interpretation {ι κ η LocalState PrimitiveState : Type}
    {localSpec : OracleSpec ι} {backendSpec : OracleSpec κ} {base : OracleSpec η}
    (count : Nat) (localImpl : QueryImpl localSpec (StateT LocalState (OracleComp backendSpec)))
    (primitive : QueryImpl backendSpec (StateT PrimitiveState (OracleComp base))) :
    (primitive.mapStateTBase (familyImpl count localImpl)).flattenStateT =
      sourceFamily count ((primitive.mapStateTBase localImpl).flattenStateT) := by
  funext query state
  simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, familyImpl, sourceFamily, StateT.run, StateT.mk, bind_pure_comp, simulateQ_map]
  change (fun x => (x.1.1, x.1.2, x.2)) <$>
    (((fun a => (a.1, Function.update state.1 query.1 a.2)) <$>
      simulateQ primitive (localImpl query.2 (state.1 query.1))).run state.2) = _
  rw [StateT.run_map]
  simp only [Functor.map_map, StateT.run]
  rfl

/-- Adaptive instance selection and stopping retain every complete role state and the single shared primitive state. -/
theorem schedule_interpretation {ι κ η LocalState PrimitiveState Result : Type}
    {localSpec : OracleSpec ι} {backendSpec : OracleSpec κ} {base : OracleSpec η}
    (count : Nat) (localImpl : QueryImpl localSpec (StateT LocalState (OracleComp backendSpec)))
    (primitive : QueryImpl backendSpec (StateT PrimitiveState (OracleComp base)))
    (client : OracleComp (FamilySpec localSpec count) Result)
    (state : Fin count → LocalState) (privateState : PrimitiveState) :
    (simulateQ primitive ((simulateQ (familyImpl count localImpl) client).run state)).run privateState =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceFamily count ((primitive.mapStateTBase localImpl).flattenStateT)) client).run
          (state, privateState) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, family_interpretation]

/-- Selecting an instance adds no primitive calls; the original per-step bound includes every callback result. -/
theorem step_bound {ι κ LocalState : Type} {localSpec : OracleSpec ι} {backendSpec : OracleSpec κ}
    (count : Nat) (localImpl : QueryImpl localSpec (StateT LocalState (OracleComp backendSpec)))
    (predicate : backendSpec.Domain → Prop) [DecidablePred predicate]
    (query : (FamilySpec localSpec count).Domain) (bound : Nat)
    (bounded : ∀ state, ((localImpl query.2).run state).IsQueryBoundP predicate bound)
    (state : Fin count → LocalState) :
    ((familyImpl count localImpl query).run state).IsQueryBoundP predicate bound := by
  simpa only [familyImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff] using bounded (state query.1)

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

/-- Each selected Server invokes the already checked native peer-map source with one common primitive interpreter. -/
theorem server_interpretation {Metadata PeerMetadata PrimitiveState ι : Type}
    {base : OracleSpec ι} (count : Nat)
    (primitive : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) :
    (primitive.mapStateTBase (familyImpl count
      (RawCtxServerMixed.serverImpl (PeerMetadata := PeerMetadata) senderId route decode))).flattenStateT =
      sourceFamily count (RawCtxServerMixed.sourceImpl primitive senderId route decode) := by
  rw [family_interpretation, RawCtxServerMixed.server_interpretation]

/-- Every selected Beacon retains its actual lifecycle and fields under the same shared primitive interpreter. -/
theorem beacon_interpretation {Identity DhPair KemPair PrimitiveState ι : Type}
    {base : OracleSpec ι} (count : Nat)
    (primitive : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) :
    (primitive.mapStateTBase (familyImpl count
      (RawCtxBeaconLifecycle.beaconImpl (Identity := Identity) (DhPair := DhPair) (KemPair := KemPair)
        decode))).flattenStateT =
      sourceFamily count (RawCtxBeaconLifecycle.sourceImpl primitive decode) := by
  rw [family_interpretation, RawCtxBeaconLifecycle.beacon_interpretation]

end BeaconcryptCore.Computational.RawCtxRoleFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxRoleFamily.family_interpretation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRoleFamily.family_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxRoleFamily.schedule_interpretation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRoleFamily.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxRoleFamily.step_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRoleFamily.step_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxRoleFamily.server_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRoleFamily.server_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxRoleFamily.beacon_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRoleFamily.beacon_interpretation
