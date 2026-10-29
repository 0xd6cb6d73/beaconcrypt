-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform
import BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects
import BeaconcryptCore.Computational.CborRecordWorldSimulation

/-! Actual established-record execution is independent of the private uniform-draw counter. The equations project that counter on both returned Worlds and initial Worlds, while retaining every actual native/effect counter, random-oracle cache, full kernel, owner, frame log and hidden slot. Primitive draw bills remain separate statements about the original counted execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State Primitive primitives)
open RegistrationNativeKemWorldUniform (mask)
variable {ι KemSK Reader Response Value : Type} {base : OracleSpec ι} {n : Nat}

def primitiveMask (state : Primitive) : Primitive := ({ state.1 with uniform := 0 }, state.2)

private theorem primitive_mask (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : Primitive) :
    Prod.map id primitiveMask <$> (primitives setup codec query).run state =
      (fun result => (result.1, ({ state.1 with
        uniform := 0
        native := Function.update state.1.native (RawCtxMixedOwner.callKind query)
          (state.1.native (RawCtxMixedOwner.callKind query) + 1) }, result.2.2))) <$>
        (PqxdhDeploymentNative.primitives setup codec query).run ((), state.2) := by
  have forgot := congrArg (fun work => (fun result => (result.1, ({ state.1 with
        uniform := 0
        native := Function.update state.1.native (RawCtxMixedOwner.callKind query)
          (state.1.native (RawCtxMixedOwner.callKind query) + 1) }, result.2.2))) <$> work)
    (PqxdhRecordLiftWorld.countCoin_forget
      ((PqxdhDeploymentNative.primitives setup codec query).run ((), state.2)) state.1.uniform)
  simpa only [primitives, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map, id_eq, primitiveMask, Function.comp_def] using forgot

/-- The actual primitive callback observes no uniform-counter input and retains its original native-call charge. -/
theorem primitive_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : Primitive) :
    Prod.map id primitiveMask <$> (primitives setup codec query).run state =
      Prod.map id primitiveMask <$> (primitives setup codec query).run (primitiveMask state) := by
  rw [primitive_mask, primitive_mask]
  rfl

/-- The equality applies to arbitrary adaptive native record programs, with all random-oracle effects retained. -/
theorem primitive_program_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Value) (state : Primitive) :
    Prod.map id primitiveMask <$> (simulateQ (primitives setup codec) work).run state =
      Prod.map id primitiveMask <$> (simulateQ (primitives setup codec) work).run (primitiveMask state) := by
  let normalized : QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive ProbComp) :=
    fun query before => Prod.map id primitiveMask <$> (primitives setup codec query).run before
  have step : ∀ query before, Prod.map id primitiveMask <$> (primitives setup codec query).run before =
      (normalized query).run (primitiveMask before) := primitive_input setup codec
  have first := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized primitiveMask step work state
  have second := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized primitiveMask step work (primitiveMask state)
  exact first.trans second.symm

/-- Actual Server routing retains the entire peer map, consumed kernel and frame log under the counter projection. -/
theorem server_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) (state : State n) :
    Prod.map id mask <$> (PqxdhRecordLiftWorld.serverStep setup codec route query).run state =
      Prod.map id mask <$> (PqxdhRecordLiftWorld.serverStep setup codec route query).run (mask state) := by
  cases found : state.server with
  | none =>
      cases query <;> simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, found,
        mask, map_pure, Prod.map, id_eq]
  | some server =>
      let work := PqxdhDeploymentNative.logged
        ((MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _ => server.sender)
          route codec.frameRead query).run server.records)
      let assemble := fun (result : ((RawCtxServerMixed.SourceSpec.Range query ×
          RawCtxServerRouting.State Unit (Std.Array U8 281#usize)) × List PqxdhDeploymentNative.Frame) × Primitive) =>
        (result.1.1.1, PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.serverTag query) result.1.2
          { state with server := some { server with records := result.1.1.2 }, primitive := result.2 })
      have law := congrArg (fun computation => assemble <$> computation)
        (primitive_program_input setup codec work state.primitive)
      simpa only [PqxdhRecordLiftWorld.serverStep, StateT.run, found, mask, bind_pure_comp,
        Functor.map_map, Prod.map, id_eq, primitiveMask, PqxdhRecordLiftWorld.produce, work, assemble] using law

/-- Actual Beacon records retain owner phase, raw attempts, the consumed full kernel and produced frames. -/
theorem beacon_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n) :
    Prod.map id mask <$> (PqxdhRecordLiftWorld.beaconStep setup codec owner query).run state =
      Prod.map id mask <$> (PqxdhRecordLiftWorld.beaconStep setup codec owner query).run (mask state) := by
  cases found : state.owners[owner]? with
  | none => simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, mask, found, map_pure, Prod.map, id_eq]
  | some phase =>
      let work := PqxdhDeploymentNative.logged
        ((PqxdhRecordLiftBeacon.handler codec.frameRead query).run ⟨phase, state.ownerRaw owner⟩)
      let assemble := fun (result : ((RawCtxMixedOwner.SourceSpec.Range query ×
          PqxdhRecordLiftBeacon.State) × List PqxdhDeploymentNative.Frame) × Primitive) =>
        (result.1.1.1, PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag owner) result.1.2
          { state with owners := state.owners.set owner result.1.1.2.phase
                       ownerRaw := Function.update state.ownerRaw owner result.1.1.2.rawAttempts
                       primitive := result.2 })
      have law := congrArg (fun computation => assemble <$> computation)
        (primitive_program_input setup codec work state.primitive)
      simpa only [PqxdhRecordLiftWorld.beaconStep, StateT.run, mask, found, bind_pure_comp,
        Functor.map_map, Prod.map, id_eq, primitiveMask, PqxdhRecordLiftWorld.produce, work, assemble] using law

/-- Every native World request is independent of the hidden uniform counter, including lazy installation and all record paths. -/
theorem handler_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (state : State n) :
    Prod.map id mask <$> (PqxdhRecordLiftWorld.handler setup codec route query).run state =
      Prod.map id mask <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (mask state) := by
  cases query with
  | inl created =>
      cases found : state.server <;> simp only [PqxdhRecordLiftWorld.handler,
        PqxdhRecordLiftWorld.initializeServer, StateT.run, mask, found, map_pure, Prod.map, id_eq]
  | inr query => cases query with
    | inl effect => exact RegistrationNativeKemWorldEffects.effects_input effect state
    | inr record => cases record with
      | inl server => cases server with
        | inl query => exact server_input setup codec route (.inl query) state
        | inr raw => exact server_input setup codec route (.inr raw) state
      | inr beacon =>
          rcases beacon with ⟨owner, query⟩
          cases query with
          | inl plaintext => exact beacon_input setup codec owner (.inl plaintext) state
          | inr raw => exact beacon_input setup codec owner (.inr raw) state

/-- Cursor refusal reads only public Control and therefore retains the same actual early-admission branch. -/
theorem guarded_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (state : State n) :
    Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run state =
      Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run (mask state) := by
  have shell : CborRecordWorldCursor.worldShell (mask state) = CborRecordWorldCursor.worldShell state := rfl
  simp only [CborRecordWorldSimulation.guarded, StateT.run, shell]
  cases refused : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell state) with
  | none => exact handler_input setup codec route query state
  | some reply => simp only [map_pure, Prod.map, id_eq, RegistrationNativeKemWorldUniform.mask_idempotent]

/-- Arbitrary interleavings retain all actual record, administrative and shared-cache state when only the external KEM coin ledger is projected. -/
theorem guarded_program_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) Value)
    (state : State n) :
    Prod.map id mask <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run state =
      Prod.map id mask <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run (mask state) := by
  let normalized : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT (State n) ProbComp) :=
    fun query before => Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run before
  have step : ∀ query before, Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run before =
      (normalized query).run (mask before) := guarded_input setup codec route
  have first := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized mask step work state
  have second := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ normalized mask step work (mask state)
  simpa only [RegistrationNativeKemWorldUniform.mask_idempotent] using first.trans second.symm

end BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.primitive_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.primitive_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.primitive_program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.primitive_program_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.server_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.server_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.beacon_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.beacon_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.handler_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.guarded_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.guarded_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.guarded_program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform.guarded_program_input
