-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap

/-! Global native World, private KEM and owner lenses preserve a pure ML signing-key representation map. The complete existing caches, counters, parsed ordinal and indexed KEM pool are retained. These operational source maps require no generation/sign equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaMap (Map nativeState)
open PqxdhServerAuthExperiment (Setup Checks)
variable {left right : Source} {n : Nat} {KemSK Value Other Next OtherNext ι : Type} {base : OracleSpec ι}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

abbrev Natural (mapping : Map left right) (value : Value → Other)
    (first : RegistrationNativeExperiment.M n KemSK left Value)
    (second : RegistrationNativeExperiment.M n KemSK right Other) : Prop :=
  ∀ before, Prod.map value (nativeState mapping) <$> first.run before = second.run (nativeState mapping before)

theorem pure_natural (mapping : Map left right) (value : Value → Other) (input : Value) :
    Natural (n := n) (KemSK := KemSK) mapping value (pure input) (pure (value input)) := by
  intro before
  simp only [StateT.run_pure, map_pure]
  rfl

theorem bind_natural (mapping : Map left right) (value : Value → Other) (nextValue : Next → OtherNext)
    (first : RegistrationNativeExperiment.M n KemSK left Value) (second : RegistrationNativeExperiment.M n KemSK right Other)
    (nextFirst : Value → RegistrationNativeExperiment.M n KemSK left Next)
    (nextSecond : Other → RegistrationNativeExperiment.M n KemSK right OtherNext)
    (initial : Natural mapping value first second)
    (continued : ∀ input, Natural mapping nextValue (nextFirst input) (nextSecond (value input))) :
    Natural mapping nextValue (first >>= nextFirst) (second >>= nextSecond) := by
  intro before
  simp only [StateT.run_bind, map_bind]
  rw [← initial before, bind_map_left]
  apply bind_congr
  intro result
  exact continued result.1 result.2

theorem server_natural (mapping : Map left right)
    (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) :
    Natural (KemSK := KemSK) mapping id (RegistrationNativeExperiment.server work) (RegistrationNativeExperiment.server work) := by
  intro before
  simp only [RegistrationNativeExperiment.server, StateT.run, Functor.map_map]
  rfl

theorem world_natural (mapping : Map left right) (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    Natural (KemSK := KemSK) mapping id (RegistrationNativeExperiment.world work) (RegistrationNativeExperiment.world work) :=
  server_natural mapping _

set_option backward.isDefEq.respectTransparency false in
theorem trusted_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Natural mapping id (RegistrationNativeExperiment.trusted setup checks representation created left query)
      (RegistrationNativeExperiment.trusted setup checks representation created right query) := by
  cases query with
  | inl effect => exact world_natural mapping _
  | inr query =>
      intro before
      simp only [RegistrationNativeExperiment.trusted, StateT.run, bind_pure_comp, Functor.map_map]
      rfl

theorem simulate_natural {Query : Type} {spec : OracleSpec Query} (mapping : Map left right)
    (first : QueryImpl spec (RegistrationNativeExperiment.M n KemSK left))
    (second : QueryImpl spec (RegistrationNativeExperiment.M n KemSK right))
    (queries : ∀ query, Natural mapping id (first query) (second query)) (work : OracleComp spec Value) :
    Natural mapping id (simulateQ first work) (simulateQ second work) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq first second (nativeState mapping) queries work

set_option backward.isDefEq.respectTransparency false in
theorem record_natural (mapping : Map left right) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery) :
    Natural (n := n) mapping id (RegistrationNativeExperiment.record setup wire route query left)
      (RegistrationNativeExperiment.record setup wire route query right) := by
  cases query with
  | inl command => exact world_natural mapping _
  | inr command =>
      rcases command with ⟨index, command⟩
      cases command with
      | inl plaintext =>
          intro before
          simp only [RegistrationNativeExperiment.record, StateT.run, nativeState, RegistrationNativeMldsaMap.owners_lookup]
          cases before.beacons[index]? with
          | none => simp only [Option.map_none, map_pure]; rfl
          | some current =>
              simp only [Option.map_some]
              exact world_natural mapping _ before
      | inr raw =>
          intro before
          simp only [RegistrationNativeExperiment.record, StateT.run, nativeState, RegistrationNativeMldsaMap.owners_lookup]
          cases before.beacons[index]? with
          | none => simp only [Option.map_none, map_pure]; rfl
          | some current =>
              simp only [Option.map_some]
              exact world_natural mapping _ before

set_option backward.isDefEq.respectTransparency false in
theorem beacon_natural (mapping : Map left right) (value : Value → Other) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (first : RegistrationNativeBeaconFrontend.M n KemSK left RegistrationServerRoleBackend.State Value)
    (second : RegistrationNativeBeaconFrontend.M n KemSK right RegistrationServerRoleBackend.State Other)
    (related : RegistrationNativeMldsaOrdinaryMap.Natural mapping value first second) :
    Natural mapping value (RegistrationNativeExperiment.beacon setup checks representation created first)
      (RegistrationNativeExperiment.beacon setup checks representation created second) := by
  intro before
  have body := related before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world)
  have shared := simulate_natural mapping
    (RegistrationNativeExperiment.trusted setup checks representation created left)
    (RegistrationNativeExperiment.trusted setup checks representation created right)
    (trusted_natural mapping setup checks representation created)
    ((first.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) before
  let post : (((Value × RegistrationNativeBeaconFrontend.State left) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×
      RegistrationNativeExperiment.State n KemSK right) → Other × RegistrationNativeExperiment.State n KemSK right := fun result =>
    (value result.1.1.1, { result.2 with
      beacons := RegistrationNativeMldsaMap.owners mapping result.1.1.2
      server := { result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })
  calc
    _ = post <$> (Prod.map id (nativeState mapping) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created left)
          ((first.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before) := by
      simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, Functor.map_map]
      rfl
    _ = post <$> (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created right)
        ((first.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run (nativeState mapping before) :=
      congrArg (fun work => post <$> work) shared
    _ = _ := by
      simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp]
      dsimp only [nativeState, StateT.run] at body ⊢
      rw [← body, simulateQ_map, map_apply]
      simp only [Functor.map_map]
      rfl

def NonML : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.create _ _ _) | .inr (.bundle _) | .inr (.build _ _) => False
  | _ => True

theorem parsed_natural (mapping : Map left right) :
    Natural (n := n) (KemSK := KemSK) mapping id
      (modify fun state => { state with parsedAccepts := state.parsedAccepts + 1 })
      (modify fun state => { state with parsedAccepts := state.parsedAccepts + 1 }) := by
  intro before
  simp only [StateT.run_modify, map_pure]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem create_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array Std.U8 32#usize) (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64) :
    Natural (n := n) mapping id
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup left edPin mlPin keyId))
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup right edPin mlPin keyId)) :=
  beacon_natural mapping id setup checks representation created _ _
    (RegistrationNativeMldsaControllerMap.create_natural mapping setup edPin mlPin keyId)

set_option backward.isDefEq.respectTransparency false in
theorem non_ml_natural (mapping : Map left right) (sameVerify : left.verify = right.verify)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential left)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : NonML query) :
    Natural (n := n) mapping id
      (RegistrationNativeExperiment.handler setup checks wire route representation created left credential query)
      (RegistrationNativeExperiment.handler setup checks wire route representation created right (RegistrationNativeMldsaMap.credential mapping credential) query) := by
  cases query with
  | inl coin => exact world_natural mapping _
  | inr command => cases command with
    | create edPin mlPin keyId => exact ordinary.elim
    | bundle index => exact ordinary.elim
    | build handle application => exact ordinary.elim
    | accept packet =>
        apply bind_natural mapping id id _ _ _ _ (parsed_natural mapping)
        intro _parsed
        simp only [sameVerify]
        exact server_natural mapping _
    | finish index packet =>
        exact beacon_natural mapping id setup checks representation created _ _
          (RegistrationNativeMldsaControllerMap.finish_natural mapping sameVerify setup wire index packet)
    | hmac key message => exact pure_natural mapping id _
    | hash bytes => exact world_natural mapping _
    | serverSend keyId plaintext => exact record_natural mapping setup wire route (.inl (.inl (plaintext, keyId)))
    | serverRaw raw => exact record_natural mapping setup wire route (.inl (.inr raw))
    | beaconSend index plaintext => exact record_natural mapping setup wire route (.inr (index, .inl plaintext))
    | beaconRaw index raw => exact record_natural mapping setup wire route (.inr (index, .inr raw))

end BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.pure_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.pure_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.bind_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.bind_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.server_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.server_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.world_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.world_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.trusted_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.trusted_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.simulate_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.simulate_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.record_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.record_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.beacon_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.beacon_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.parsed_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.parsed_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.create_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.create_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.non_ml_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap.non_ml_natural
