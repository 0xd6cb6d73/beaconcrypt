-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds
/-! Actual ordinary source sends and receives each make at most one shared commitment hash. The receive KDF window is a separate primitive category. Routing, frame journals, refused operations and mutable frame writing retain their exact states without adding physical shared hashes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformCtxLeafHashBounds (Bounded coins private_work)
open RegistrationNativePlatformCtxBirthdayBudget (IsHash)
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

def IsNativeHash (query : RawCtxMixedOwner.NativeSpec.Domain) : Prop := RawCtxMixedOwner.callKind query = .hash
instance : DecidablePred IsNativeHash := fun _ => by unfold IsNativeHash; infer_instance

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

/-- Literal ordinary primitive interpretation forwards only the explicit commitment hash. -/
theorem primitive_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : RawCtxMixedOwner.NativeSpec.Domain) :
    Bounded (RegistrationNativePlatformCtxOrdinaryPrimitives.primitives setup codec reserve query)
      (if IsNativeHash query then 1 else 0) := by
  rcases query with request | input | opening | bytes | frame
  all_goals simp only [IsNativeHash, RawCtxMixedOwner.callKind, reduceCtorEq, ite_false, ite_true]
  · apply private_work
    intro before
    simp only [RegistrationNativePlatformCtxPrimitives.program, StateT.run]
    exact coins _
  · apply private_work
    intro before
    simp only [RegistrationNativePlatformCtxPrimitives.program, StateT.run]
    exact coins _
  · apply private_work
    intro before
    simp only [RegistrationNativePlatformCtxPrimitives.program, StateT.run]
    exact coins _
  · apply private_work
    intro before
    simp only [RegistrationNativePlatformCtxPrimitives.program, StateT.run, RegistrationNativePlatformCtxBackend.hash,
      isQueryBoundP_query_bind_iff, IsHash, not_true_eq_false, false_or, ite_true]
    exact ⟨by decide, fun _ => by trivial⟩
  · intro before previous
    simp only [RegistrationNativePlatformCtxOrdinaryPrimitives.primitives, StateT.run, isQueryBoundP_map_iff]
    exact coins _

/-- All adaptive primitive scripts keep their source hash budget in complete primitive/P state. -/
theorem program_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : OracleComp RawCtxMixedOwner.NativeSpec A) (cap : Nat) (bounded : work.IsQueryBoundP IsNativeHash cap) :
    Bounded (simulateQ (RegistrationNativePlatformCtxOrdinaryPrimitives.primitives setup codec reserve) work) cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => intro before previous; simp only [simulateQ_pure, StateT.run_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
    intro before previous
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply (isQueryBoundP_bind (primitive_bound setup codec reserve query before previous)
      (fun result _ => ih result.1.1 _ (bounded.2 result.1.1) result.1.2 result.2)).mono
    by_cases active : IsNativeHash query <;> simp_all only [ite_true, ite_false, not_true_eq_false, false_or]
    all_goals omega

/-- The exact frame-attempt journal leaves all primitive queries unchanged. -/
theorem logged_bound (work : OracleComp RawCtxMixedOwner.NativeSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP IsNativeHash cap) :
    (PqxdhDeploymentNative.logged work).IsQueryBoundP IsNativeHash cap := by
  have same := PqxdhDeploymentNative.logged_forget work []
  rw [← same, isQueryBoundP_map_iff] at bounded
  exact bounded

attribute [local irreducible] MldsaServerRouting.send MldsaServerRouting.receive

private theorem server_handler_bound (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (server : PqxdhRecordLiftWorld.Server)
    (query : RawCtxServerMixed.SourceSpec.Domain) :
    ((MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _ => server.sender) route decode query).run server.records).IsQueryBoundP IsNativeHash 1 := by
  cases query with
  | inl input => exact MldsaServerRouting.send_bound _ _ input.1 input.2 server.records .hash
  | inr raw => exact MldsaServerRouting.raw_bound _ route decode raw server.records .hash

/-- Actual Server sends and raw receives retain their one-hash cap, full frame journal and P writer effects. -/
theorem server_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) :
    Bounded (RegistrationNativePlatformCtxOrdinaryWorld.serverStep (n := n) setup codec reserve route query) 1 := by
  intro before previous
  cases found : before.server with
  | none => cases query <;> simp only [RegistrationNativePlatformCtxOrdinaryWorld.serverStep, StateT.run, found, state_pure_apply, isQueryBoundP_pure]
  | some server =>
    simp only [RegistrationNativePlatformCtxOrdinaryWorld.serverStep, StateT.run, found, state_bind_apply,
      state_pure_apply, bind_pure_comp, isQueryBoundP_map_iff]
    exact program_bound setup codec reserve _ 1 (logged_bound _ 1 (server_handler_bound route codec.frameRead server query)) before.primitive previous

/-- Actual Beacon sends and raw receives retain one shared hash independently of the receive KDF window. -/
theorem beacon_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    Bounded (RegistrationNativePlatformCtxOrdinaryWorld.beaconStep (n := n) setup codec reserve owner query) 1 := by
  intro before previous
  cases found : before.owners[owner]? with
  | none => simp only [RegistrationNativePlatformCtxOrdinaryWorld.beaconStep, StateT.run, found, state_pure_apply, isQueryBoundP_pure]
  | some phase =>
    simp only [RegistrationNativePlatformCtxOrdinaryWorld.beaconStep, StateT.run, found, state_bind_apply,
      state_pure_apply, bind_pure_comp, isQueryBoundP_map_iff]
    apply program_bound setup codec reserve _ 1
    apply logged_bound
    have actual := PqxdhRecordLiftBeacon.handler_bound codec.frameRead query ⟨phase, before.ownerRaw owner⟩ .hash
    cases query <;> exact actual

def worldCap (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) : Nat :=
  match query with
  | .inl _ => 0
  | .inr (.inl query) => if PqxdhRecordLiftInterface.effectKind query = .hash then 1 else 0
  | .inr (.inr _) => 1

/-- Actual environment bookkeeping and coins cost zero; its explicit shared hash costs one. -/
theorem effect_bound (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Bounded (RegistrationNativePlatformCtxRunner.privateWork (RegistrationNativePlatformCtxEffects.program query) :
      RegistrationNativePlatformCtxRunner.M (PqxdhRecordLiftWorld.State n) Platform _)
      (if PqxdhRecordLiftInterface.effectKind query = .hash then 1 else 0) := by
  apply private_work
  intro before
  cases query with
  | inl query =>
      simp only [RegistrationNativePlatformCtxEffects.program, StateT.run, PqxdhRecordLiftInterface.effectKind,
        reduceCtorEq, ite_false]
      exact coins _
  | inr query =>
      cases query <;> simp only [RegistrationNativePlatformCtxEffects.program, StateT.run,
        PqxdhRecordLiftInterface.effectKind, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact coins _
        | simp [RegistrationNativePlatformCtxBackend.hash, IsHash]

/-- Literal routing uses one hash per ordinary source call and only the explicit hash cost for Env operations. -/
theorem handler_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) :
    Bounded (RegistrationNativePlatformCtxOrdinaryWorld.handler setup codec reserve route query) (worldCap query) := by
  rcases query with created | effects | serverQuery | beaconQuery
  · intro before previous
    cases found : before.server <;> simp only [RegistrationNativePlatformCtxOrdinaryWorld.handler,
      RegistrationNativePlatformCtxOrdinaryWorld.initializeWorld, StateT.run, found, state_pure_apply, isQueryBoundP_pure]
  · exact effect_bound effects
  · rcases serverQuery with input | raw
    · exact server_bound setup codec reserve route (.inl input)
    · exact server_bound setup codec reserve route (.inr raw)
  · rcases beaconQuery with ⟨owner, plaintext | raw⟩
    · exact beacon_bound setup codec reserve owner (.inl plaintext)
    · exact beacon_bound setup codec reserve owner (.inr raw)

/-- Public shell refusals add no hash calls and preserve the same ordinary source allowances. -/
theorem guarded_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) :
    Bounded (RegistrationNativePlatformCtxOrdinaryWorld.guarded setup codec reserve route query) (worldCap query) := by
  intro before previous
  cases refused : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply => simp only [RegistrationNativePlatformCtxOrdinaryWorld.guarded, StateT.run, refused, state_pure_apply, isQueryBoundP_pure]
  | none =>
      simp only [RegistrationNativePlatformCtxOrdinaryWorld.guarded, StateT.run, refused]
      exact handler_bound setup codec reserve route query before previous
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.primitive_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.logged_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.logged_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.server_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.server_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.beacon_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.effect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.effect_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.guarded_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds.guarded_bound
