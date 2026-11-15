-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundle

/-! Source-key transport for the actual generation-free Beacon Init program. Working owners, mutable environment and complete global native state are mapped together; named signing requests retain all public operands. Ordinary source parts use only the separately checked no-ML source maps. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaMap (Map owners owner nativeState)
open RegistrationNativeMldsaSignMap (transform)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
variable {left right : Source} {n : Nat} {KemSK Value Other Next OtherNext ι : Type} {base : OracleSpec ι}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

def localState (mapping : Map left right) (before : Local n KemSK left) : Local n KemSK right :=
  (owners mapping before.1, (before.2.1, nativeState mapping before.2.2))

abbrev Natural (mapping : Map left right) (value : Value → Other)
    (first : StateT (Local n KemSK left) (OracleComp (RegistrationNativeMldsaProgram.Spec left)) Value)
    (second : StateT (Local n KemSK right) (OracleComp (RegistrationNativeMldsaProgram.Spec right)) Other) : Prop :=
  ∀ before, Prod.map value (localState mapping) <$> transform mapping (first.run before) = second.run (localState mapping before)

theorem pure_natural (mapping : Map left right) (value : Value → Other) (input : Value) :
    Natural (n := n) (KemSK := KemSK) mapping value (pure input) (pure (value input)) := by
  intro before
  simp only [transform, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

theorem bind_natural (mapping : Map left right) (value : Value → Other) (nextValue : Next → OtherNext)
    (first : StateT (Local n KemSK left) (OracleComp (RegistrationNativeMldsaProgram.Spec left)) Value)
    (second : StateT (Local n KemSK right) (OracleComp (RegistrationNativeMldsaProgram.Spec right)) Other)
    (nextFirst : Value → StateT (Local n KemSK left) (OracleComp (RegistrationNativeMldsaProgram.Spec left)) Next)
    (nextSecond : Other → StateT (Local n KemSK right) (OracleComp (RegistrationNativeMldsaProgram.Spec right)) OtherNext)
    (initial : Natural mapping value first second)
    (continued : ∀ input, Natural mapping nextValue (nextFirst input) (nextSecond (value input))) :
    Natural mapping nextValue (first >>= nextFirst) (second >>= nextSecond) := by
  intro before
  simp only [StateT.run_bind, transform, simulateQ_bind, map_bind]
  rw [← initial before, bind_map_left]
  apply bind_congr
  intro result
  exact continued result.1 result.2

theorem simulate_natural {Query : Type} {spec : OracleSpec Query} (mapping : Map left right)
    (first : QueryImpl spec (StateT (Local n KemSK left) (OracleComp (RegistrationNativeMldsaProgram.Spec left))))
    (second : QueryImpl spec (StateT (Local n KemSK right) (OracleComp (RegistrationNativeMldsaProgram.Spec right))))
    (queries : ∀ query, Natural mapping id (first query) (second query)) (work : OracleComp spec Value) :
    Natural mapping id (simulateQ first work) (simulateQ second work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, id_eq] using pure_natural mapping id value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind_natural mapping id id _ _ _ _ (queries query) ih

set_option backward.isDefEq.respectTransparency false in
theorem lower_natural (mapping : Map left right) (value : Value → Other) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (first : RegistrationNativeBeaconFrontend.M n KemSK left RegistrationServerRoleBackend.State Value)
    (second : RegistrationNativeBeaconFrontend.M n KemSK right RegistrationServerRoleBackend.State Other)
    (related : RegistrationNativeMldsaOrdinaryMap.Natural mapping value first second) (before : Local n KemSK left) :
    Prod.map value (localState mapping) <$> (lower setup checks representation created first).run before =
      (lower setup checks representation created second).run (localState mapping before) := by
  have body := related before.1 before.2.1
  have shared := RegistrationNativeMldsaGlobalMap.simulate_natural mapping
    (RegistrationNativeExperiment.trusted setup checks representation created left)
    (RegistrationNativeExperiment.trusted setup checks representation created right)
    (RegistrationNativeMldsaGlobalMap.trusted_natural mapping setup checks representation created)
    ((first.run before.1).run before.2.1) before.2.2
  let post : (((Value × RegistrationNativeBeaconFrontend.State left) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×
      RegistrationNativeExperiment.State n KemSK right) → Other × Local n KemSK right := fun result =>
    (value result.1.1.1, (owners mapping result.1.1.2, (result.1.2, result.2)))
  calc
    _ = post <$> (Prod.map id (nativeState mapping) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created left)
          ((first.run before.1).run before.2.1)).run before.2.2) := by
      simp only [lower, StateT.run, Functor.map_map]
      rfl
    _ = post <$> (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created right)
        ((first.run before.1).run before.2.1)).run (nativeState mapping before.2.2) := congrArg (fun work => post <$> work) shared
    _ = _ := by
      simp only [lower, StateT.run]
      dsimp only [localState, StateT.run] at body ⊢
      rw [← body, simulateQ_map, map_apply]
      simp only [Functor.map_map]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem native_natural (mapping : Map left right) (value : Value → Other) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (first : RegistrationNativeBeaconFrontend.M n KemSK left RegistrationServerRoleBackend.State Value)
    (second : RegistrationNativeBeaconFrontend.M n KemSK right RegistrationServerRoleBackend.State Other)
    (related : RegistrationNativeMldsaOrdinaryMap.Natural mapping value first second) :
    Natural mapping value (RegistrationNativeMldsaBundle.native setup checks representation created first)
      (RegistrationNativeMldsaBundle.native setup checks representation created second) := by
  intro before
  change Prod.map value (localState mapping) <$> transform mapping
      (RegistrationNativeMldsaProgram.lift ((lower setup checks representation created first).run before)) = _
  rw [RegistrationNativeMldsaSignMap.transform_lift]
  have lifted := congrArg (RegistrationNativeMldsaProgram.lift (source := right))
    (lower_natural mapping value setup checks representation created first second related before)
  simpa only [RegistrationNativeMldsaBundle.native, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativeMldsaProgram.lift, StateT.run, simulateQ_map] using lifted

private def NonSigning : RegistrationBeaconInitExecutor.Spec.Domain → Prop
  | .inl (.sign _ _ _) => False
  | _ => True

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_outgoing (mapping : Map left right) (setup : Setup base KemSK)
    (index : Nat) (current : RegistrationNativeBeaconFrontend.Owner left)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    RegistrationNativeMldsaOrdinaryMap.Natural (n := n) (Auxiliary := RegistrationServerRoleBackend.State) mapping id
      (RegistrationNativeBeaconFrontend.outgoing setup left index current query)
      (RegistrationNativeBeaconFrontend.outgoing setup right index (owner mapping current) query) := by
  classical
  rcases query with (hash | ⟨request, payload, digest⟩) | ed
  · exact RegistrationNativeMldsaOrdinaryMap.hash_natural mapping hash
  · exact RegistrationNativeMldsaOrdinaryMap.pure_natural mapping id _
  · by_cases matching : ed.public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys current.identitySeed).ed25519
    · simp only [RegistrationNativeBeaconFrontend.outgoing, owner, ite_eq_left matching]
      apply RegistrationNativeMldsaOrdinaryMap.bind_natural mapping id id _ _ _ _ (RegistrationNativeMldsaOrdinaryMap.history_natural mapping index _ _)
      intro _logged
      exact RegistrationNativeMldsaOrdinaryMap.pure_natural mapping id _
    · simp only [RegistrationNativeBeaconFrontend.outgoing, owner, ite_eq_right matching]
      exact RegistrationNativeMldsaOrdinaryMap.pure_natural mapping id _

set_option backward.isDefEq.respectTransparency false in
theorem outgoing_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (current : RegistrationNativeBeaconFrontend.Owner left) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Natural (n := n) mapping id (RegistrationNativeMldsaBundle.outgoing setup checks representation created index current query)
      (RegistrationNativeMldsaBundle.outgoing setup checks representation created index (owner mapping current) query) :=
  native_natural mapping id setup checks representation created _ _ (ordinary_outgoing mapping setup index current query)

set_option backward.isDefEq.respectTransparency false in
theorem afterPublished_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (current : RegistrationNativeBeaconFrontend.Owner left) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Natural (n := n) mapping id (RegistrationNativeMldsaBundle.afterPublished setup checks representation created index current oneTime published)
      (RegistrationNativeMldsaBundle.afterPublished setup checks representation created index (owner mapping current) oneTime published) := by
  cases published with
  | fail error => exact pure_natural mapping id _
  | div => exact pure_natural mapping id _
  | ok outcome => cases outcome with
    | Err previous => exact pure_natural mapping id _
    | Ok finished =>
        apply bind_natural mapping id id _ _ _ _ (native_natural mapping id setup checks representation created _ _
          (RegistrationNativeMldsaOrdinaryMap.phase_natural mapping index (.initSent finished.pending oneTime)))
        intro _updated
        apply bind_natural mapping id id _ _ _ _ (native_natural mapping id setup checks representation created _ _
          (RegistrationNativeMldsaOrdinaryMap.effect_natural mapping _))
        intro _advanced
        exact pure_natural mapping id _

set_option backward.isDefEq.respectTransparency false in
private theorem published_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (current : RegistrationNativeBeaconFrontend.Owner left) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Natural (n := n) mapping id
      (do
        let published ← simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index current)
          (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨current.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup current)
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ current.pin)
        RegistrationNativeMldsaBundle.afterPublished setup checks representation created index current oneTime published)
      (do
        let published ← simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index (owner mapping current))
          (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨(owner mapping current).pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup (owner mapping current))
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ (owner mapping current).pin)
        RegistrationNativeMldsaBundle.afterPublished setup checks representation created index (owner mapping current) oneTime published) := by
  apply bind_natural mapping id id _ _ _ _ (simulate_natural mapping _ _
    (outgoing_natural mapping setup checks representation created index current) _)
  intro published
  exact afterPublished_natural mapping setup checks representation created index current oneTime published

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
theorem bundle_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) :
    Natural (n := n) mapping id (RegistrationNativeMldsaBundle.bundle (source := left) setup checks wire representation created index)
      (RegistrationNativeMldsaBundle.bundle (source := right) setup checks wire representation created index) := by
  unfold RegistrationNativeMldsaBundle.bundle
  apply bind_natural mapping (owners mapping) id _ _ _ _ (native_natural mapping (owners mapping) setup checks representation created _ _
    (RegistrationNativeMldsaOrdinaryMap.get_natural mapping))
  intro before
  simp only [RegistrationNativeMldsaMap.owners_lookup]
  cases before[index]? with
  | none => exact pure_natural mapping id _
  | some current =>
      simp only [Option.map_some]
      dsimp only [owner]
      cases current.phase with
      | initSent pending oneTime | established completed | aborted previous => exact pure_natural mapping id _
      | fresh =>
          apply bind_natural mapping id id _ _ _ _ (native_natural mapping id setup checks representation created _ _
            (RegistrationNativeMldsaOrdinaryMap.sample_natural mapping PqxdhJointGapDh.sampleScalar))
          intro oneTime
          exact published_natural mapping setup checks wire representation created index current oneTime
      | freshWithCoins oneTime =>
          apply bind_natural mapping id id _ _ _ _ (pure_natural mapping id oneTime)
          intro actual
          exact published_natural mapping setup checks wire representation created index current actual

/-- Closing the mutable owner/environment lens commutes with private-key representation change. -/
theorem close_map (mapping : Map left right) (before : Local n KemSK left) :
    RegistrationNativeMldsaShared.close (localState mapping before) = nativeState mapping (RegistrationNativeMldsaShared.close before) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem sourceBundle_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK left) :
    Prod.map id (nativeState mapping) <$> transform mapping
      ((RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index).run before) =
      (RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index).run (nativeState mapping before) := by
  have localLaw := bundle_natural mapping setup checks wire representation created index
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))
  have closed := congrArg (fun work => Prod.map id RegistrationNativeMldsaShared.close <$> work) localLaw
  simp only [RegistrationNativeMldsaBundle.sourceBundle, StateT.run, transform, simulateQ_map, Functor.map_map] at closed ⊢
  exact closed

end BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.pure_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.pure_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.bind_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.bind_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.simulate_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.simulate_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.lower_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.lower_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.native_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.native_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.outgoing_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.outgoing_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.afterPublished_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.afterPublished_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.bundle_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.bundle_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.close_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.close_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.sourceBundle_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap.sourceBundle_natural
