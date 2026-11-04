-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal
/-! The actual corrected public frontend counts external platform uniform requests separately from native effects, ML/native samplers and routed KEM requests. Local embedding preserves this bill; literal creation and corrected finish emit none. Individual P samplers retain their supplied per-site cap with complete values and P poststates. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform I KemSK A : Type} {base : OracleSpec I}

def IsExternal : (Spec n KemSK).Domain → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred (IsExternal (n := n) (KemSK := KemSK)) := fun query => by
  cases query <;> dsimp [IsExternal] <;> infer_instance

def IsLocalExternal : (LocalSpec n KemSK).Domain → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred (IsLocalExternal (n := n) (KemSK := KemSK)) := fun query => by
  cases query <;> dsimp [IsLocalExternal] <;> infer_instance

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The actual local embedding preserves the complete external-uniform bill. -/
theorem embed_bound (work : OracleComp (LocalSpec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) cap) :
    (simulateQ embedLocal work).IsQueryBoundP (IsExternal (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  cases query <;> simp [embedLocal, publicCoin, IsExternal, IsLocalExternal, isQueryBoundP_query_iff]

/-- Root/material/routed/native requests never become external platform coins. -/
theorem local_zero (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) :
    (simulateQ (localQuery selected) work).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  rcases query with message | (message | query) | query
  · simp [localQuery, IsLocalExternal, isQueryBoundP_query_iff]
  · simp [localQuery, IsLocalExternal, isQueryBoundP_query_iff]
  · simp [localQuery, IsLocalExternal, isQueryBoundP_query_iff]
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro routed
    simp [IsLocalExternal, isQueryBoundP_query_iff]

theorem local_handler_zero (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (before : Platform) :
    ((simulateQ (localHandler selected) work).run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible
    exact impossible.elim
  · intro query _ current
    simpa only [localHandler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_zero selected (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _)

/-- Every actual P sampler retains its supplied per-site coin cap under local reification, with its exact result and poststate. -/
theorem platform_bound (work : StateT Platform ProbComp A) (before : Platform) (cap : Nat)
    (bounded : (work.run before).IsTotalQueryBound cap) :
    ((platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ _ cap ((isQueryBoundP_true_iff _ _).mpr bounded)
  intro coin
  simp [localCoin, IsLocalExternal, isQueryBoundP_query_iff]

theorem platformFull_bound (work : StateT Platform ProbComp A) (before : Platform) (cap : Nat)
    (bounded : (work.run before).IsTotalQueryBound cap) :
    ((platformFull (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP (IsExternal (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ _ cap ((isQueryBoundP_true_iff _ _).mpr bounded)
  intro coin
  simp [publicCoin, IsExternal, isQueryBoundP_query_iff]

theorem trusted_zero (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A) (before : Platform) :
    ((simulateQ trusted work).run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible
    exact impossible.elim
  · intro query _ current
    simp only [trusted, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    exact local_zero false _

theorem create_zero (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.create (trusted (n := n) (KemSK := KemSK)) setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run before).IsQueryBoundP
      (IsLocalExternal (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, map_apply, isQueryBoundP_map_iff]
  exact trusted_zero _ before

/-- Corrected assigned-ID finish uses only old native/material capabilities and adds no external allocation sampler. -/
theorem finish_zero (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((finish (n := n) setup wire source index packet).run owners).run env).run before).IsQueryBoundP
      (IsLocalExternal (KemSK := KemSK)) 0 := by
  simp only [finish, StateT.run]
  cases owners[index]? with
  | none => trivial
  | some owner =>
    simp only [map_apply, isQueryBoundP_map_iff]
    exact local_handler_zero false _ before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.embed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.embed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.local_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.local_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.local_handler_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.local_handler_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.platform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.platform_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.platformFull_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.platformFull_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.trusted_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.trusted_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.create_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.create_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.finish_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal.finish_zero
