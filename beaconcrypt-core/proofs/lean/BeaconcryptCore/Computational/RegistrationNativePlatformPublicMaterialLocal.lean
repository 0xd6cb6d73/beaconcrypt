-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage
import BeaconcryptCore.Computational.RegistrationNativePublicCaps
/-! Demand-counting embeddings for the corrected public frontend preserve actual routed KEM queries, external coins and mutable platform state. Trusted owner and writer programs cannot manufacture material-service requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

def IsDemand : (Spec n KemSK).Domain → Prop
  | .inl query => RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK) query
  | .inr _ => False
instance : DecidablePred (IsDemand (n := n) (KemSK := KemSK)) := fun query => by
  cases query <;> dsimp [IsDemand] <;> infer_instance

def IsLocalDemand : (LocalSpec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inl _))) => True
  | _ => False
instance : DecidablePred (IsLocalDemand (n := n) (KemSK := KemSK)) := fun query => by
  rcases query with (_ | (_ | _) | _) | _ <;> first | exact isTrue trivial | exact isFalse id

theorem embed_bound (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) count) :
    (simulateQ embedLocal work).IsQueryBoundP (IsDemand (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  rcases query with (_ | (_ | _) | _) | _ <;>
    simp [embedLocal, publicCoin, IsDemand, RegistrationNativePublicCaps.IsDemand, IsLocalDemand, isQueryBoundP_query_iff]

theorem local_bound (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count) :
    (simulateQ (localQuery selected) work).IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  rcases query with message | (message | query) | query
  · simp [localQuery, IsLocalDemand, RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]
  · simp [localQuery, IsLocalDemand, RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]
  · simp [localQuery, IsLocalDemand, RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro routed
    simp [IsLocalDemand, isQueryBoundP_query_iff]

theorem local_handler_bound (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count) (before : Platform) :
    ((simulateQ (localHandler selected) work).run before).IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [localHandler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_bound selected (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 1 (by simp [isQueryBoundP_query_iff, counted])
  · intro query free current
    simpa only [localHandler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_bound selected (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 0 (by simp [isQueryBoundP_query_iff, free])

theorem platform_zero (work : StateT Platform ProbComp Value) (before : Platform) :
    ((platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [localCoin, IsLocalDemand, isQueryBoundP_query_iff]

private theorem trusted_zero (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (before : Platform) :
    ((simulateQ trusted work).run before).IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible; exact impossible.elim
  · intro query _ current
    simp only [trusted, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    apply local_bound false _ 0
    cases query <;> simp [RegistrationBeaconReferenceCompiler.trustedLift,
      RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]

private def mixed
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (Base n KemSK Platform)
  | .inl query => trusted query
  | .inr query => writer implementation query

private theorem owner_program_zero
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) Value) (before : Platform) :
    ((simulateQ (mixed implementation) work).run before).IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible; exact impossible.elim
  · intro query _ current
    cases query with
    | inl query => simpa only [mixed, simulateQ_spec_query] using
        trusted_zero (((RegistrationNativeBeaconFrontend.Trusted n KemSK).query query) : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) _) current
    | inr query => exact platform_zero (implementation query) current

theorem create_zero (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.create (trusted (n := n) (KemSK := KemSK)) setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run before).IsQueryBoundP
      (IsLocalDemand (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, map_apply, isQueryBoundP_map_iff]
  exact trusted_zero _ before

theorem bundle_zero (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.bundle (trusted (n := n) (KemSK := KemSK)) (writer implementation) setup source selected publicPrekey index).run owners).run env).run before).IsQueryBoundP
      (IsLocalDemand (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, isQueryBoundP_map_iff]
  have evaluated := congrArg (fun work : RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State
      (Base n KemSK Platform) (RustM (Option (alloc.vec.Vec U8))) =>
        ((work.run (owners.map RegistrationNativePublicOwners.restore)).run env).run before)
    (RegistrationNativePlatformGenericBundle.program_evaluate
      (mixed implementation) setup source index)
  simp only [mixed, StateT.run] at evaluated
  rw [← evaluated]
  exact owner_program_zero implementation _ before

private def acceptHandler (selected : Bool) (reserve : StateT Platform ProbComp Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (Base n KemSK Platform)
  | .inl query => localHandler selected query
  | .inr _ => platform reserve

theorem accept_zero (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformServerOpenControl.accept (localHandler (n := n) selected) (platform reserve) setup checks verify packet).run front).run env).run before).IsQueryBoundP
      (IsLocalDemand (KemSK := KemSK)) 0 := by
  have source := congrArg (fun work => ((work.run front).run env).run before)
    (RegistrationNativePlatformServerOpenSyntax.accept_source (acceptHandler (n := n) (KemSK := KemSK) selected reserve) setup checks verify packet)
  have implementation_eq : RegistrationNativePlatformServerOpenSyntax.implementation (acceptHandler (n := n) (KemSK := KemSK) selected reserve) = localHandler (n := n) (KemSK := KemSK) selected := by
    funext query
    rfl
  rw [implementation_eq] at source
  simp only [acceptHandler] at source
  rw [← source]
  change ((simulateQ (acceptHandler selected reserve)
    (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run front).run env)).run before).IsQueryBoundP _ 0
  apply (RegistrationNativePlatformServerOpenSyntaxFree.accept_free setup checks verify packet front env).simulateQ_run_of_step
  · intro query counted current
    cases query with
    | inl query =>
      cases query with
      | inl message => exact counted.elim
      | inr query => cases query with
        | inr query => exact counted.elim
        | inl query => cases query with
          | inl message => exact (local_handler_bound selected (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query (.inr (.inl (.inl message)))) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 1 (by simp [RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]) current)
          | inr query =>
            exact (local_handler_bound selected (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query (.inr (.inl (.inr query)))) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 0 (by cases query <;> simp [RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]) current).mono (Nat.zero_le 1)
    | inr query => exact counted.elim
  · intro query free current
    cases query with
    | inl query =>
      rcases query with message | (message | query) | query
      · simp [acceptHandler, localHandler, StateT.run_lift, bind_pure_comp,
          localQuery, IsLocalDemand, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      · exact (free (by trivial)).elim
      · simp [acceptHandler, localHandler, StateT.run_lift, bind_pure_comp,
          localQuery, IsLocalDemand, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      · simpa only [acceptHandler, localHandler, StateT.run_lift, bind_pure_comp,
          isQueryBoundP_map_iff, simulateQ_spec_query] using
          local_bound selected (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query (.inr (.inr query))) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 0
            (by simp [RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff])
    | inr query => exact platform_zero reserve current

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.embed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.embed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.local_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.local_handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.local_handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.platform_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.platform_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.create_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.create_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.bundle_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.bundle_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.accept_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal.accept_zero
