-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInstallFree
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
import BeaconcryptCore.Computational.RegistrationNativePairedSafe
/-! Installation counts for the literal corrected owner, OPEN acceptance and external-writer dictionaries. Every mutable platform reply is retained and no old complete callback equation is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePairedSafe (GlobalInstall)
open RegistrationNativeSecretWordAtomOwnerInstallPrefix (NativeInstall)
open RegistrationNativeG3MaterializedOrdinary (TrustedInstall)
variable {n : Nat} {E Platform ι KemSK A : Type} {base : OracleSpec ι}

def LocalInstall (role : Role) : (LocalSpec n KemSK).Domain → Prop
  | .inl query => GlobalInstall (KemSK := KemSK) role (.inl query)
  | .inr _ => False
instance (role : Role) : DecidablePred (LocalInstall (n := n) (KemSK := KemSK) role) := fun query => by
  cases query <;> dsimp [LocalInstall] <;> infer_instance

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : V → W) (work : StateT S m V) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

theorem local_bound (role : Role) (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (NativeInstall (KemSK := KemSK) role) count) :
    (simulateQ (localQuery selected) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  rcases query with message | (message | common) | query
  · simp [localQuery, LocalInstall, NativeInstall, GlobalInstall, isQueryBoundP_query_iff]
  · simp [localQuery, LocalInstall, NativeInstall, GlobalInstall, isQueryBoundP_query_iff]
  · simp only [localQuery, isQueryBoundP_query_iff, LocalInstall, GlobalInstall, NativeInstall]
    intro installed
    simp only [installed, ite_true]
    decide
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro routed
    simp [LocalInstall, GlobalInstall, isQueryBoundP_query_iff]

theorem platform_zero (role : Role) (work : StateT Platform ProbComp A) (before : Platform) :
    ((platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [localCoin, LocalInstall, isQueryBoundP_query_iff]

private theorem trusted_bound (role : Role) (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (TrustedInstall (KemSK := KemSK) role) count) (before : Platform) :
    ((simulateQ trusted work).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simp only [trusted, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    apply local_bound role false _ 1
    cases query with
    | inl effect =>
      simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect, isQueryBoundP_query_iff]
      intro installed
      decide
    | inr query => simp only [TrustedInstall] at counted
  · intro query free current
    simp only [trusted, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    apply local_bound role false _ 0
    cases query with
    | inl effect =>
      cases effect with
      | inl coin => simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect, NativeInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]
      | inr capability =>
        cases capability <;> simp_all [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect, NativeInstall, TrustedInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]
    | inr query => simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed, NativeInstall, isQueryBoundP_query_iff]

private def mixed (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (Base n KemSK Platform)
  | .inl query => trusted query
  | .inr query => writer implementation query

private theorem owner_program_bound (role : Role)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformOwnerInstallFree.Install (E := E) (KemSK := KemSK) role) count)
    (before : Platform) :
    ((simulateQ (mixed implementation) work).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    cases query with
    | inl query =>
      simpa only [mixed, simulateQ_spec_query] using trusted_bound role
        (((RegistrationNativeBeaconFrontend.Trusted n KemSK).query query) : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) _) 1
        (by simp [isQueryBoundP_query_iff]) current
    | inr query => exact counted.elim
  · intro query free current
    cases query with
    | inl query =>
      simpa only [mixed, simulateQ_spec_query] using trusted_bound role
        (((RegistrationNativeBeaconFrontend.Trusted n KemSK).query query) : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) _) 0
        (by simp only [isQueryBoundP_query_iff]; intro installed; exact (free installed).elim) current
    | inr query => exact platform_zero role (implementation query) current

theorem create_zero (role : Role) (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.create (trusted (n := n) (KemSK := KemSK)) setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, map_apply, isQueryBoundP_map_iff]
  exact trusted_bound role _ 0 (RegistrationNativeG3MaterializedOrdinary.native_create_free role setup edPin mlPin keyId _ env) before

theorem bundle_zero (role : Role) (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.bundle (trusted (n := n) (KemSK := KemSK)) (writer implementation) setup source selected publicPrekey index).run owners).run env).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, isQueryBoundP_map_iff]
  have evaluated := congrArg (fun work : RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State
      (Base n KemSK Platform) (RustM (Option (alloc.vec.Vec U8))) =>
        ((work.run (owners.map RegistrationNativePublicOwners.restore)).run env).run before)
    (RegistrationNativePlatformGenericBundle.program_evaluate (mixed implementation) setup source index)
  simp only [mixed, StateT.run] at evaluated
  rw [← evaluated]
  exact owner_program_bound role implementation _ 0
    (RegistrationNativePlatformOwnerInstallFree.program_free role setup index _ env) before

theorem local_handler_bound (role : Role) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (NativeInstall (KemSK := KemSK) role) count) (before : Platform) :
    ((simulateQ (localHandler selected) work).run before).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [localHandler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_bound role selected (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 1 (by simp [isQueryBoundP_query_iff])
  · intro query free current
    simpa only [localHandler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_bound role selected (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 0 (by simp [isQueryBoundP_query_iff, free])

private def acceptHandler (selected : Bool) (reserve : StateT Platform ProbComp Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (Base n KemSK Platform)
  | .inl query => localHandler selected query
  | .inr _ => platform reserve
private def SyntaxInstall (role : Role) : (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK).Domain → Prop
  | .inl query => NativeInstall (KemSK := KemSK) role query
  | .inr _ => False
private instance (role : Role) : DecidablePred (SyntaxInstall (n := n) (KemSK := KemSK) role) := fun query => by
  cases query <;> dsimp [SyntaxInstall] <;> infer_instance
private theorem syntax_admin (role : Role) (query : (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK).Domain)
    (installed : SyntaxInstall role query) :
    RegistrationNativePlatformServerOpenSyntaxBounds.queryKind query = .admin := by
  rcases query with (message | (message | (publication | environment)) | kem) | reserve
  · exact installed.elim
  · exact installed.elim
  · exact installed.elim
  · rcases environment with coin | capability
    · exact installed.elim
    · cases capability <;> simp_all [SyntaxInstall, NativeInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
        RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,
        RegistrationNativePlatformServerOpenSyntaxBounds.queryKind,
        RegistrationNativePlatformServerOpenSyntaxBounds.protocolKind, PqxdhRecordLiftInterface.effectKind]
  · exact installed.elim
  · exact installed.elim

theorem accept_zero (role : Role) (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformServerOpenControl.accept (localHandler (n := n) selected) (platform reserve) setup checks verify packet).run front).run env).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
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
  have bounded : (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run front).run env).IsQueryBoundP (SyntaxInstall (n := n) (KemSK := KemSK) role) 0 :=
    (RegistrationNativePlatformServerOpenSyntaxBounds.accept_bound (n := n) (KemSK := KemSK) setup checks verify .admin packet front env).of_imp (syntax_admin (n := n) (KemSK := KemSK) role)
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    cases query with
    | inl query =>
      simpa only [acceptHandler, simulateQ_spec_query] using local_handler_bound role selected
        (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 1
        (by simp [isQueryBoundP_query_iff]) current
    | inr query => exact counted.elim
  · intro query free current
    cases query with
    | inl query =>
      simpa only [acceptHandler, simulateQ_spec_query] using local_handler_bound role selected
        (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 0
        (by simp only [isQueryBoundP_query_iff]; intro installed; exact (free installed).elim) current
    | inr query => exact platform_zero role reserve current

theorem embedding_bound (role : Role) (work : OracleComp (LocalSpec n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (LocalInstall (KemSK := KemSK) role) count) :
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed (simulateQ embedLocal work)).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) count := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl query =>
    simp only [QueryImpl.compose, embedLocal, simulateQ_spec_query, RegistrationNativePlatformPublicCoinEmbedding.embed,
      isQueryBoundP_query_iff, LocalInstall]
    intro installed
    simp only [installed, ite_true]
    decide
  | inr coin => simp [QueryImpl.compose, embedLocal, publicCoin,
      RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal,
      LocalInstall, GlobalInstall,
      RegistrationNativeSecretWordAtomInstallCaps.Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,
      isQueryBoundP_query_iff]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.local_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.platform_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.platform_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.create_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.create_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.bundle_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.bundle_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.local_handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.local_handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.accept_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.accept_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.embedding_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal.embedding_bound
