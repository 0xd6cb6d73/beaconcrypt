-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh
import BeaconcryptCore.Computational.RegistrationAgreementGuardState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Projection of actual source private Server captures to the literal native Server role backend. The selected uniform scalar and actual KEM encapsulation primitive interpretations are explicit; source RNG and opaque key poststates remain in the preceding exact capture representation. The native projection is derived per query and keeps every optional rejection. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 CipherArray Keys KeyPair)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open AdapterPublicAgreementPrimitiveModel (Model)
open PqxdhRootTableInitialization (rootArray)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : CryptoOperations (RustT ProbComp)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

def keys (identity : material.EdSecretKey) : Keys := ⟨identity, .None, .None, .None⟩

def project (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (before : AdapterPublicAgreementServerCapture.State R) : Bool × RegistrationServerRoleBackend.State :=
  ⟨before.ready, ⟨_root_.Option.map (fun key => view.kxSecret key.secret_key) before.ephemeral⟩⟩

noncomputable def encapsulation (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (key : PqxdhKemIndCca.MlKem768PublicKey) : ProbComp (CipherArray × Array32) :=
  (fun result => (PqxdhAcceptedRegistration.ciphertextArray result.1, rootArray result.2)) <$>
    simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)

structure Entropy (model : Model (m := ProbComp) generator setup checks view) : Prop where
  sample : model.sample = PqxdhJointGapDh.sampleScalar
  encapsulate : ∀ key, model.encapsulate key = encapsulation setup key

noncomputable def implementation (model : Model (m := ProbComp) generator setup checks view)
    (identity : material.EdSecretKey) : QueryImpl Spec (StateT (Bool × RegistrationServerRoleBackend.State) ProbComp) :=
  RegistrationAgreementGuardState.implementation (RegistrationAgreementShared.auxiliary setup.source
    (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))

noncomputable section

omit material primitive crypto in
private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m]
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl
omit material primitive crypto in
private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before, before) := rfl
omit material primitive crypto in
private theorem state_set_apply {S : Type} {m : Type → Type} [Monad m]
    (after before : S) : (set after : StateT S m Unit) before = pure ((), after) := rfl
omit material primitive crypto in
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (before : S) : (modify change : StateT S m Unit) before = pure ((), change before) := rfl
omit material primitive crypto in
private theorem state_bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
omit material primitive crypto in
private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl
omit material primitive crypto in
private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  rw [bind_pure_comp]

theorem query (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (before : AdapterPublicAgreementServerCapture.State R)
    (request : Request) (allowed : RegistrationAgreementRoleCoverage.Allowed request) :
    Prod.map id (project view) <$>
      (AdapterPublicAgreementServerCapture.implementation model (keys identity) request).run before =
      (implementation model identity request).run (project view before) := by
  change Prod.map id (project view) <$> Prod.map id AdapterPublicAgreementServerCapture.decode <$>
      (AdapterPublicAgreementPrimitiveModel.implementation model (keys identity) request).run
        (AdapterPublicAgreementServerCapture.encode model (keys identity) before) = _
  rw [Functor.map_map]
  cases flag : before.ready <;> cases request with
  | convertPublic key =>
    simp [StateT.run, state_pure_apply, state_map_apply, state_lift_apply, flag, AdapterPublicAgreementPrimitiveModel.implementation, implementation,
      RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation,
      RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
      RegistrationServerRoleBackend.localBackend,
      AdapterPublicAgreementServerCapture.decode, AdapterPublicAgreementServerCapture.encode, project]
  | convertSecret role =>
    change role = .LocalIdentity at allowed
    subst role
    simp [StateT.run, state_pure_apply, state_set_apply, state_bind_apply, state_map_apply, state_lift_apply, flag, AdapterPublicAgreementPrimitiveModel.implementation, implementation,
      RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation, state_modify_apply,
      RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
      RegistrationServerRoleBackend.selected_conversion setup model.representation,

      AdapterPublicAgreementServerCapture.decode, AdapterPublicAgreementServerCapture.encode, project]
  | generate role =>
    change role = .ServerEphemeral at allowed
    subst role
    simp [StateT.run, state_get_apply, state_set_apply, state_bind_apply, state_map_apply, state_lift_apply, flag, AdapterPublicAgreementPrimitiveModel.implementation, implementation,
      RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation,
      RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
      RegistrationServerRoleBackend.localBackend, PqxdhServerAuthExperiment.generateEphemeral,
      entropy.sample,
      StateT.run,
      AdapterPublicAgreementServerCapture.decode, AdapterPublicAgreementServerCapture.encode,
      project, model.generation.privateView, RegistrationAgreementRoot.nativeOption,

      bind_pure_comp, Functor.map_map]
  | encapsulate input =>
    cases input with
    | none =>
      simp [StateT.run, state_pure_apply, state_get_apply, state_set_apply, state_bind_apply, state_map_apply, state_lift_apply, StateT.run, state_pure_apply, state_get_apply, state_set_apply, state_bind_apply, state_map_apply, state_lift_apply, flag, AdapterPublicAgreementPrimitiveModel.implementation, AdapterPublicAgreementPrimitiveModel.encapsulate,
        implementation, RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation,
        RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
        RegistrationServerRoleBackend.localBackend,
        StateT.run,
        AdapterPublicAgreementServerCapture.decode, AdapterPublicAgreementServerCapture.encode, project]
    | some input =>
      cases parsed : model.publicParsing.parse input with
      | Err error =>
        have invalid : checks.kemKey (RegistrationRootInput.pqKey input) = false := by
          apply Bool.eq_false_iff.mpr
          intro valid
          obtain ⟨key, actual⟩ := (model.publicParsing.admission input).mp valid
          rw [parsed] at actual
          cases actual
        simp [StateT.run, state_pure_apply, state_get_apply, state_set_apply, state_bind_apply, state_map_apply, state_lift_apply, StateT.run, state_pure_apply, state_get_apply, state_set_apply, state_bind_apply, state_map_apply, state_lift_apply, flag, AdapterPublicAgreementPrimitiveModel.implementation, AdapterPublicAgreementPrimitiveModel.encapsulate,
          parsed, invalid, implementation, RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation,
          RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
          RegistrationServerRoleBackend.localBackend,
          StateT.run,
          AdapterPublicAgreementServerCapture.decode, AdapterPublicAgreementServerCapture.encode, project]
      | Ok key =>
        have valid := (model.publicParsing.admission input).mpr ⟨key, parsed⟩
        simp [StateT.run, state_get_apply, state_set_apply, state_bind_apply, state_map_apply, state_lift_apply, StateT.run, state_get_apply, state_set_apply, state_bind_apply, state_map_apply, state_lift_apply, flag, AdapterPublicAgreementPrimitiveModel.implementation, AdapterPublicAgreementPrimitiveModel.encapsulate,
          parsed, valid, implementation, RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation,
          RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
          RegistrationServerRoleBackend.localBackend,
          StateT.run,
          AdapterPublicAgreementServerCapture.decode, AdapterPublicAgreementServerCapture.encode, project,
          entropy.encapsulate, encapsulation, PqxdhServerAuthExperiment.encapsulate, simulateQ_map,
          RegistrationAgreementRoot.nativeOption, bind_pure_comp, Functor.map_map]
  | decapsulate input =>
    cases input <;>
      simp [StateT.run, state_pure_apply, state_map_apply, state_lift_apply, StateT.run, state_pure_apply, state_map_apply, state_lift_apply, flag, AdapterPublicAgreementPrimitiveModel.implementation, AdapterPublicAgreementPrimitiveModel.decapsulate,
        keys, implementation, RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation,
        RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
        RegistrationServerRoleBackend.localBackend,
        AdapterPublicAgreementServerCapture.decode, AdapterPublicAgreementServerCapture.encode, project]
  | dh request =>
    rcases request with ⟨role, publicKey⟩
    cases present : before.ephemeral <;> cases role <;>
      simp [StateT.run, state_pure_apply, state_get_apply, state_bind_apply, state_map_apply, StateT.run, state_pure_apply, state_get_apply, state_bind_apply, state_map_apply, AdapterPublicAgreementPrimitiveModel.implementation, AdapterPublicAgreementPrimitiveModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, AdapterPublicAgreementServerCapture.encode, flag, present, keys,
        implementation, RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation,
        RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
        RegistrationServerRoleBackend.localBackend,
        StateT.run, AdapterPublicAgreementServerCapture.decode, project,
        AdapterPublicAgreementNativeDh.identity_native, AdapterPublicAgreementNativeDh.scalar_native]
    all_goals rfl
  | root request =>
    simp [StateT.run, state_pure_apply, state_map_apply, state_lift_apply, flag, AdapterPublicAgreementPrimitiveModel.implementation, implementation,
      RegistrationAgreementGuardState.implementation, RegistrationAgreementIdentityGuard.implementation,
      RegistrationAgreementShared.auxiliary,
      AdapterPublicAgreementServerCapture.decode, AdapterPublicAgreementServerCapture.encode, project]
theorem program {Value : Type} (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (before : AdapterPublicAgreementServerCapture.State R)
    (work : OracleComp Spec Value) (bounded : RegistrationAgreementRoleCoverage.Bound work) :
    Prod.map id (project view) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity)) work).run before =
      (simulateQ (implementation model identity) work).run (project view before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind request next ih =>
    rw [RegistrationAgreementRoleCoverage.Bound, isQueryBound_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have rest : ∀ reply after,
        Prod.map id (project view) <$>
          (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity)) (next reply)).run after =
          (simulateQ (implementation model identity) (next reply)).run (project view after) :=
      fun reply after => ih reply after (bounded.2 reply)
    simp only [rest]
    calc
      _ = (Prod.map id (project view) <$>
          (AdapterPublicAgreementServerCapture.implementation model (keys identity) request).run before) >>=
          fun result => (simulateQ (implementation model identity) (next result.1)).run result.2 := by
        rw [bind_map_left]
        rfl
      _ = _ := by rw [query model entropy identity before request bounded.1]

theorem server (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) :
    Prod.map id (fun after => (project view after).2) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
        (RegistrationAgreementExecutor.server control status authenticated)).run ⟨rng, false, .None⟩ =
      (simulateQ (RegistrationAgreementShared.auxiliary setup.source
        (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
          (RegistrationAgreementExecutor.server control status authenticated)).run RegistrationServerRoleBackend.empty := by
  have projected := program model entropy identity ⟨rng, false, .None⟩ _
    (RegistrationAgreementRoleCoverage.server_bound control status authenticated)
  calc
    _ = Prod.map id Prod.snd <$> (Prod.map id (project view) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
        (RegistrationAgreementExecutor.server control status authenticated)).run ⟨rng, false, .None⟩) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by
      rw [projected]
      exact RegistrationAgreementGuardState.server _ control status authenticated RegistrationServerRoleBackend.empty

theorem lookup (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (pending : peer.RegistrationLookup) (consumed : Bool) :
    Prod.map id (fun after => (project view after).2) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
        (continueWith (pending.resume consumed) (drive 9))).run ⟨rng, false, .None⟩ =
      (simulateQ (RegistrationAgreementShared.auxiliary setup.source
        (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
          (continueWith (pending.resume consumed) (drive 9))).run RegistrationServerRoleBackend.empty := by
  have projected := program model entropy identity ⟨rng, false, .None⟩ _
    (RegistrationAgreementRoleCoverage.lookup_bound pending consumed)
  calc
    _ = Prod.map id Prod.snd <$> (Prod.map id (project view) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
        (continueWith (pending.resume consumed) (drive 9))).run ⟨rng, false, .None⟩) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by
      rw [projected]
      exact RegistrationAgreementGuardState.lookup _ pending consumed RegistrationServerRoleBackend.empty

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative.server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative.lookup
