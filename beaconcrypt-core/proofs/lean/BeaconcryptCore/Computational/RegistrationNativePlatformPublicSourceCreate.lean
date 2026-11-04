-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerBody
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerAllowed
import BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed
/-! The actual common-P constructor restores the selected scalar at the exact eager successful birth. Every original constructor prefix, sampler, optional rejection and generated-key state is retained. Only the named native instrumentation view is applied after the reached owner/environment write. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSourceOwnerCommit (Output restoreOutput observe view commit)
open RegistrationNativePublicSourceState (restore project nativeView owners)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable def work (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) (RustM (Option Nat)) :=
  RegistrationNativePlatformPublicOwners.create RegistrationNativePlatformPublicFrontend.trusted setup source selected
    (setup.dh.publicKey scalar) edPin mlPin keyId

private theorem mixed_source {A : Type}
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (tree : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A) :
    simulateQ (fun query => match query with
        | .inl query => RegistrationNativePlatformPublicFrontend.trusted query
        | .inr query => RegistrationNativePlatformPublicFrontend.writer writer query)
      (simulateQ RegistrationNativePlatformGenericBundle.trustedLift tree) =
      simulateQ RegistrationNativePlatformPublicFrontend.trusted tree := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.compose, RegistrationNativePlatformGenericBundle.trustedLift, simulateQ_spec_query]

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The exact public owner-mask equation supplies the eager constructor's complete free tree on the same P. -/
theorem equation (setup : Setup base KemSK)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (frontend : RegistrationNativePublicFrontend.State source) (previous : Platform)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) frontend.beacons) :
    restoreOutput scalar <$> (((work (n := n) setup source selected scalar edPin mlPin keyId).run frontend.beacons).run frontend.environment).run previous =
      simulateQ (RegistrationNativePlatformSourceOwnerEmbedding.embed (n := n))
        ((simulateQ (RegistrationNativePlatformSourceOwnerLanguage.handler (n := n) writer)
          (simulateQ RegistrationNativePlatformGenericBundle.trustedLift
            (((RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId).run (owners scalar frontend.beacons)).run frontend.environment))).run previous) := by
  have masked := congrArg (fun action => action.run previous)
    (RegistrationNativePlatformPublicOwners.create_source (RegistrationNativePlatformPublicFrontend.trusted (n := n) (Platform := Platform))
      setup source selected scalar edPin mlPin keyId frontend.beacons frontend.environment canonical)
  have embedded := congrArg (fun action => action.run previous)
    (RegistrationNativePlatformSourceOwnerLanguage.embedding_program writer
      (simulateQ RegistrationNativePlatformGenericBundle.trustedLift
        (((RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId).run (owners scalar frontend.beacons)).run frontend.environment)))
  have mixed := congrArg (fun action => action.run previous)
    (mixed_source (n := n) (KemSK := KemSK) writer
      (((RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId).run (owners scalar frontend.beacons)).run frontend.environment))
  have joined := embedded.trans mixed
  unfold restoreOutput
  simpa only [work, StateT.run_map, StateT.run, map_apply, RegistrationNativePlatformGenericBundle.liftLegacy,
    RegistrationNativePlatformSourceOwnerLanguage.embedding, Prod.map_def, id_eq] using masked.trans joined.symm

private theorem mixed_allowed {A : Type}
    (tree : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A)
    (allowed : tree.AllQueriesSatisfy (RegistrationNativePublicSourceTrusted.Allowed (KemSK := KemSK))) :
    (simulateQ (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) tree).AllQueriesSatisfy
      (RegistrationNativePlatformSourceOwnerAllowed.Allowed (E := E) (KemSK := KemSK)) := by
  induction tree using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformGenericBundle.trustedLift]
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨(RegistrationNativePlatformSourceOwnerAllowed.trusted_allowed (E := E) query).mpr allowed.1,
      fun value => ih value (allowed.2 value)⟩

/-- Every actual eager constructor query is an allowed World/indexed leaf; the proof follows its exact source mask equality. -/
theorem allowed (setup : Setup base KemSK) (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (frontend : RegistrationNativePublicFrontend.State source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) frontend.beacons) :
    (simulateQ (RegistrationNativePlatformGenericBundle.trustedLift (E := E))
      (((RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId).run (owners scalar frontend.beacons)).run frontend.environment)).AllQueriesSatisfy
        (RegistrationNativePlatformSourceOwnerAllowed.Allowed (E := E) (KemSK := KemSK)) := by
  apply mixed_allowed
  have masked := RegistrationNativePublicCreateMask.create_mask (n := n) setup source selected scalar edPin mlPin keyId
    (frontend.beacons.map RegistrationNativePublicOwners.restore) frontend.environment
  rw [RegistrationNativePublicOwnerRestore.restored_dummy selected scalar (setup.dh.publicKey scalar) frontend.beacons canonical] at masked
  rw [← masked, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind
    (RegistrationNativeTrustedAllowed.create_allowed setup edPin mlPin keyId _ frontend.environment)
    (fun _ => allQueriesSatisfy_pure _ _)

private theorem native_tree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (tree : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    simulateQ (RegistrationNativePlatformExperiment.bundleHandler (n := n) RegistrationNativePlatformMldsaProgram.coins
      setup checks representation created source writer) (simulateQ RegistrationNativePlatformGenericBundle.trustedLift tree) =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (simulateQ (RegistrationNativeExperiment.trusted (n := n) setup checks representation created source) tree) := by
  rw [← QueryImpl.simulateQ_compose]
  have leaves : RegistrationNativePlatformExperiment.bundleHandler (n := n) RegistrationNativePlatformMldsaProgram.coins
      setup checks representation created source writer ∘ₛ RegistrationNativePlatformGenericBundle.trustedLift =
    RegistrationNativePlatformExperiment.trusted RegistrationNativePlatformMldsaProgram.coins setup checks representation created source := by
    funext query
    simp only [QueryImpl.compose, RegistrationNativePlatformGenericBundle.trustedLift, simulateQ_spec_query,
      RegistrationNativePlatformExperiment.bundleHandler]
  rw [leaves]
  exact (RegistrationNativePlatformInterpret.state_simulate RegistrationNativePlatformMldsaProgram.coins
    (RegistrationNativeExperiment.trusted (n := n) setup checks representation created source) tree).symm

/-- The literal common-P public constructor has the exact eager native source result and reached platform state. -/
theorem create_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePlatformPublicSourceExecution.State n KemSK Platform source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) before.1.1.beacons) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (RegistrationNativePlatformPublicSourceExecution.execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
          (work (n := n) setup source selected scalar edPin mlPin keyId)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
          (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId))).run
          (restore roots scalar before.1.1 before.2)).run before.1.2 := by
  let tree := simulateQ (RegistrationNativePlatformGenericBundle.trustedLift (E := E))
    (((RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId).run (owners scalar before.1.1.beacons)).run before.1.1.environment)
  have safe := RegistrationNativePlatformSourceOwnerAllowed.compiled_safe writer tree
    (allowed (E := E) setup selected scalar edPin mlPin keyId before.1.1 canonical) before.1.2
  have raw := RegistrationNativePlatformSourceOwnerBody.raw_source setup checks wire route representation created scalar credential roots
    (work (n := n) setup source selected scalar edPin mlPin keyId) ((simulateQ (RegistrationNativePlatformSourceOwnerLanguage.handler (n := n) writer) tree).run before.1.2)
    before (equation setup writer selected scalar edPin mlPin keyId before.1.1 before.1.2 canonical) safe
  have target := RegistrationNativePlatformSourceOwnerBody.native_returned setup checks representation created writer tree
    (restore roots scalar before.1.1 before.2) before.1.2
  dsimp only [tree] at target
  rw [native_tree setup checks representation created writer] at target
  have combined := raw.trans target
  simpa only [Function.comp_def, RegistrationNativePlatformSourceOwnerBody.returned,
    RegistrationNativePlatformExperiment.liftNative, RegistrationNativePlatformInterpret.state,
    RegistrationNativeExperiment.beacon, StateT.run, map_apply, simulateQ_map, bind_pure_comp, Functor.map_map,
    RegistrationNativePlatformSourceOwnerCommit.view, RegistrationNativePlatformSourceOwnerCommit.commit,
    restore, RegistrationWorldAgreementCompiler.erase, RegistrationWorldAgreementCompiler.join,
    RegistrationServerMaterialSourceState.restore, RegistrationServerReferenceRestore.restore, Prod.map_def, id_eq] using combined
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate.equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate.equation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate.allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate.allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate.create_source
