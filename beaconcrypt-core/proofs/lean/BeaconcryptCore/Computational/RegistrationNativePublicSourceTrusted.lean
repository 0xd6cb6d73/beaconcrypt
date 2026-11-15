-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld
import BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks
import BeaconcryptCore.Computational.RegistrationNativeMainViewLift

/-! Public environment and indexed KEM callbacks of an actual local owner controller use the same source World and opaque pool. Local role primitives are lowered inside that controller, so its external interface never gains access to the selected Server's ordinary role backend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceTrusted
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore project nativeView)
open RegistrationNativePublicSourceEffects (close fromPrivate toPrivate)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def Allowed : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain → Prop
  | .inr (.inl _) => False
  | _ => True

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before =
      (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem sampled_apply {First Second : Type} (work : ProbComp First) (observe : First → Second)
    (before : PqxdhRecordLiftWorld.State n) :
    PqxdhRecordLiftWorld.sampled (observe <$> work) before =
      Prod.map observe id <$> PqxdhRecordLiftWorld.sampled work before :=
  RegistrationNativeKemReferenceWorld.sampled_map work observe before

private theorem pool_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (query : (PqxdhLiveKemBirth.PoolSpec KemSK).Domain) (before : State n KemSK source) :
    (fun result => (result.1, project roots scalar before.1 (fromPrivate result.2))) <$>
      (RegistrationNativeKemReferenceWorld.kem setup RegistrationNativePublicInterpreter.unavailable
        (.inr (.inl query))).run (toPrivate before.2) =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.trusted setup checks representation created source (.inr (.inr (.inl query)))).run
          (restore roots scalar before.1 before.2) := by
  simp only [RegistrationNativeKemReferenceWorld.kem, RegistrationNativeExperiment.trusted,
    RegistrationNativeKemInterface.source, StateT.run]
  rw [sampled_apply, sampled_apply]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, fromPrivate, toPrivate,
    project, nativeView, restore, RegistrationServerMaterialSourceState.restore,
    RegistrationServerReferenceRestore.restore, RegistrationServerMaterialSourceState.nativeView,
    RegistrationWorldAgreementCompiler.join]

/-- Actual externally requested indexed operations retain the entire source protocol state and private pool. Ordinary role callbacks remain locally owned and are not added as an oracle capability. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (allowed : Allowed query)
    (before : State n KemSK source) :
    (fun result => (result.1, project roots scalar before.1 result.2)) <$>
      (close setup created.seed scalar (simulateQ
        (RegistrationNativePublicInterpreter.handler setup wire route (RegistrationNativeMldsa.owned source credential))
        (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
          (RegistrationBeaconReferenceCompiler.trustedLift query)))).run before.2 =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.trusted setup checks representation created source query).run
          (restore roots scalar before.1 before.2) := by
  cases query with
  | inl query =>
      have closed := RegistrationNativePublicSourceWorld.world_source setup created.seed scalar roots
        (PqxdhRecordLiftWorld.effects query) before
      simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect,
        RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
        RegistrationNativePublicInterpreter.handler, RegistrationNativePublicInterpreter.common,
        RegistrationNativePublicInterpreter.effect, RegistrationNativeExperiment.trusted] at closed ⊢
      convert closed using 1 <;> rfl
  | inr query => cases query with
    | inl query => exact allowed.elim
    | inr query => cases query with
      | inl query =>
          simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed, simulateQ_spec_query]
          rw [RegistrationNativePublicSourceEffects.routed_real]
          have closed := RegistrationNativePublicSourceEffects.kem_source setup created.seed scalar (.inr (.inl query)) before.2
          have mapped := congrArg (fun work => (fun result => (result.1, project roots scalar before.1 (fromPrivate result.2))) <$> work) closed
          simp only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativePublicSourceEffects.layout] at mapped
          rw [RegistrationNativePublicSourceTrusted.pool_source setup checks representation created scalar roots query before] at mapped
          exact mapped
      | inr key =>
          simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed, simulateQ_spec_query]
          rw [RegistrationNativePublicSourceEffects.routed_real]
          simp only [RegistrationNativePublicInterpreter.kem]
          have closed := RegistrationNativePublicSourceWorld.world_source setup created.seed scalar roots
            (PqxdhRecordLiftWorld.sampled (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key))) before
          simp only [RegistrationNativeExperiment.trusted, RegistrationNativeKemInterface.source,
            RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
            StateT.run, lift_apply, sampled_apply, bind_pure_comp,
            Functor.map_map, Prod.map_def, id_eq] at closed ⊢
          convert closed using 1 <;> rfl

noncomputable def implementation (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK)
      (StateT (RegistrationNativePublicInterpreter.State n KemSK) ProbComp) := fun query =>
  close setup seed scalar (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign)
    (simulateQ (RegistrationNativePublicFrontend.liftLocal false) (RegistrationBeaconReferenceCompiler.trustedLift query)))

private theorem close_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (close setup seed scalar (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign)
      (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
        (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work)))).run before =
      (simulateQ (implementation setup wire route sign seed scalar) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, close, StateT.run,
        StateT.monad_bind_def, StateT.bind, simulateQ_bind, implementation]
      apply bind_congr
      rintro ⟨value, after⟩
      exact ih value after

private theorem program_project (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (allowed : work.AllQueriesSatisfy (Allowed (KemSK := KemSK)))
    (frontend : RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (fun result => (result.1, project roots scalar frontend result.2)) <$>
      (simulateQ (implementation setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar) work).run before =
      Prod.map id nativeView <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run
          (restore roots scalar frontend before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      calc
        _ = (implementation setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar query).run before >>= fun reached =>
              Prod.map id nativeView <$>
                (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) (next reached.1)).run
                  (project roots scalar frontend reached.2) := by
          apply bind_congr
          rintro ⟨value, after⟩
          exact (ih value (allowed.2 value) after).trans
            (RegistrationNativeMainViewLift.trusted_program setup checks representation created (next value)
              (restore roots scalar frontend after))
        _ = ((fun result => (result.1, project roots scalar frontend result.2)) <$>
            (implementation setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar query).run before) >>= fun reached =>
              Prod.map id nativeView <$>
                (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) (next reached.1)).run reached.2 := by
          rw [bind_map_left]
        _ = (Prod.map id nativeView <$>
            (RegistrationNativeExperiment.trusted setup checks representation created source query).run
              (restore roots scalar frontend before)) >>= fun reached =>
              Prod.map id nativeView <$>
                (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) (next reached.1)).run reached.2 := by
          have actual : (fun result => (result.1, project roots scalar frontend result.2)) <$>
              (implementation setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar query).run before =
              Prod.map id nativeView <$>
                (RegistrationNativeExperiment.trusted setup checks representation created source query).run
                  (restore roots scalar frontend before) :=
            query_source setup checks wire route representation created scalar credential roots query allowed.1 (frontend, before)
          rw [actual]
        _ = _ := by
          rw [bind_map_left]
          apply bind_congr
          rintro ⟨value, after⟩
          exact (RegistrationNativeMainViewLift.trusted_program setup checks representation created (next value) after).symm

/-- A complete adaptive local owner program retains its actual native result, roster, pool and World after only the named analysis view. The syntactic callback condition excludes the selected-role capability absent from the concrete local controller. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (allowed : work.AllQueriesSatisfy (Allowed (KemSK := KemSK))) (before : State n KemSK source) :
    (fun result => (result.1, project roots scalar before.1 result.2)) <$>
      (close setup created.seed scalar (simulateQ
        (RegistrationNativePublicInterpreter.handler setup wire route (RegistrationNativeMldsa.owned source credential))
        (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
          (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work)))).run before.2 =
      Prod.map id nativeView <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run
          (restore roots scalar before.1 before.2) := by
  rw [close_program]
  exact program_project setup checks wire route representation created scalar credential roots work allowed before.1 before.2

end BeaconcryptCore.Computational.RegistrationNativePublicSourceTrusted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceTrusted.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceTrusted.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceTrusted.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceTrusted.program_source
