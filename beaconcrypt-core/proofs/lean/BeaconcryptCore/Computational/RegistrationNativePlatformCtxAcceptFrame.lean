-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
/-! The actual post-authentication source collector and one-use retention commute with replacement of the shared CTX cache. Each agreement primitive keeps its literal sampler, native auxiliary output, request journal and signing receipts; no whole controller law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
open RegistrationNativePlatformCtxSdkCoupling (Coupled replace realize)
variable {n : Nat} {I KemSK Auxiliary Platform A : Type} {base : OracleSpec I}

/-- The literal native agreement leaf samples the same primitive and retains every request/receipt field under cache replacement. -/
theorem agreement_query (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (cache : RegistrationNativePlatformCtxBackend.Cache)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id (fun current => RegistrationNativePlatformCtxLocal.attach current
      (RegistrationNativePlatformCtxCacheFrame.replace cache current.world.1)) <$>
      (RegistrationWorldAgreement.agreement source primitive query).run before =
      (RegistrationWorldAgreement.agreement source primitive query).run
        (RegistrationNativePlatformCtxLocal.attach before (RegistrationNativePlatformCtxCacheFrame.replace cache before.world.1)) := by
  have framed := RegistrationNativePlatformCtxCacheFrame.sampled cache
    ((RegistrationAgreementShared.auxiliary source primitive query).run before.auxiliary) before.world.1
  have mapped := congrArg (fun action => (fun result => (result.1.1,
    RegistrationWorldAgreement.State.mk result.1.2 (before.requests ++ RegistrationWorldAgreement.recorded query)
      before.recordRequests (result.2, before.world.2))) <$> action) framed
  simpa only [RegistrationWorldAgreement.agreement, StateT.run, bind_pure_comp, Functor.map_map,
    RegistrationNativePlatformCtxLocal.attach, Prod.map_def, id_eq] using mapped

/-- The same cache frame holds through the actual full adaptive agreement tree. -/
theorem agreement_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (cache : RegistrationNativePlatformCtxBackend.Cache)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id (fun current => RegistrationNativePlatformCtxLocal.attach current
      (RegistrationNativePlatformCtxCacheFrame.replace cache current.world.1)) <$>
      (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run before =
      (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run
        (RegistrationNativePlatformCtxLocal.attach before (RegistrationNativePlatformCtxCacheFrame.replace cache before.world.1)) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (agreement_query source primitive · cache) work before

/-- Actual SDK replay lookup and collected source agreement have no hash cache dependence. -/
theorem agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (cache : RegistrationNativePlatformCtxBackend.Cache) (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id (replace cache) <$> (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before =
      (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run (replace cache before) := by
  have framed := agreement_program setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed)
    (RegistrationReplaySchedule.begin before.control authenticated before.consumed) cache before.world
  have mapped := congrArg (fun action => (fun result => (result.1, {replace cache before with world := result.2})) <$> action) framed
  simpa only [RegistrationServerNativeSource.agree, StateT.run, Functor.map_map, replace, Prod.map_def, id_eq] using mapped

/-- The literal one-use token insertion changes no cache or signing receipt coordinate. -/
theorem retain (created : PqxdhLiveServerConstruction.Created Unit) (accepted : agreement.ServerAgreement)
    (cache : RegistrationNativePlatformCtxBackend.Cache) (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id (replace cache) <$> (RegistrationServerNativeSource.retain created accepted).run before =
      (RegistrationServerNativeSource.retain created accepted).run (replace cache before) := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore, StateT.run, replace]
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div => simp only [map_pure]; rfl
  | ok selected => rcases selected with ⟨token, history⟩; cases token <;> simp only [map_pure] <;> rfl

noncomputable def ordinary (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp A) :
    M (RegistrationServerFrontendCompiler.State n) Platform A :=
  privateWork (RegistrationNativePlatformInterpret.state RegistrationNativePlatformCtxBackend.coin work)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before
private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

/-- Ordinary primitive sampling crosses the shared backend only at its uniform branch, retaining the same complete native/platform state. -/
theorem ordinary_source (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp A)
    (frame : ∀ cache before, Prod.map id (replace cache) <$> work.run before = work.run (replace cache before)) :
    Coupled (ordinary (Platform := Platform) work)
      (RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins work) := by
  intro before
  unfold ordinary
  rw [RegistrationNativePlatformCtxRunner.private_run]
  have framed := frame before.2.1 before.1.1
  have mapped := congrArg (fun action => (fun result => (result.1, (result.2, before.1.2))) <$> action) framed
  simpa only [RegistrationNativePlatformInterpret.state, RegistrationNativePlatformServerSdk.liftNative,
    RegistrationNativePlatformCtxBackend.coins, RegistrationNativePlatformMldsaProgram.lift_coins,
    RegistrationNativePlatformPackedState.pack, StateT.run, state_map_apply, state_lift_apply,
    bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.agreement_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.agreement_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.agreement_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.agreement_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.agree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.retain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame.ordinary_source
