-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementServerWorld
import BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! After the actual replay lookup admits a Fresh call, the literal source query handler, full private RNG/captures and same counted trace refine the actual full native Server agreement and its indexed source evaluator. Every complete native state field is restored; the private KEM pool is retained. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementServerNativeWorld
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementPrimitiveModel (Model)
open AdapterPublicAgreementServerNative (Entropy keys)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open RegistrationAgreementQueryTrace (trace)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : CryptoOperations (RustT ProbComp)]
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

noncomputable def restore (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (((RustM agreement.AgreementEffect) × RegistrationAgreementQueryTrace.Trace) ×
      AdapterPublicAgreementInterpreter.Capture R) × PqxdhRecordLiftWorld.State n) :
    RustM (RustM agreement.AgreementEffect × RegistrationNativeExperiment.State n KemSK source) := do
  let (value, world) ← AdapterPublicAgreementServerWorld.restoreSource view before.server.world result
  .ok (value, { before with server := { before.server with world := world } })

noncomputable section
theorem native (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (identityView : view.edSecret identity = created.seed) (rng : R) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    restore view before <$>
      (PqxdhRecordLiftWorld.sampled
        (((simulateQ (AdapterPublicAgreementInterpreter.handler generator (keys identity))
          (trace (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) [])).run ⟨rng, .None, .None⟩).run)).run before.server.world.world.1 =
      RustM.ok <$> (RegistrationNativeExperiment.server
        (RegistrationServerNativeSource.agree setup checks model.representation created packet authenticated)).run before := by
  have actual := AdapterPublicAgreementServerWorld.source_world model entropy identity rng before.server.control authenticated before.server.world
  rw [identityView] at actual
  have lifted := congrArg (fun work => (fun result => do
      let (value, world) ← result
      .ok (value, { before with server := { before.server with world := world } })) <$> work) actual
  unfold restore
  simp only [Functor.map_map, bind_tc_ok, RegistrationNativeExperiment.server,
    RegistrationServerNativeSource.agree, RegistrationReplaySchedule.begin_eq, fresh, Bool.false_eq_true,
    ↓reduceIte, StateT.run] at lifted ⊢
  convert lifted using 1
  apply congrArg (fun function => function <$> _)
  funext result
  cases reply : AdapterPublicAgreementServerWorld.restoreSource view before.server.world result with
  | ok pair => cases pair; rfl
  | fail error => rfl
  | div => rfl
theorem indexed (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (identityView : view.edSecret identity = created.seed) (rng : R) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    restore view before <$>
      (PqxdhRecordLiftWorld.sampled
        (((simulateQ (AdapterPublicAgreementInterpreter.handler generator (keys identity))
          (trace (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) [])).run ⟨rng, .None, .None⟩).run)).run before.server.world.world.1 =
      RustM.ok <$> (Prod.map id (fun current => RegistrationNativeKemServerState.toNative current.1 current.2) <$>
        (RegistrationNativeKemCountedTrusted.execute setup
          (RegistrationNativeKemCountedServerPrimitive.agree setup checks model.representation created authenticated)).run
            (RegistrationNativeKemCountedTrusted.project before)) := by
  rw [RegistrationNativeKemCountedServerSource.agree_native setup checks model.representation created packet authenticated before]
  exact native model entropy identity created identityView rng packet authenticated before fresh

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementServerNativeWorld

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerNativeWorld.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerNativeWorld.native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerNativeWorld.indexed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerNativeWorld.indexed
