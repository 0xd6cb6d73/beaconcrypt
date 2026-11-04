-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementServerTrace
import BeaconcryptCore.Computational.RegistrationAgreementWorldTrace
import BeaconcryptCore.Computational.RegistrationServerBackendReset
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The same literal source request handler is interpreted with its full opaque captures and caller RNG before projecting to the actual native Server role, complete query/reply trace and counted shared World. No whole handler equality is supplied as a contract. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementServerWorld
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementPrimitiveModel (Model)
open AdapterPublicAgreementServerNative (Entropy keys)
open AdapterPublicAgreementInterpreter (Capture)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open RegistrationAgreementQueryTrace (Trace trace)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : CryptoOperations (RustT ProbComp)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

def project (view : AdapterPublicWrapperState.MaterialView source KemSK) (after : Capture R) : RegistrationServerRoleBackend.State :=
  ⟨_root_.Option.map (fun key => view.kxSecret key.secret_key) after.ephemeral⟩

def restoreRole {n : Nat} {Value : Type} (before : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (result : RustM ((Value × Trace) × RegistrationServerRoleBackend.State) × PqxdhRecordLiftWorld.State n) :
    RustM (Value × RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State) := do
  let value ← result.1
  .ok (RegistrationAgreementWorldTrace.restore before (value, result.2))

def restoreSource {n : Nat} {Value : Type} (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (before : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (result : RustM ((Value × Trace) × Capture R) × PqxdhRecordLiftWorld.State n) :
    RustM (Value × RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State) :=
  restoreRole before ((Prod.map id (project view) <$> result.1), result.2)

noncomputable section
theorem source_trace (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (journal : Trace) :
    (fun reply => Prod.map id (project view) <$> reply) <$>
      ((simulateQ (AdapterPublicAgreementInterpreter.handler generator (keys identity))
        (trace (RegistrationAgreementExecutor.server control status authenticated) journal)).run ⟨rng, .None, .None⟩).run =
      RustM.ok <$> (simulateQ (RegistrationAgreementShared.auxiliary setup.source
        (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
        (trace (RegistrationAgreementExecutor.server control status authenticated) journal)).run RegistrationServerRoleBackend.empty := by
  rw [AdapterPublicAgreementPrimitiveModel.program model (keys identity), RustT.run_lift]
  have captured := AdapterPublicAgreementServerCapture.program model (keys identity) ⟨rng, false, .None⟩
    (trace (RegistrationAgreementExecutor.server control status authenticated) journal)
  change (simulateQ (AdapterPublicAgreementPrimitiveModel.implementation model (keys identity))
    (trace (RegistrationAgreementExecutor.server control status authenticated) journal)).run ⟨rng, .None, .None⟩ = _ at captured
  rw [captured, Functor.map_map]
  have coupled := AdapterPublicAgreementServerTrace.server model entropy identity rng control status authenticated journal
  rw [← coupled]
  simp only [Functor.map_map]
  apply congrArg (fun function => function <$> _)
  funext pair
  rcases pair with ⟨value, after⟩
  rfl
theorem source_world {n : Nat}
    (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit)
    (before : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State) :
    restoreSource view before <$>
      (PqxdhRecordLiftWorld.sampled
        (((simulateQ (AdapterPublicAgreementInterpreter.handler generator (keys identity))
          (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) [])).run ⟨rng, .None, .None⟩).run)).run before.world.1 =
      RustM.ok <$> (simulateQ (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before := by
  have coupled := source_trace model entropy identity rng control .Fresh authenticated []
  rw [← RegistrationServerBackendReset.server_trace setup checks model.representation (view.edSecret identity)
    control authenticated [] before.auxiliary] at coupled
  have counted := congrArg (fun work => (PqxdhRecordLiftWorld.sampled work).run before.world.1) coupled
  rw [RegistrationAgreementSampledState.sampled_map, RegistrationAgreementSampledState.sampled_map] at counted
  rw [RegistrationAgreementWorldTrace.actual, Functor.map_map]
  calc
    _ = restoreRole before <$>
      (Prod.map (fun reply => Prod.map id (project view) <$> reply) id <$>
        (PqxdhRecordLiftWorld.sampled
          (((simulateQ (AdapterPublicAgreementInterpreter.handler generator (keys identity))
            (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) [])).run ⟨rng, .None, .None⟩).run)).run before.world.1) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by
      rw [counted, Functor.map_map]
      rfl

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementServerWorld

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerWorld.source_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerWorld.source_trace

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerWorld.source_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerWorld.source_world
