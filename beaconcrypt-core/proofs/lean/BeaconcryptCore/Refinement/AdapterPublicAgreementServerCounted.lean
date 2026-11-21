-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The exact source private-capture/native-role coupling commutes with the original World uniform-query counter. Source captures retain the updated caller RNG and opaque generated key. Projection forgets those private representations while retaining every actual native ephemeral scalar and complete World poststate. This module does not identify a separately implemented SDK platform dictionary. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementPrimitiveModel (Model)
open AdapterPublicAgreementServerNative (Entropy keys project)
open BeaconcryptCore.Computational RegistrationAgreementExecutor

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

theorem sampled_map {n : Nat} {Input Output : Type} (observe : Input → Output) (work : ProbComp Input)
    (world : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.sampled (observe <$> work)).run world =
      Prod.map observe id <$> (PqxdhRecordLiftWorld.sampled work).run world := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, simulateQ_map,
    state_map_apply, bind_pure_comp, Functor.map_map]
  rfl

variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : CryptoOperations (RustT ProbComp)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}
noncomputable section

theorem program {n : Nat} {Value : Type} (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (before : AdapterPublicAgreementServerCapture.State R)
    (work : OracleComp Spec Value) (covered : RegistrationAgreementRoleCoverage.Bound work)
    (world : PqxdhRecordLiftWorld.State n) :
    Prod.map (Prod.map id (project view)) id <$>
      (PqxdhRecordLiftWorld.sampled
        ((simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity)) work).run before)).run world =
      (PqxdhRecordLiftWorld.sampled
        ((simulateQ (AdapterPublicAgreementServerNative.implementation model identity) work).run (project view before))).run world := by
  rw [← sampled_map, AdapterPublicAgreementServerNative.program model entropy identity before work covered]

theorem server {n : Nat} (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (world : PqxdhRecordLiftWorld.State n) :
    Prod.map (Prod.map id (fun after => (project view after).2)) id <$>
      (PqxdhRecordLiftWorld.sampled
        ((simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
          (RegistrationAgreementExecutor.server control status authenticated)).run ⟨rng, false, .None⟩)).run world =
      (PqxdhRecordLiftWorld.sampled
        ((simulateQ (RegistrationAgreementShared.auxiliary setup.source
          (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
          (RegistrationAgreementExecutor.server control status authenticated)).run RegistrationServerRoleBackend.empty)).run world := by
  rw [← sampled_map, AdapterPublicAgreementServerNative.server model entropy identity rng control status authenticated]

theorem lookup {n : Nat} (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (pending : peer.RegistrationLookup) (consumed : Bool)
    (world : PqxdhRecordLiftWorld.State n) :
    Prod.map (Prod.map id (fun after => (project view after).2)) id <$>
      (PqxdhRecordLiftWorld.sampled
        ((simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
          (continueWith (pending.resume consumed) (drive 9))).run ⟨rng, false, .None⟩)).run world =
      (PqxdhRecordLiftWorld.sampled
        ((simulateQ (RegistrationAgreementShared.auxiliary setup.source
          (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
          (continueWith (pending.resume consumed) (drive 9))).run RegistrationServerRoleBackend.empty)).run world := by
  rw [← sampled_map, AdapterPublicAgreementServerNative.lookup model entropy identity rng pending consumed]
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted.sampled_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted.sampled_map

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted.server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerCounted.lookup
