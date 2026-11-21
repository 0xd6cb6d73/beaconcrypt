-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative
import BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The same actual Core request tree returns its complete query/reply trace in the source-capture/native-role coupling. Readiness erasure preserves this trace, including all root callbacks and rejected primitive replies. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementServerTrace
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementPrimitiveModel (Model)
open AdapterPublicAgreementServerNative (Entropy keys project)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open RegistrationAgreementQueryTrace (Trace trace)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : CryptoOperations (RustT ProbComp)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}
noncomputable section

theorem server (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (journal : Trace) :
    Prod.map id (fun after => (project view after).2) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
        (trace (RegistrationAgreementExecutor.server control status authenticated) journal)).run ⟨rng, false, .None⟩ =
      (simulateQ (RegistrationAgreementShared.auxiliary setup.source
        (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
        (trace (RegistrationAgreementExecutor.server control status authenticated) journal)).run RegistrationServerRoleBackend.empty := by
  have projected := AdapterPublicAgreementServerNative.program model entropy identity ⟨rng, false, .None⟩ _
    (RegistrationAgreementQueryTrace.bound _ (RegistrationAgreementRoleCoverage.server_bound control status authenticated) journal)
  calc
    _ = Prod.map id Prod.snd <$> (Prod.map id (project view) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
        (trace (RegistrationAgreementExecutor.server control status authenticated) journal)).run ⟨rng, false, .None⟩) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by
      rw [projected]
      change Prod.map id Prod.snd <$>
        (simulateQ (RegistrationAgreementGuardState.implementation
          (RegistrationAgreementShared.auxiliary setup.source
            (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))) _).run
          (false, RegistrationServerRoleBackend.empty) = _
      rw [RegistrationAgreementGuardState.program]
      have erased := congrArg (fun work => work.run RegistrationServerRoleBackend.empty)
        (RegistrationAgreementQueryTraceGuard.server
          (RegistrationAgreementShared.auxiliary setup.source
            (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
          control status authenticated journal)
      simpa only [StateT.run_map, Functor.map_map, Prod.map, id_eq] using erased

theorem lookup (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (pending : peer.RegistrationLookup) (consumed : Bool)
    (journal : Trace) :
    Prod.map id (fun after => (project view after).2) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
        (trace (continueWith (pending.resume consumed) (drive 9)) journal)).run ⟨rng, false, .None⟩ =
      (simulateQ (RegistrationAgreementShared.auxiliary setup.source
        (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
        (trace (continueWith (pending.resume consumed) (drive 9)) journal)).run RegistrationServerRoleBackend.empty := by
  have projected := AdapterPublicAgreementServerNative.program model entropy identity ⟨rng, false, .None⟩ _
    (RegistrationAgreementQueryTrace.bound _ (RegistrationAgreementRoleCoverage.lookup_bound pending consumed) journal)
  calc
    _ = Prod.map id Prod.snd <$> (Prod.map id (project view) <$>
      (simulateQ (AdapterPublicAgreementServerCapture.implementation model (keys identity))
        (trace (continueWith (pending.resume consumed) (drive 9)) journal)).run ⟨rng, false, .None⟩) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by
      rw [projected]
      change Prod.map id Prod.snd <$>
        (simulateQ (RegistrationAgreementGuardState.implementation
          (RegistrationAgreementShared.auxiliary setup.source
            (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))) _).run
          (false, RegistrationServerRoleBackend.empty) = _
      rw [RegistrationAgreementGuardState.program]
      have erased := congrArg (fun work => work.run RegistrationServerRoleBackend.empty)
        (RegistrationAgreementQueryTraceGuard.lookup
          (RegistrationAgreementShared.auxiliary setup.source
            (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
          pending consumed journal)
      simpa only [StateT.run_map, Functor.map_map, Prod.map, id_eq] using erased
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementServerTrace

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerTrace.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerTrace.server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerTrace.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerTrace.lookup
