-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementServerNative
import BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The literal SDK Server agreement entry and replay-lookup executor have the exact actual native role result under the individually stated selected entropy/backend interpretations. Only the private caller RNG is projected from this result comparison; its full actual updates and opaque generated key remain in the source capture correspondence. No success assumption or aggregate controller law is used. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementServerSource
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open AdapterPublicAgreementPrimitiveModel (Model)
open AdapterPublicAgreementServerNative (Entropy keys project)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : CryptoOperations (RustT ProbComp)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

noncomputable section

theorem run_result (model : Model (m := ProbComp) generator setup checks view) (keys : Keys)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R) :
    (fun result => Prod.fst <$> result) <$>
      (AdapterPublicAgreementSourceEntries.run generator keys work rng).run =
      Prod.fst <$> (simulateQ (AdapterPublicAgreementServerCapture.implementation model keys) work).run ⟨rng, false, .None⟩ := by
  unfold AdapterPublicAgreementSourceEntries.run
  rw [AdapterPublicAgreementPrimitiveModel.program model keys]
  simp only [RustT.run_bind, RustT.run_lift]
  have captured := AdapterPublicAgreementServerCapture.program model keys ⟨rng, false, .None⟩ work
  change (simulateQ (AdapterPublicAgreementPrimitiveModel.implementation model keys) work).run
    ⟨rng, .None, .None⟩ = _ at captured
  rw [captured]
  simp only [map_bind, bind_map_left, RustT.run_liftRust, RustT.run_pure, pure_bind, Functor.map_map]
  conv_rhs => rw [← bind_pure_comp]
  apply bind_congr
  rintro ⟨reply, after⟩
  cases reply <;> simp only [Prod.map, id_eq, map_pure] <;> rfl

theorem server (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) :
    (fun result => Prod.fst <$> result) <$>
      ((do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control status authenticated)
           beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT ProbComp) generator phase (keys identity) rng) :
        RustT ProbComp (agreement.AgreementEffect × R)).run =
      Prod.fst <$> (simulateQ (RegistrationAgreementShared.auxiliary setup.source
        (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
          (RegistrationAgreementExecutor.server control status authenticated)).run RegistrationServerRoleBackend.empty := by
  rw [AdapterPublicAgreementSourceEntries.server generator (keys identity) control status authenticated rng,
    run_result model]
  have actual := congrArg (fun work => Prod.fst <$> work)
    (AdapterPublicAgreementServerNative.server model entropy identity rng control status authenticated)
  simpa only [Functor.map_map, Prod.map, id_eq] using actual

theorem lookup (model : Model (m := ProbComp) generator setup checks view) (entropy : Entropy model)
    (identity : material.EdSecretKey) (rng : R) (pending : peer.RegistrationLookup) (consumed : Bool) :
    (fun result => Prod.fst <$> result) <$>
      ((do let phase ← AdapterRecordRequestMonad.liftRust (pending.resume consumed)
           beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT ProbComp) generator phase (keys identity) rng) :
        RustT ProbComp (agreement.AgreementEffect × R)).run =
      Prod.fst <$> (simulateQ (RegistrationAgreementShared.auxiliary setup.source
        (RegistrationServerRoleBackend.native setup checks model.representation (view.edSecret identity)))
          (continueWith (pending.resume consumed) (drive 9))).run RegistrationServerRoleBackend.empty := by
  rw [AdapterPublicAgreementSourceEntries.lookup generator (keys identity) pending consumed rng,
    run_result model]
  have actual := congrArg (fun work => Prod.fst <$> work)
    (AdapterPublicAgreementServerNative.lookup model entropy identity rng pending consumed)
  simpa only [Functor.map_map, Prod.map, id_eq] using actual
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementServerSource

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerSource.run_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerSource.run_result

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerSource.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerSource.server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerSource.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerSource.lookup
