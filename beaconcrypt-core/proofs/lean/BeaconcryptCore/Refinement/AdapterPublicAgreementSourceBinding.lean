-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel
import BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries
import BeaconcryptCore.Refinement.AdapterPublicServerToken
import BeaconcryptCore.Computational.RegistrationAgreementNestedState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual source Server agreement preserves the authenticated identity in every successful result. Private RNG updates, opaque generated keys and external shared poststate are retained in the source run; only its returned binding is inspected. The source interpretation is derived from the selected individual primitive contracts. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementPrimitiveModel (Model)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}
noncomputable section

theorem run (model : Model (m := m) generator setup checks view) (keys : Keys)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R) :
    (AdapterPublicAgreementSourceEntries.run generator keys work rng).run =
      (fun result => do
        let completed ← result.1
        .ok (completed, result.2.rng)) <$>
        (simulateQ (AdapterPublicAgreementPrimitiveModel.implementation model keys) work).run ⟨rng, .None, .None⟩ := by
  unfold AdapterPublicAgreementSourceEntries.run
  rw [AdapterPublicAgreementPrimitiveModel.program model keys]
  simp only [RustT.run_bind, RustT.run_lift, RustT.run_liftRust, RustT.run_pure, bind_map_left, pure_bind]
  rw [← bind_pure_comp]
  apply bind_congr
  rintro ⟨result, after⟩
  cases result <;> rfl
end
section Shared
variable {S : Type}
variable [sharedCrypto : CryptoOperations (RustT (StateT S ProbComp))]
omit crypto [Monad m] [LawfulMonad m] in
theorem server_binding (model : Model (m := StateT S ProbComp) generator setup checks view) (keys : Keys)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (rng nextRng : R) (before after : S)
    (supported : (.ok (.ServerComplete completed, nextRng), after) ∈ support
      (((AdapterPublicAgreementSourceEntries.run (m := StateT S ProbComp) generator keys
        (RegistrationAgreementExecutor.server control status authenticated) rng).run).run before)) :
    completed.binding = authenticated.binding := by
  rw [run model keys] at supported
  simp only [StateT.run_map, support_map] at supported
  obtain ⟨⟨⟨reply, capture⟩, sharedAfter⟩, called, returned⟩ := supported
  cases reply with
  | fail error | div => simp only [bind_tc_fail, bind_tc_div, Prod.mk.injEq, reduceCtorEq, false_and] at returned
  | ok result =>
    simp only [bind_tc_ok, Prod.mk.injEq, RustM.ok.injEq] at returned
    obtain ⟨⟨same, _rngSame⟩, stateSame⟩ := returned
    cases same
    cases stateSame
    apply RegistrationAgreementExecutor.interpreted_server_binding
      (RegistrationAgreementNestedState.implementation (AdapterPublicAgreementPrimitiveModel.implementation model keys))
      (⟨rng, .None, .None⟩, before) (capture, after) control status authenticated completed
    rw [RegistrationAgreementNestedState.program]
    change (.ok (.ServerComplete completed), (capture, after)) ∈ support
      ((fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((simulateQ (AdapterPublicAgreementPrimitiveModel.implementation model keys)
          (RegistrationAgreementExecutor.server control status authenticated)).run ⟨rng, .None, .None⟩).run before)
    rw [support_map]
    exact Set.mem_image_of_mem _ called

omit crypto [Monad m] [LawfulMonad m] in
theorem lookup_binding (model : Model (m := StateT S ProbComp) generator setup checks view) (keys : Keys)
    (pending : peer.RegistrationLookup) (consumed : Bool) (completed : agreement.ServerAgreement)
    (rng nextRng : R) (before after : S)
    (supported : (.ok (.ServerComplete completed, nextRng), after) ∈ support
      (((do let phase ← AdapterRecordRequestMonad.liftRust (pending.resume consumed)
            beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT (StateT S ProbComp))
              generator phase keys rng).run).run before)) :
    completed.binding = pending.authenticated.binding := by
  rw [AdapterPublicAgreementSourceEntries.lookup, AdapterPublicServerToken.lookup_program] at supported
  exact server_binding model keys pending.control _ pending.authenticated completed rng nextRng before after supported
end Shared
end BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding.run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding.server_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding.server_binding

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding.lookup_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding.lookup_binding
