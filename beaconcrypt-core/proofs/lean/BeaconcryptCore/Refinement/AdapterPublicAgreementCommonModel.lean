-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter
import BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries
import BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel
import BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage
import BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional
import BeaconcryptCore.Refinement.AdapterPublicAgreementPublicConversion
import BeaconcryptCore.Refinement.AdapterPublicAgreementHkdf
import BeaconcryptCore.Refinement.AdapterPublicAgreementKemDecapsulation
import BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! A reached-field source primitive model for the NoEntropy Beacon path. It has no generation or encapsulation contract; actual Core query coverage excludes those branches on every reply path. Each source-query equality is derived from individual selected primitive functional/sampling contracts. No aggregate handler, controller, acceptance or security conclusion is an assumed field. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open AdapterPublicAgreementFields (Array32 CipherArray KemArray LocalIdentity KeyPair Keys)
open AdapterPublicAgreementInterpreter (Capture)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open PqxdhRootTableInitialization (rootArray)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

structure Model (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) where
  representation : RegistrationServerRoleBackend.ConvertedIdentity setup
  scalar : AdapterPublicAgreementFunctional.Scalar (m := m) setup.source.crypto
  getters : AdapterPublicAgreementFunctional.KeyGetters (m := m) view
  identity : AdapterPublicAgreementFunctional.IdentityConversion (m := m) view representation.converted
  conversion : AdapterPublicAgreementPublicConversion.Contract (m := m) setup.source.crypto view
  hkdf : AdapterPublicAgreementHkdf.Contract (m := m) setup.source.crypto
  decapsulate : CipherArray → KemSK → m (core.option.Option Array32)
  decapView : AdapterPublicAgreementKemDecapsulation.Views
  cipherParsing : AdapterPublicAgreementKemDecapsulation.Ciphertext (m := m) decapView
  shared : AdapterPublicAgreementKemDecapsulation.Shared (m := m) decapView
  decap : AdapterPublicAgreementKemDecapsulation.Contract (m := m) view decapView shared decapsulate

variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}
open AdapterPublicAgreementPrimitiveModel (selected)

noncomputable def decapsulate (model : Model (m := m) setup view)
    (input : core.option.Option CipherArray) (secret : core.option.Option material.KemSecretKey) : m (core.option.Option Array32) :=
  match input, secret with
  | .Some input, .Some secret => model.decapsulate input (view.kemSecret secret)
  | _, _ => pure .None

omit material primitive crypto [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl

omit material primitive crypto in
private theorem map_lift {A B : Type} (function : A → B) (work : m A) :
    function <$> RustT.lift work = RustT.lift (function <$> work) := by
  apply RustT.ext
  change ((RustM.ok <$> work) >>= fun result : RustM A =>
    match result with
    | .ok value => (pure (.ok (function value)) : m (RustM B))
    | .fail error => pure (.fail error)
    | .div => pure .div) = _
  simp only [bind_map_left, bind_pure_comp, RustT.run_lift, Functor.map_map]

noncomputable section

theorem decapsulate_source (model : Model (m := m) setup view)
    (input : core.option.Option CipherArray) (secret : core.option.Option material.KemSecretKey) :
    AdapterPublicAgreementFields.decapsulate (m := m) input secret = RustT.lift (decapsulate model input secret) := by
  cases input with
  | none => exact (RustT.lift_pure _).symm
  | some input => cases secret with
    | none =>
      unfold AdapterPublicAgreementFields.decapsulate
      dsimp only
      rw [model.cipherParsing.operation, pure_bind]
      exact (RustT.lift_pure _).symm
    | some secret =>
      exact AdapterPublicAgreementKemDecapsulation.decoded view model.decapView model.cipherParsing model.shared
        model.decapsulate model.decap input secret
def dh (_model : Model (m := m) setup view) (keys : Keys)
    (before : Capture R) (request : agreement.DhRequest) : core.option.Option Array32 :=
  match selected (view := view) keys before request.secret_role with
  | .None => .None
  | .Some secret => AdapterPublicAgreementFunctional.scalarReply setup.source.crypto secret request.public_key

theorem dh_source (model : Model (m := m) setup view) (keys : Keys)
    (before : Capture R) (request : agreement.DhRequest) :
    AdapterPublicAgreementFields.dh (m := m) generator keys before.localIdentity before.ephemeral request =
      pure (dh model keys before request) := by
  rcases request with ⟨role, publicKey⟩
  cases role with
  | LocalIdentity =>
    cases present : before.localIdentity with
    | none =>
      simp only [AdapterPublicAgreementFields.dh, dh, selected, present,
        core.option.Option.as_ref, AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind]
    | some secret =>
      simpa only [AdapterPublicAgreementFields.dh, dh, selected, present,
        core.option.Option.as_ref, AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind,
        beaconcrypt_public_request.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832] using
        AdapterPublicAgreementFunctional.local_dh generator setup.source.crypto model.scalar secret publicKey
  | ServerEphemeral =>
    cases present : before.ephemeral with
    | none =>
      simp only [AdapterPublicAgreementFields.dh, dh, selected, present,
        core.option.Option.as_ref, AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind]
    | some secret =>
      simpa only [AdapterPublicAgreementFields.dh, dh, selected, present,
        core.option.Option.as_ref, AdapterPublicWrapperRequestMonad.Option.and_then, lift_ok, pure_bind,
        beaconcrypt_public_request.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832] using
        AdapterPublicAgreementFunctional.ephemeral_dh generator view model.getters setup.source.crypto model.scalar secret publicKey
  | BeaconPrekey =>
    cases present : keys.beacon_prekey with
    | none =>
      simp only [AdapterPublicAgreementFields.dh, dh, selected, present,
        AdapterPublicWrapperRequestMonad.Option.and_then]
    | some secret =>
      simpa only [AdapterPublicAgreementFields.dh, dh, selected, present,
        AdapterPublicWrapperRequestMonad.Option.and_then,
        beaconcrypt_public_request.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832] using
        AdapterPublicAgreementFunctional.prekey_dh generator view model.getters setup.source.crypto model.scalar secret publicKey
  | BeaconOneTime =>
    cases present : keys.beacon_one_time with
    | none =>
      simp only [AdapterPublicAgreementFields.dh, dh, selected, present,
        AdapterPublicWrapperRequestMonad.Option.and_then]
    | some secret =>
      simpa only [AdapterPublicAgreementFields.dh, dh, selected, present,
        AdapterPublicWrapperRequestMonad.Option.and_then,
        beaconcrypt_public_request.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832] using
        AdapterPublicAgreementFunctional.one_time_dh generator view model.getters setup.source.crypto model.scalar secret publicKey

noncomputable def implementation (model : Model (m := m) setup view) (keys : Keys) :
    QueryImpl Spec (StateT (Capture R) m)
  | .convertPublic key => pure (RegistrationPublicConversion.convert setup.source.crypto key)
  | .convertSecret _ => do
    modify fun before => { before with localIdentity := .Some ⟨model.representation.converted (view.edSecret keys.identity_secret)⟩ }
    pure true
  | .generate _ => pure .None
  | .encapsulate _ => pure .None
  | .decapsulate input => StateT.lift (decapsulate model input keys.beacon_kem)
  | .dh request => do
    let before ← get
    pure (dh model keys before request)
  | .root request => pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))

theorem query (model : Model (m := m) setup view) (keys : Keys)
    (request : Request) (before : Capture R) (allowed : RegistrationAgreementBeaconCoverage.Allowed request) :
    (AdapterPublicAgreementInterpreter.handler generator keys request).run before =
      RustT.lift ((implementation model keys request).run before) := by
  cases request with
  | convertPublic key =>
    simp only [AdapterPublicAgreementInterpreter.handler, implementation,
      AdapterPublicAgreementPublicConversion.converted_public setup.source.crypto view model.conversion,
      StateT.run_lift, StateT.run_pure,  RustT.lift_pure, pure_bind]
  | convertSecret role =>
    simp only [AdapterPublicAgreementInterpreter.handler, implementation,
      AdapterPublicAgreementFunctional.converted_identity view model.representation.converted model.identity,
      StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
      pure_bind, core.option.Option.is_some, lift_ok,  RustT.lift_pure]
  | generate role => exact False.elim allowed
  | encapsulate input => exact False.elim allowed
  | decapsulate input =>
    simp only [AdapterPublicAgreementInterpreter.handler, implementation, decapsulate_source model,
      StateT.run_lift]
    apply RustT.ext
    simp only [  bind_pure_comp, map_lift, RustT.run_lift, Functor.map_map]
  | dh request =>
    simp only [AdapterPublicAgreementInterpreter.handler, implementation, dh_source model,
      StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure,
      pure_bind,  RustT.lift_pure]
  | root request =>
    simp only [AdapterPublicAgreementInterpreter.handler, implementation,
      AdapterPublicAgreementHkdf.root setup.source.crypto model.hkdf,
      StateT.run_lift, StateT.run_pure,  RustT.lift_pure, pure_bind]

theorem program {Value : Type} (model : Model (m := m) setup view) (keys : Keys)
    (work : OracleComp Spec Value) (before : Capture R) (bounded : RegistrationAgreementBeaconCoverage.Bound work) :
    (simulateQ (AdapterPublicAgreementInterpreter.handler generator keys) work).run before =
      RustT.lift ((simulateQ (implementation model keys) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, RustT.lift_pure]
  | query_bind request next ih =>
    rw [RegistrationAgreementBeaconCoverage.Bound, isQueryBound_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query model keys request before bounded.1]
    have rest : ∀ reply after,
        (simulateQ (AdapterPublicAgreementInterpreter.handler generator keys) (next reply)).run after =
          RustT.lift ((simulateQ (implementation model keys) (next reply)).run after) :=
      fun reply after => ih reply after (bounded.2 reply)
    simp only [rest]
    exact (RustT.lift_bind _ _).symm

theorem beacon_execute (model : Model (m := m) setup view) (keys : Keys)
    (authenticated : registration.AuthenticatedResponse) (rng : R) :
    ((do let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
         beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng) :
      RustT m (agreement.AgreementEffect × R)).run =
      (fun result => do
        let completed ← result.1
        .ok (completed, result.2.rng)) <$>
        (simulateQ (implementation model keys) (RegistrationAgreementExecutor.beacon authenticated)).run
          ⟨rng, .None, .None⟩ := by
  rw [AdapterPublicAgreementSourceEntries.beacon generator keys authenticated rng]
  unfold AdapterPublicAgreementSourceEntries.run
  rw [program model keys _ _ (RegistrationAgreementBeaconCoverage.beacon_bound authenticated)]
  simp only [RustT.run_bind, RustT.run_lift, RustT.run_liftRust, RustT.run_pure, bind_map_left, pure_bind]
  rw [← bind_pure_comp]
  apply bind_congr
  rintro ⟨result, after⟩
  cases result <;> rfl

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.decapsulate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.decapsulate_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.dh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.dh_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.beacon_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel.beacon_execute
