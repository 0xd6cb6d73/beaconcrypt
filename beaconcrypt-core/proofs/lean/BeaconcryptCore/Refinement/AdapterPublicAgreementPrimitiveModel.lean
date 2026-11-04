-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementInterpreter
import BeaconcryptCore.Refinement.AdapterPublicAgreementGeneration
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
/-! A realized source primitive backend retaining the actual opaque private captures and caller RNG. This full entropy model requires the selected generation/encapsulation contracts and is not the NoEntropy Beacon instantiation; the Beacon uses only reached-field contracts and separate Core query coverage. Each source-query equality is derived from individual selected primitive functional/sampling contracts. No aggregate handler, controller, acceptance or security conclusion is an assumed field. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel
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

structure Model {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) where
  representation : RegistrationServerRoleBackend.ConvertedIdentity setup
  scalar : AdapterPublicAgreementFunctional.Scalar (m := m) setup.source.crypto
  getters : AdapterPublicAgreementFunctional.KeyGetters (m := m) view
  identity : AdapterPublicAgreementFunctional.IdentityConversion (m := m) view representation.converted
  conversion : AdapterPublicAgreementPublicConversion.Contract (m := m) setup.source.crypto view
  hkdf : AdapterPublicAgreementHkdf.Contract (m := m) setup.source.crypto
  sample : m PqxdhJointGapDh.ScalarBytes
  generation : AdapterPublicAgreementGeneration.Contract generator view
    (fun scalar => rootArray (setup.dh.publicKey scalar)) sample
  encapsulate : PqxdhKemIndCca.MlKem768PublicKey → m (CipherArray × Array32)
  encapView : AdapterPublicAgreementKemEncapsulation.Views
  encapGetters : AdapterPublicAgreementKemEncapsulation.Getters (m := m) encapView
  publicParsing : AdapterPublicAgreementKemEncapsulation.PublicKey (m := m) view
    (fun input => checks.kemKey (RegistrationRootInput.pqKey input))
  encap : AdapterPublicAgreementKemEncapsulation.Contract generator view encapView encapsulate
  decapsulate : CipherArray → KemSK → m (core.option.Option Array32)
  decapView : AdapterPublicAgreementKemDecapsulation.Views
  cipherParsing : AdapterPublicAgreementKemDecapsulation.Ciphertext (m := m) decapView
  shared : AdapterPublicAgreementKemDecapsulation.Shared (m := m) decapView
  decap : AdapterPublicAgreementKemDecapsulation.Contract (m := m) view decapView shared decapsulate

variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

noncomputable def encapsulate (model : Model (m := m) generator setup checks view)
    (input : core.option.Option KemArray) (rng : R) : m (core.option.Option (CipherArray × Array32) × R) :=
  match input with
  | .None => pure (.None, rng)
  | .Some input => match model.publicParsing.parse input with
    | .Err _ => pure (.None, rng)
    | .Ok key => (fun bytes => (.Some bytes, (model.encap.realize key bytes rng).2.2)) <$>
        model.encapsulate (RegistrationRootInput.pqKey input)

noncomputable def decapsulate (model : Model (m := m) generator setup checks view)
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

theorem encapsulate_source (model : Model (m := m) generator setup checks view)
    (input : core.option.Option KemArray) (rng : R) :
    AdapterPublicAgreementFields.encapsulate (m := m) generator input rng = RustT.lift (encapsulate model input rng) := by
  cases input with
  | none => exact (RustT.lift_pure _).symm
  | some input =>
    cases parsed : model.publicParsing.parse input with
    | Err error =>
      simpa only [encapsulate, parsed, RustT.lift_pure] using
        AdapterPublicAgreementKemEncapsulation.rejected generator view _ model.publicParsing input error parsed rng
    | Ok key =>
      simpa only [encapsulate, parsed] using
        AdapterPublicAgreementKemEncapsulation.admitted generator view _ model.publicParsing model.encapView
          model.encapGetters model.encapsulate model.encap input key parsed rng

theorem decapsulate_source (model : Model (m := m) generator setup checks view)
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
def selected (keys : Keys) (before : Capture R) (role : agreement.DhSecretRole) : core.option.Option Array32 :=
  match role with
  | .LocalIdentity => match before.localIdentity with
    | .None => .None
    | .Some key => .Some key.value
  | .ServerEphemeral => match before.ephemeral with
    | .None => .None
    | .Some key => .Some (rootArray (view.kxSecret key.secret_key))
  | .BeaconPrekey => match keys.beacon_prekey with
    | .None => .None
    | .Some key => .Some (rootArray (view.kxSecret key))
  | .BeaconOneTime => match keys.beacon_one_time with
    | .None => .None
    | .Some key => .Some (rootArray (view.kxSecret key))

def dh (_model : Model (m := m) generator setup checks view) (keys : Keys)
    (before : Capture R) (request : agreement.DhRequest) : core.option.Option Array32 :=
  match selected (view := view) keys before request.secret_role with
  | .None => .None
  | .Some secret => AdapterPublicAgreementFunctional.scalarReply setup.source.crypto secret request.public_key

theorem dh_source (model : Model (m := m) generator setup checks view) (keys : Keys)
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

noncomputable def implementation (model : Model (m := m) generator setup checks view) (keys : Keys) :
    QueryImpl Spec (StateT (Capture R) m)
  | .convertPublic key => pure (RegistrationPublicConversion.convert setup.source.crypto key)
  | .convertSecret _ => do
    modify fun before => { before with localIdentity := .Some ⟨model.representation.converted (view.edSecret keys.identity_secret)⟩ }
    pure true
  | .generate _ => do
    let before ← get
    let scalar ← StateT.lift model.sample
    let (key, nextRng) := model.generation.realize scalar before.rng
    set { before with rng := nextRng, ephemeral := .Some key }
    pure (.Some (rootArray (setup.dh.publicKey scalar)))
  | .encapsulate input => do
    let before ← get
    let (reply, nextRng) ← StateT.lift (encapsulate model input before.rng)
    set { before with rng := nextRng }
    pure reply
  | .decapsulate input => StateT.lift (decapsulate model input keys.beacon_kem)
  | .dh request => do
    let before ← get
    pure (dh model keys before request)
  | .root request => pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))

theorem query (model : Model (m := m) generator setup checks view) (keys : Keys)
    (request : Request) (before : Capture R) :
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
  | generate role =>
    simp only [AdapterPublicAgreementInterpreter.handler, implementation,
      AdapterPublicAgreementGeneration.fields generator view _ model.sample model.generation model.getters.publicKey,
      StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
    apply RustT.ext
    simp only [  bind_pure_comp, map_lift, RustT.run_lift, Functor.map_map]
  | encapsulate input =>
    simp only [AdapterPublicAgreementInterpreter.handler, implementation, encapsulate_source model,
      StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
    apply RustT.ext
    simp only [  bind_pure_comp, map_lift, RustT.run_lift, Functor.map_map]
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

theorem program {Value : Type} (model : Model (m := m) generator setup checks view) (keys : Keys)
    (work : OracleComp Spec Value) (before : Capture R) :
    (simulateQ (AdapterPublicAgreementInterpreter.handler generator keys) work).run before =
      RustT.lift ((simulateQ (implementation model keys) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, RustT.lift_pure]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, query model keys request, ih]
    exact (RustT.lift_bind _ _).symm

theorem execute (model : Model (m := m) generator setup checks view) (keys : Keys)
    (phase : agreement.AgreementEffect) (rng : R) (bounded : rank phase ≤ 9) :
    (beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng).run =
      (fun result => do
        let completed ← result.1
        .ok (completed, result.2.rng)) <$>
        (simulateQ (implementation model keys) (drive 9 phase)).run ⟨rng, .None, .None⟩ := by
  rw [AdapterPublicAgreementInterpreter.execute_nine generator keys phase rng bounded,
    AdapterPublicAgreementInterpreter.runDrive, program model keys]
  simp only [RustT.run_bind, RustT.run_lift, RustT.run_liftRust, RustT.run_pure, bind_map_left, pure_bind]
  rw [← bind_pure_comp]
  apply bind_congr
  rintro ⟨result, after⟩
  cases result <;> rfl

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.encapsulate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.encapsulate_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.decapsulate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.decapsulate_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.dh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.dh_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel.execute
