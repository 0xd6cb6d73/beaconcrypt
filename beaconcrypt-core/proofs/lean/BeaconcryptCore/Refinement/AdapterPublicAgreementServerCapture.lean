-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveModel
import BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual entropy-backed source handler carries a private conversion-readiness bit together with its entire updated RNG and opaque generated ephemeral key pair. The two representations commute for every callback and every adaptive request program. No native backend correspondence is assumed here. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 Keys KeyPair)
open AdapterPublicAgreementInterpreter (Capture)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open AdapterPublicAgreementPrimitiveModel (Model)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

structure State (R : Type) where
  rng : R
  ready : Bool
  ephemeral : core.option.Option KeyPair

noncomputable def encode (model : Model (m := m) generator setup checks view) (keys : Keys)
    (before : State R) : Capture R :=
  ⟨before.rng, if before.ready then .Some ⟨model.representation.converted (view.edSecret keys.identity_secret)⟩ else .None,
    before.ephemeral⟩

def decode (before : Capture R) : State R :=
  ⟨before.rng, _root_.Option.isSome before.localIdentity, before.ephemeral⟩

noncomputable def implementation (model : Model (m := m) generator setup checks view) (keys : Keys) :
    QueryImpl Spec (StateT (State R) m) := fun request before =>
  Prod.map id decode <$> (AdapterPublicAgreementPrimitiveModel.implementation model keys request).run (encode model keys before)

noncomputable section

omit [LawfulMonad m] in
theorem decode_encode (model : Model (m := m) generator setup checks view) (keys : Keys) (before : State R) :
    decode (encode model keys before) = before := by
  cases before with
  | mk rng flag ephemeral => cases flag <;> rfl

theorem query (model : Model (m := m) generator setup checks view) (keys : Keys)
    (request : Request) (before : State R) :
    (AdapterPublicAgreementPrimitiveModel.implementation model keys request).run (encode model keys before) =
      Prod.map id (encode model keys) <$> (implementation model keys request).run before := by
  change (AdapterPublicAgreementPrimitiveModel.implementation model keys request).run (encode model keys before) =
    Prod.map id (encode model keys) <$> Prod.map id decode <$>
      (AdapterPublicAgreementPrimitiveModel.implementation model keys request).run (encode model keys before)
  rw [Functor.map_map]
  cases request with
  | convertPublic key =>
    simp only [AdapterPublicAgreementPrimitiveModel.implementation, StateT.run_pure, map_pure,
      Prod.map_apply, id_eq, decode_encode]
  | convertSecret role =>
    simp only [AdapterPublicAgreementPrimitiveModel.implementation, StateT.run_bind, StateT.run_modify,
      StateT.run_pure, pure_bind, map_pure]
    cases before with
    | mk rng flag ephemeral => cases flag <;> rfl
  | generate role =>
    simp only [AdapterPublicAgreementPrimitiveModel.implementation, StateT.run_bind, StateT.run_get,
      StateT.run_lift, StateT.run_map, StateT.run_set, pure_bind, map_pure, bind_pure_comp, Functor.map_map]
    apply congrArg (fun function => function <$> model.sample)
    funext scalar
    cases before with
    | mk rng flag ephemeral => cases flag <;> rfl
  | encapsulate input =>
    simp only [AdapterPublicAgreementPrimitiveModel.implementation, StateT.run_bind, StateT.run_get,
      StateT.run_lift, StateT.run_map, StateT.run_set, pure_bind, map_pure, bind_pure_comp, Functor.map_map]
    apply congrArg (fun function => function <$> AdapterPublicAgreementPrimitiveModel.encapsulate model input before.rng)
    funext result
    rcases result with ⟨reply, nextRng⟩
    cases before with
    | mk rng flag ephemeral => cases flag <;> rfl
  | decapsulate input =>
    simp only [AdapterPublicAgreementPrimitiveModel.implementation, StateT.run_lift,
      bind_pure_comp, Functor.map_map]
    apply congrArg (fun function => function <$> AdapterPublicAgreementPrimitiveModel.decapsulate model input keys.beacon_kem)
    funext reply
    change (reply, encode model keys before) = (reply, encode model keys (decode (encode model keys before)))
    rw [decode_encode]
  | dh request =>
    simp only [AdapterPublicAgreementPrimitiveModel.implementation, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind, map_pure, Prod.map_apply, id_eq, decode_encode]
  | root request =>
    simp only [AdapterPublicAgreementPrimitiveModel.implementation, StateT.run_pure, map_pure,
      Prod.map_apply, id_eq, decode_encode]

theorem program {Value : Type} (model : Model (m := m) generator setup checks view) (keys : Keys)
    (before : State R) (work : OracleComp Spec Value) :
    (simulateQ (AdapterPublicAgreementPrimitiveModel.implementation model keys) work).run (encode model keys before) =
      Prod.map id (encode model keys) <$> (simulateQ (implementation model keys) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query model keys request before]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨reply, after⟩
    exact ih reply after
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture.decode_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture.decode_encode

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementServerCapture.program
