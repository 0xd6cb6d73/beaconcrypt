-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto
import BeaconcryptCore.Refinement.AdapterPublicAgreementSourceEntries
import BeaconcryptCore.Computational.RegistrationAgreementQueryTrace
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Counting each actual source primitive field yields the same literal source agreement executor as counting its complete original computation. This source correspondence is derived for arbitrary primitive errors and every returned RNG; it is not supplied as a whole-handler law. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementMonadMap
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (Capture handler)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {left right : Type → Type} [Monad left] [LawfulMonad left] [Monad right] [LawfulMonad right]
variable [Transformation left right]
variable [original : CryptoOperations (RustT left)]
local notation "Mapped" => RustT (right)
noncomputable section

theorem query {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (request : Request) (before : Capture R) :
    letI : CryptoOperations Mapped := AdapterPublicAgreementMonadCrypto.operations original
    (handler (m := right) generator keys request).run before =
      mapped ((handler (m := left) generator keys request).run before) := by
  let : CryptoOperations Mapped := AdapterPublicAgreementMonadCrypto.operations original
  cases request with
  | convertPublic key =>
    simp only [handler, StateT.run_lift, AdapterPublicAgreementMonadCrypto.convertPublic, mapped_bind, mapped_pure]
  | convertSecret role =>
    simp only [handler, StateT.run_bind, StateT.run_lift, StateT.run_modify, pure_bind,
      AdapterPublicAgreementMonadCrypto.convertSecret, mapped_bind, mapped_liftRust, mapped_pure]
  | generate role =>
    simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind,
      AdapterPublicAgreementMonadCrypto.generate, mapped_bind, mapped_pure]
  | encapsulate input =>
    simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind,
      AdapterPublicAgreementMonadCrypto.encapsulate, mapped_bind, mapped_pure]
  | decapsulate input =>
    simp only [handler, StateT.run_lift, AdapterPublicAgreementMonadCrypto.decapsulate, mapped_bind, mapped_pure]
  | dh request =>
    simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind,
      AdapterPublicAgreementMonadCrypto.dh, mapped_bind, mapped_pure]
  | root request =>
    simp only [handler, StateT.run_lift, AdapterPublicAgreementMonadCrypto.root, mapped_bind, mapped_pure]

theorem program {R E Value : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (before : Capture R) :
    letI : CryptoOperations Mapped := AdapterPublicAgreementMonadCrypto.operations original
    (simulateQ (handler (m := right) generator keys) work).run before =
      mapped ((simulateQ (handler (m := left) generator keys) work).run before) := by
  let : CryptoOperations Mapped := AdapterPublicAgreementMonadCrypto.operations original
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, mapped_pure]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query, mapped_bind]
    apply bind_congr
    rintro ⟨reply, after⟩
    exact ih reply after

theorem execute {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (phase : agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations Mapped := AdapterPublicAgreementMonadCrypto.operations original
    beaconcrypt_public_request.pqxdh.execute_agreement (m := Mapped) generator phase keys rng =
      mapped (beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT left) generator phase keys rng) := by
  let : CryptoOperations Mapped := AdapterPublicAgreementMonadCrypto.operations original
  rw [AdapterPublicAgreementInterpreter.execute_source, AdapterPublicAgreementInterpreter.execute_source]
  unfold AdapterPublicAgreementInterpreter.runLoop
  rw [program, mapped_bind]
  apply bind_congr
  rintro ⟨result, after⟩
  simp only [mapped_bind, mapped_liftRust, mapped_pure]
theorem entry {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (start : RustM agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations Mapped := AdapterPublicAgreementMonadCrypto.operations original
    (do let phase ← AdapterRecordRequestMonad.liftRust start
        beaconcrypt_public_request.pqxdh.execute_agreement (m := Mapped) generator phase keys rng) =
      mapped ((do
        let phase ← AdapterRecordRequestMonad.liftRust start
        beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT left) generator phase keys rng) :
        RustT left (agreement.AgreementEffect × R)) := by
  let : CryptoOperations Mapped := AdapterPublicAgreementMonadCrypto.operations original
  rw [mapped_bind, mapped_liftRust]
  apply bind_congr
  intro phase
  exact execute generator keys phase rng

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter


/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter.execute

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter.entry
