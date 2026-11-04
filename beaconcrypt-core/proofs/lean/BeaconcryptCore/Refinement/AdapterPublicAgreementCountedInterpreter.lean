-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto
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
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementCountedRust
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (Capture handler)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {n : Nat}
variable [original : CryptoOperations (RustT ProbComp)]
local notation "World" => PqxdhRecordLiftWorld.State n
local notation "Counted" => RustT (StateT World ProbComp)
noncomputable section

theorem query {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (request : Request) (before : Capture R) :
    letI : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
    (handler (m := StateT World ProbComp) generator keys request).run before =
      counted ((handler (m := ProbComp) generator keys request).run before) := by
  let : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
  cases request with
  | convertPublic key =>
    simp only [handler, StateT.run_lift, AdapterPublicAgreementCountedCrypto.convertPublic, counted_bind, counted_pure]
  | convertSecret role =>
    simp only [handler, StateT.run_bind, StateT.run_lift, StateT.run_modify, pure_bind,
      AdapterPublicAgreementCountedCrypto.convertSecret, counted_bind, counted_liftRust, counted_pure]
  | generate role =>
    simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind,
      AdapterPublicAgreementCountedCrypto.generate, counted_bind, counted_pure]
  | encapsulate input =>
    simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind,
      AdapterPublicAgreementCountedCrypto.encapsulate, counted_bind, counted_pure]
  | decapsulate input =>
    simp only [handler, StateT.run_lift, AdapterPublicAgreementCountedCrypto.decapsulate, counted_bind, counted_pure]
  | dh request =>
    simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind,
      AdapterPublicAgreementCountedCrypto.dh, counted_bind, counted_pure]
  | root request =>
    simp only [handler, StateT.run_lift, AdapterPublicAgreementCountedCrypto.root, counted_bind, counted_pure]

theorem program {R E Value : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (before : Capture R) :
    letI : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
    (simulateQ (handler (m := StateT World ProbComp) generator keys) work).run before =
      counted ((simulateQ (handler (m := ProbComp) generator keys) work).run before) := by
  let : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, counted_pure]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query, counted_bind]
    apply bind_congr
    rintro ⟨reply, after⟩
    exact ih reply after

theorem execute {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (phase : agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
    beaconcrypt_public_request.pqxdh.execute_agreement (m := Counted) generator phase keys rng =
      counted (beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT ProbComp) generator phase keys rng) := by
  let : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
  rw [AdapterPublicAgreementInterpreter.execute_source, AdapterPublicAgreementInterpreter.execute_source]
  unfold AdapterPublicAgreementInterpreter.runLoop
  rw [program, counted_bind]
  apply bind_congr
  rintro ⟨result, after⟩
  simp only [counted_bind, counted_liftRust, counted_pure]
theorem entry {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (start : RustM agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
    (do let phase ← AdapterRecordRequestMonad.liftRust start
        beaconcrypt_public_request.pqxdh.execute_agreement (m := Counted) generator phase keys rng) =
      counted ((do let phase ← AdapterRecordRequestMonad.liftRust start
                   beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT ProbComp) generator phase keys rng) :
        RustT ProbComp (agreement.AgreementEffect × R)) := by
  let : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
  rw [counted_bind, counted_liftRust]
  apply bind_congr
  intro phase
  exact execute generator keys phase rng

theorem trace_erasure {R E Value : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (before : Capture R) :
    letI : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
    (fun result => (result.1.1, result.2)) <$>
      (simulateQ (handler (m := StateT World ProbComp) generator keys)
        (RegistrationAgreementQueryTrace.trace work [])).run before =
      (simulateQ (handler (m := StateT World ProbComp) generator keys) work).run before := by
  let : CryptoOperations Counted := AdapterPublicAgreementCountedCrypto.operations original
  have erased := congrArg (fun tree =>
    (simulateQ (handler (m := StateT World ProbComp) generator keys) tree).run before)
      (RegistrationAgreementQueryTrace.erasure work [])
  simpa only [simulateQ_map, StateT.run_map] using erased

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.execute

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.entry

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.trace_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedInterpreter.trace_erasure
