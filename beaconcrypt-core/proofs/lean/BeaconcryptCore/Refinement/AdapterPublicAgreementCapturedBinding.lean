-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicSuccessfulOracleSupport
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter
import BeaconcryptCore.Computational.RegistrationAgreementMetadata
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual captured SDK agreement preserves the original authenticated binding on every successful completion, even for arbitrary source primitive dictionaries and enclosing failures. The result follows from the same typed free request tree and original Core metadata invariant; no second primitive model or whole source-controller contract is needed. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementCapturedBinding
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementInterpreter (Capture handler)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK PlatformState : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]

theorem supported {R E Value : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (keys : AdapterPublicAgreementFields.Keys)
    (work : OracleComp Spec Value) (rng : R) (value : Value)
    (journal : RegistrationAgreementQueryTrace.Trace) (capture : Capture R)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (previous next : PlatformState)
    (called : ((.ok ((value, journal), capture), after), next) ∈ support
      ((((AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng).run).run before).run previous)) :
    value ∈ support work := by
  let : CryptoOperations (RustT (RegistrationNativePlatformExperiment.M n KemSK mlSource (StateT PlatformState ProbComp))) :=
    AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  have traced : (value, journal) ∈ support (RegistrationAgreementQueryTrace.trace work []) := by
    unfold AdapterPublicAgreementNativePlatformInterpreter.captured at called
    exact AdapterPublicSuccessfulOracleSupport.successful (handler generator keys)
      (RegistrationAgreementQueryTrace.trace work []) (value, journal) ⟨rng, .None, .None⟩ capture before after previous next called
  rw [← RegistrationAgreementQueryTrace.erasure work [], support_map]
  exact ⟨(value, journal), traced, rfl⟩

theorem server {R E : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (keys : AdapterPublicAgreementFields.Keys) (rng : R)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus) (authenticated : registration.AuthenticatedInit)
    (completed : agreement.ServerAgreement) (journal : RegistrationAgreementQueryTrace.Trace) (capture : Capture R)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (previous next : PlatformState)
    (called : ((.ok ((.ok (.ServerComplete completed), journal), capture), after), next) ∈ support
      ((((AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys
        (RegistrationAgreementExecutor.server control status authenticated) rng).run).run before).run previous)) :
    completed.binding = authenticated.binding :=
  RegistrationAgreementExecutor.server_binding control status authenticated completed
    (supported coins generator keys _ rng _ journal capture before after previous next called)

end BeaconcryptCore.Refinement.AdapterPublicAgreementCapturedBinding

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCapturedBinding.supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCapturedBinding.supported

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCapturedBinding.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCapturedBinding.server
