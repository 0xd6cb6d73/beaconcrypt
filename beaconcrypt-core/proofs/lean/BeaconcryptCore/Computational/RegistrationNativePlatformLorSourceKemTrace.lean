-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem
/-! The genuine source observer records queries and replies without changing their private KEM support. The granular source KEM contract therefore lifts to the same interpreter with its chronological trace, retaining all persistent private state. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
variable {n : Nat} {KemSK Private : Type}
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))

/-- Every traced source query has the exact same reply and persistent private transition as its underlying interpreter. -/
theorem query_support (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordFrontendTrace.State × Private)
    (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query × (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (supported : result ∈ support ((RegistrationNativePlatformLorStatefulSupport.trace implementation query).run before)) :
    (result.1,result.2.2) ∈ support ((implementation query).run before.2) := by
  rw [RegistrationNativePlatformLorStatefulSupport.trace,
    QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
  simp only [RegistrationNativeSecretWordFrontendTrace.handler,StateT.run,simulateQ_map,
    simulateQ_spec_query,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  change reached ∈ support (((fun reply => (reply,RegistrationNativeSecretWordFrontendTrace.finish query reply
    (RegistrationNativeSecretWordFrontendTrace.begin query before.1))) <$> implementation query).run before.2) at called
  rw [StateT.run_map,support_map] at called
  obtain ⟨actual,original,equal⟩ := called
  cases equal
  exact original

/-- The source trace derives the same granular KEM contract without any new constructor or controller premise. -/
theorem contract (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (provider : QueryImpl (RegistrationNativeSecretWordKemInterface.Routed KemSK)
      (StateT (RegistrationNativeSecretWordKemProvider.State KemSK) ProbComp))
    (prior : RegistrationNativePlatformLorSourceKem.Contract implementation kem input provider) :
    RegistrationNativePlatformLorSourceKem.Contract (RegistrationNativePlatformLorStatefulSupport.trace implementation)
      (fun current => kem current.2) input provider := by
  constructor
  · intro message before result supported
    exact prior.prepare message before.2 (result.1,result.2.2) (query_support implementation _ before result supported)
  · intro query before result supported
    exact prior.routed query before.2 (result.1,result.2.2) (query_support implementation _ before result supported)
  · intro query quiet before result supported
    exact prior.quiet query quiet before.2 (result.1,result.2.2) (query_support implementation query before result supported)

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace.query_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace.query_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace.contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace.contract
