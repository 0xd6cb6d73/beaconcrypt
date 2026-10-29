-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks

/-! Concrete source execution cannot create an output outside its actual open client's query tree. These support laws transport structural frontend invariants through the private root/World/pool interpreters without a desired simulation premise. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State)
variable {n : Nat} {ι κ τ KemSK Value : Type}
variable {base : OracleSpec ι} {spec : OracleSpec κ} {target : OracleSpec τ}

/-- Any concrete oracle interpretation preserves the original open program's set of possible outputs. -/
theorem simulate_support (implementation : QueryImpl spec (OracleComp target))
    (work : OracleComp spec Value) (value : Value)
    (supported : value ∈ support (simulateQ implementation work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure output => exact supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, reached⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, by simp, ih reply reached⟩

/-- The actual full source interpretation preserves every output-only structural invariant of the mixed client, keeping its frontend poststate in the observed value. -/
theorem frontend_support (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK) (result : Value × State n KemSK)
    (supported : result ∈ support ((RegistrationNativePublicSourceEffects.close setup seed scalar
      (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) work)).run before)) :
    result.1 ∈ support work := by
  have reached := simulate_support
    (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    ((simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) work).run before) result supported
  apply support_simulateQ_run'_subset (RegistrationNativePublicInterpreter.handler setup wire route sign) work before
  rw [StateT.run'_eq, support_map]
  exact ⟨result, reached, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport.simulate_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport.simulate_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport.frontend_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport.frontend_support
