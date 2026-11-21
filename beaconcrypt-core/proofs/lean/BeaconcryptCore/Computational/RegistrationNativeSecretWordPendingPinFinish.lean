-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinInterface
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditFinish

/-! The actual incoming Word controller never creates a new pending capability. Failed aborted-state moves retain the original controller; a successful move consumes it before authentication or material effects. Thus the stored-pin invariant survives every incoming outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordPendingPin (Coherent Holds holds_iff)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Terminal)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem terminal_coherent (owner : SelectedOwner source) (valid : Terminal owner.phase) : Coherent owner := by
  cases phase : owner.phase <;> simp only [phase, Terminal] at valid
  all_goals simp only [Coherent, phase]

/-- Actual successful aborted-state consumption makes the same pending capability terminal; every other incoming outcome retains its original stored-pin relation. -/
theorem finish_coherent (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (prior : Coherent owner)
    (supported : result ∈ support (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner).run env)) :
    Coherent result.1.2 := by
  have original := supported
  cases phase : owner.phase <;>
    simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get, pure_bind, phase] at supported
  all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact prior }
  case initSent pending oneTime =>
    cases moved : pending.aborted_state <;> simp only [moved] at supported
    all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact prior }
    case ok aborted =>
      exact terminal_coherent result.1.2
        (RegistrationNativeSecretWordOwnerCreditFinish.finish_consumes setup packet owner env pending oneTime aborted phase moved result original)

/-- The full actual incoming roster controller preserves the stored-pin property for the same owner and all untouched owners under arbitrary original Word replies. -/
theorem finish_keeps (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (prior : Holds owners) (supported : result ∈ support
      (((RegistrationNativeSecretWordOwners.finish (n := n) setup source index packet).run owners).run env)) : Holds result.1.2 := by
  cases found : owners[index]? with
  | none =>
      simp only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      exact prior
  | some owner =>
      simp only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, support_map] at supported
      obtain ⟨reached, called, equal⟩ := supported
      have original : reached ∈ support
          (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner.view).run env) := by
        cases choice : owner.scalar with
        | none => simpa only [choice, StateT.run] using called
        | some scalar =>
            exact PqxdhDeploymentEnvironment.support_simulateQ_subset (RegistrationNativeSecretWordOwners.ordinary setup scalar)
              (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner.view).run env)
              (by simpa only [choice, StateT.run] using called)
      have kept := finish_coherent setup packet owner.view env reached (prior index owner found) original
      cases equal
      apply (holds_iff _).mpr
      intro selected member
      rcases List.mem_or_eq_of_mem_set member with previous | rfl
      · exact (holds_iff owners).mp prior selected previous
      · exact kept

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFinish.finish_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFinish.finish_coherent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFinish.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFinish.finish_keeps
