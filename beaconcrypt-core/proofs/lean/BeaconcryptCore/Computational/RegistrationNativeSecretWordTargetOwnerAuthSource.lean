-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth

/-! Actual stateful lowering of mandatory response authentication retains the source controller's exact pending owner and supplied packet. The proof forgets only interpretation effects for this immutable public receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuthSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordTargetServerExecution (lower lower_run Auxiliary)
open RegistrationNativeSecretWordInterpreter (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT (State n KemSK) ProbComp))

/-- A result of the actual closed local lowering is a possible result of that same original open environment program. -/
theorem output (work : StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (before after : Auxiliary n KemSK) (value : Value)
    (supported : (value, after) ∈ support ((lower implementation work).run before)) :
    value ∈ support (work.run' before.1) := by
  rw [lower_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have possible : reached.1 ∈ support (work.run before.1) := by
    apply support_simulateQ_run'_subset implementation _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  rw [StateT.run'_eq, support_map]
  exact ⟨reached.1, possible, congrArg Prod.fst equal⟩

/-- Successful actual mandatory authentication retains its caller's exact pending owner and supplied packet. -/
theorem packet (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (authenticated : registration.AuthenticatedResponse) (before after : Auxiliary n KemSK)
    (supported : (.ok (.Ok authenticated), after) ∈ support
      ((lower implementation (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
        (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
          (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some packet => .Some packet)))))).run before)) :
    ∃ supplied, packet = some supplied ∧ authenticated = ⟨pending, supplied⟩ := by
  have possible := output (Value := RustM RegistrationResponseExecutor.ResponseResult) implementation _ before after (RustM.ok (core.result.Result.Ok authenticated)) supported
  simp only [StateT.run'_eq, StateT.run_lift, bind_pure_comp, Functor.map_map, id_map'] at possible
  have bare := RegistrationNativePublicSourceSupport.simulate_support _ _ _
    (RegistrationNativePublicSourceSupport.simulate_support _ _ _ possible)
  cases packet with
  | none =>
      simp only [RegistrationResponseExecutor.begin_malformed, mem_support_pure_iff] at bare
      cases bare
  | some supplied =>
      exact ⟨supplied, rfl, RegistrationNativeSecretWordTargetOwnerAuth.packet pending supplied authenticated bare⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuthSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuthSource.output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuthSource.output
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuthSource.packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuthSource.packet
