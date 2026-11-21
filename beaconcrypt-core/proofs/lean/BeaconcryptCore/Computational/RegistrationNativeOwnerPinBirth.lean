-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceNativeProgram
import BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport

/-! A successful actual Beacon constructor retains precisely the configured classical and ML Server pins. Pin selection is pure and retains the full supplied Server key. No generated identity, signature-origin or timing premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}

private theorem common_pin (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (pin : session.ServerAuthenticationPin)
    (supported : .ok (some pin) ∈ support
      (RegistrationNativeIdentitySourceCommon.program (n := n) source edPin mlPin keyId)) :
    pin.binding = ⟨edPin, keyId⟩ ∧ pin.public_key = mlPin := by
  simp only [RegistrationNativeIdentitySourceCommon.program, registration.begin_server_pin, session.ServerAuthenticationPin.new,
    mem_support_pure_iff, RustM.ok.injEq, Option.some.injEq] at supported
  subst pin
  exact ⟨rfl, rfl⟩

/-- Every successful native preparation retains the exact supplied binding and ML public pin. -/
theorem prepare_pin (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : EnvState RegistrationServerRoleBackend.State) (prepared : Prepared source)
    (afterOwners : State source) (afterEnv : EnvState RegistrationServerRoleBackend.State)
    (supported : ((.ok (some prepared), afterOwners), afterEnv) ∈ support
      (((prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env)) :
    prepared.pin.binding = ⟨edPin, keyId⟩ ∧ prepared.pin.public_key = mlPin := by
  rw [RegistrationNativeIdentitySourceNativeProgram.prepare_run, support_map] at supported
  obtain ⟨reply, reached, returned⟩ := supported
  cases returned
  rw [RegistrationNativeIdentitySourceCommon.nativeProgram, mem_support_bind_iff] at reached
  obtain ⟨earlier, prefixReached, suffixReached⟩ := reached
  have prefixActual := RegistrationNativePublicSourceSupport.simulate_support _ _ _ prefixReached
  cases earlier with
  | fail error => simp only [RegistrationNativeIdentitySourceCommon.afterNative, mem_support_pure_iff] at suffixReached; cases suffixReached
  | div => simp only [RegistrationNativeIdentitySourceCommon.afterNative, mem_support_pure_iff] at suffixReached; cases suffixReached
  | ok chosen => cases chosen with
    | none => simp only [RegistrationNativeIdentitySourceCommon.afterNative, mem_support_pure_iff] at suffixReached; cases suffixReached
    | some selected =>
        have pins := common_pin source edPin mlPin keyId selected prefixActual
        simp only [RegistrationNativeIdentitySourceCommon.afterNative, RegistrationNativeIdentitySourceSuffix.native,
          mem_support_bind_iff, mem_support_pure_iff, RustM.ok.injEq, Option.some.injEq] at suffixReached
        obtain ⟨identity, _identity, scalar, _scalar, returned⟩ := suffixReached
        cases returned
        exact pins

/-- Actual successful creation appends an owner with the literal configured pins at the returned public owner index. -/
theorem create_pin (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : EnvState RegistrationServerRoleBackend.State) (index : Nat)
    (afterOwners : State source) (afterEnv : EnvState RegistrationServerRoleBackend.State)
    (supported : ((.ok (some index), afterOwners), afterEnv) ∈ support
      (((create (n := n) setup source edPin mlPin keyId).run owners).run env)) :
    ∃ owner, afterOwners[index]? = some owner ∧ owner.pin.binding = ⟨edPin, keyId⟩ ∧ owner.pin.public_key = mlPin := by
  rw [RegistrationNativeBeaconBirth.create_program] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨earlier, reached, continued⟩ := supported
  cases actual : earlier.1.1 with
  | fail error => simp only [actual, mem_support_pure_iff] at continued; cases continued
  | div => simp only [actual, mem_support_pure_iff] at continued; cases continued
  | ok result => cases result with
    | none => simp only [actual, mem_support_pure_iff] at continued; cases continued
    | some prepared =>
        have shape : earlier = ((.ok (some prepared), earlier.1.2), earlier.2) := by rw [← actual]
        have ready : ((.ok (some prepared), earlier.1.2), earlier.2) ∈ support
            (((prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env) := by
          rw [← shape]
          exact reached
        have pins := prepare_pin source edPin mlPin keyId owners env prepared earlier.1.2 earlier.2 ready
        simp only [actual] at continued
        rw [RegistrationNativeBeaconBirth.append_program] at continued
        simp only [mem_support_bind_iff, mem_support_pure_iff] at continued
        obtain ⟨born, _born, worldOwner, _allocated, returned⟩ := continued
        cases returned
        refine ⟨RegistrationNativeBeaconBirth.owner setup source prepared.pin
          prepared.identity prepared.prekey born worldOwner, ?_, pins.1, pins.2⟩
        simp only [List.getElem?_append, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero]

end BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth.prepare_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth.prepare_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth.create_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth.create_pin
