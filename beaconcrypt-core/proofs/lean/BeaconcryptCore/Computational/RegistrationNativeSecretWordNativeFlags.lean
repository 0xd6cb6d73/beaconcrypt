-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput

/-! Native descriptor flags may alias distinct symbolic words after candidate evaluation. Their preparation validity is nevertheless identical. The actual validity-gated update is monotone, so reflecting symbolic live flags into native flags does not assume that word evaluation is injective. These finite laws support the native flagged-to-checked source comparison. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags
variable {Word Native : Type}

def Valid (valid : Native → Bool) (flags : Native → Bool) : Prop :=
  ∀ message, flags message = true → valid message = true

def Refines (evaluate : Word → Native) (words : Word → Bool) (native : Native → Bool) : Prop :=
  ∀ message, words message = true → native (evaluate message) = true

/-- Cold native preparation flags are valid for every actual optional-input predicate. -/
theorem valid_cold (valid : Native → Bool) : Valid valid (fun _ => false) := by
  intro message impossible
  cases impossible

/-- Cold symbolic flags reflect into cold native flags without an injectivity assumption. -/
theorem refines_cold (evaluate : Word → Native) : Refines evaluate (fun _ => false) (fun _ => false) := by
  intro message impossible
  cases impossible

variable [DecidableEq Word] [DecidableEq Native]

/-- Updating preparation at its actual validity preserves validity of every previously set native descriptor. -/
theorem valid_prepare (valid : Native → Bool) (flags : Native → Bool) (before : Valid valid flags)
    (message : Native) : Valid valid (Function.update flags message (valid message)) := by
  intro current active
  by_cases same : current = message
  · subst current
    exact (Function.update_self _ _ _).symm.trans active
  · exact before current (by simpa only [Function.update_of_ne same] using active)

/-- A validity-gated preparation cannot clear any previously live native flag, including a byte-aliased descriptor. -/
theorem keeps_prepare (valid : Native → Bool) (flags : Native → Bool) (before : Valid valid flags)
    (message current : Native) (active : flags current = true) :
    Function.update flags message (valid message) current = true := by
  by_cases same : current = message
  · subst current
    exact (Function.update_self _ _ _).trans (before message active)
  · simpa only [Function.update_of_ne same] using active

/-- Symbolic preparation reflects into actual native preparation even when another symbolic descriptor has the same evaluated bytes. -/
theorem refines_prepare (evaluate : Word → Native) (valid : Native → Bool)
    (words : Word → Bool) (native : Native → Bool) (nativeValid : Valid valid native)
    (before : Refines evaluate words native) (message : Word) (success : Bool)
    (coherent : success = valid (evaluate message)) :
    Refines evaluate (Function.update words message success)
      (Function.update native (evaluate message) (valid (evaluate message))) := by
  intro current active
  by_cases same : current = message
  · subst current
    have actual : success = true := by simpa only [Function.update_self] using active
    exact (Function.update_self _ _ _).trans (coherent.symm.trans actual)
  · have old : words current = true := by simpa only [Function.update_of_ne same] using active
    exact keeps_prepare valid native nativeValid (evaluate message) (evaluate current) (before current old)

/-- Actual optional DH/input validity agrees under candidate evaluation; the entire protected head and KEM field are retained. -/
theorem input_coherent (joint : PqxdhJointIdentity.Primitives) (dh : PqxdhJointGapDh.DhInterface joint)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : RegistrationNativeSecretWordMessage.Message) :
    (RegistrationNativeRelatedFamily.input joint dh seed scalar (RegistrationNativeSecretWordMessage.eval candidate message)).isSome =
      (RegistrationNativeSecretWordMessage.input joint dh seed scalar message).isSome := by
  have source := congrArg Option.isSome (RegistrationNativeSecretWordMessage.input_eval joint dh seed scalar candidate message)
  simpa only [Option.isSome_map] using source.symm
end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.valid_cold' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.valid_cold
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.refines_cold' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.refines_cold
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.valid_prepare' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.valid_prepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.keeps_prepare' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.keeps_prepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.refines_prepare' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.refines_prepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.input_coherent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags.input_coherent
