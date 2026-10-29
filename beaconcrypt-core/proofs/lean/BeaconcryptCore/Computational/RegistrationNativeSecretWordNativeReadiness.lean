-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeFlags
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource

/-! An additive private observer derives preparation safety for evaluated native descriptors from the actual symbolic live-Ready certificate. Evaluation may alias atom and literal descriptors; validity-gated monotonicity handles those aliases. The observer forwards every original callback and retains every ordinary World, KEM and trace result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message eval input)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked Prepared AllPrepared Prefix)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

structure Audit where
  native : RegistrationNativeRelatedFamily.Message → Bool
  bad : Bool

def initial : Audit := ⟨fun _ => false, false⟩

def valid (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (message : RegistrationNativeRelatedFamily.Message) : Bool :=
  (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message).isSome

def step (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) : (Spec n KemSK).Domain → Audit → Audit
  | .inl (.inl message), before =>
      { before with native := Function.update before.native (eval candidate message) (valid setup seed scalar (eval candidate message)) }
  | .inl (.inr (.inl (.inl message))), before =>
      { before with bad := before.bad || (valid setup seed scalar (eval candidate message) && !(before.native (eval candidate message))) }
  | _, before => before

def Good (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (audit : Audit) (before : State n KemSK) : Prop :=
  RegistrationNativeSecretWordNativeFlags.Valid (valid setup seed scalar) audit.native ∧
    RegistrationNativeSecretWordNativeFlags.Refines (eval candidate) before.flags audit.native ∧ audit.bad = false

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (Spec n KemSK) (StateT (Audit × State n KemSK) (OracleComp RegistrationNativeSecretWordService.Combined)) := fun query before =>
  (fun result => (result.1, (step setup seed scalar candidate query before.1, result.2))) <$>
    (handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider query).run before.2

/-- The additive observer erases to precisely the actual checked callback with its full state. -/
theorem erase_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (query : (Spec n KemSK).Domain) (before : Audit × State n KemSK) :
    Prod.map id Prod.snd <$> (handler setup wire route sign inside provider seed scalar candidate query).run before =
      (handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider query).run before.2 := by
  simp only [handler, StateT.run, Functor.map_map, Prod.map_def, id_eq, id_map']

/-- Complete adaptive execution retains every original result and state after erasing only the extra observer. -/
theorem erase_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (work : OracleComp (Spec n KemSK) Value) (before : Audit × State n KemSK) :
    Prod.map id Prod.snd <$> (simulateQ (handler setup wire route sign inside provider seed scalar candidate) work).run before =
      (simulateQ (handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (erase_query setup wire route sign inside provider seed scalar candidate) work before

/-- The actual cold symbolic initialization reflects into cold native flags with no alias or input-validity premise. -/
theorem initial_good (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
    (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    Good setup seed scalar candidate initial (RegistrationNativeSecretWordInterpreter.initial ordinary kem) := by
  exact ⟨RegistrationNativeSecretWordNativeFlags.valid_cold _, RegistrationNativeSecretWordNativeFlags.refines_cold _, rfl⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness.erase_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness.erase_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness.erase_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness.erase_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness.initial_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadiness.initial_good
