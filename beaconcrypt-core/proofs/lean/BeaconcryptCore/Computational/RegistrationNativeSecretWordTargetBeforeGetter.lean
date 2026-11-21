-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase

/-! The actual ordered Server prefix before encapsulation cannot spend the selected getter. All admission checks, local ephemeral generation and request logs still execute under their actual source handlers and retain every reached state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordInterface (LocalSpec liftLocal)
open RegistrationNativeSecretWordTargetPhaseCore (Selected)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private def IsEncap {Reader E Shared : Type} : (RegistrationNativeSecretWordServerCollect.Spec Reader E Shared).Domain → Prop
  | .encapsulate _ => True
  | _ => False
private instance {Reader E Shared : Type} : DecidablePred (IsEncap (Reader := Reader) (E := E) (Shared := Shared)) := fun query => by
  cases query <;> first | exact isTrue trivial | exact isFalse id

private theorem before_bound {Reader E Shared : Type} (verified : PqxdhServerRootPreparation.Verified Reader) :
    (RegistrationNativeSecretWordTargetCollector.beforeGetter (E := E) (Shared := Shared) verified).IsQueryBoundP (IsEncap (Reader := Reader) (E := E) (Shared := Shared)) 0 := by
  unfold RegistrationNativeSecretWordTargetCollector.beforeGetter
  simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk,
        Option.elimM, Option.elim_some, bind_map_left,
        Bool.not_true, Bool.false_eq_true, ite_false])
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [IsEncap], ?_⟩)
    | (intro answer; cases answer)

private theorem backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : Environment) :
    (simulateQ (liftLocal true) ((RegistrationNativeSecretWordServerCompiler.backend (n := n) setup checks query).run before)).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordTargetServerPhase.effect_free true _

private theorem backend_program_free (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Environment) :
    (simulateQ (liftLocal true) ((simulateQ (RegistrationNativeSecretWordServerCompiler.backend (n := n) setup checks) work).run before)).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible current
    exact impossible.elim
  · intro query _ current
    exact backend_free setup checks query current

private theorem ordinary_free (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    (simulateQ (liftLocal true) ((RegistrationNativeSecretWordServerCompiler.ordinaryPrefix (n := n) setup checks query).run before)).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 := by
  cases query <;> simp only [RegistrationNativeSecretWordServerCompiler.ordinaryPrefix,
    PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact backend_program_free setup checks _ before
    | (simp only [StateT.run]; trivial)

private theorem prefix_step (setup : Setup base KemSK) (checks : Checks)
    (query : (RegistrationNativeSecretWordServerCollect.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    (simulateQ (liftLocal true) ((RegistrationNativeSecretWordServerCompiler.prefixImpl (n := n) setup checks query).run before)).IsQueryBoundP
      (Selected (KemSK := KemSK)) (if IsEncap (Reader := registration.InitPacket) (E := Unit) (Shared := PqxdhJointIdentity.PeerEncoding) query then 1 else 0) := by
  cases query
  all_goals simp only [RegistrationNativeSecretWordServerCompiler.prefixImpl, IsEncap, ite_true, ite_false]
  all_goals first
    | exact ordinary_free setup checks _ before
    | (simp only [StateT.run]; split <;>
        simp [RegistrationNativeSecretWordInterface.localKem, liftLocal, RegistrationNativeSecretWordInterface.route,
          RegistrationNativeSecretWordInterface.routedKem, Selected, isQueryBoundP_map_iff, isQueryBoundP_query_iff])

/-- The actual complete pre-getter AST has zero selected-getter queries; the footprint is derived from its literal callback order. -/
theorem before_free (setup : Setup base KemSK) (checks : Checks)
    (verified : PqxdhServerRootPreparation.Verified registration.InitPacket) (before : Environment) :
    (simulateQ (liftLocal true)
      ((simulateQ (RegistrationNativeSecretWordServerCompiler.prefixImpl (n := n) setup checks)
        (RegistrationNativeSecretWordTargetCollector.beforeGetter verified)).run before)).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply (before_bound (E := Unit) (Shared := PqxdhJointIdentity.PeerEncoding) verified).simulateQ_run_of_step
  · intro query counted current
    have step := prefix_step (n := n) setup checks query current
    simp only [ite_eq_left counted] at step
    convert step using 1; rfl
  · intro query quiet current
    have step := prefix_step (n := n) setup checks query current
    simp only [ite_eq_right quiet] at step
    convert step using 1; rfl

/-- Actual concrete pre-getter execution retains the current early-provider marker, independently of outer material replies. -/
theorem before_phase (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (verified : PqxdhServerRootPreparation.Verified registration.InitPacket)
    (before : Auxiliary n KemSK) (result : Option (PqxdhServerRootPreparation.Ephemeral Unit) × Auxiliary n KemSK)
    (supported : result ∈ support ((lower
      (localImpl setup wire route sign input inside
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge) outer true)
      (simulateQ (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks)
        (RegistrationNativeSecretWordTargetCollector.beforeGetter verified))).run before)) :
    result.2.2.kem.2 = before.2.kem.2 :=
  RegistrationNativeSecretWordTargetServerPhase.lower_phase setup wire route sign input inside selected pairs publicKey challenge outer
    _ before result (before_free setup checks verified before.1) supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter.before_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter.before_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter.before_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter.before_phase
