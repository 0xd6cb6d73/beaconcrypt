-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps

/-! Closing the actual mixed symbolic frontend introduces protected-table or suffix-key queries only at its original material demands. Every ordinary World/publication/record component and the complete indexed KEM provider use only the existing coin surface. Thus the final ordinary recovery adversary receives the frontend's actual build-plus-finish allowance, rather than an extra whole-client cap assumption. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps
open RegistrationNativeSecretWordInterpreter (State M Provider roots ordinary routed handler)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsDemand : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inl _))) => True
  | _ => False

instance : DecidablePred (IsDemand (n := n) (KemSK := KemSK)) := fun query => by
  rcases query with (message | (message | common) | kem) | record <;> dsimp only [IsDemand] <;> infer_instance

private theorem coins_free (kind : Kind) (work : ProbComp Value) :
    (simulateQ RegistrationNativeSecretWordService.coins work).IsQueryBoundP (Counted kind) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind coin next ih =>
      cases kind <;>
        simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeSecretWordService.coins,
          isQueryBoundP_query_bind_iff, Counted, RegistrationNativeSecretWordRecoveryCompiler.IsKey,
          RegistrationNativeSecretWordRecoveryCompiler.IsSuffix, RegistrationNativeSecretWord.IsKey,
          ite_false, not_false_eq_true, true_or, true_and]
      all_goals intro reply; exact ih reply

/-- Every actual ordinary native World component contributes zero queries to either alias-recovery oracle. -/
theorem ordinary_free (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) (before : State n KemSK) (kind : Kind) :
    ((ordinary hmac work).run before).IsQueryBoundP (Counted kind) 0 := by
  simp only [ordinary, StateT.run, isQueryBoundP_map_iff]
  exact coins_free kind _

/-- The entire actual candidate-free indexed KEM provider is simulated locally and contributes no protected-table or suffix-key call. -/
theorem routed_free (provider : Provider KemSK) (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain)
    (before : State n KemSK) (kind : Kind) :
    ((routed provider query).run before).IsQueryBoundP (Counted kind) 0 := by
  simp only [routed, StateT.run, isQueryBoundP_map_iff]
  exact coins_free kind _

/-- The concrete mixed callback bills at most one query of either class exactly at material demand. -/
theorem handler_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : (Spec n KemSK).Domain) (before : State n KemSK) (kind : Kind) :
    ((handler setup wire route sign input inside provider query).run before).IsQueryBoundP (Counted kind)
      (if IsDemand (n := n) (KemSK := KemSK) query then 1 else 0) := by
  rcases query with (message | (message | common) | kem) | record
  · simpa only [handler, roots, StateT.run, isQueryBoundP_map_iff, IsDemand, ite_false,
      RegistrationNativeSecretWordServiceCaps.IsDemand] using
      RegistrationNativeSecretWordServiceCaps.handler_bound (n := n) setup.source input inside (.inl message) before.flags kind
  · simpa only [handler, roots, StateT.run, isQueryBoundP_map_iff, IsDemand, ite_true,
      RegistrationNativeSecretWordServiceCaps.IsDemand] using
      RegistrationNativeSecretWordServiceCaps.handler_bound (n := n) setup.source input inside (.inr message) before.flags kind
  · exact ordinary_free _ _ before kind
  · exact routed_free provider kem before kind
  · exact ordinary_free _ _ before kind

/-- Every actual mixed adaptive execution inherits both ordinary recovery bills from its original material-demand allowance. -/
theorem program_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (Spec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (IsDemand (n := n) (KemSK := KemSK)) cap) (before : State n KemSK) (kind : Kind) :
    ((simulateQ (handler setup wire route sign input inside provider) work).run before).IsQueryBoundP (Counted kind) cap :=
  bounded.simulateQ_run_of_step
    (fun query counted state => by simpa only [ite_eq_left counted] using handler_bound setup wire route sign input inside provider query state kind)
    (fun query free state => by simpa only [ite_eq_right free] using handler_bound setup wire route sign input inside provider query state kind)
    before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps.ordinary_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps.ordinary_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps.routed_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps.routed_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps.program_bound
