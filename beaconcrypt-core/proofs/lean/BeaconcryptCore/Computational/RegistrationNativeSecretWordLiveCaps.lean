-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCaps

/-! Structural zero-demand and name-specific material bounds give actual preparation safety at every reached checked prefix. The concrete flag-extension theorem supplies monotonicity; no global preparation certificate or source equation is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec LocalSpec WordPairedPublicSpec)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared Prepared)
open RegistrationNativeSecretWordLiveFlags (Valid)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def Bad (flags : Message → Bool) : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inl message))) => flags message = false
  | _ => False

def BadLocal (flags : Message → Bool) : (LocalSpec n KemSK).Domain → Prop
  | .inr (.inl (.inl message)) => flags message = false
  | _ => False

def BadPublic (flags : Message → Bool) : (WordPairedPublicSpec n).Domain → Prop
  | .inl message => flags message = false
  | .inr _ => False

instance (flags : Message → Bool) : DecidablePred (Bad (n := n) (KemSK := KemSK) flags) := fun query => by
  rcases query with (_ | (message | _) | _) | _
  all_goals first | exact isFalse id | exact inferInstanceAs (Decidable (flags message = false))

instance (flags : Message → Bool) : DecidablePred (BadLocal (n := n) (KemSK := KemSK) flags) := fun query => by
  rcases query with _ | (message | _) | _
  all_goals first | exact isFalse id | exact inferInstanceAs (Decidable (flags message = false))

instance (flags : Message → Bool) : DecidablePred (BadPublic (n := n) flags) := fun query => by
  cases query with
  | inl message => exact inferInstanceAs (Decidable (flags message = false))
  | inr query => exact isFalse id

/-- An actual symbolic program demanding only names already flagged at its entry remains preparation-safe at every reached checked continuation. -/
theorem of_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK) (valid : Valid input before)
    (bounded : work.IsQueryBoundP (Bad (KemSK := KemSK) before.flags) 0) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider) work before := by
  have queries := (isQueryBoundP_zero_iff work (fun query => ¬Bad (KemSK := KemSK) before.flags query)).mp
    (by simpa only [not_not] using bounded)
  apply RegistrationNativeSecretWordLivePrefix.supplied setup wire route sign input inside provider work before valid
  apply queries.mono
  intro query safe
  rcases query with (message | (message | common) | kem) | record
  · trivial
  · intro _realized
    exact Bool.eq_true_of_not_eq_false safe
  · trivial
  · trivial
  · trivial

/-- The actual zero-demand AST bill directly supplies preparation safety, including every optional failure continuation. -/
theorem no_demand (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK) (valid : Valid input before)
    (free : work.IsQueryBoundP (RegistrationNativeSecretWordFrontendCaps.IsDemand (KemSK := KemSK)) 0) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider) work before := by
  apply of_bound setup wire route sign input inside provider work before valid
  apply IsQueryBoundP.of_imp _ free
  intro query bad
  rcases query with (message | (message | common) | kem) | record
  · exact bad.elim
  · trivial
  · exact bad.elim
  · exact bad.elim
  · exact bad.elim

/-- Actual local routing preserves the identity of every material name and hence its concrete zero-unprepared-demand bill. -/
theorem local_bound (flags : Message → Bool) (selected : Bool)
    (work : OracleComp (LocalSpec n KemSK) Value) (bounded : work.IsQueryBoundP (BadLocal (KemSK := KemSK) flags) 0) :
    (simulateQ (RegistrationNativeSecretWordInterface.liftLocal selected) work).IsQueryBoundP (Bad (KemSK := KemSK) flags) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  rcases query with message | (message | common) | kem
  · simp [RegistrationNativeSecretWordInterface.liftLocal, Bad, BadLocal, isQueryBoundP_query_iff]
  · simp [RegistrationNativeSecretWordInterface.liftLocal, Bad, BadLocal, isQueryBoundP_query_iff]
    intro absent
    simp only [absent, ite_true]
    decide
  · simp [RegistrationNativeSecretWordInterface.liftLocal, Bad, BadLocal, isQueryBoundP_query_iff]
  · rcases kem with other | (pool | key)
    · simp [RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordInterface.route,
        RegistrationNativeSecretWordInterface.routedKem, Bad, BadLocal, isQueryBoundP_query_iff]
    · simp [RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordInterface.route,
        RegistrationNativeSecretWordInterface.routedKem, Bad, BadLocal, isQueryBoundP_query_iff]
    · cases selected <;> simp [RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordInterface.route,
        RegistrationNativeSecretWordInterface.routedKem, Bad, BadLocal, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps.of_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps.of_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps.no_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps.no_demand
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps.local_bound
