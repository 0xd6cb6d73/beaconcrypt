-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyOnline

/-! The executable concrete early provider is the routed specialization of the generic online early-CCA source. The embedding adds only an empty auxiliary coordinate and retains the complete private pool, transcript and getter marker. Its whole-program corollary removes only that empty coordinate and the private marker. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline
open PqxdhKemIndCca
open RegistrationNativeKemEarlyOnline (online)
open RegistrationNativeSecretWordKemEarly (actual actualOrdinary)
open RegistrationNativeSecretWordKemProvider (ambient)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev ActualState (KemSK : Type) := PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase

def embed (before : ActualState KemSK) : RegistrationNativeKemEarlyOnline.State Unit KemSK :=
  (((), before.1), before.2)

private theorem ordinary_embed (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : ActualState KemSK) :
    Prod.map id embed <$> (actualOrdinary baseImpl kem selected pairs challenge candidate query).run before =
      RegistrationNativeKemEarlyOnline.carry before.2 <$>
        (RegistrationNativeKemCandidateReserved.reserved baseImpl kem (ambient baseImpl kem)
          selected pairs challenge candidate query).run ((), before.1) := by
  simp only [actualOrdinary, StateT.run, Functor.map_map]
  congr 1

/-- The exact concrete routed early provider retains its complete pool and phase through the generic online source. -/
theorem query_embed (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : ActualState KemSK) :
    Prod.map id embed <$> (actual baseImpl kem selected pairs publicKey challenge candidate query).run before =
      (online baseImpl kem (ambient baseImpl kem) selected pairs publicKey challenge candidate query).run (embed before) := by
  rcases query with query | (query | key)
  all_goals try (simpa only [actual, online, StateT.run, embed] using
    ordinary_embed baseImpl kem selected pairs challenge candidate _ before)
  cases phase : before.2 with
  | some value =>
      simpa only [actual, online, StateT.run, embed, phase] using
        ordinary_embed baseImpl kem selected pairs challenge candidate (.inr (.inr key)) before
  | none =>
      by_cases matching : key = publicKey <;>
        simp only [actual, online, StateT.run, embed, phase, matching, ite_true, ite_false,
          map_bind, map_pure, Prod.map_def, id_eq]

/-- Arbitrary adaptive native continuations preserve the entire actual routed provider state under this literal embedding. -/
theorem program_embed (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (RegistrationNativePublicFrontend.RoutedKem KemSK) Value) (before : ActualState KemSK) :
    Prod.map id embed <$> (simulateQ (actual baseImpl kem selected pairs publicKey challenge candidate) work).run before =
      (simulateQ (online baseImpl kem (ambient baseImpl kem) selected pairs publicKey challenge candidate) work).run (embed before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed
    (query_embed baseImpl kem selected pairs publicKey challenge candidate) work before

/-- The concrete early provider executes the unchanged whole routed native program with the exact early ordinary-CCA source distribution, including all indexed-key and reply history state. -/
theorem program_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (RegistrationNativePublicFrontend.RoutedKem KemSK) Bool) (before : PqxdhLiveKemBirth.Pool KemSK) :
    ((fun result => (result.1, result.2.1)) <$>
      (simulateQ (actual baseImpl kem selected pairs publicKey challenge candidate) work).run (before, none)) =ᵈ
      (Prod.map id Prod.snd <$>
        (simulateQ (RegistrationNativeKemCandidateReserved.reserved baseImpl kem (ambient baseImpl kem)
          selected pairs challenge candidate)
          (RegistrationNativeKemEarlyGame.intercept publicKey challenge candidate work)).run ((), before)) := by
  have source := (RegistrationNativeKemEarlyOnline.program_source baseImpl kem (ambient baseImpl kem)
    selected pairs publicKey challenge candidate work ((), before)).map (Prod.map id Prod.snd)
  have embedded := program_embed baseImpl kem selected pairs publicKey challenge candidate work (before, none)
  simp only [embed] at embedded
  rw [← embedded] at source
  simpa only [Functor.map_map, embed, Prod.map_def, id_eq, Function.comp_def] using source
end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline.query_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline.query_embed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline.program_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline.program_embed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline.program_source
