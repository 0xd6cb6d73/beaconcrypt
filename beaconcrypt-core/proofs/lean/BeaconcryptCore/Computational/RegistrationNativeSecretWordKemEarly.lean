-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider

/-! An early ordinary-CCA challenge protects exact selected-handle decapsulation from the handle's genuine birth, including before the selected Server getter. The public ciphertext is a provider parameter; the opaque candidate is absent from executable state. The same optional phase records only whether the selected getter has run. Missing handles, nonmatching getters, other ciphertexts and the complete native reply transcript retain their original behavior. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open PqxdhLiveKemBirth (Query)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordKemInterface (Routed)
open RegistrationNativeSecretWordKemPool (Pool eval record created)
open RegistrationNativeSecretWordKemProvider (State evalState evalReply ordinary pool ambient)
variable {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def early (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) : QueryImpl (Routed KemSK) (StateT (State KemSK) ProbComp) := fun query before =>
  match query, before.2 with
  | .inr (.inr key), none => do
      let _ ← $ᵗ MlKemSharedSecret
      let reply ← if key = publicKey then pure (challenge, Word.atom)
        else Prod.map id Word.literal <$> simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
      pure (reply, (before.1, some challenge))
  | query, _ => (ordinary baseImpl kem selected pairs (some challenge) query).run before

noncomputable def actualOrdinary (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK)
      (StateT (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) ProbComp) := fun query before =>
  (fun result => (result.1, (result.2.2, before.2))) <$>
    (RegistrationNativeKemCandidateReserved.reserved baseImpl kem (ambient baseImpl kem) selected pairs challenge candidate query).run
      ((), before.1)

noncomputable def actual (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK)
      (StateT (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) ProbComp) := fun query before =>
  match query, before.2 with
  | .inr (.inr key), none => do
      let _ ← $ᵗ MlKemSharedSecret
      let reply ← if key = publicKey then pure (challenge, candidate)
        else simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
      pure (reply, (before.1, some (challenge, candidate)))
  | query, _ => (actualOrdinary baseImpl kem selected pairs challenge candidate query).run before

/-- The ordinary portion of the early provider restores every native reply, generated key, typed transcript and current getter marker. -/
theorem ordinary_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : (Routed KemSK).Domain) (before : State KemSK) :
    (fun result => (evalReply candidate query result.1, evalState candidate result.2)) <$>
      (ordinary baseImpl kem selected pairs (some challenge) query).run before =
      (actualOrdinary baseImpl kem selected pairs challenge candidate query).run (evalState candidate before) := by
  rcases before with ⟨before, phase⟩
  rcases query with (query | key) | query | key
  all_goals try cases query
  all_goals simp only [evalReply, RegistrationNativeSecretWordKemPool.reply, ordinary, actualOrdinary,
    evalState, RegistrationNativeKemCandidateReserved.reserved, RegistrationNativeKemReservation.reserved,
    RegistrationNativeKemInterface.source, RegistrationNativeKemRouting.publicAmbient, ambient,
    StateT.run, StateT.lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, Word.eval]
  all_goals try rfl
  case create =>
    cases found : pairs[before.keys.length]? <;>
      simp [pool, eval, created, record, PqxdhLiveKemBirth.poolImpl, PqxdhLiveKemBirth.created,
        PqxdhLiveKemBirth.record, found, RegistrationNativeSecretWordKemPool.observation,
        RegistrationNativeSecretWordKemPool.reply, Functor.map_map]
  case reveal handle =>
    simp [pool, eval, record, PqxdhLiveKemBirth.poolImpl, PqxdhLiveKemBirth.record,
      RegistrationNativeSecretWordKemPool.observation, RegistrationNativeSecretWordKemPool.reply]
  case decapsulate handle ciphertext =>
    cases found : before.keys[handle]? <;>
      simp only [pool, eval, found, Option.some.injEq, bind_pure_comp, map_pure, Functor.map_map]
    · simp [record, PqxdhLiveKemBirth.record, RegistrationNativeSecretWordKemPool.observation,
        RegistrationNativeSecretWordKemPool.reply]
    · by_cases chosen : handle = selected ∧ challenge = ciphertext
      · rcases chosen with ⟨rfl, rfl⟩
        simp [record, PqxdhLiveKemBirth.record, RegistrationNativeSecretWordKemPool.observation,
          RegistrationNativeSecretWordKemPool.reply, Word.eval]
      · have chosen' : ¬(handle = selected ∧ ciphertext = challenge) := by
          intro yes
          exact chosen ⟨yes.1, yes.2.symm⟩
        simp only [chosen, chosen', ite_false, Functor.map_map]
        congr 1
        funext answer
        cases answer <;> simp [record, PqxdhLiveKemBirth.record, RegistrationNativeSecretWordKemPool.observation,
          RegistrationNativeSecretWordKemPool.reply, Word.eval]

/-- Every early-provider query evaluates to its exact concrete candidate source, including pre-getter selected decapsulation and a nonmatching first getter. -/
theorem query_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (Routed KemSK).Domain) (before : State KemSK) :
    (fun result => (evalReply candidate query result.1, evalState candidate result.2)) <$>
      (early baseImpl kem selected pairs publicKey challenge query).run before =
      (actual baseImpl kem selected pairs publicKey challenge candidate query).run (evalState candidate before) := by
  rcases before with ⟨before, marker⟩
  rcases query with (query | key) | query | key
  all_goals try cases query
  all_goals try (simpa only [early, actual, evalState, StateT.run] using
    ordinary_source baseImpl kem selected pairs challenge candidate _ (before, marker))
  case inr.inr =>
    cases marker with
    | some value => simpa only [early, actual, evalState, Option.map_some, StateT.run] using
        ordinary_source baseImpl kem selected pairs challenge candidate (.inr (.inr key)) (before, some value)
    | none =>
        by_cases matching : key = publicKey <;>
          simp [early, actual, evalState, evalReply, StateT.run, matching, Word.eval, Prod.map_def,
            map_bind, map_pure, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly.ordinary_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly.query_source
