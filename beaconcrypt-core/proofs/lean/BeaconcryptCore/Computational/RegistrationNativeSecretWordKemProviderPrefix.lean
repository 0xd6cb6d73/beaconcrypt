-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPoolLiteral

/-! Before the first selected getter, ordinary callbacks use literal KEM replies and retain the absent phase. Their evaluated source is the actual reserved native provider, including public encapsulations and all optional indexed failures. The actual getter's independent counted draw is handled separately. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProviderPrefix
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open PqxdhLiveKemBirth (Query)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordKemPool (Pool eval record created)
open RegistrationNativeSecretWordKemProvider (evalState evalReply provider ordinary reference pool ambient)
variable {ι KemSK : Type} {base : OracleSpec ι}

/-- Every ordinary prechallenge query retains the exact source reply, complete generated keys/transcript and absent first-getter phase. -/
theorem query_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (candidate : MlKemSharedSecret) (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain)
    (ordinaryQuery : ¬RegistrationNativeKemRouting.IsExposed query) (before : Pool KemSK) :
    (fun result => (evalReply candidate query result.1, evalState candidate result.2)) <$>
      (provider baseImpl kem selected pairs publicKey query).run (before, none) =
      (reference baseImpl kem selected pairs publicKey query).run (evalState candidate (before, none)) := by
  rcases query with (query | key) | query | key
  all_goals try cases query
  all_goals try exact False.elim (ordinaryQuery trivial)
  all_goals simp only [evalReply, RegistrationNativeSecretWordKemPool.reply, provider, ordinary,
    reference, evalState, Option.map_none, RegistrationNativeKemSwitchReserved.source,
    RegistrationNativeKemSwitchReserved.carry, RegistrationNativeKemReservation.reserved,
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
      simp only [pool, eval, found, reduceCtorEq, and_false, ite_false,
        bind_pure_comp, map_pure, Functor.map_map, PqxdhLiveKemBirth.poolImpl]
    · simp [record, PqxdhLiveKemBirth.record, RegistrationNativeSecretWordKemPool.observation,
        RegistrationNativeSecretWordKemPool.reply]
    · try simp only [bind_pure_comp, Functor.map_map]
      congr 1
      funext answer
      cases answer <;> simp [record, PqxdhLiveKemBirth.record, RegistrationNativeSecretWordKemPool.observation,
        RegistrationNativeSecretWordKemPool.reply, Word.eval]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProviderPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProviderPrefix.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProviderPrefix.query_source
