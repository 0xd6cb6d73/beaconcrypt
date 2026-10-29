-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemPool
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal

/-! The executable symbolic native provider contains no candidate shared-secret bytes. It retains genuine reserved creation, the current live key prefix, all typed observations and the first-getter ciphertext phase. Ordinary public encapsulations remain literal; only the first matching selected getter and later selected-handle exact-ciphertext decapsulations return the opaque atom. The original getter coin program is still executed, so the shared sampler bill is retained. Its unused uniform draw is separated from the mathematical candidate in the delayed-sampling source proof. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open PqxdhLiveKemBirth (Query)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordKemInterface (WordPoolSpec Routed)
open RegistrationNativeSecretWordKemPool (Pool eval record created)
variable {ι KemSK : Type} {base : OracleSpec ι}

abbrev Phase := Option MlKem768Ciphertext
abbrev State (KemSK : Type) := Pool KemSK × Phase

def evalState (candidate : MlKemSharedSecret) (before : State KemSK) : PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase :=
  (eval candidate before.1, before.2.map (fun ciphertext => (ciphertext, candidate)))

noncomputable def pool (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (phase : Phase) :
    QueryImpl (WordPoolSpec KemSK) (StateT (Pool KemSK) ProbComp) := fun query before =>
  match query with
  | .create => match pairs[before.keys.length]? with
    | some pair => pure (created before pair)
    | none => created before <$> simulateQ (kemAmbientImpl baseImpl) kem.keygen
  | .decapsulate handle ciphertext => do
      let answer ← match before.keys[handle]? with
        | none => pure none
        | some pair =>
            if handle = selected ∧ phase = some ciphertext then pure (some Word.atom)
            else Option.map Word.literal <$> simulateQ (kemAmbientImpl baseImpl) (kem.decaps pair.2 ciphertext)
      pure (answer, record (.decapsulate handle ciphertext) answer before)
  | .reveal handle =>
      let answer := (before.keys[handle]?).map Prod.snd
      pure (answer, record (.reveal handle) answer before)

noncomputable def ordinary (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (phase : Phase) :
    QueryImpl (Routed KemSK) (StateT (State KemSK) ProbComp)
  | .inl (.inl query) => fun before =>
      (fun result => (result, before)) <$> RegistrationNativePublicInterpreter.unavailable query
  | .inl (.inr key) => fun before =>
      (fun result => ((result.1, Word.literal result.2), before)) <$>
        simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
  | .inr (.inl query) => fun before =>
      (fun result => (result.1, (result.2, before.2))) <$> (pool baseImpl kem selected pairs phase query).run before.1
  | .inr (.inr key) => fun before =>
      (fun result => ((result.1, Word.literal result.2), before)) <$>
        simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)

noncomputable def provider (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) :
    QueryImpl (Routed KemSK) (StateT (State KemSK) ProbComp) := fun query before =>
  match before.2 with
  | some _ => (ordinary baseImpl kem selected pairs before.2 query).run before
  | none => match query with
    | .inr (.inr key) => do
        let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)
        let _ ← $ᵗ MlKemSharedSecret
        let reply ← if key = publicKey then pure (pair.1, Word.atom)
          else Prod.map id Word.literal <$> simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
        pure (reply, (before.1, some pair.1))
    | query => (ordinary baseImpl kem selected pairs none query).run before

noncomputable def ambient (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) :=
  RegistrationNativeKemRouting.publicAmbient baseImpl kem
    (fun query => (StateT.lift (RegistrationNativePublicInterpreter.unavailable query) : StateT Unit ProbComp _))

noncomputable def reference (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) :
    QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK)
      (StateT (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) ProbComp) := fun query before =>
  (fun result => (result.1, (result.2.1.2, result.2.2))) <$>
    (RegistrationNativeKemSwitchReserved.source baseImpl kem (ambient baseImpl kem) selected pairs publicKey false query).run
      (((), before.1), before.2)

/-- The retained first-getter phase contains only ciphertext bytes; evaluating it restores the supplied candidate at that exact original phase. -/
theorem eval_phase (candidate : MlKemSharedSecret) (before : Pool KemSK) (ciphertext : MlKem768Ciphertext) :
    evalState candidate (before, some ciphertext) = (eval candidate before, some (ciphertext, candidate)) := rfl

/-- Empty symbolic initialization restores the exact native empty pool and absent getter phase. -/
theorem empty_state (candidate : MlKemSharedSecret) :
    evalState (KemSK := KemSK) candidate (RegistrationNativeSecretWordKemPool.empty, none) = (PqxdhLiveKemBirth.empty, none) := rfl

def evalReply (candidate : MlKemSharedSecret) : (query : (Routed KemSK).Domain) → (Routed KemSK).Range query →
    (RegistrationNativePublicFrontend.RoutedKem KemSK).Range query
  | .inl (.inl _), value => value
  | .inl (.inr _), value => Prod.map id (Word.eval candidate) value
  | .inr (.inl query), value => RegistrationNativeSecretWordKemPool.reply candidate query value
  | .inr (.inr _), value => Prod.map id (Word.eval candidate) value

/-- After the genuine first getter, every symbolic callback evaluates to the actual total candidate provider on the same complete live pool and phase. This includes inactive dummy-ciphertext substitution and every optional failure. -/
theorem post_query (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (candidate : MlKemSharedSecret) (challenge : MlKem768Ciphertext)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : Pool KemSK) :
    (fun result => (evalReply candidate query result.1, evalState candidate result.2)) <$>
      (provider baseImpl kem selected pairs publicKey query).run (before, some challenge) =
      (reference baseImpl kem selected pairs publicKey query).run (evalState candidate (before, some challenge)) := by
  rcases query with (query | key) | query | key
  all_goals try cases query
  all_goals simp only [evalReply, RegistrationNativeSecretWordKemPool.reply, provider, ordinary, reference, evalState, Option.map_some,
    RegistrationNativeKemSwitchReserved.source, RegistrationNativeKemSwitchReserved.carry,
    RegistrationNativeKemCandidateReserved.reserved, RegistrationNativeKemReservation.reserved,
    RegistrationNativeKemInterface.source, RegistrationNativeKemRouting.publicAmbient, ambient,
    StateT.run, StateT.lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
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
        simp only [pool, eval, found, Option.some.injEq, bind_pure_comp,
          map_pure, Functor.map_map]
      · simp [record, PqxdhLiveKemBirth.record, RegistrationNativeSecretWordKemPool.observation,
          RegistrationNativeSecretWordKemPool.reply]
      · by_cases chosen : handle = selected ∧ challenge = ciphertext
        · rcases chosen with ⟨rfl, rfl⟩
          simp [record, PqxdhLiveKemBirth.record,
            RegistrationNativeSecretWordKemPool.observation, RegistrationNativeSecretWordKemPool.reply,
            Word.eval]
        · have chosen' : ¬(handle = selected ∧ ciphertext = challenge) := by
            intro yes
            exact chosen ⟨yes.1, yes.2.symm⟩
          simp only [chosen, chosen', ite_false, Functor.map_map]
          congr 1
          funext answer
          cases answer <;> simp [record, PqxdhLiveKemBirth.record,
            RegistrationNativeSecretWordKemPool.observation, RegistrationNativeSecretWordKemPool.reply,
            Word.eval]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider.eval_phase' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider.eval_phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider.empty_state' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider.empty_state

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider.post_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider.post_query
