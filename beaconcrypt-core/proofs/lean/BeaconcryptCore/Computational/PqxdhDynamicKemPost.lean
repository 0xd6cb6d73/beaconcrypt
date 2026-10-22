import BeaconcryptCore.Computational.PqxdhDynamicKemRouter

/-!
Postchallenge dynamic routing evaluates the selected exact ciphertext using the challenger candidate, and every other selected ciphertext through the ordinary blocked CCA interface. The full real-source comparison consumes the existing functional decapsulation and ordinary recipient correctness contract. This substitution does not identify independent owners whose public bytes or output bytes coincide. The candidate is supplied as internal reduction input and returned to the source client on that exact selected request. These generic clients are unrestricted; candidate nonexposure requires the later source/adversary boundary.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemPost
open PqxdhDynamicKemRouter PqxdhKemIndCca PqxdhPrivateKemSource
open PqxdhLiveKemBirth (Query PoolSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

noncomputable def evaluate (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (MlKemCCAOracleSpec baseSpec) Result) : ProbComp Result :=
  simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_postChallengeImpl secret challenge) client)

set_option backward.isDefEq.respectTransparency false in
/-- Local other-key primitive work is interpreted exactly, with every original ambient request retained. -/
theorem ambient (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (unifSpec + baseSpec) Result) :
    evaluate baseImpl kem secret challenge (ccaAmbient client) =
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [ccaAmbient, simulateQ_bind, simulateQ_spec_query, evaluate]
      have baseQuery : simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
          (kem.IND_CCA_postChallengeImpl secret challenge (.inl query)) =
            PqxdhInitializerSecrecy.kemAmbientImpl baseImpl query := by
        unfold KEMScheme.IND_CCA_postChallengeImpl QueryImpl.add
        simp only [QueryImpl.liftTarget_self, QueryImpl.id'_apply, simulateQ_spec_query]
      rw [baseQuery]
      change (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl query >>= fun answer =>
        evaluate baseImpl kem secret challenge (ccaAmbient (next answer))) = _
      simp only [ih]

set_option backward.isDefEq.respectTransparency false in
/-- The real supplied candidate recovers the exact source decapsulation on every indexed path. Recipient correctness is needed only for the selected challenge ciphertext. -/
theorem decapsulation_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (selected : Nat) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some candidate))
    (keys : Reservation KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) :
    evaluate baseImpl kem secret challenge (postDecapsulation kem selected challenge candidate keys index ciphertext) =
      evalKem baseImpl kem secret (PqxdhLiveKemRouting.pre kem selected keys (default, index) ciphertext) := by
  classical
  cases found : keys index with
  | none => simp [postDecapsulation, PqxdhLiveKemRouting.pre, found, evaluate, evalKem]
  | some pair =>
      by_cases owner : index = selected
      · subst index
        by_cases same : ciphertext = challenge
        · subst ciphertext
          simp [postDecapsulation, PqxdhLiveKemRouting.pre, found, evaluate, evalKem,
            PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl, KEMScheme.IND_CCA_preChallengeImpl,
            QueryImpl.add, agreement]
        · simp [postDecapsulation, PqxdhLiveKemRouting.pre, found, same, evaluate, evalKem,
            PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl, KEMScheme.IND_CCA_preChallengeImpl,
            KEMScheme.IND_CCA_postChallengeImpl, QueryImpl.add]
      · cases key : pair.2 <;>
          simp only [postDecapsulation, PqxdhLiveKemRouting.pre, found, ite_eq_right owner, key]
        · rfl
        · rw [ambient, evalKem_ambient]

set_option backward.isDefEq.respectTransparency false in
/-- Before and after challenge, each dynamic callback retains the same full state and stopping behavior on the real supplied secret. -/
theorem step_pre (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (selected : Nat) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some candidate))
    (reservation : Reservation KemSK) (query : Query) (state : State KemSK) :
    evaluate baseImpl kem secret challenge (((post kem selected reservation challenge candidate query).run).run state) =
      evalKem baseImpl kem secret (((pre kem selected reservation query).run).run state) := by
  cases query with
  | create =>
      cases found : reservation state.created <;>
        simp [post, pre, router, OptionT.run_mk, StateT.run, found, evaluate, evalKem]
  | reveal index =>
      cases found : lookup reservation state index with
      | none => simp [post, pre, router, OptionT.run_mk, StateT.run, found, evaluate, evalKem]
      | some pair =>
          by_cases chosen : index = selected
          · subst index
            simp [post, pre, router, OptionT.run_mk, StateT.run, found, evaluate, evalKem]
          · simp [post, pre, router, OptionT.run_mk, StateT.run, found, chosen, evaluate, evalKem]
  | decapsulate index ciphertext =>
      simp only [post, pre, router, OptionT.run_mk, StateT.run, bind_pure_comp]
      change evaluate baseImpl kem secret challenge
        ((fun reply => (some reply, record (.decapsulate index ciphertext) reply state)) <$>
          postDecapsulation kem selected challenge candidate (lookup reservation state) index ciphertext) =
        evalKem baseImpl kem secret
          ((fun reply => (some reply, record (.decapsulate index ciphertext) reply state)) <$>
            PqxdhLiveKemRouting.pre kem selected (lookup reservation state) (default, index) ciphertext)
      simpa only [evaluate, evalKem, simulateQ_map] using
        congrArg (Functor.map (fun reply => (some reply, record (.decapsulate index ciphertext) reply state)))
          (decapsulation_source baseImpl kem secret selected challenge candidate agreement (lookup reservation state) index ciphertext)

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive postchallenge source program, including creation and selected-reveal stopping, preserves its complete state through the blocked ordinary CCA interpretation. -/
theorem program_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some candidate))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK) :
    evaluate baseImpl kem secret challenge
      (((simulateQ (post kem selected (redact selected pairs) challenge candidate) client).run).run state) =
      (((simulateQ (source baseImpl kem selected pairs) client).run).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      change evaluate baseImpl kem secret challenge
        (((post kem selected (redact selected pairs) challenge candidate query).run).run state >>= fun result =>
          (result.1.elim (pure none) (fun value => (simulateQ (post kem selected (redact selected pairs) challenge candidate) (next value)).run)).run result.2) = _
      unfold evaluate
      simp only [simulateQ_bind]
      rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (kem.IND_CCA_postChallengeImpl secret challenge)
          (((post kem selected (redact selected pairs) challenge candidate query).run).run state)) =
            (((source baseImpl kem selected pairs query).run).run state)
        from (step_pre baseImpl kem secret selected challenge candidate agreement (redact selected pairs) query state).trans
          (PqxdhDynamicKemRouter.step_source baseImpl kem selected pairs target secret present query state)]
      apply bind_congr
      rintro ⟨none | reply, after⟩
      · rfl
      · exact ih reply after

/-- Ordinary recipient correctness on the actual keygen and encapsulation support supplies the only special-ciphertext premise. There is no public-key injectivity or additional protocol-authentication assumption. -/
theorem supported_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret))
    (generated : (target, secret) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (encapsulated : (challenge, candidate) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps target)))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK) :
    evaluate baseImpl kem secret challenge
      (((simulateQ (post kem selected (redact selected pairs) challenge candidate) client).run).run state) =
      (((simulateQ (source baseImpl kem selected pairs) client).run).run state) :=
  program_source baseImpl kem selected pairs target secret present challenge candidate
    (PqxdhChallengeSecretRouting.honest_decapsulation_program baseImpl kem functional correct generated encapsulated) client state

end BeaconcryptCore.Computational.PqxdhDynamicKemPost

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemPost.ambient' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemPost.ambient
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemPost.decapsulation_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemPost.decapsulation_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemPost.step_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemPost.step_pre
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemPost.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemPost.program_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemPost.supported_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemPost.supported_source
