-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound

/-! One actual alias client samples the complete candidate-independent KEM family/challenge context through its ordinary coin surface before running the original frontend. Its complete recovery adversary therefore owns that prior sampling once, and no average of absolute PRF advantages is substituted for one explicit advantage. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordService (Combined coins)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value P : Type} {base : OracleSpec ι}

structure Profile (KemSK : Type) where
  pairs : List (MlKem768PublicKey × KemSK)
  publicKey : MlKem768PublicKey
  challenge : MlKem768Ciphertext

private theorem probability_source {S A : Type}
    (handler : QueryImpl Combined (StateT S ProbComp))
    (coin : ∀ query before, (handler (.inl (.inl query))).run before =
      (fun reply => (reply, before)) <$> (unifSpec.query query : ProbComp _))
    (work : ProbComp A) (before : S) :
    (simulateQ handler (simulateQ coins work)).run before = (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : handler ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) := by
    funext query
    apply StateT.ext
    intro current
    simp only [QueryImpl.compose, coins, simulateQ_spec_query, QueryImpl.liftTarget_apply]
    change handler (.inl (.inl query)) current =
      ((unifSpec.query query : ProbComp _) >>= fun reply => pure (reply, current))
    rw [bind_pure_comp]
    exact coin query current
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem logged_coins (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (query : unifSpec.Domain) (before : RegistrationNativeSecretWord.Cache × List Secret) :
    (RawCtxSelectedQueryTrace.recorded (RegistrationNativeSecretWordRecoveryCompiler.closed keySource candidate)
      RegistrationNativeSecretWordRecoveryCompiler.literals (.inl (.inl query))).run before =
      (fun reply => (reply, before)) <$> (unifSpec.query query : ProbComp _) := by
  simp only [RawCtxSelectedQueryTrace.recorded, RegistrationNativeSecretWordRecoveryCompiler.closed,
    RegistrationNativeSecretWordRecoveryCompiler.literals, RegistrationNativeSecretWord.literals,
    RegistrationNativeSecretWord.symbolic, RegistrationNativeG3CellEager.lazy,
    StateT.run, List.append_nil, bind_pure_comp,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift, ]
  change (fun result => (result.1, (result.2, before.2))) <$>
    ((unifSpec.query query : ProbComp _) >>= fun reply => pure (reply, before.1)) = _
  rw [bind_pure_comp, Functor.map_map]

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (selected selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
  (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

noncomputable def inner (profile : Profile KemSK) :=
  RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign
    (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
    (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected profile.pairs profile.publicKey profile.challenge)
    selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem

noncomputable def client (prior : ProbComp (Profile KemSK)) := do
  let profile ← simulateQ coins prior
  inner setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem profile

/-- All original suffix/key bills remain the original build-plus-finish allowance after the actual complete prior is sampled by ordinary coins. -/
theorem client_bound (prior : ProbComp (Profile KemSK)) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (kind : Kind) :
    (client setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem prior).IsQueryBoundP
      (Counted kind) (budget.cap 4 + budget.cap 5) := by
  apply (OracleComp.isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) ?_ ?_).mono (by omega)
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ prior 0 (isQueryBoundP_false prior 0)
    intro query
    cases kind <;> simp [coins, Counted, RegistrationNativeSecretWordRecoveryCompiler.IsKey,
      RegistrationNativeSecretWordRecoveryCompiler.IsSuffix, RegistrationNativeSecretWord.IsKey, isQueryBoundP_query_iff]
  · intro profile _possible
    exact RegistrationNativeSecretWordAliasClient.client_bound setup checks wire source route sign _ _ _
      selected selectedAccept publicPrekey serverKeyId bounds mode work budget bounded front ordinary kem kind

/-- Actual prior coins leave the complete symbolic cache and literal log untouched, so the same original frontend execution follows from the actual empty state. -/
theorem logged_source (prior : ProbComp (Profile KemSK)) (candidate : Secret) :
    RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (client setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem prior) =
      (do let profile ← prior
          RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
            (inner setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem profile)) := by
  unfold RegistrationNativeSecretWordRecoveryBound.logged client
  simp only [simulateQ_bind, StateT.run_bind]
  rw [probability_source _ (logged_coins setup.source candidate)]
  simp only [bind_map_left]

/-- Actual prior coins also preserve the entire literal byte cache before the same original frontend resumes. -/
theorem bytes_source (prior : ProbComp (Profile KemSK)) (candidate : Secret) :
    (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
      (client setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem prior)).run ∅ =
      (do let profile ← prior
          (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
            (inner setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem profile)).run ∅) := by
  unfold client
  simp only [simulateQ_bind, StateT.run_bind]
  rw [probability_source]
  · simp only [bind_map_left]
  · intro query before
    rfl

/-- Sampling the full candidate-independent prior inside the actual outer client has the same observed byte law as sampling that prior before the uniformly hidden candidate. -/
theorem bytesView_source {Observation : Type} (prior : ProbComp (Profile KemSK))
    (observe : Secret → (RegistrationNativeSecretWordAliasClient.Result source n KemSK Value ×
      RegistrationNativeSecretWordSource.ByteCache) → Observation) :
    RegistrationNativeSecretWordRecoveryBound.bytesView setup.source observe
      (client setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem prior) =ᵈ
      (do let profile ← prior
          RegistrationNativeSecretWordRecoveryBound.bytesView setup.source observe
            (inner setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem profile)) := by
  simp only [RegistrationNativeSecretWordRecoveryBound.bytesView, bytes_source, map_bind]
  exact OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Secret) prior _

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter.logged_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter.logged_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter.bytes_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter.bytes_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter.bytesView_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter.bytesView_source
