import BeaconcryptCore.Computational.PqxdhInitialCurrentAliases
import BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound

/-!
The current initializer security capstone consumes only the actual authenticated-root source resource certificate. It derives the number of private initializer attempts, the complete actual sampler/observer uniform bills, and the ordinary Extract/HMAC challenger costs. No whole-observer bound or free ambient-work premise is supplied by the caller.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets
open PqxdhInitialCurrentAliases
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhCorrelatedExtractFamily PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhInitialLegalObserver
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))


variable (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)

/-- Every actual prepared mode makes at most one Server initializer plus one request per allowed Beacon finish, including every failed attempt. -/
theorem client_initial (context : Context env kem attachedVerify primitives program post) :
    (client env baseImpl kem attachedVerify primitives program post context).IsQueryBoundP
      PqxdhInitialRootAliases.IsInitializer (1 + c.privatePost) := by
  cases mode : context.state with
  | completed decision => simp only [client, mode]; trivial
  | pending prepared ephemeral =>
      simp only [client, mode]
      have bound := PqxdhInitialBuilderServiceBound.accepted_initial env baseImpl kem attachedVerify primitives program post c
        context.secretKey (selected env kem attachedVerify primitives program post context) prepared
        (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
          ephemeral context.ciphertext (List.Vector.replicate 32 0))
      have same : PqxdhInitialRootAliases.IsInitializer = PqxdhInitialObserverCallbackBudgets.IsService := by
        funext query
        cases query <;> simp [PqxdhInitialRootAliases.IsInitializer, PqxdhInitialObserverCallbackBudgets.IsService]
      simpa only [same] using bound

/-- The current initializer capstone has no externally supplied initializer count: the actual source certificate yields the loss (1+postFinish)/2^256. -/
theorem primitive_bound (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
 :
    (uniformGame (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
      (protocol env kem attachedVerify primitives program post))).boolDistAdvantage
      (consistentRandom env baseImpl kem attachedVerify primitives program post) ≤
    (extractRealGame hmac (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
      (fullExtractReduction hmac .ratchet (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))).boolDistAdvantage
      (extractUniformGame (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
        (fullExtractReduction hmac .ratchet (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))) +
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet
      (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
      (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))).boolDistAdvantage
      (hmacPrfRandomGame (fullExpandReduction .ratchet
        (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
        (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))) +
      (((1 + c.privatePost : Nat) : ENNReal) / (2 ^ 256 : ENNReal)).toReal :=
  PqxdhInitialCurrentAliases.primitive_bound env baseImpl kem attachedVerify primitives program post hmac correct
    (1 + c.privatePost) (client_initial env baseImpl kem attachedVerify primitives program post c)

noncomputable def qSample : Nat := c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) + c.qEncap) + 32
noncomputable def qObserver : Nat := c.uPost + c.qBase * c.bPost + c.qDecap * c.dPost + 32 * c.privatePost

/-- The exact serialized Extract sampler retains the source-derived preparation and comparison-root bill. -/
theorem joint_uniform :
    (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post).IsTotalQueryBound
      (qSample env baseImpl kem program post c) :=
  RawCtxInitialSecrecy.joint_bound _ _ (PqxdhInitialObserverBudgets.sample_uniform env baseImpl kem attachedVerify primitives program post c)

/-- Every supplied full comparison output invokes the same actual64 observer and its derived complete source bill. -/
theorem observer_uniform (context : Context env kem attachedVerify primitives program post)
    (output : FullOutput) :
    (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post context output).IsTotalQueryBound
      (qObserver env baseImpl kem program post c) :=
  PqxdhInitialObserverBudgets.observe_uniform env baseImpl kem attachedVerify primitives program post c context _

/-- The constructed ordinary HMAC reduction has two challenge queries and pays all source-derived sampler and observer uniform work. -/
theorem reduction_bounds :
    (fullExpandReduction .ratchet (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
      (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post)).IsQueryBoundP IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
      (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post)).IsQueryBoundP
        PqxdhFullSecretInputKdf.IsHmacUniformQuery
          (qSample env baseImpl kem program post c + qObserver env baseImpl kem program post c) :=
  ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ (joint_uniform env baseImpl kem attachedVerify primitives program post c)
      (observer_uniform env baseImpl kem attachedVerify primitives program post c)⟩

set_option maxRecDepth 2048 in
/-- All ordinary Extract/HMAC and full-output comparison games retain exact source-derived sampler/observer bills and separately charge their64/76/128-byte comparison work. -/
theorem challenger_uniform (hmac : HmacSha512) :

    (extractRealGame hmac (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post) (fullExtractReduction hmac .ratchet (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))).IsTotalQueryBound
        ((qSample env baseImpl kem program post c) + (qObserver env baseImpl kem program post c)) ∧
      (extractUniformGame (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post) (fullExtractReduction hmac .ratchet (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))).IsTotalQueryBound
        ((qSample env baseImpl kem program post c) + (64 + (qObserver env baseImpl kem program post c))) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post) (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))).IsTotalQueryBound
        (64 + ((qSample env baseImpl kem program post c) + (qObserver env baseImpl kem program post c))) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post) (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))).IsTotalQueryBound
        ((qSample env baseImpl kem program post c) + (64 + (64 + (qObserver env baseImpl kem program post c)))) ∧
      (independentFullGame (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post) (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post)).IsTotalQueryBound
        ((qSample env baseImpl kem program post c) + (76 + (qObserver env baseImpl kem program post c))) := by
  exact ⟨isTotalQueryBound_bind (joint_uniform env baseImpl kem attachedVerify primitives program post c) (fun pair => observer_uniform env baseImpl kem attachedVerify primitives program post c pair.1 _),
    fullExtractUniform_uniform_query_bound _ _ _ _ (joint_uniform env baseImpl kem attachedVerify primitives program post c) (observer_uniform env baseImpl kem attachedVerify primitives program post c),
    fullHmacReal_uniform_query_bound _ _ _ _ (joint_uniform env baseImpl kem attachedVerify primitives program post c) (observer_uniform env baseImpl kem attachedVerify primitives program post c),
    fullHmacRandom_uniform_query_bound _ _ _ (joint_uniform env baseImpl kem attachedVerify primitives program post c) (observer_uniform env baseImpl kem attachedVerify primitives program post c),
    independentFullGame_uniform_query_bound _ _ (joint_uniform env baseImpl kem attachedVerify primitives program post c) (observer_uniform env baseImpl kem attachedVerify primitives program post c)⟩

/-- The explicit Extract distinguisher retains the whole current source observer bill for every supplied secret PRK. -/
theorem extract_work (hmac : HmacSha512) (context : Context env kem attachedVerify primitives program post) (key : HmacBlock) :
    (fullExtractReduction hmac .ratchet (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post)
      context key).IsTotalQueryBound (qObserver env baseImpl kem program post c) :=
  observer_uniform env baseImpl kem attachedVerify primitives program post c context _

set_option maxRecDepth 2048 in
/-- The actual random64 initializer game pays exactly the literal64-byte response draw in addition to all current source sampler and observer work; no76-byte comparison cost is reassigned to it. -/
theorem random_uniform :
    (PqxdhInitialCurrentSecrecy.random env baseImpl kem attachedVerify primitives program post).IsTotalQueryBound
      (qSample env baseImpl kem program post c + (64 + qObserver env baseImpl kem program post c)) :=
  isTotalQueryBound_bind (PqxdhInitialObserverBudgets.sample_uniform env baseImpl kem attachedVerify primitives program post c)
    (fun pair => isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
      (fun _ => PqxdhInitialObserverBudgets.observe_uniform env baseImpl kem attachedVerify primitives program post c pair.1 _))

end BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.client_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.client_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.primitive_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.joint_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.joint_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.observer_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.observer_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.challenger_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.challenger_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.extract_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.extract_work

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.random_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets.random_uniform
