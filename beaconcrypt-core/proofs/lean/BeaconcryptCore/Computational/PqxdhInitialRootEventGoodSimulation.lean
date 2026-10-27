import BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint
import BeaconcryptCore.Computational.PqxdhInitialRootEventSource

/-!
The actual authenticated-root experiment discharges the generic endpoint's good-sample simulation obligation. Both completed and pending modes keep their full original result. The pending branch retains the initial root computed from the encapsulated secret and the exact native builder and adaptive postchallenge schedule. Decapsulation correctness is used only as the current good-sample equation; its failure remains charged by the separate ordinary correctness-error endpoint.

The selected secret key remains private interpreter context. The ordinary CCA reduction owns its challenger-supplied shared secret inside private root routing; the executable protocol retains its permitted inputs without either secret field. No perfect correctness, successful acceptance, authentication, state preservation or new primitive security premise is supplied here.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootEventGoodSimulation
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhJointKdfGame PqxdhChallengeSecretRouting
open PqxdhStatefulPhase1EufCma PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateRootSource
open PqxdhPhase2GeneratedDriver PqxdhInitialRootEventExperiment PqxdhPrivateAcceptedRoot
open PqxdhAuthenticatedRootExperiment (Post)

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)

/-- The complete actual continuation equals the constructed ordinary routed continuation on one good functional decapsulation result. -/
theorem nativeAfter_routed (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (secretKey : KemSK)
    (mode : Mode setup (driver env.toDriverEnvironment program).State)
    (ciphertext : MlKem768Ciphertext) (shared : MlKemSharedSecret)
    (agreement : kem.decaps secretKey ciphertext = pure (some shared)) :
    nativeAfter env baseImpl kem attachedVerify primitives program post accepted publicKey secretKey mode ciphertext shared =
      PqxdhAuthenticatedRootEndpoint.routedAfter env.source baseImpl kem
        (protocol env kem attachedVerify primitives program post accepted) publicKey secretKey mode ciphertext shared := by
  cases mode with
  | completed decision =>
    simp only [nativeAfter, PqxdhAuthenticatedRootEndpoint.routedAfter, protocol, PqxdhAuthenticatedRootExperiment.protocol, simulateQ_pure]
  | pending prepared ephemeral =>
    simp only [nativeAfter, PqxdhAuthenticatedRootEndpoint.routedAfter, protocol, PqxdhAuthenticatedRootExperiment.protocol, Option.map_some]
    exact nativeAccepted_reduction env baseImpl kem attachedVerify primitives program post accepted
      secretKey prepared _ shared agreement

/-- Actual mode dispatch and complete native postchallenge simulation discharge the endpoint obligation on every supported good sample. No additional preservation or acceptance premise remains. -/
theorem goodSimulation (functional : FunctionalDecapsulation kem) :
    PqxdhAuthenticatedRootEndpoint.GoodSimulation env.source baseImpl kem functional
      (protocol env kem attachedVerify primitives program post accepted)
      (nativeAfter env baseImpl kem attachedVerify primitives program post accepted) := by
  intro keys _ state _ pair _ good
  exact nativeAfter_routed env baseImpl kem attachedVerify primitives program post accepted
    keys.1 keys.2 state pair.1 pair.2
    ((functional.exact keys.2 pair.1).trans (congrArg pure good))

end BeaconcryptCore.Computational.PqxdhInitialRootEventGoodSimulation

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventGoodSimulation.nativeAfter_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventGoodSimulation.nativeAfter_routed

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventGoodSimulation.goodSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventGoodSimulation.goodSimulation
