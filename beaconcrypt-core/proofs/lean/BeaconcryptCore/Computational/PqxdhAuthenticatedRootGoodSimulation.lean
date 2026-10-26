import BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment

/-!
The actual authenticated-root experiment discharges the generic endpoint's good-sample simulation obligation. Both completed and pending modes keep their full original result. The pending branch retains the initial root computed from the encapsulated secret and the exact native builder and adaptive postchallenge schedule. Decapsulation correctness is used only as the current good-sample equation; its failure remains charged by the separate ordinary correctness-error endpoint.

The selected secret key remains private interpreter context. The ordinary CCA reduction owns its challenger-supplied shared secret inside private root routing; the executable protocol retains its permitted inputs without either secret field. No perfect correctness, successful acceptance, authentication, state preservation or new primitive security premise is supplied here.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootGoodSimulation
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhJointKdfGame PqxdhChallengeSecretRouting
open PqxdhStatefulPhase1EufCma PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateRootSource
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPrivateAcceptedRoot

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- The complete actual continuation equals the constructed ordinary routed continuation on one good functional decapsulation result. -/
theorem nativeAfter_routed (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (secretKey : KemSK)
    (mode : Mode setup (driver env.toDriverEnvironment program).State)
    (ciphertext : MlKem768Ciphertext) (shared : MlKemSharedSecret)
    (agreement : kem.decaps secretKey ciphertext = pure (some shared)) :
    nativeAfter env baseImpl kem attachedVerify primitives program post publicKey secretKey mode ciphertext shared =
      PqxdhAuthenticatedRootEndpoint.routedAfter env.source baseImpl kem
        (protocol env kem attachedVerify primitives program post) publicKey secretKey mode ciphertext shared := by
  cases mode with
  | completed decision =>
    simp only [nativeAfter, PqxdhAuthenticatedRootEndpoint.routedAfter, protocol, simulateQ_pure]
  | pending prepared ephemeral =>
    simp only [nativeAfter, PqxdhAuthenticatedRootEndpoint.routedAfter, protocol, Option.map_some]
    exact nativeAccepted_reduction env baseImpl kem attachedVerify primitives program post
      secretKey prepared _ shared agreement

/-- Actual mode dispatch and complete native postchallenge simulation discharge the endpoint obligation on every supported good sample. No additional preservation or acceptance premise remains. -/
theorem goodSimulation (functional : FunctionalDecapsulation kem) :
    PqxdhAuthenticatedRootEndpoint.GoodSimulation env.source baseImpl kem functional
      (protocol env kem attachedVerify primitives program post)
      (nativeAfter env baseImpl kem attachedVerify primitives program post) := by
  intro keys _ state _ pair _ good
  exact nativeAfter_routed env baseImpl kem attachedVerify primitives program post
    keys.1 keys.2 state pair.1 pair.2
    ((functional.exact keys.2 pair.1).trans (congrArg pure good))

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootGoodSimulation

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootGoodSimulation.nativeAfter_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootGoodSimulation.nativeAfter_routed

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootGoodSimulation.goodSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootGoodSimulation.goodSimulation
