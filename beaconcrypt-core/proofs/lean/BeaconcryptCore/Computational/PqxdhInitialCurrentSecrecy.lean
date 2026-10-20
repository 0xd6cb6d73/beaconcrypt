import BeaconcryptCore.Computational.PqxdhInitialLegalObserver
import BeaconcryptCore.Computational.RawCtxInitialSecrecy

/-!
The actual current uniform-root endpoint is connected to ordinary fixed-salt Extract and uniform-secret HMAC PRF through its root-free response observer. The exact sampler retains all pre-root preparation and then draws an independent32-byte root. A single selected coordinate supplies the same complete64-byte initializer response to both actual role constructors and every repeat. Other coordinates and public HKDF remain real. This one-coordinate hybrid does not assume coordinate-to-root injectivity or independent output per ownership event.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdf PqxdhJointKdfGame
open PqxdhInitialRootLabelService PqxdhInitialLegalObserver PqxdhKemIndCca
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- The typed response at the actual initializer request is exactly the first64 bytes of the same fixed76-byte expansion. No nonce is introduced into source initialization. -/
theorem response_prefix (fixed : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    realInitial fixed root = RawCtxSelectedInitialConstructor.response64
      (initialPrefix (productionStream fixed.crypto (FixedHkdfDomain.ratchet.address root.toList))) := by
  have shared := PqxdhRootTableInitialization.initialResponse_prefix fixed root
  simp only [PqxdhRootTableInitialization.initialResponse_bytes] at shared
  unfold realInitial RawCtxSourceHkdf.initialResponse RawCtxSelectedInitialConstructor.response64
  congr 2
  exact congrArg (List.map BeaconcryptCore.Refinement.ProtocolComposition.concreteByte) shared

section Current
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

noncomputable def joint : SecretInputSampler (Context env kem attachedVerify primitives program post) :=
  RawCtxInitialSecrecy.joint (sample env baseImpl kem attachedVerify primitives program post)

noncomputable def observer : FullObserver (Context env kem attachedVerify primitives program post) :=
  fun context output => observe env baseImpl kem attachedVerify primitives program post context
    (RawCtxSelectedInitialConstructor.response64 (initialPrefix output))

noncomputable def random : ProbComp Bool := do
  let (context, _) ← sample env baseImpl kem attachedVerify primitives program post
  let output ← $ᵗ HmacBlock
  observe env baseImpl kem attachedVerify primitives program post context
    (RawCtxSelectedInitialConstructor.response64 output)

/-- The full-output comparison observer consumes exactly the typed64 source response at the current prepared-context sampler. -/
theorem source_game :
    sourceFullGame env.source .ratchet (joint env baseImpl kem attachedVerify primitives program post)
      (observer env baseImpl kem attachedVerify primitives program post) =
      (sample env baseImpl kem attachedVerify primitives program post >>= fun pair =>
        observe env baseImpl kem attachedVerify primitives program post pair.1 (realInitial env.source pair.2)) := by
  simp only [sourceFullGame, joint, RawCtxInitialSecrecy.joint, bind_map_left, observer, response_prefix]

/-- The comparison's uniform76 output exposes only its first64 bytes, giving exactly the actual64 response distribution for the complete current continuation. -/
theorem random_comparison :
    𝒟[independentFullGame (joint env baseImpl kem attachedVerify primitives program post)
      (observer env baseImpl kem attachedVerify primitives program post)] =
      𝒟[random env baseImpl kem attachedVerify primitives program post] := by
  apply evalDist_eq_of_evalSPMF_eq
  simp only [independentFullGame, joint, RawCtxInitialSecrecy.joint, bind_map_left, random]
  refine evalSPMF_bind_congr' (m := ProbComp) _ (fun pair => ?_)
  have projected := congrArg (fun distribution : SPMF HmacBlock => distribution >>= fun output =>
    𝒮[observe env baseImpl kem attachedVerify primitives program post pair.1
      (RawCtxSelectedInitialConstructor.response64 output)]) initialPrefix_uniform_vcvioLegacy
  simpa only [← evalSPMF_bind, bind_map_left, observer] using projected

/-- The current protocol's actual uniform-root endpoint reduces with coefficient one to fixed-salt Extract at its exact joint sampler and ordinary uniform-secret HMAC PRF. The one selected initializer response remains shared across all repeated source requests. -/
theorem primitive_bound (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac) :
    (uniformGame (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
      (protocol env kem attachedVerify primitives program post))).boolDistAdvantage
      (random env baseImpl kem attachedVerify primitives program post) ≤
    (extractRealGame hmac (joint env baseImpl kem attachedVerify primitives program post)
      (fullExtractReduction hmac .ratchet (observer env baseImpl kem attachedVerify primitives program post))).boolDistAdvantage
      (extractUniformGame (joint env baseImpl kem attachedVerify primitives program post)
        (fullExtractReduction hmac .ratchet (observer env baseImpl kem attachedVerify primitives program post))) +
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet
      (joint env baseImpl kem attachedVerify primitives program post)
      (observer env baseImpl kem attachedVerify primitives program post))).boolDistAdvantage
      (hmacPrfRandomGame (fullExpandReduction .ratchet
        (joint env baseImpl kem attachedVerify primitives program post)
        (observer env baseImpl kem attachedVerify primitives program post))) := by
  have realLaw :=
    PqxdhInitialLegalObserver.current_game env baseImpl kem attachedVerify primitives program post
  have randomLaw := random_comparison env baseImpl kem attachedVerify primitives program post
  simpa only [source_game, ProbComp.boolDistAdvantage, realLaw, randomLaw] using
    sourceFullAdvantage_le_extract_add_hmac env.source hmac correct .ratchet
      (joint env baseImpl kem attachedVerify primitives program post)
      (observer env baseImpl kem attachedVerify primitives program post)

/-- The constructed ordinary PRF reduction has two challenge queries. Its complete sampler and real observer uniform/local work are accounted separately. -/
theorem hmac_queries :
    (fullExpandReduction .ratchet (joint env baseImpl kem attachedVerify primitives program post)
      (observer env baseImpl kem attachedVerify primitives program post)).IsQueryBoundP IsHmacChallengeQuery 2 :=
  fullExpandReduction_hmac_query_bound _ _ _

end Current
end BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.response_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.response_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.source_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.source_game

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.random_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.random_comparison

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.primitive_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.hmac_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy.hmac_queries
