import BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot

/-!
# Source server root resource bounds

These bounds count all chosen uniform/base/decapsulation resource classes through the actual source preparation and common branches. The supplied native key-generation and encapsulation interfaces retain explicit per-call budgets. Encapsulation on a target-abort branch is real source work; the one-key challenger may then make an additional ignored encapsulation, which remains part of its separate full interpreted-prefix budget.
-/

open OracleSpec OracleComp ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot

open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhStatefulPhase1EufCma
open PqxdhStatefulPhase1Authentication PqxdhInitializerSecrecy
open PqxdhSecretInputKdf PqxdhSecretInputInitializer PqxdhAuthenticatedRoot PqxdhJointKdfGame

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK IdentitySK : Type}

/-- Preparation charges ephemeral generation, source encapsulation on abort, and the complete abort continuation. -/
theorem prepareTarget_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qEphemeral qEncap qObserver : ℕ)
    (ephemeralBound : (ephemeralGen.liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEphemeral)
    (encapBound : ∀ target, ((kem.encaps target).liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEncap)
    (observerBound : ∀ identitySk result execution,
      (observeCommon source kem setup selector observer identitySk result execution).IsQueryBoundP p qObserver)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector) :
    (prepareTarget source kem setup selector observer server ephemeralGen identitySk result).IsQueryBoundP p
      (qEphemeral + (qEncap + qObserver)) := by
  unfold prepareTarget
  refine OracleComp.isQueryBoundP_bind ephemeralBound fun ephemeral _ => ?_
  cases rootFailure source.crypto server.ikSk ephemeral.toList result.identity
      result.before.publicKey result.after.publicKey with
  | none => simp
  | some failure =>
      refine OracleComp.isQueryBoundP_bind (encapBound _) fun pair _ => ?_
      simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using observerBound identitySk result _

/-- Accepted non-target keys use actual encapsulation under their selected public key, with complete source work charged. -/
theorem acceptedCommon_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qEphemeral qEncap qObserver : ℕ)
    (ephemeralBound : (ephemeralGen.liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEphemeral)
    (encapBound : ∀ target, ((kem.encaps target).liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEncap)
    (observerBound : ∀ identitySk result execution,
      (observeCommon source kem setup selector observer identitySk result execution).IsQueryBoundP p qObserver)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    (acceptedCommon source kem setup selector observer server application ephemeralGen
      identitySk result identity keys).IsQueryBoundP p (qEphemeral + (qEncap + qObserver)) := by
  unfold acceptedCommon
  split
  · exact (observerBound identitySk result _).mono (by omega)
  · refine OracleComp.isQueryBoundP_bind ephemeralBound fun ephemeral _ => ?_
    refine OracleComp.isQueryBoundP_bind (encapBound _) fun pair _ => ?_
    exact observerBound identitySk result _

/-- Rejection and every accepted candidate are covered together; no honest-key premise enters the bound. -/
theorem allCandidateCommon_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qEphemeral qEncap qObserver : ℕ)
    (ephemeralBound : (ephemeralGen.liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEphemeral)
    (encapBound : ∀ target, ((kem.encaps target).liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEncap)
    (observerBound : ∀ identitySk result execution,
      (observeCommon source kem setup selector observer identitySk result execution).IsQueryBoundP p qObserver)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector) :
    (allCandidateCommon source kem setup selector observer server application ephemeralGen verifyFn
      identitySk result).IsQueryBoundP p (qEphemeral + (qEncap + qObserver)) := by
  unfold allCandidateCommon
  cases acceptPhase1Candidate verifyFn result.candidate with
  | none => exact (observerBound identitySk result _).mono (by omega)
  | some selected =>
      exact acceptedCommon_query_bound source kem setup selector observer server application
        ephemeralGen p qEphemeral qEncap qObserver ephemeralBound encapBound observerBound identitySk result selected.1 selected.2

/-- Every source prechallenge resource class has the signed-prefix cost plus the complete server branch cost. -/
theorem sourceProtocol_prefix_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qSigned qEphemeral qEncap qObserver : ℕ)
    (signedBound : ∀ target,
      (borrowedPhase1Prefix sigAlg kem setup selector target).IsQueryBoundP p qSigned)
    (ephemeralBound : (ephemeralGen.liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEphemeral)
    (encapBound : ∀ target, ((kem.encaps target).liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEncap)
    (observerBound : ∀ identitySk result execution,
      (observeCommon source kem setup selector observer identitySk result execution).IsQueryBoundP p qObserver)
    (target : TargetKemPublicKey) :
    ((rootInitializer sigAlg kem setup selector verifyFn
      (sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn)).preChallenge target).IsQueryBoundP p
        (qSigned + (qEphemeral + (qEncap + qObserver))) := by
  apply conditionalPrefix_query_bound sigAlg kem setup selector verifyFn _ p qSigned
    (qEphemeral + (qEncap + qObserver)) signedBound
  intro retained
  simpa only [max_self] using dispatch_query_bound verifyFn
    (sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn) p
    (qEphemeral + (qEncap + qObserver)) (qEphemeral + (qEncap + qObserver))
    (prepareTarget_query_bound source kem setup selector observer server ephemeralGen p
      qEphemeral qEncap qObserver ephemeralBound encapBound observerBound)
    (allCandidateCommon_query_bound source kem setup selector observer server application ephemeralGen verifyFn p
      qEphemeral qEncap qObserver ephemeralBound encapBound observerBound)
    (fun _ _ => by simp [sourceProtocol]) retained

/-- Target postchallenge observers inherit each source resource cap, including public root and symmetric KDF evaluations. -/
theorem sourceProtocol_post_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (p : (InitializerPostSpec baseSpec).Domain → Prop) [DecidablePred p] (q : ℕ)
    (observerBound : ∀ identitySk result execution,
      (observer.main identitySk result execution).IsQueryBoundP p q)
    (transcript : InitializerPublicTranscript (RootMode
      (sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn)))
    (known : PqxdhHiddenRoot.KnownPqxdhRootCoordinates) (root : RootOutput) :
    ((rootInitializer sigAlg kem setup selector verifyFn
      (sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn)).main transcript known root).IsQueryBoundP p q :=
  rootInitializer_post_query_bound sigAlg kem setup selector verifyFn _ p q
    (fun identitySk result _ _ _ _ => observerBound identitySk result _) transcript known root

/--
info: 'BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot.prepareTarget_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms prepareTarget_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot.sourceProtocol_prefix_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourceProtocol_prefix_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot.sourceProtocol_post_query_bound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourceProtocol_post_query_bound

end BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot
