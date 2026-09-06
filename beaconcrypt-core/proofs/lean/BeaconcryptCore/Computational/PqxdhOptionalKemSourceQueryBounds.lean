import BeaconcryptCore.Computational.PqxdhOptionalKemSource

/-!
# Optional source encapsulation resource bounds

Every accepted candidate charges its actual optional encapsulation attempt, including rejection. The reduction separately charges ordinary total target encapsulation and optional arbitrary-key encapsulation; its worst-case prechallenge cap uses the maximum of those budgets. Uniform, base, and logical-decapsulation classes remain independently selectable, and postchallenge and challenger work retain the existing explicit bounds.
-/

open OracleSpec OracleComp ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhOptionalKemSource

open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhStatefulPhase1EufCma
open PqxdhStatefulPhase1Authentication PqxdhInitializerSecrecy
open PqxdhSecretInputKdf PqxdhSecretInputInitializer PqxdhAuthenticatedRoot PqxdhJointKdfGame
open PqxdhSourceAuthenticatedRoot

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK IdentitySK : Type}

/-- Accepted non-target keys use actual encapsulation under their selected public key, with complete source work charged. -/
theorem acceptedCommon_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qEphemeral qEncap qObserver : ℕ)
    (ephemeralBound : (ephemeralGen.liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEphemeral)
    (encapBound : ∀ target, ((native.encaps target).liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEncap)
    (observerBound : ∀ identitySk result execution,
      (observeCommon source kem setup selector observer identitySk result execution).IsQueryBoundP p qObserver)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    (acceptedCommon source kem native setup selector observer server application ephemeralGen
      identitySk result identity keys).IsQueryBoundP p (qEphemeral + (qEncap + qObserver)) := by
  unfold acceptedCommon
  split
  · exact (observerBound identitySk result _).mono (by omega)
  · refine OracleComp.isQueryBoundP_bind ephemeralBound fun ephemeral _ => ?_
    refine OracleComp.isQueryBoundP_bind (encapBound _) fun encapsulated _ => ?_
    cases encapsulated <;> exact observerBound identitySk result _

/-- Rejection and every accepted candidate are covered together; no honest-key premise enters the bound. -/
theorem allCandidateCommon_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qEphemeral qEncap qObserver : ℕ)
    (ephemeralBound : (ephemeralGen.liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEphemeral)
    (encapBound : ∀ target, ((native.encaps target).liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEncap)
    (observerBound : ∀ identitySk result execution,
      (observeCommon source kem setup selector observer identitySk result execution).IsQueryBoundP p qObserver)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector) :
    (allCandidateCommon source kem native setup selector observer server application ephemeralGen verifyFn
      identitySk result).IsQueryBoundP p (qEphemeral + (qEncap + qObserver)) := by
  unfold allCandidateCommon
  cases acceptPhase1Candidate verifyFn result.candidate with
  | none => exact (observerBound identitySk result _).mono (by omega)
  | some selected =>
      exact acceptedCommon_query_bound source kem native setup selector observer server application
        ephemeralGen p qEphemeral qEncap qObserver ephemeralBound encapBound observerBound identitySk result selected.1 selected.2


/-- Every source prechallenge resource class has the signed-prefix cost plus the complete server branch cost. -/
theorem sourceProtocol_prefix_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qSigned qEphemeral qTotal qNative qObserver : ℕ)
    (signedBound : ∀ target,
      (borrowedPhase1Prefix sigAlg kem setup selector target).IsQueryBoundP p qSigned)
    (ephemeralBound : (ephemeralGen.liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qEphemeral)
    (encapBound : ∀ target, ((kem.encaps target).liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qTotal)
    (nativeBound : ∀ target, ((native.encaps target).liftComp (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qNative)
    (observerBound : ∀ identitySk result execution,
      (observeCommon source kem setup selector observer identitySk result execution).IsQueryBoundP p qObserver)
    (target : TargetKemPublicKey) :
    ((rootInitializer sigAlg kem setup selector verifyFn
      (sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn)).preChallenge target).IsQueryBoundP p
        (qSigned + (qEphemeral + (max qTotal qNative + qObserver))) := by
  apply conditionalPrefix_query_bound sigAlg kem setup selector verifyFn _ p qSigned
    (qEphemeral + (max qTotal qNative + qObserver)) signedBound
  intro retained
  simpa only [max_self] using dispatch_query_bound verifyFn
    (sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn) p
    (qEphemeral + (max qTotal qNative + qObserver)) (qEphemeral + (max qTotal qNative + qObserver))
    (fun identitySk result => (prepareTarget_query_bound source kem setup selector observer server ephemeralGen p
      qEphemeral qTotal qObserver ephemeralBound encapBound observerBound identitySk result).mono (by omega))
    (fun identitySk result => (allCandidateCommon_query_bound source kem native setup selector observer server application ephemeralGen verifyFn p
      qEphemeral qNative qObserver ephemeralBound nativeBound observerBound identitySk result).mono (by omega))
    (fun _ _ => by simp [sourceProtocol, PqxdhSourceAuthenticatedRoot.sourceProtocol]) retained

/-- Optional parsing/encapsulation adds no logical CCA access; all selector and observer attempts remain counted, including blocked-ciphertext attempts. -/
theorem sourceProtocol_decapsulation_bound
    (source : FixedHkdfSha512NoSaltSource)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (qSelector qObserver : ℕ)
    (selectorBound : ∀ transcript,
      (selector.mainConcrete kem transcript).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qSelector)
    (observerBound : ∀ identitySk result execution,
      (observeCommon source kem setup selector observer identitySk result execution).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery qObserver)
    (target : TargetKemPublicKey) :
    ((rootInitializer sigAlg kem setup selector verifyFn
      (sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn)).preChallenge target).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (qSelector + qObserver) := by
  simpa only [Nat.zero_add, max_self] using sourceProtocol_prefix_query_bound source sigAlg kem native setup selector
    observer server application ephemeralGen verifyFn IsMlKemLogicalDecapsulationQuery qSelector 0 0 0 qObserver
    (borrowedPhase1Prefix_decapsulation_bound sigAlg kem setup selector qSelector selectorBound)
    (liftPhase1Ambient_noDecapsulationQuery _)
    (fun _ => liftPhase1Ambient_noDecapsulationQuery _)
    (fun _ => liftPhase1Ambient_noDecapsulationQuery _) observerBound target

/-- Target postchallenge observers inherit each source resource cap, including public root and symmetric KDF evaluations. -/
theorem sourceProtocol_post_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
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
      (sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn)))
    (known : PqxdhHiddenRoot.KnownPqxdhRootCoordinates) (root : RootOutput) :
    ((rootInitializer sigAlg kem setup selector verifyFn
      (sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn)).main transcript known root).IsQueryBoundP p q :=
  rootInitializer_post_query_bound sigAlg kem setup selector verifyFn _ p q
    (fun identitySk result _ _ _ _ => observerBound identitySk result _) transcript known root

/--
info: 'BeaconcryptCore.Computational.PqxdhOptionalKemSource.acceptedCommon_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms acceptedCommon_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhOptionalKemSource.sourceProtocol_prefix_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourceProtocol_prefix_query_bound

end BeaconcryptCore.Computational.PqxdhOptionalKemSource
