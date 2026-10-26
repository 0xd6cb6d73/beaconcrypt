import BeaconcryptCore.Computational.PqxdhAuthenticatedRoot

/-!
# Complete conditional-root query accounting

Every oracle class is charged through the complete source prefix and conditional continuation. Uniform and base work in supplied generators and signatures has explicit bounds. Logical decapsulation is contributed only by the selector and subsequent continuation; no ambient operation is silently assigned zero uniform or base cost.
-/

open OracleSpec OracleComp ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRoot

open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhStatefulPhase1EufCma
open PqxdhStatefulPhase1Authentication PqxdhInitializerSecrecy
open PqxdhSecretInputKdf PqxdhSecretInputInitializer

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK IdentitySK : Type}

set_option backward.isDefEq.respectTransparency false in
/-- Source-ordered setup and all three actual signing computations are included in every resource-class bound. -/
theorem borrowedPhase1Tail_query_bound
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qOne qSign qSelect : ℕ)
    (oneBound : ∀ identity before target,
      (OracleComp.liftComp (setup.oneTime identity before target)
        (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qOne)
    (signBound : ∀ identity identitySk message,
      (OracleComp.liftComp (sigAlg.sign identity identitySk message)
        (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qSign)
    (selectorBound : ∀ transcript, (selector.mainConcrete kem transcript).IsQueryBoundP p qSelect)
    (identity : Ed25519PublicKey) (identitySk : IdentitySK)
    (before : PrivatePrekey setup.PrivatePre) (target : TargetKemPublicKey) :
    (borrowedPhase1Tail sigAlg kem setup selector identity identitySk before target).IsQueryBoundP p
      (qOne + (qSign + (qSign + (qSign + qSelect)))) := by
  unfold borrowedPhase1Tail
  refine OracleComp.isQueryBoundP_bind (oneBound _ _ _) fun after _ => ?_
  refine OracleComp.isQueryBoundP_bind (signBound _ _ _) fun pre _ => ?_
  refine OracleComp.isQueryBoundP_bind (signBound _ _ _) fun one _ => ?_
  refine OracleComp.isQueryBoundP_bind (signBound _ _ _) fun pq _ => ?_
  simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using selectorBound _

set_option backward.isDefEq.respectTransparency false in
/-- Identity and prekey generation are charged before the complete one-time/signature/selector tail. -/
theorem borrowedPhase1Prefix_query_bound
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qIdentity qPre qTail : ℕ)
    (identityBound : (OracleComp.liftComp sigAlg.keygen
      (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qIdentity)
    (preBound : ∀ identity, (OracleComp.liftComp (setup.prekey identity)
      (MlKemCCAOracleSpec baseSpec)).IsQueryBoundP p qPre)
    (tailBound : ∀ identity identitySk before target,
      (borrowedPhase1Tail sigAlg kem setup selector identity identitySk before target).IsQueryBoundP p qTail)
    (target : TargetKemPublicKey) :
    (borrowedPhase1Prefix sigAlg kem setup selector target).IsQueryBoundP p
      (qIdentity + (qPre + qTail)) := by
  unfold borrowedPhase1Prefix
  refine OracleComp.isQueryBoundP_bind identityBound fun pair _ => ?_
  refine OracleComp.isQueryBoundP_bind (preBound _) fun before _ => ?_
  simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using tailBound _ _ _ _

/-- The only logical decapsulation operations in the borrowed prefix come from the selector. -/
theorem borrowedPhase1Prefix_decapsulation_bound
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) (qD : ℕ)
    (selectorBound : ∀ transcript,
      (selector.mainConcrete kem transcript).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qD)
    (target : TargetKemPublicKey) :
    (borrowedPhase1Prefix sigAlg kem setup selector target).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qD := by
  have tailBound := borrowedPhase1Tail_query_bound sigAlg kem setup selector
    IsMlKemLogicalDecapsulationQuery 0 0 qD
    (fun _ _ _ => liftPhase1Ambient_noDecapsulationQuery _)
    (fun _ _ _ => liftPhase1Ambient_noDecapsulationQuery _) selectorBound
  simpa only [Nat.zero_add] using borrowedPhase1Prefix_query_bound sigAlg kem setup selector
    IsMlKemLogicalDecapsulationQuery 0 0 qD
    (liftPhase1Ambient_noDecapsulationQuery _)
    (fun _ => liftPhase1Ambient_noDecapsulationQuery _)
    (by simpa only [Nat.zero_add] using tailBound) target

/-- Conditional branch selection takes the larger branch cap; completed work is still fully charged. -/
theorem dispatch_query_bound
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK)
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qPrepare qCommon : ℕ)
    (prepareBound : ∀ identitySk result,
      (protocol.prepare identitySk result).IsQueryBoundP p qPrepare)
    (nonTargetBound : ∀ identitySk result,
      (protocol.nonTarget identitySk result).IsQueryBoundP p qCommon)
    (forgeryBound : ∀ identitySk result,
      (protocol.onForgery identitySk result).IsQueryBoundP p qCommon)
    (retained : IdentitySK × StatefulPhase1Result kem setup selector) :
    (dispatch verifyFn protocol retained).IsQueryBoundP p (max qPrepare qCommon) := by
  rcases retained with ⟨identitySk, result⟩
  cases admitted : admission verifyFn result <;>
    by_cases bad : result.badBit verifyFn = true <;>
    by_cases eligible : protocol.targetEligible identitySk result = true <;>
    simp [dispatch, admitted, bad, eligible]
  all_goals first
    | exact (prepareBound identitySk result).mono (Nat.le_max_left qPrepare qCommon)
    | exact (nonTargetBound identitySk result).mono (Nat.le_max_right qPrepare qCommon)
    | exact (forgeryBound identitySk result).mono (Nat.le_max_right qPrepare qCommon)

/-- The full conditional prefix adds its complete branch work to the retained signed-prefix budget. -/
theorem conditionalPrefix_query_bound
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK)
    (p : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred p]
    (qPrefix qDispatch : ℕ)
    (prefixBound : ∀ target, (borrowedPhase1Prefix sigAlg kem setup selector target).IsQueryBoundP p qPrefix)
    (dispatchBound : ∀ retained, (dispatch verifyFn protocol retained).IsQueryBoundP p qDispatch)
    (target : TargetKemPublicKey) :
    (conditionalPrefix sigAlg kem setup selector verifyFn protocol target).IsQueryBoundP p
      (qPrefix + qDispatch) :=
  OracleComp.isQueryBoundP_bind (prefixBound target) fun retained _ => dispatchBound retained

/-- The pending observer's bounds cover all postchallenge work; completed branches make no postchallenge query. -/
theorem rootInitializer_post_query_bound
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK)
    (p : (InitializerPostSpec baseSpec).Domain → Prop) [DecidablePred p] (q : ℕ)
    (finishBound : ∀ identitySk result prepared transcript known root,
      (protocol.finish identitySk result prepared transcript known root).IsQueryBoundP p q)
    (transcript : InitializerPublicTranscript (RootMode protocol))
    (known : PqxdhHiddenRoot.KnownPqxdhRootCoordinates) (root : RootOutput) :
    ((rootInitializer sigAlg kem setup selector verifyFn protocol).main transcript known root).IsQueryBoundP p q := by
  cases mode : transcript.context with
  | completed decision => simp [rootInitializer, mode]
  | pending identitySk result prepared =>
      simpa only [rootInitializer, mode] using finishBound identitySk result prepared _ known root

/-- Six CCA-source resource caps and the two public KDF caps are inherited by the constructed reduction. -/
theorem rootInitializer_query_bounds
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK)
    (qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym : ℕ)
    (prefixBounds : ∀ target,
      (conditionalPrefix sigAlg kem setup selector verifyFn protocol target).IsQueryBoundP IsMlKemUniformQuery qUPre ∧
      (conditionalPrefix sigAlg kem setup selector verifyFn protocol target).IsQueryBoundP IsMlKemBaseQuery qBPre ∧
      (conditionalPrefix sigAlg kem setup selector verifyFn protocol target).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDPre)
    (finishBounds : ∀ identitySk result prepared transcript known root,
      (protocol.finish identitySk result prepared transcript known root).IsQueryBoundP IsInitializerUniformQuery qUPost ∧
      (protocol.finish identitySk result prepared transcript known root).IsQueryBoundP IsInitializerBaseQuery qBPost ∧
      (protocol.finish identitySk result prepared transcript known root).IsQueryBoundP IsInitializerLogicalDecapsulationQuery qDPost ∧
      (protocol.finish identitySk result prepared transcript known root).IsQueryBoundP IsInitializerRootQuery qRoot ∧
      (protocol.finish identitySk result prepared transcript known root).IsQueryBoundP IsInitializerSymmetricQuery qSym) :
    (rootInitializer sigAlg kem setup selector verifyFn protocol).MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym ∧
    (toKemOneKeyAdversary source kem (rootInitializer sigAlg kem setup selector verifyFn protocol)).MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost := by
  have bounds : (rootInitializer sigAlg kem setup selector verifyFn protocol).MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym := by
    refine ⟨prefixBounds, ?_⟩
    intro transcript known root
    cases mode : transcript.context with
    | completed decision => simp [rootInitializer, mode]
    | pending identitySk result prepared =>
        simpa only [rootInitializer, mode] using finishBounds identitySk result prepared _ known root
  exact ⟨bounds, toKemOneKeyAdversary_makesAtMostQueries source kem _ bounds⟩

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRoot.rootInitializer_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rootInitializer_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRoot.borrowedPhase1Prefix_decapsulation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms borrowedPhase1Prefix_decapsulation_bound

end BeaconcryptCore.Computational.PqxdhAuthenticatedRoot
