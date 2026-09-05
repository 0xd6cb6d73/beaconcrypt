import BeaconcryptCore.Computational.PqxdhStatefulPhase1Authentication

/-!
# Conditional authenticated-root experiment

The Phase-1 prefix generates its own signing identity around a borrowed target KEM key. Accepted unchanged fields alone leave a target-root computation pending. Rejection and attacker-owned acceptance finish in the unrestricted prechallenge phase, preserving all permitted decapsulation answers; the challenge-blocked phase is used only for the authenticated target. Changed same-identity fields are the one stopped EUF event.

The protocol continuation receives its retained identity/private state separately from its public challenge transcript. It never receives the KEM secret key. Preparation runs before encapsulation, so target-root-dependent records must be constructed by the continuation from its supplied root. The four DH coordinates are parameters of this component interface; source instantiation must identify their actual production computations.
-/

open OracleSpec OracleComp ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRoot

open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhHiddenRoot PqxdhJointKdfGame
open PqxdhStatefulPhase1EufCma PqxdhStatefulPhase1Authentication
open PqxdhInitializerSecrecy PqxdhSecretInputKdf PqxdhSecretInputInitializer

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK : Type} {IdentitySK : Type}

/-- The private protocol evaluator's exact root boundary; none of these callbacks receives the target KEM secret key. -/
structure RootProtocol
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) (IdentitySK : Type) where
  Private : Type
  /-- The actual registration/reveal policy decides target eligibility before ephemeral generation. -/
  targetEligible : IdentitySK → StatefulPhase1Result kem setup selector → Bool := fun _ _ => true
  prepare : IdentitySK → StatefulPhase1Result kem setup selector →
    OracleComp (MlKemCCAOracleSpec baseSpec) (Bool ⊕ Private)
  coordinates : IdentitySK → StatefulPhase1Result kem setup selector → Private →
    TargetKemPublicKey → MlKem768Ciphertext → KnownPqxdhRootCoordinates
  finish : IdentitySK → StatefulPhase1Result kem setup selector → Private →
    InitializerPublicTranscript Unit → KnownPqxdhRootCoordinates → RootOutput →
    OracleComp (InitializerPostSpec baseSpec) Bool
  nonTarget : IdentitySK → StatefulPhase1Result kem setup selector →
    OracleComp (MlKemCCAOracleSpec baseSpec) Bool
  onForgery : IdentitySK → StatefulPhase1Result kem setup selector →
    OracleComp (MlKemCCAOracleSpec baseSpec) Bool

inductive RootMode
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (protocol : RootProtocol kem setup selector IdentitySK) where
  | completed (decision : Bool)
  | pending (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector)
      (prepared : protocol.Private)

/-- Admission dispatches the complete common computation or retains one prepared target-root state. -/
noncomputable def dispatch
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {setup : StatefulPhase1Setup baseSpec}
    {selector : StatefulPhase1Selector kem setup.Context}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK)
    (retained : IdentitySK × StatefulPhase1Result kem setup selector) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (RootMode protocol) := do
  let (identitySk, result) := retained
  if result.badBit verifyFn then
    return .completed (← protocol.onForgery identitySk result)
  else
    match admission verifyFn result with
    | .unchanged =>
      if protocol.targetEligible identitySk result then
        let prepared ← protocol.prepare identitySk result
        return match prepared with
          | .inl decision => .completed decision
          | .inr ready => .pending identitySk result ready
      else return .completed (← protocol.nonTarget identitySk result)
    | _ => return .completed (← protocol.nonTarget identitySk result)

/-- Non-target work is completed before the challenger creates a ciphertext that it will block. -/
noncomputable def conditionalPrefix
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK) (target : TargetKemPublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (RootMode protocol) :=
  borrowedPhase1Prefix sigAlg kem setup selector target >>= dispatch verifyFn protocol

/-- Dummy coordinates are used only in a completed branch whose decision ignores the candidate root. -/
def unusedCoordinates : KnownPqxdhRootCoordinates :=
  ⟨List.Vector.replicate 32 0, List.Vector.replicate 32 0,
    List.Vector.replicate 32 0, List.Vector.replicate 32 0⟩

/-- The existing KEM/Extract/HMAC endpoint is instantiated with the exact conditional Phase-1 schedule. -/
noncomputable def rootInitializer
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK) : InitializerAdversary kem where
  State := RootMode protocol
  Context := RootMode protocol
  preChallenge := conditionalPrefix sigAlg kem setup selector verifyFn protocol
  knownCoordinates state pk ct := match state with
    | .completed _ => unusedCoordinates
    | .pending identitySk result prepared => protocol.coordinates identitySk result prepared pk ct
  publicContext state _ _ := state
  main transcript known root := match transcript.context with
    | .completed decision => pure decision
    | .pending identitySk result prepared =>
      protocol.finish identitySk result prepared
        ⟨transcript.publicKey, transcript.ciphertext, ()⟩ known root

/-- Interpret every common branch through the unrestricted CCA interface, keeping the key confined to the handler. -/
noncomputable def runCommon
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (kemSk : KemSK)
    (work : OracleComp (MlKemCCAOracleSpec baseSpec) Bool) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (localKemPreChallengeImpl kem kemSk) work)

/-- The source continuation encapsulates only on unchanged target admission; common branches retain their full source computation. -/
noncomputable def sourceContinuation
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK) (filterForgery : Bool)
    (state : IdentitySK × StatefulPhase1Result kem setup selector × KemSK) : ProbComp Bool := do
  let identitySk := state.1
  let result := state.2.1
  let kemSk := state.2.2
  if filterForgery && result.badBit verifyFn then
    runCommon baseImpl kem kemSk (protocol.onForgery identitySk result)
  else
    match admission verifyFn result with
    | .unchanged =>
      if protocol.targetEligible identitySk result then
        let prepared ← simulateQ (kemAmbientImpl baseImpl)
          (simulateQ (localKemPreChallengeImpl kem kemSk) (protocol.prepare identitySk result))
        match prepared with
        | .inl decision => pure decision
        | .inr ready =>
          let (ct, secret) ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps result.target)
          let known := protocol.coordinates identitySk result ready result.target ct
          simulateQ (kemAmbientImpl baseImpl)
            (simulateQ (kem.IND_CCA_postChallengeImpl kemSk ct)
              (simulateQ (initializerPostRealImpl source kem)
                (protocol.finish identitySk result ready ⟨result.target, ct, ()⟩ known
                  (productionHiddenRoot source known secret))))
      else runCommon baseImpl kem kemSk (protocol.nonTarget identitySk result)
    | _ => runCommon baseImpl kem kemSk (protocol.nonTarget identitySk result)

noncomputable def sourceGame
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK) (filterForgery : Bool) : ProbComp Bool :=
  privateSourcePrefix baseImpl sigAlg kem setup selector >>= fun state =>
    sourceContinuation source baseImpl kem setup selector verifyFn protocol filterForgery state

/-- The unfiltered game keeps actual attacker-owned, changed, and rejected behavior; filtering only accepted same-identity substitution costs one EUF term. -/
theorem sourceGame_authentication_hop
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn)
    (protocol : RootProtocol kem setup selector IdentitySK) :
    (sourceGame source baseImpl sigAlg kem setup selector verifyFn protocol false).boolDistAdvantage
      (sourceGame source baseImpl sigAlg kem setup selector verifyFn protocol true) ≤
    ((statefulPhase1ToEUFCMA sigAlg kem setup selector).advantage
      (runtimeOfImpl (kemAmbientImpl baseImpl))).toReal := by
  simpa [sourceGame, sourceContinuation] using
    privateContinuationAdvantage_le_eufCma baseImpl sigAlg kem setup selector verifyFn deterministic
      (fun state => sourceContinuation source baseImpl kem setup selector verifyFn protocol false state)
      (fun state => runCommon baseImpl kem state.2.2 (protocol.onForgery state.1 state.2.1))

/-- Every interpreted borrowed prefix retains the actual challenger public key in its honest material. -/
theorem borrowedPrefix_target
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (target : TargetKemPublicKey) (kemSk : KemSK) :
    ∀ retained ∈ support (simulateQ (kemAmbientImpl baseImpl)
      (simulateQ (localKemPreChallengeImpl kem kemSk)
        (borrowedPhase1Prefix sigAlg kem setup selector target))),
      retained.2.target = target := by
  simp [borrowedPhase1Prefix_local_exact, statefulPhase1TailReference]
  aesop

/-- An unused total probabilistic computation changes no continued output distribution. -/
theorem evalDist_discard {A B : Type} (work : ProbComp A) (next : ProbComp B) :
    𝒟[work >>= fun _ => next] = 𝒟[next] := by
  exact evalDist_ext (fun output => by simp)

/-- Dispatch completes every non-target oracle interaction before the challenge; the pending branch uses the exact blocked handler. -/
theorem dispatch_finish_eq_source
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK)
    (target : TargetKemPublicKey) (kemSk : KemSK)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector)
    (target_eq : result.target = target) :
    𝒟[do
      let mode ← simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (localKemPreChallengeImpl kem kemSk)
          (dispatch verifyFn protocol (identitySk, result)))
      simulateQ (kemAmbientImpl baseImpl)
        (oneKeyFinish kem (runtimeOfImpl (kemAmbientImpl baseImpl))
          (toKemOneKeyAdversary source kem
            (rootInitializer sigAlg kem setup selector verifyFn protocol))
          (target, kemSk, mode) true)] =
    𝒟[sourceContinuation source baseImpl kem setup selector verifyFn protocol true
      (identitySk, result, kemSk)] := by
  apply evalDist_ext
  intro output
  cases admitted : admission verifyFn result <;>
    by_cases bad : result.badBit verifyFn = true <;>
    by_cases eligible : protocol.targetEligible identitySk result = true <;>
    simp [dispatch, sourceContinuation, bad, admitted, oneKeyFinish,
      toKemOneKeyAdversary, rootInitializer,
      runtimeOfImpl_liftProbComp,
      simulateQ_kemAmbient_liftM_ProbComp,
      runCommon, target_eq, eligible, probOutput_bind_eq_tsum, ← mul_assoc, ENNReal.mul_inv_cancel_right,
      Fintype.card_ne_zero]
  apply tsum_congr
  intro ready
  cases ready <;> simp [probOutput_bind_eq_tsum]

set_option backward.isDefEq.respectTransparency false in
/-- The full source-ordered filtered execution is exactly the standard one-key challenger schedule after interpretation. -/
theorem sourceGame_filtered_eq_initializerReal
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (protocol : RootProtocol kem setup selector IdentitySK) :
    𝒟[sourceGame source baseImpl sigAlg kem setup selector verifyFn protocol true] =
      𝒟[initializerRealGame source baseImpl kem
        (rootInitializer sigAlg kem setup selector verifyFn protocol)] := by
  unfold sourceGame
  rw [privateSourcePrefix_borrowed_complete]
  simp only [initializerRealGame, oneKeyBranchMain, oneKeyPrefix,
    toKemOneKeyAdversary, rootInitializer, conditionalPrefix,
    simulateQ_bind, bind_assoc, pure_bind]
  apply evalDist_bind_congr'
  intro pair
  apply evalDist_bind_congr
  intro retained supported
  exact (dispatch_finish_eq_source source baseImpl sigAlg kem setup selector verifyFn protocol
    pair.1 pair.2 retained.1 retained.2
    (borrowedPrefix_target baseImpl sigAlg kem setup selector pair.1 pair.2 retained supported)).symm

/-- One unfiltered source-shaped root execution has four explicit coefficient-one reductions, with no honest-selection premise. -/
theorem authenticatedRootAdvantage_le_euf_add_kem_add_extract_add_hmac
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn)
    (protocol : RootProtocol kem setup selector IdentitySK) :
    let adversary := rootInitializer sigAlg kem setup selector verifyFn protocol
    let sample := secretInputSample baseImpl kem adversary
    let observer := rootObserver source baseImpl kem adversary
    (sourceGame source baseImpl sigAlg kem setup selector verifyFn protocol false).boolDistAdvantage
        (independentInitializerGame source baseImpl kem adversary) ≤
      ((statefulPhase1ToEUFCMA sigAlg kem setup selector).advantage
        (runtimeOfImpl (kemAmbientImpl baseImpl))).toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (toKemOneKeyAdversary source kem adversary).toINDCCA +
      (extractRealGame hmac sample (extractReduction hmac observer)).boolDistAdvantage
        (extractUniformGame sample (extractReduction hmac observer)) +
      (hmacPrfRealGame hmac (expandReduction sample observer)).boolDistAdvantage
        (hmacPrfRandomGame (expandReduction sample observer)) := by
  dsimp only
  have hroot := initializerAdvantage_le_kem_add_extract_add_hmac source hmac correct baseImpl kem
    (rootInitializer sigAlg kem setup selector verifyFn protocol)
  have heq := sourceGame_filtered_eq_initializerReal source baseImpl sigAlg kem setup selector
    verifyFn protocol
  have hfiltered :
      (sourceGame source baseImpl sigAlg kem setup selector verifyFn protocol true).boolDistAdvantage
        (independentInitializerGame source baseImpl kem
          (rootInitializer sigAlg kem setup selector verifyFn protocol)) =
      (initializerRealGame source baseImpl kem
        (rootInitializer sigAlg kem setup selector verifyFn protocol)).boolDistAdvantage
        (independentInitializerGame source baseImpl kem
          (rootInitializer sigAlg kem setup selector verifyFn protocol)) := by
    simp only [ProbComp.boolDistAdvantage, probOutput_def, heq]
  have composed := (ProbComp.boolDistAdvantage_triangle
    (sourceGame source baseImpl sigAlg kem setup selector verifyFn protocol false)
    (sourceGame source baseImpl sigAlg kem setup selector verifyFn protocol true)
    (independentInitializerGame source baseImpl kem
      (rootInitializer sigAlg kem setup selector verifyFn protocol))).trans
      (add_le_add (sourceGame_authentication_hop source baseImpl sigAlg kem setup selector verifyFn
        deterministic protocol) (hfiltered.trans_le hroot))
  simpa only [add_assoc] using composed

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRoot.authenticatedRootAdvantage_le_euf_add_kem_add_extract_add_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms authenticatedRootAdvantage_le_euf_add_kem_add_extract_add_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRoot.sourceGame_filtered_eq_initializerReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourceGame_filtered_eq_initializerReal

end BeaconcryptCore.Computational.PqxdhAuthenticatedRoot
