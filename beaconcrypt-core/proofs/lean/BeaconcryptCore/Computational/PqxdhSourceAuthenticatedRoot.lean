import BeaconcryptCore.Computational.PqxdhAuthenticatedRootQueryBounds
import BeaconcryptCore.Refinement.ProtocolComposition

/-!
# Production server DH and authenticated-root continuation

The source adapter supplies the server's own Ed25519 seed, the freshly generated X25519 ephemeral secret, the selected beacon identity public key, and its signed prekey/one-time fields to the four DH operations in source order. The target beacon's Ed25519 secret is never required for these server computations. This is functional protocol wiring, not an X25519 security assumption.

The continued record and published peer state are constructed from the supplied root. No record derived from the old root is stored in the sampler context. Rejected or non-target candidates execute their entire actual source continuation in the unrestricted prechallenge phase.
-/

open OracleSpec OracleComp ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot

open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhHiddenRoot PqxdhJointKdfGame
open PqxdhStatefulPhase1EufCma PqxdhStatefulPhase1Authentication
open PqxdhInitializerSecrecy PqxdhSecretInputKdf PqxdhAuthenticatedRoot

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK IdentitySK : Type}

/-- Four exact source DH calls, including public conversion of the selected beacon identity. -/
def serverCoordinates (c : Pqxdh.Crypto) (serverSeed ephemeral : Pqxdh.Bytes)
    (identity : Ed25519PublicKey) (prekey oneTime : X25519PublicKey) : KnownPqxdhRootCoordinates :=
  ⟨⟨c.x25519 (c.xsk serverSeed) prekey.toList, c.x25519_length _ _⟩,
   ⟨c.x25519 ephemeral ((c.xpkConv identity.toList).getD []), c.x25519_length _ _⟩,
   ⟨c.x25519 ephemeral prekey.toList, c.x25519_length _ _⟩,
   ⟨c.x25519 ephemeral oneTime.toList, c.x25519_length _ _⟩⟩

/-- The computational sampler uses the exact source prefix and selected KEM contribution, totaling 192 bytes. -/
theorem serverCoordinates_rootInput (c : Pqxdh.Crypto) (serverSeed ephemeral : Pqxdh.Bytes)
    (identity : Ed25519PublicKey) (prekey oneTime : X25519PublicKey)
    (converted : Pqxdh.Bytes) (conversion : c.xpkConv identity.toList = some converted)
    (secret : MlKemSharedSecret) :
    hiddenRootIKM (serverCoordinates c serverSeed ephemeral identity prekey oneTime) secret =
      Pqxdh.ikmOf (Pqxdh.serverDHs c serverSeed ephemeral converted prekey.toList oneTime.toList)
        secret.toList ∧
    (hiddenRootIKM (serverCoordinates c serverSeed ephemeral identity prekey oneTime) secret).length = 192 := by
  constructor
  · simp [serverCoordinates, hiddenRootIKM, Pqxdh.ikmOf, Pqxdh.serverDHs, conversion]
  · exact hiddenRootIKM_length _ _

/-- Public conversion and all-zero rejection are evaluated independently of the KEM secret and candidate root. -/
def rootFailure (c : Pqxdh.Crypto) (serverSeed ephemeral : Pqxdh.Bytes)
    (identity : Ed25519PublicKey) (prekey oneTime : X25519PublicKey) : Option Pqxdh.ServerError :=
  match c.xpkConv identity.toList with
  | none => some .badEncoding
  | some converted =>
    if Pqxdh.dhNonZero (Pqxdh.serverDHs c serverSeed ephemeral converted prekey.toList oneTime.toList)
      then none else some .zeroDH

/-- Registration consumption and response/peer publication are constructed only from the supplied root. -/
def finishFromRoot (c : Pqxdh.Crypto) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes) (identity : Ed25519PublicKey) (oneTime : X25519PublicKey)
    (ephemeral : Pqxdh.Bytes) (ciphertext : MlKem768Ciphertext) (root : RootOutput) :
    Except Pqxdh.ServerError Pqxdh.KexResponse × Pqxdh.ServerState :=
  let consumed := { server with consumed := (identity.toList ++ oneTime.toList) :: server.consumed }
  if application = some [] then (.error .emptyAppMessage, consumed)
  else Pqxdh.serverEmit c consumed identity.toList root.toList ciphertext.toList
    (c.xpub ephemeral) (application.getD [0xFF])

/-- Retain all source-generated values and complete protocol poststate, including failed publication after consumption. -/
structure ServerExecution where
  ephemeral : Option (List.Vector UInt8 32)
  ciphertext : Option MlKem768Ciphertext
  outcome : Except Pqxdh.ServerError Pqxdh.KexResponse × Pqxdh.ServerState

/-- Remaining code sees the complete source execution through the same public-KDF/CCA interface as the root continuation. -/
structure SourceObserver
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) (IdentitySK : Type) where
  main : IdentitySK → StatefulPhase1Result kem setup selector → ServerExecution →
    OracleComp (InitializerPostSpec baseSpec) Bool

/-- Source aborts, including their retained ephemeral/ciphertext when already generated, use the unrestricted prechallenge interpreter. -/
def observeCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector)
    (execution : ServerExecution) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  simulateQ (initializerPostRealImpl source kem) (observer.main identitySk result execution)

/-- Actual source evaluation after an accepted typed registration, for every identity and KEM public key. -/
noncomputable def acceptedCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  if identity.toList ++ keys.oneTime.toList ∈ server.consumed then
    observeCommon source kem setup selector observer identitySk result
      ⟨none, none, .error .registrationReplay, server⟩
  else
    let ephemeral ← OracleComp.liftComp ephemeralGen (MlKemCCAOracleSpec baseSpec)
    let (ciphertext, secret) ← OracleComp.liftComp (kem.encaps keys.pqKey) (MlKemCCAOracleSpec baseSpec)
    let outcome := match rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
      | some failure => (.error failure, server)
      | none => finishFromRoot source.crypto server application identity keys.oneTime ephemeral.toList ciphertext
          (productionHiddenRoot source
            (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)
    observeCommon source kem setup selector observer identitySk result
      ⟨some ephemeral, some ciphertext, outcome⟩

/-- Attacker-owned and changed candidates use the same actual verification, freshness, ephemeral, encapsulation, conversion, DH, and record operations. -/
noncomputable def allCandidateCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  match acceptPhase1Candidate verifyFn result.candidate with
  | none => observeCommon source kem setup selector observer identitySk result
      ⟨none, none, .error .badEncoding, server⟩
  | some (identity, keys) => acceptedCommon source kem setup selector observer server application
      ephemeralGen identitySk result identity keys

/-- Pending preparations retain the generated ephemeral; aborts still encapsulate in source order before returning their full unrestricted continuation. -/
noncomputable def prepareTarget
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Bool ⊕ List.Vector UInt8 32) := do
  let ephemeral ← OracleComp.liftComp ephemeralGen (MlKemCCAOracleSpec baseSpec)
  match rootFailure source.crypto server.ikSk ephemeral.toList result.identity
      result.before.publicKey result.after.publicKey with
  | none => pure (.inr ephemeral)
  | some failure =>
      let (ciphertext, _) ← OracleComp.liftComp (kem.encaps result.target) (MlKemCCAOracleSpec baseSpec)
      let decision ← observeCommon source kem setup selector observer identitySk result
        ⟨some ephemeral, some ciphertext, .error failure, server⟩
      pure (.inl decision)

/-- Instantiation of the conditional root boundary with actual server operations and actual selected fields. -/
noncomputable def sourceProtocol
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) :
    RootProtocol kem setup selector IdentitySK where
  Private := List.Vector UInt8 32
  targetEligible _ result := decide (result.identity.toList ++ result.after.publicKey.toList ∉ server.consumed)
  prepare := prepareTarget source kem setup selector observer server ephemeralGen
  coordinates _ result ephemeral _ _ := serverCoordinates source.crypto server.ikSk ephemeral.toList
    result.identity result.before.publicKey result.after.publicKey
  finish identitySk result ephemeral transcript _known root :=
    observer.main identitySk result ⟨some ephemeral, some transcript.ciphertext,
      finishFromRoot source.crypto server application result.identity result.after.publicKey
        ephemeral.toList transcript.ciphertext root⟩
  nonTarget := allCandidateCommon source kem setup selector observer server application ephemeralGen verifyFn
  onForgery _ _ := pure false

/-- The concrete target sampler is the exact 192-byte server input, including the actual four DH coordinates. -/
theorem sourceProtocol_rootInput
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector)
    (ephemeral : List.Vector UInt8 32) (target : TargetKemPublicKey)
    (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret)
    (converted : Pqxdh.Bytes) (conversion : source.crypto.xpkConv result.identity.toList = some converted) :
    hiddenRootIKM ((sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn).coordinates
      identitySk result ephemeral target ciphertext) secret =
      Pqxdh.ikmOf (Pqxdh.serverDHs source.crypto server.ikSk ephemeral.toList converted
        result.before.publicKey.toList result.after.publicKey.toList) secret.toList :=
  (serverCoordinates_rootInput source.crypto server.ikSk ephemeral.toList result.identity
    result.before.publicKey result.after.publicKey converted conversion secret).1

/-- Direct source order: generate ephemeral, encapsulate, convert/validate DH, then either abort or construct records from the actual root. -/
noncomputable def directTargetContinuation
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector) (kemSk : KemSK) : ProbComp Bool := do
  let ephemeral ← simulateQ (kemAmbientImpl baseImpl) ephemeralGen
  let (ciphertext, secret) ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps result.target)
  match rootFailure source.crypto server.ikSk ephemeral.toList result.identity
      result.before.publicKey result.after.publicKey with
  | some failure =>
      runCommon baseImpl kem kemSk (observeCommon source kem setup selector observer identitySk result
        ⟨some ephemeral, some ciphertext, .error failure, server⟩)
  | none =>
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (kem.IND_CCA_postChallengeImpl kemSk ciphertext)
        (simulateQ (initializerPostRealImpl source kem)
          (observer.main identitySk result ⟨some ephemeral, some ciphertext,
            finishFromRoot source.crypto server application result.identity result.after.publicKey
              ephemeral.toList ciphertext
              (productionHiddenRoot source
                (serverCoordinates source.crypto server.ikSk ephemeral.toList result.identity
                  result.before.publicKey result.after.publicKey) secret)⟩)))

/-- The actual one-session receive experiment selects its target internally; every other candidate and every replay stays real. -/
noncomputable def actualContinuation
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (state : IdentitySK × StatefulPhase1Result kem setup selector × KemSK) : ProbComp Bool :=
  match admission verifyFn state.2.1 with
  | .unchanged =>
    if state.2.1.identity.toList ++ state.2.1.after.publicKey.toList ∉ server.consumed then
      directTargetContinuation source baseImpl kem setup selector observer server application ephemeralGen
        state.1 state.2.1 state.2.2
    else runCommon baseImpl kem state.2.2
      (allCandidateCommon source kem setup selector observer server application ephemeralGen verifyFn state.1 state.2.1)
  | _ => runCommon baseImpl kem state.2.2
      (allCandidateCommon source kem setup selector observer server application ephemeralGen verifyFn state.1 state.2.1)

/-- Both forms preserve the complete observer; abort classification may move past no random generator and changes no local oracle simulation. -/
theorem sourceContinuation_eq_actual
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (state : IdentitySK × StatefulPhase1Result kem setup selector × KemSK) :
    sourceContinuation source baseImpl kem setup selector verifyFn
      (sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn) false state =
    actualContinuation source baseImpl kem setup selector observer server application ephemeralGen verifyFn state := by
  rcases state with ⟨identitySk, result, kemSk⟩
  cases admitted : admission verifyFn result <;>
    by_cases fresh : result.identity.toList ++ result.after.publicKey.toList ∉ server.consumed <;>
    simp [sourceContinuation, actualContinuation, sourceProtocol, admitted, fresh,
      prepareTarget, directTargetContinuation, localKemPreChallengeImpl_base]
  apply bind_congr
  intro ephemeral
  cases failure : rootFailure source.crypto server.ikSk ephemeral.toList result.identity
      result.before.publicKey result.after.publicKey <;>
    simp [localKemPreChallengeImpl_base, runCommon]

/-- One complete source-ordered Phase-1 execution followed by its actual selected server computation. -/
noncomputable def actualGame
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) : ProbComp Bool :=
  privateSourcePrefix baseImpl sigAlg kem setup selector >>= fun state =>
    actualContinuation source baseImpl kem setup selector observer server application ephemeralGen verifyFn state

/-- The computational root interface erases exactly to the source execution, retaining every interpreted uniform query and all source poststate. -/
theorem sourceGame_eq_actualGame
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) :
    sourceGame source baseImpl sigAlg kem setup selector verifyFn
      (sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn) false =
    actualGame source baseImpl sigAlg kem setup selector observer server application ephemeralGen verifyFn := by
  unfold sourceGame actualGame
  apply bind_congr
  exact sourceContinuation_eq_actual source baseImpl kem setup selector observer server application ephemeralGen verifyFn

/-- The actual source DH/root/record execution has four explicit coefficient-one reductions and internally selects its fresh authenticated target. -/
theorem actualRootAdvantage_le_euf_add_kem_add_extract_add_hmac
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn) :
    let protocol := sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn
    let adversary := rootInitializer sigAlg kem setup selector verifyFn protocol
    let sample := PqxdhSecretInputInitializer.secretInputSample baseImpl kem adversary
    let continuation := PqxdhSecretInputInitializer.rootObserver source baseImpl kem adversary
    (actualGame source baseImpl sigAlg kem setup selector observer server application ephemeralGen verifyFn).boolDistAdvantage
        (PqxdhSecretInputInitializer.independentInitializerGame source baseImpl kem adversary) ≤
      ((statefulPhase1ToEUFCMA sigAlg kem setup selector).advantage
        (runtimeOfImpl (kemAmbientImpl baseImpl))).toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (toKemOneKeyAdversary source kem adversary).toINDCCA +
      (extractRealGame hmac sample (extractReduction hmac continuation)).boolDistAdvantage
        (extractUniformGame sample (extractReduction hmac continuation)) +
      (hmacPrfRealGame hmac (expandReduction sample continuation)).boolDistAdvantage
        (hmacPrfRandomGame (expandReduction sample continuation)) := by
  have bound := authenticatedRootAdvantage_le_euf_add_kem_add_extract_add_hmac source hmac correct
    baseImpl sigAlg kem setup selector verifyFn deterministic
    (sourceProtocol source kem setup selector observer server application ephemeralGen verifyFn)
  dsimp only at bound ⊢
  rw [sourceGame_eq_actualGame] at bound
  exact bound

/--
info: 'BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot.sourceContinuation_eq_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourceContinuation_eq_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot.actualRootAdvantage_le_euf_add_kem_add_extract_add_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actualRootAdvantage_le_euf_add_kem_add_extract_add_hmac

end BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRoot
