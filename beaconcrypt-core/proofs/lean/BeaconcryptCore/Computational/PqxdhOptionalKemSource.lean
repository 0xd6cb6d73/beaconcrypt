import BeaconcryptCore.Computational.PqxdhSourceAuthenticatedRootQueryBounds

/-!
# Optional source encapsulation and honest-key support

Arbitrary typed ML-KEM public keys enter an optional source encapsulation interface. Rejection retains the already generated ephemeral and leaves registration state unchanged. The ordinary total IND-CCA interface is used only on public keys in the evaluated honest key-generation support. Its compatibility contract is equality of the encapsulation output distributions, including success, at precisely those keys; it states no authentication or secrecy conclusion.
-/

open OracleSpec OracleComp ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhOptionalKemSource

open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhHiddenRoot PqxdhJointKdfGame
open PqxdhStatefulPhase1EufCma PqxdhStatefulPhase1Authentication
open PqxdhInitializerSecrecy PqxdhSecretInputKdf PqxdhAuthenticatedRoot
open PqxdhSourceAuthenticatedRoot

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK IdentitySK : Type}

/-- Typed native public-key decoding and encapsulation may reject an arbitrary 1184-byte input. -/
structure SourceKemInterface (baseSpec : OracleSpec iota) where
  encaps : PqxdhKemIndCca.MlKem768PublicKey → OracleComp (unifSpec + baseSpec)
    (Option (MlKem768Ciphertext × MlKemSharedSecret))

/-- Functional compatibility with the ordinary total scheme on its actual generated-key support. This is independent of IND-CCA security. -/
def HonestKeyCompatibility
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec) : Prop :=
  ∀ pair ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen),
    𝒟[simulateQ (kemAmbientImpl baseImpl) (native.encaps pair.1)] =
      𝒟[Option.some <$> simulateQ (kemAmbientImpl baseImpl) (kem.encaps pair.1)]

/-- Native rejection is excluded for generated keys by functional compatibility, not by an IND-CCA security implication. -/
theorem honestEncapsulation_no_failure
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec) (compatible : HonestKeyCompatibility baseImpl kem native)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (supported : pair ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen)) :
    none ∉ support (simulateQ (kemAmbientImpl baseImpl) (native.encaps pair.1)) := by
  rw [mem_support_iff_of_evalDist_eq (compatible pair supported)]
  simp

/-- Actual source evaluation after an accepted typed registration, for every identity and KEM public key. -/
noncomputable def acceptedCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
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
    let encapsulated ← OracleComp.liftComp (native.encaps keys.pqKey) (MlKemCCAOracleSpec baseSpec)
    match encapsulated with
    | none =>
      observeCommon source kem setup selector observer identitySk result
        ⟨some ephemeral, none, .error .badEncoding, server⟩
    | some (ciphertext, secret) =>
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
    (native : SourceKemInterface baseSpec)
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
  | some (identity, keys) => acceptedCommon source kem native setup selector observer server application
      ephemeralGen identitySk result identity keys

/-- Total target preparation is confined to the authenticated unchanged branch; every other selected public key uses the optional source operation. -/
noncomputable def sourceProtocol
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) :
    RootProtocol kem setup selector IdentitySK :=
  { PqxdhSourceAuthenticatedRoot.sourceProtocol source kem setup selector observer server application
      ephemeralGen verifyFn with
    nonTarget := allCandidateCommon source kem native setup selector observer server application ephemeralGen verifyFn }

/-- Direct source order: generate ephemeral, encapsulate, convert/validate DH, then either abort or construct records from the actual root. -/
noncomputable def directTargetContinuation
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector) (kemSk : KemSK) : ProbComp Bool := do
  let ephemeral ← simulateQ (kemAmbientImpl baseImpl) ephemeralGen
  let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (native.encaps result.target)
  match encapsulated with
  | none => runCommon baseImpl kem kemSk (observeCommon source kem setup selector observer identitySk result
      ⟨some ephemeral, none, .error .badEncoding, server⟩)
  | some (ciphertext, secret) =>
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

/-- Honest-key compatibility is lifted through the entire target observer, including every abort and retained poststate. -/
theorem directTargetContinuation_eq_total
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identitySk : IdentitySK) (result : StatefulPhase1Result kem setup selector) (kemSk : KemSK)
    (compatible : 𝒟[simulateQ (kemAmbientImpl baseImpl) (native.encaps result.target)] =
      𝒟[Option.some <$> simulateQ (kemAmbientImpl baseImpl) (kem.encaps result.target)]) :
    𝒟[directTargetContinuation source baseImpl kem native setup selector observer server application
      ephemeralGen identitySk result kemSk] =
    𝒟[PqxdhSourceAuthenticatedRoot.directTargetContinuation source baseImpl kem setup selector
      observer server application ephemeralGen identitySk result kemSk] := by
  unfold directTargetContinuation PqxdhSourceAuthenticatedRoot.directTargetContinuation
  apply evalDist_bind_congr'
  intro ephemeral
  rw [evalDist_bind, compatible, ← evalDist_bind]
  simp
  rfl

/-- The actual one-session receive experiment selects its target internally; every other candidate and every replay stays real. -/
noncomputable def actualContinuation
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
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
      directTargetContinuation source baseImpl kem native setup selector observer server application ephemeralGen
        state.1 state.2.1 state.2.2
    else runCommon baseImpl kem state.2.2
      (allCandidateCommon source kem native setup selector observer server application ephemeralGen verifyFn state.1 state.2.1)
  | _ => runCommon baseImpl kem state.2.2
      (allCandidateCommon source kem native setup selector observer server application ephemeralGen verifyFn state.1 state.2.1)


/-- Target compatibility is needed only for the internally identified unchanged fresh branch; arbitrary candidates retain the optional operation. -/
theorem sourceContinuation_eq_actual
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (state : IdentitySK × StatefulPhase1Result kem setup selector × KemSK)
    (compatible : 𝒟[simulateQ (kemAmbientImpl baseImpl) (native.encaps state.2.1.target)] =
      𝒟[Option.some <$> simulateQ (kemAmbientImpl baseImpl) (kem.encaps state.2.1.target)]) :
    𝒟[sourceContinuation source baseImpl kem setup selector verifyFn
      (sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn) false state] =
    𝒟[actualContinuation source baseImpl kem native setup selector observer server application ephemeralGen verifyFn state] := by
  rcases state with ⟨identitySk, result, kemSk⟩
  cases admitted : admission verifyFn result <;>
    by_cases fresh : result.identity.toList ++ result.after.publicKey.toList ∉ server.consumed <;>
    simp [sourceContinuation, actualContinuation, sourceProtocol,
      PqxdhSourceAuthenticatedRoot.sourceProtocol, admitted, fresh]
  rw [directTargetContinuation_eq_total source baseImpl kem native setup selector observer server application
    ephemeralGen identitySk result kemSk compatible]
  have exactEq := congrArg evalDist (PqxdhSourceAuthenticatedRoot.sourceContinuation_eq_actual source baseImpl
    kem setup selector observer server application ephemeralGen verifyFn (identitySk, result, kemSk))
  simp [sourceContinuation, PqxdhSourceAuthenticatedRoot.actualContinuation,
    PqxdhSourceAuthenticatedRoot.sourceProtocol, admitted, fresh] at exactEq
  convert exactEq using 1
  apply bind_congr
  intro mode
  cases mode <;> rfl


/-- One complete source-ordered Phase-1 execution followed by its actual selected server computation. -/
noncomputable def actualGame
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) : ProbComp Bool :=
  privateSourcePrefix baseImpl sigAlg kem setup selector >>= fun state =>
    actualContinuation source baseImpl kem native setup selector observer server application ephemeralGen verifyFn state

/-- Complete source distributions agree after deriving honest-target support from the generated prefix. No selected-candidate honesty hypothesis is present. -/
theorem sourceGame_eq_actualGame
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec) (compatible : HonestKeyCompatibility baseImpl kem native)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) :
    𝒟[sourceGame source baseImpl sigAlg kem setup selector verifyFn
      (sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn) false] =
    𝒟[actualGame source baseImpl sigAlg kem native setup selector observer server application ephemeralGen verifyFn] := by
  unfold sourceGame actualGame
  rw [privateSourcePrefix_borrowed_complete, privateSourcePrefix_borrowed_complete]
  apply evalDist_bind_congr
  intro pair pairSupported
  apply evalDist_bind_congr
  intro retained retainedSupported
  apply sourceContinuation_eq_actual source baseImpl kem native setup selector observer server application ephemeralGen verifyFn
  simpa only [borrowedPrefix_target baseImpl sigAlg kem setup selector pair.1 pair.2 retained retainedSupported] using
    compatible pair pairSupported

/-- The actual source DH/root/record execution has four explicit coefficient-one reductions and internally selects its fresh authenticated target. -/
theorem actualRootAdvantage_le_euf_add_kem_add_extract_add_hmac
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) IdentitySK)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : SourceKemInterface baseSpec) (compatible : HonestKeyCompatibility baseImpl kem native)
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (observer : SourceObserver kem setup selector IdentitySK)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn) :
    let protocol := sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn
    let adversary := rootInitializer sigAlg kem setup selector verifyFn protocol
    let sample := PqxdhSecretInputInitializer.secretInputSample baseImpl kem adversary
    let continuation := PqxdhSecretInputInitializer.rootObserver source baseImpl kem adversary
    (actualGame source baseImpl sigAlg kem native setup selector observer server application ephemeralGen verifyFn).boolDistAdvantage
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
    (sourceProtocol source kem native setup selector observer server application ephemeralGen verifyFn)
  dsimp only at bound ⊢
  have heq := sourceGame_eq_actualGame source baseImpl sigAlg kem native compatible setup selector
    observer server application ephemeralGen verifyFn
  simpa only [ProbComp.boolDistAdvantage, probOutput_def, heq] using bound

/--
info: 'BeaconcryptCore.Computational.PqxdhOptionalKemSource.sourceGame_eq_actualGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourceGame_eq_actualGame

/--
info: 'BeaconcryptCore.Computational.PqxdhOptionalKemSource.actualRootAdvantage_le_euf_add_kem_add_extract_add_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actualRootAdvantage_le_euf_add_kem_add_extract_add_hmac

end BeaconcryptCore.Computational.PqxdhOptionalKemSource
