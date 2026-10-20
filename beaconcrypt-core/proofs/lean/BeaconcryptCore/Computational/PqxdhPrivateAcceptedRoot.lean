import BeaconcryptCore.Computational.PqxdhCorrelatedRootSource
import BeaconcryptCore.Computational.PqxdhServerRegistrationPublication

/-!
The private accepted-root continuation runs after actual root production and registration consumption, before response construction or publication. It retains the same complete generated prefix, private selector context, identity histories and actual optional source branches. The legacy observer is recovered by an exact full-program specialization, not by undoing earlier publication. Root and ephemeral values remain private protocol inputs, and only the final Boolean is observed.

The actual all-candidate source is bounded by the same coefficient-one joint-use weak-EUF plus ordinary KEM IND-CCA terms. Public CCA challenge suppression stays separate from private protocol root derivation: every matching private ciphertext uses the same supplied secret. Functional pure decapsulation and actual supported native/total compatibility remain explicit. This module changes no primitive endpoint, introduces no independent-root assumption and does not discharge native whole-prefix/state representations, pinned-Server authentication, evolving/reveal policy or global security.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhSecretInputInitializer
open PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot PqxdhPrivateRootSource
open PqxdhChallengeSecretRouting
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev CorrelatedSpec (baseSpec : OracleSpec ι) :=
  PostSourceSpec baseSpec + (RootRequest →ₒ Option RootOutput)

/-- Private source values at the accepted-root continuation, after consumption and before publication. -/
structure Ready where
  consumed : Pqxdh.ServerState
  application : Option Pqxdh.Bytes
  identity : Ed25519PublicKey
  oneTime : X25519PublicKey
  ephemeral : List.Vector UInt8 32
  ciphertext : MlKem768Ciphertext
  root : RootOutput

def ready (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (identity : Ed25519PublicKey) (oneTime : X25519PublicKey)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (root : RootOutput) : Ready :=
  ⟨{ server with consumed := (identity.toList ++ oneTime.toList) :: server.consumed },
    application, identity, oneTime, ephemeral, ciphertext, root⟩

/-- Both callbacks are private protocol continuation; only the final Boolean is observed. -/
structure Continuation (setup : StatefulPhase1Setup baseSpec) (Selection : Type) where
  completed : Option (Outcome (Retained setup Unit Selection)) → ServerExecution →
    OracleComp (CorrelatedSpec baseSpec) Bool
  accepted : Option (Outcome (Retained setup Unit Selection)) → Ready →
    OracleComp (CorrelatedSpec baseSpec) Bool

def localCoins {Result : Type} (client : ProbComp Result) : OracleComp (LocalPostSpec baseSpec) Result :=
  simulateQ (fun coin => ((LocalPostSpec baseSpec).query (.inl (.inl (.inl coin))) :
    OracleComp (LocalPostSpec baseSpec) _)) client

/-- Public HKDF queries use the same supplied source function. Source services preserve complete private identity state. -/
def localSourceImpl
    (source : FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) :
    QueryImpl (CorrelatedSpec baseSpec) (StateT (BareState count) (OracleComp (LocalPostSpec baseSpec))) :=
  fun query state => match query with
  | .inl (.inl request) => localCoins ((bareImpl attachedVerify primitives count request).run state)
  | .inl (.inr (.inl request)) => do
      let answer ← (LocalPostSpec baseSpec).query (.inl request)
      pure (answer, state)
  | .inl (.inr (.inr request)) =>
      pure (request.project (productionStream source.crypto request.address), state)
  | .inr request => do
      let answer ← (LocalPostSpec baseSpec).query (.inr request)
      pure (answer, state)

def localObserve
    (source : FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : ServerExecution) (state : BareState count) : OracleComp (LocalPostSpec baseSpec) Bool :=
  Prod.fst <$> ((simulateQ (localSourceImpl source attachedVerify primitives count)
    (observer.completed output execution)).run state)

def localAccepted
    (source : FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : Ready) (state : BareState count) : OracleComp (LocalPostSpec baseSpec) Bool :=
  Prod.fst <$> ((simulateQ (localSourceImpl source attachedVerify primitives count)
    (observer.accepted output execution)).run state)

/-- Private root requests always perform the original decapsulation, including the active challenge. -/
noncomputable def sourcePost
    (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext) :
    QueryImpl (LocalPostSpec baseSpec) (OracleComp (MlKemCCAOracleSpec baseSpec))
  | .inl request => match challenge with
      | none => (MlKemCCAOracleSpec baseSpec).query request
      | some ciphertext => blockChallenge ciphertext request
  | .inr request => do
      let recovered ← (MlKemCCAOracleSpec baseSpec).query (.inr request.ciphertext)
      pure (recovered.map (productionHiddenRoot source request.coordinates))

noncomputable def observe
    (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : ServerExecution) (state : BareState count) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  simulateQ (sourcePost source challenge)
    (localObserve source attachedVerify primitives count setup observer output execution state)

noncomputable def acceptedObserve
    (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : Ready) (state : BareState count) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  simulateQ (sourcePost source challenge)
    (localAccepted source attachedVerify primitives count setup observer output execution state)

theorem sourcePost_interpreter
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    localKemPreChallengeImpl kem secret ∘ₛ sourcePost source (some challenge) =
      actualImpl source kem secret challenge := by
  funext request
  cases request with
  | inl request =>
      exact congrFun (blockChallenge_interpreter kem secret challenge) request
  | inr request =>
      simp only [QueryImpl.compose, sourcePost, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rfl

theorem sourcePost_complete {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (LocalPostSpec baseSpec) Result) :
    evalKem baseImpl kem secret (simulateQ (sourcePost source (some challenge)) client) =
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (actualImpl source kem secret challenge) client) := by
  simp only [evalKem, ← QueryImpl.simulateQ_compose, sourcePost_interpreter]

/-- All typed accepted identities and candidate KEM keys execute optional native encapsulation in actual source order. -/
noncomputable def acceptedCommon
    (source : FixedHkdfSha512NoSaltSource)
    (_kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  if identity.toList ++ keys.oneTime.toList ∈ server.consumed then
    observe source none attachedVerify primitives count setup observer output
      ⟨none, none, .error .registrationReplay, server⟩ state
  else
    let ephemeral ← OracleComp.liftComp ephemeralGen (MlKemCCAOracleSpec baseSpec)
    let encapsulated ← OracleComp.liftComp (native.encaps keys.pqKey) (MlKemCCAOracleSpec baseSpec)
    match encapsulated with
    | none =>
        observe source none attachedVerify primitives count setup observer output
          ⟨some ephemeral, none, .error .badEncoding, server⟩ state
    | some (ciphertext, secret) =>
        match rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
        | some failure =>
            observe source none attachedVerify primitives count setup observer output
              ⟨some ephemeral, some ciphertext, .error failure, server⟩ state
        | none =>
            acceptedObserve source none attachedVerify primitives count setup observer output
              (ready server application identity keys.oneTime ephemeral ciphertext
                (productionHiddenRoot source
                  (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)) state

/-- Source optional verification controls the real continuation, including attacker-owned candidates and all rejection branches. -/
noncomputable def allCandidateCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32)) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  match output.bind (·.accepted) with
  | none => observe source none attachedVerify primitives count setup observer output
      ⟨none, none, .error .badEncoding, server⟩ state
  | some (identity, keys) => acceptedCommon source kem native attachedVerify primitives count setup observer output
      state server application ephemeralGen identity keys

/-- Actual private root requests remain unrestricted after target success; the public CCA service alone blocks its challenge. -/
noncomputable def targetAfterEncapsulation
    (_kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  let output := prepared.1
  let identity := output.context.publicIdentity.ed25519
  let generated := output.context.generated
  match encapsulated with
  | none =>
      observe parameters.source none attachedVerify primitives 1 setup observer (some output)
        ⟨some ephemeral, none, .error .badEncoding, parameters.server⟩ prepared.2
  | some (ciphertext, secret) =>
      match rootFailure parameters.source.crypto parameters.server.ikSk ephemeral.toList identity
        generated.before.publicKey generated.after.publicKey with
      | some failure =>
          observe parameters.source none attachedVerify primitives 1 setup observer (some output)
            ⟨some ephemeral, some ciphertext, .error failure, parameters.server⟩ prepared.2
      | none =>
          acceptedObserve parameters.source (some ciphertext) attachedVerify primitives 1 setup observer (some output)
            (ready parameters.server parameters.application identity generated.after.publicKey ephemeral ciphertext
              (productionHiddenRoot parameters.source
                (serverCoordinates parameters.source.crypto parameters.server.ikSk ephemeral.toList identity
                  generated.before.publicKey generated.after.publicKey) secret)) prepared.2

/-- Optional source encapsulation retains ephemeral generation and native failure before every later DH/root operation. -/
noncomputable def nativeTargetContinuation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  let ephemeral ← ccaAmbient parameters.ephemeralGen
  let encapsulated ← ccaAmbient (parameters.native.encaps prepared.1.context.generated.target)
  targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral encapsulated

/-- Ordinary total encapsulation is a separate target-only presentation, justified later by actual generated-key support. -/
noncomputable def totalTargetContinuation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  let ephemeral ← ccaAmbient parameters.ephemeralGen
  let encapsulated ← ccaAmbient (kem.encaps prepared.1.context.generated.target)
  targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral (some encapsulated)

/-- All accepted, attacker-owned, changed and rejected candidates remain in the same source root game. -/
noncomputable def nativeNext
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  if targetEligible parameters prepared then
    nativeTargetContinuation kem parameters attachedVerify primitives setup observer prepared
  else allCandidateCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer
    (some prepared.1) prepared.2 parameters.server parameters.application parameters.ephemeralGen

/-- Source game uses the real optional native interface and the source-shaped private prefix before the observer sees any root-dependent output. -/
noncomputable def actualGame
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State) : ProbComp Bool :=
  continuedSource attachedVerify primitives baseImpl kem setup selector
    (nativeNext kem parameters attachedVerify primitives setup observer) false


def finishReady (c : Pqxdh.Crypto) (execution : Ready) : ServerExecution :=
  ⟨some execution.ephemeral, some execution.ciphertext,
    if execution.application = some [] then (.error .emptyAppMessage, execution.consumed)
    else Pqxdh.serverEmit c execution.consumed execution.identity.toList execution.root.toList
      execution.ciphertext.toList (c.xpub execution.ephemeral.toList)
      (execution.application.getD [0xFF])⟩

/-- Earlier publication is a specialization of the private accepted-root continuation. -/
def legacy (source : FixedHkdfSha512NoSaltSource)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : PqxdhCorrelatedRootSource.CorrelatedObserver setup Selection) :
    Continuation setup Selection where
  completed := observer.main
  accepted output execution := observer.main output (finishReady source.crypto execution)

theorem finishReady_ready (c : Pqxdh.Crypto) (server : Pqxdh.ServerState)
    (application : Option Pqxdh.Bytes) (identity : Ed25519PublicKey) (oneTime : X25519PublicKey)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (root : RootOutput) :
    finishReady c (ready server application identity oneTime ephemeral ciphertext root) =
      ⟨some ephemeral, some ciphertext,
        finishFromRoot c server application identity oneTime ephemeral.toList ciphertext root⟩ := rfl

theorem observe_legacy
    (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : PqxdhCorrelatedRootSource.CorrelatedObserver setup Selection)
    (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : ServerExecution) (state : BareState count) :
    observe source challenge attachedVerify primitives count setup (legacy source setup observer)
      output execution state =
      PqxdhCorrelatedRootSource.observe source challenge attachedVerify primitives count setup observer
        output execution state := rfl

theorem acceptedObserve_legacy
    (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : PqxdhCorrelatedRootSource.CorrelatedObserver setup Selection)
    (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : Ready) (state : BareState count) :
    acceptedObserve source challenge attachedVerify primitives count setup (legacy source setup observer)
      output execution state =
      PqxdhCorrelatedRootSource.observe source challenge attachedVerify primitives count setup observer
        output (finishReady source.crypto execution) state := rfl

theorem acceptedCommon_legacy
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : PqxdhCorrelatedRootSource.CorrelatedObserver setup Selection)
    (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    acceptedCommon source kem native attachedVerify primitives count setup (legacy source setup observer)
      output state server application ephemeralGen identity keys =
      PqxdhCorrelatedRootSource.acceptedCommon source kem native attachedVerify primitives count setup observer
        output state server application ephemeralGen identity keys := by
  simp only [acceptedCommon, PqxdhCorrelatedRootSource.acceptedCommon, observe_legacy]
  split
  · rfl
  · congr 1
    funext ephemeral
    congr 1
    funext encapsulated
    cases encapsulated with
    | none => rfl
    | some pair =>
      rcases pair with ⟨ciphertext, secret⟩
      cases failure : rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime <;>
        simp only [acceptedObserve_legacy, finishReady_ready]

theorem allCandidateCommon_legacy
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : PqxdhCorrelatedRootSource.CorrelatedObserver setup Selection)
    (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32)) :
    allCandidateCommon source kem native attachedVerify primitives count setup (legacy source setup observer)
      output state server application ephemeralGen =
      PqxdhCorrelatedRootSource.allCandidateCommon source kem native attachedVerify primitives count setup observer
        output state server application ephemeralGen := by
  simp only [allCandidateCommon, PqxdhCorrelatedRootSource.allCandidateCommon,
    observe_legacy, acceptedCommon_legacy]
  rfl

theorem targetAfterEncapsulation_legacy
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : PqxdhCorrelatedRootSource.CorrelatedObserver setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    targetAfterEncapsulation kem parameters attachedVerify primitives setup
      (legacy parameters.source setup observer) prepared ephemeral encapsulated =
      PqxdhCorrelatedRootSource.targetAfterEncapsulation kem parameters attachedVerify primitives setup
        observer prepared ephemeral encapsulated := by
  cases encapsulated with
  | none => rfl
  | some pair =>
    rcases pair with ⟨ciphertext, secret⟩
    simp only [targetAfterEncapsulation, PqxdhCorrelatedRootSource.targetAfterEncapsulation, observe_legacy]
    cases rootFailure parameters.source.crypto parameters.server.ikSk ephemeral.toList
      prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
      prepared.1.context.generated.after.publicKey <;>
      simp only [acceptedObserve_legacy, finishReady_ready]

theorem nativeNext_legacy
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : PqxdhCorrelatedRootSource.CorrelatedObserver setup Selection)
    (prepared : Prepared setup Selection) :
    nativeNext kem parameters attachedVerify primitives setup
      (legacy parameters.source setup observer) prepared =
      PqxdhCorrelatedRootSource.nativeNext kem parameters attachedVerify primitives setup observer prepared := by
  simp only [nativeNext, PqxdhCorrelatedRootSource.nativeNext, nativeTargetContinuation,
    PqxdhCorrelatedRootSource.nativeTargetContinuation, targetAfterEncapsulation_legacy,
    allCandidateCommon_legacy]

/-- Specialization retains the complete private generation/selection continuation before the final observation. -/
theorem actualGame_legacy
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : PqxdhCorrelatedRootSource.CorrelatedObserver setup selector.State) :
    actualGame baseImpl kem parameters attachedVerify primitives setup selector
      (legacy parameters.source setup observer) =
      PqxdhCorrelatedRootSource.actualGame baseImpl kem parameters attachedVerify primitives setup selector observer := by
  have same := funext (nativeNext_legacy kem parameters attachedVerify primitives setup observer)
  simp only [actualGame, PqxdhCorrelatedRootSource.actualGame, same]

/-- Functional honest-key compatibility is lifted through every target rejection, actual source record construction, and complete observer continuation. -/
theorem nativeTarget_eq_total
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) (secret : KemSK)
    (supported : (prepared.1.context.generated.target, secret) ∈
      support (simulateQ (kemAmbientImpl baseImpl) kem.keygen)) :
    𝒟[evalKem baseImpl kem secret
      (nativeTargetContinuation kem parameters attachedVerify primitives setup observer prepared)] =
      𝒟[evalKem baseImpl kem secret
        (totalTargetContinuation kem parameters attachedVerify primitives setup observer prepared)] := by
  apply evalDist_eq_of_evalSPMF_eq
  simp only [nativeTargetContinuation, totalTargetContinuation, evalKem_bind, evalKem_ambient]
  apply evalSPMF_bind_congr'
  intro ephemeral
  rw [evalSPMF_bind, (VCVioLegacy.evalSPMF_eq_iff_evalDistEq _ _).2 (compatible _ supported),
    ← evalSPMF_bind]
  simp only [bind_map_left]

/-- Only the internally recognized unchanged target uses the ordinary total KEM presentation. Arbitrary selected public keys still use the optional source operation. -/
noncomputable def totalNext
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  if targetEligible parameters prepared then
    totalTargetContinuation kem parameters attachedVerify primitives setup observer prepared
  else allCandidateCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer
    (some prepared.1) prepared.2 parameters.server parameters.application parameters.ephemeralGen

/-- The entire real source game agrees with target-only total encapsulation after proving support from the same source generation. No selected-candidate honesty or external target-support premise is used. -/
theorem actualGame_eq_total
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State) :
    𝒟[actualGame baseImpl kem parameters attachedVerify primitives setup selector observer] =
      𝒟[continuedSource attachedVerify primitives baseImpl kem setup selector
        (totalNext kem parameters attachedVerify primitives setup observer) false] := by
  apply evalDist_eq_of_evalSPMF_eq
  simp only [actualGame, continuedSource, program_complete, bind_assoc, pure_bind]
  apply evalSPMF_bind_congr'
  intro seed
  apply evalSPMF_bind_congr
  intro generated generatedSupport
  apply evalSPMF_bind_congr'
  intro selected
  simp only [nativeNext, totalNext]
  split
  · apply evalSPMF_eq_of_evalDist_eq
    apply nativeTarget_eq_total baseImpl kem parameters compatible attachedVerify primitives setup observer
    exact generate_key_support baseImpl kem setup _ generated generatedSupport
  · rfl


/-- The ordinary challenger supplies the root to the original private accepted continuation. -/
noncomputable def finishTarget
    (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (root : RootOutput) :
    OracleComp (LocalPostSpec baseSpec) Bool :=
  localAccepted parameters.source attachedVerify primitives 1 setup observer (some prepared.1)
    (ready parameters.server parameters.application prepared.1.context.publicIdentity.ed25519
      prepared.1.context.generated.after.publicKey ephemeral ciphertext root) prepared.2

/-- Original private source state and the correlated post interface surround the same accepted-root program. -/
theorem finishTarget_actual
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (root : RootOutput) :
    simulateQ (kemAmbientImpl baseImpl) (simulateQ (actualImpl parameters.source kem secret ciphertext)
      (finishTarget parameters attachedVerify primitives setup observer prepared ephemeral ciphertext root)) =
      evalKem baseImpl kem secret
        (acceptedObserve parameters.source (some ciphertext) attachedVerify primitives 1 setup observer (some prepared.1)
          (ready parameters.server parameters.application prepared.1.context.publicIdentity.ed25519
            prepared.1.context.generated.after.publicKey ephemeral ciphertext root) prepared.2) := by
  exact (sourcePost_complete parameters.source baseImpl kem secret ciphertext _).symm

/-- Filter only the charged fresh changed-acceptance branch. Every other completed branch runs through unrestricted prechallenge oracles in source order. -/
noncomputable def dispatch
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) (Mode setup Selection) := do
  if changedBit (some prepared.1, prepared.2) then pure (.completed false)
  else if targetEligible parameters prepared then
    let ephemeral ← ccaAmbient parameters.ephemeralGen
    match rootFailure parameters.source.crypto parameters.server.ikSk ephemeral.toList
      prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
      prepared.1.context.generated.after.publicKey with
    | none => pure (.pending prepared ephemeral)
    | some failure =>
        let encapsulated ← ccaAmbient (kem.encaps prepared.1.context.generated.target)
        let decision ← observe parameters.source none attachedVerify primitives 1 setup observer (some prepared.1)
          ⟨some ephemeral, some encapsulated.1, .error failure, parameters.server⟩ prepared.2
        pure (.completed decision)
  else
    let decision ← allCandidateCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer
      (some prepared.1) prepared.2 parameters.server parameters.application parameters.ephemeralGen
    pure (.completed decision)


/-- The actual generated source prefix is private ordinary CCA context, with no target secret-key field. -/
noncomputable def rootProtocol
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State) : Protocol baseSpec where
  State := Mode setup selector.State
  prepare target := borrowedPrefix attachedVerify primitives setup selector target >>=
    dispatch kem parameters attachedVerify primitives setup observer
  initialCoordinates _ _ mode := match mode with
    | .completed _ => none
    | .pending prepared ephemeral => some
        (serverCoordinates parameters.source.crypto parameters.server.ikSk ephemeral.toList
          prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
          prepared.1.context.generated.after.publicKey)
  resume _ ciphertext mode root := match mode with
    | .completed decision => pure decision
    | .pending prepared ephemeral => match root with
        | none => pure false
        | some value => finishTarget parameters attachedVerify primitives setup observer prepared ephemeral ciphertext value

/-- The native completion has no unused secret draw; completed modes still incur ordinary encapsulation. -/
noncomputable def complete
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (target : TargetKemPublicKey) (secret : KemSK) (state : protocol.State) :
    OracleComp (unifSpec + baseSpec) Bool := do
  let encapsulated ← kem.encaps target
  simulateQ (actualImpl source kem secret encapsulated.1)
    (protocol.resume target encapsulated.1 state
      ((protocol.initialCoordinates target encapsulated.1 state).map
        (fun coordinates => productionHiddenRoot source coordinates encapsulated.2)))
/-- The only filtered branch is the changed fresh accepted tuple charged to the joint signature reduction. -/
noncomputable def filteredNext
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Continuation setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  if changedBit (some prepared.1, prepared.2) then pure false
  else totalNext kem parameters attachedVerify primitives setup observer prepared


/-- Native completion preserves every filtered source branch and private root continuation. -/
theorem dispatch_complete_eq_source
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State) (prepared : Prepared setup selector.State)
    (target : TargetKemPublicKey) (secret : KemSK)
    (target_eq : prepared.1.context.generated.target = target) :
    𝒟[do
      let mode ← evalKem baseImpl kem secret
        (dispatch kem parameters attachedVerify primitives setup observer prepared)
      simulateQ (kemAmbientImpl baseImpl)
        (complete parameters.source kem
          (rootProtocol kem parameters attachedVerify primitives setup selector observer)
          target secret mode)] =
      𝒟[evalKem baseImpl kem secret
        (filteredNext kem parameters attachedVerify primitives setup observer prepared)] := by
  apply evalDist_eq_of_evalSPMF_eq
  by_cases bad : changedBit (some prepared.1, prepared.2) = true
  · apply evalSPMF_ext
    intro output
    simp [dispatch, filteredNext, bad, evalKem, complete, rootProtocol]
  · by_cases eligible : targetEligible parameters prepared = true
    · simp only [dispatch, filteredNext, bad, Bool.false_eq_true, ite_false, eligible, ite_true,
        totalNext, totalTargetContinuation, evalKem_bind, evalKem_ambient, bind_assoc]
      apply evalSPMF_bind_congr'
      intro ephemeral
      cases failure : rootFailure parameters.source.crypto parameters.server.ikSk ephemeral.toList
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
        prepared.1.context.generated.after.publicKey with
      | none =>
          simp only [complete, rootProtocol, simulateQ_bind, evalKem_pure, pure_bind,
            targetAfterEncapsulation, failure, Option.map_some, target_eq, finishTarget_actual]
      | some reason =>
          simp only [evalKem_bind, evalKem_ambient, evalKem_pure, bind_assoc, pure_bind,
            targetAfterEncapsulation, failure]
          apply evalSPMF_bind_congr'
          intro encapsulated
          apply evalSPMF_ext
          intro output
          simp [complete, rootProtocol, probOutput_bind_eq_tsum]
    · apply evalSPMF_ext
      intro output
      simp [dispatch, filteredNext, bad, eligible, totalNext, evalKem, complete,
        rootProtocol, probOutput_bind_eq_tsum]

set_option backward.isDefEq.respectTransparency false in
/-- The actual filtered prefix and complete native correlated continuation form the ordinary source experiment. -/
theorem filteredSource_eq_sourceMain
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State) :
    𝒟[continuedSource attachedVerify primitives baseImpl kem setup selector
      (filteredNext kem parameters attachedVerify primitives setup observer) false] =
      𝒟[simulateQ (kemAmbientImpl baseImpl) (sourceMain parameters.source kem
        (rootProtocol kem parameters attachedVerify primitives setup selector observer))] := by
  apply evalDist_eq_of_evalSPMF_eq
  rw [continuedSource_keyfirst]
  simp only [sourceMain, rootProtocol, simulateQ_bind, bind_assoc, evalKem_bind]
  apply evalSPMF_bind_congr'
  intro pair
  apply evalSPMF_bind_congr
  intro prepared supported
  apply evalSPMF_eq_of_evalDist_eq
  simpa only [complete, rootProtocol, simulateQ_bind, evalKem, localKemPreChallengeImpl] using
    (dispatch_complete_eq_source baseImpl kem parameters attachedVerify primitives setup selector
    observer prepared pair.1 pair.2
    (borrowedPrefix_target attachedVerify primitives baseImpl kem pair.2 setup selector pair.1 prepared supported)).symm
/-- The filtered source presentation changes only its named bad branch, preserving the same complete private prefix. -/
theorem continuedSource_filtered
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State) :
    continuedSource attachedVerify primitives baseImpl kem setup selector
      (filteredNext kem parameters attachedVerify primitives setup observer) false = (do
      let stopped ← privateRun attachedVerify primitives 1 (program baseImpl kem setup selector)
      if changedBit stopped then pure false else
        match stopped.1 with
        | none => pure false
        | some output =>
            evalKem baseImpl kem output.context.generated.secret
              (totalNext kem parameters attachedVerify primitives setup observer (eraseOutput output, stopped.2))) := by
  unfold continuedSource
  apply bind_congr
  rintro ⟨output, state⟩
  cases output with
  | none => rfl
  | some output =>
      simp only [filteredNext, erase_changedBit]
      split <;> simp only [evalKem_pure]

/-- The complete actual optional source reaches the correlated native protocol through one concrete joint-use weak-EUF reduction. -/
theorem authentication_hop
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (selectorNoCreate : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) (observer : Continuation setup selector.State) :
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).boolDistAdvantage
      (simulateQ (kemAmbientImpl baseImpl) (sourceMain parameters.source kem
        (rootProtocol kem parameters attachedVerify primitives setup selector observer))) ≤
      (advantage primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).toReal := by
  have auth := authentication_continuation_bound attachedVerify primitives adapter baseImpl kem setup selector
    selectorNoSign selectorNoCreate fallback ordinaryFallback
    (fun stopped => match stopped.1 with
      | none => pure false
      | some output =>
          evalKem baseImpl kem output.context.generated.secret
            (totalNext kem parameters attachedVerify primitives setup observer (eraseOutput output, stopped.2)))
    (fun _ => pure false)
  have totalBound :
      tvDist (continuedSource attachedVerify primitives baseImpl kem setup selector
        (totalNext kem parameters attachedVerify primitives setup observer) false)
        (continuedSource attachedVerify primitives baseImpl kem setup selector
          (filteredNext kem parameters attachedVerify primitives setup observer) false) ≤
      (advantage primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).toReal := by
    rw [continuedSource_filtered]
    exact auth
  have output := (abs_probOutput_toReal_sub_le_tvDist _ _).trans totalBound
  simpa only [ProbComp.boolDistAdvantage, evalDist_apply_singleton, probOutput_def,
    actualGame_eq_total baseImpl kem parameters compatible attachedVerify primitives setup selector observer,
    ← filteredSource_eq_sourceMain baseImpl kem parameters attachedVerify primitives setup selector observer] using output


/-- The actual authenticated prefix reaches one jointly random shared-secret world. Roots are never replaced independently. -/
theorem authenticated_correlated_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (selectorNoCreate : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (observer : Continuation setup selector.State) :
    let protocol := rootProtocol kem parameters attachedVerify primitives setup selector observer
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).boolDistAdvantage
      (simulateQ (kemAmbientImpl baseImpl)
        (randomMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)) ≤
      (advantage primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (reduction parameters.source kem protocol).toINDCCA := by
  dsimp only
  have authenticated := authentication_hop baseImpl kem parameters compatible attachedVerify primitives adapter
    setup selector selectorNoSign selectorNoCreate fallback ordinaryFallback observer
  have correlated := source_correlated_indCCA parameters.source baseImpl kem functional correct
    (rootProtocol kem parameters attachedVerify primitives setup selector observer)
  have loss :
      (simulateQ (kemAmbientImpl baseImpl) (sourceMain parameters.source kem
        (rootProtocol kem parameters attachedVerify primitives setup selector observer))).boolDistAdvantage
      (simulateQ (kemAmbientImpl baseImpl) (randomMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl))
        (rootProtocol kem parameters attachedVerify primitives setup selector observer))) =
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (reduction parameters.source kem
          (rootProtocol kem parameters attachedVerify primitives setup selector observer)).toINDCCA := by
    exact correlated.symm
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add authenticated (le_of_eq loss))


end BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.sourcePost_interpreter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.sourcePost_interpreter

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.sourcePost_complete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.sourcePost_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.finishReady_ready' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.finishReady_ready

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.observe_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.observe_legacy

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.acceptedObserve_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.acceptedObserve_legacy

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.acceptedCommon_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.acceptedCommon_legacy

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.allCandidateCommon_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.allCandidateCommon_legacy

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.targetAfterEncapsulation_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.targetAfterEncapsulation_legacy

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.nativeNext_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.nativeNext_legacy

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.actualGame_legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.actualGame_legacy

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.nativeTarget_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.nativeTarget_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.actualGame_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.actualGame_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.finishTarget_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.finishTarget_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.dispatch_complete_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.dispatch_complete_eq_source

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.filteredSource_eq_sourceMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.filteredSource_eq_sourceMain

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.continuedSource_filtered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.continuedSource_filtered

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.authentication_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.authentication_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.authenticated_correlated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot.authenticated_correlated_bound
