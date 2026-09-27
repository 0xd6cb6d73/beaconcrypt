import BeaconcryptCore.Computational.PqxdhChallengeSecretRouting

/-!
The actual private identity/prekey/KEM/one-time prefix and all-candidate optional source continuation reach one correlated shared-secret world with joint-use weak-EUF plus ordinary IND-CCA loss. The complete continuation retains source state and every private root request, including the challenge ciphertext. Only the separate ordinary public CCA service blocks that query. Actual generation support justifies target-only native/total compatibility; functional pure decapsulation is separately required by the ordinary CCA substitution. The private observer never receives the target KEM secret. Matching-ciphertext roots use one supplied secret; no independent-root Extract replacement or native global registration theorem is claimed.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhCorrelatedRootSource
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

/-- Private protocol context retains the source state; only its final decision is observed. -/
structure CorrelatedObserver (setup : StatefulPhase1Setup baseSpec) (Selection : Type) where
  main : Option (Outcome (Retained setup Unit Selection)) → ServerExecution →
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
    (observer : CorrelatedObserver setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : ServerExecution) (state : BareState count) : OracleComp (LocalPostSpec baseSpec) Bool :=
  Prod.fst <$> ((simulateQ (localSourceImpl source attachedVerify primitives count)
    (observer.main output execution)).run state)

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
    (observer : CorrelatedObserver setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : ServerExecution) (state : BareState count) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  simulateQ (sourcePost source challenge)
    (localObserve source attachedVerify primitives count setup observer output execution state)

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
    (observer : CorrelatedObserver setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
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
        let outcome := match rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
          | some failure => (.error failure, server)
          | none => finishFromRoot source.crypto server application identity keys.oneTime ephemeral.toList ciphertext
              (productionHiddenRoot source (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)
        observe source none attachedVerify primitives count setup observer output
          ⟨some ephemeral, some ciphertext, outcome⟩ state

/-- Source optional verification controls the real continuation, including attacker-owned candidates and all rejection branches. -/
noncomputable def allCandidateCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : CorrelatedObserver setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
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
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
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
          let root := productionHiddenRoot parameters.source
            (serverCoordinates parameters.source.crypto parameters.server.ikSk ephemeral.toList identity
              generated.before.publicKey generated.after.publicKey) secret
          observe parameters.source (some ciphertext) attachedVerify primitives 1 setup observer (some output)
              ⟨some ephemeral, some ciphertext,
                finishFromRoot parameters.source.crypto parameters.server parameters.application identity
                  generated.after.publicKey ephemeral.toList ciphertext root⟩ prepared.2

/-- Optional source encapsulation retains ephemeral generation and native failure before every later DH/root operation. -/
noncomputable def nativeTargetContinuation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  let ephemeral ← ccaAmbient parameters.ephemeralGen
  let encapsulated ← ccaAmbient (parameters.native.encaps prepared.1.context.generated.target)
  targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral encapsulated

/-- Ordinary total encapsulation is a separate target-only presentation, justified later by actual generated-key support. -/
noncomputable def totalTargetContinuation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  let ephemeral ← ccaAmbient parameters.ephemeralGen
  let encapsulated ← ccaAmbient (kem.encaps prepared.1.context.generated.target)
  targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral (some encapsulated)

/-- All accepted, attacker-owned, changed and rejected candidates remain in the same source root game. -/
noncomputable def nativeNext
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
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
    (observer : CorrelatedObserver setup selector.State) : ProbComp Bool :=
  continuedSource attachedVerify primitives baseImpl kem setup selector
    (nativeNext kem parameters attachedVerify primitives setup observer) false

/-- Functional honest-key compatibility is lifted through every target rejection, actual source record construction, and complete observer continuation. -/
theorem nativeTarget_eq_total
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
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
  rw [evalSPMF_bind, compatible _ supported, ← evalSPMF_bind]
  simp only [bind_map_left]

/-- Only the internally recognized unchanged target uses the ordinary total KEM presentation. Arbitrary selected public keys still use the optional source operation. -/
noncomputable def totalNext
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
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
    (observer : CorrelatedObserver setup selector.State) :
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


/-- The actual response is built inside the private continuation from its supplied root. -/
noncomputable def finishTarget
    (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (root : RootOutput) :
    OracleComp (LocalPostSpec baseSpec) Bool :=
  localObserve parameters.source attachedVerify primitives 1 setup observer (some prepared.1)
    ⟨some ephemeral, some ciphertext,
      finishFromRoot parameters.source.crypto parameters.server parameters.application
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
        ephemeral.toList ciphertext root⟩ prepared.2

/-- The source execution and private post interface retain the same original observer program and complete source state. -/
theorem finishTarget_actual
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (root : RootOutput) :
    simulateQ (kemAmbientImpl baseImpl) (simulateQ (actualImpl parameters.source kem secret ciphertext)
      (finishTarget parameters attachedVerify primitives setup observer prepared ephemeral ciphertext root)) =
      evalKem baseImpl kem secret
        (observe parameters.source (some ciphertext) attachedVerify primitives 1 setup observer (some prepared.1)
          ⟨some ephemeral, some ciphertext,
            finishFromRoot parameters.source.crypto parameters.server parameters.application
              prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
              ephemeral.toList ciphertext root⟩ prepared.2) := by
  exact (sourcePost_complete parameters.source baseImpl kem secret ciphertext _).symm
/-- Filter only the charged fresh changed-acceptance branch. Every other completed branch runs through unrestricted prechallenge oracles in source order. -/
noncomputable def dispatch
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
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
    (observer : CorrelatedObserver setup selector.State) : Protocol baseSpec where
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
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : CorrelatedObserver setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  if changedBit (some prepared.1, prepared.2) then pure false
  else totalNext kem parameters attachedVerify primitives setup observer prepared


/-- Native completion preserves every filtered source branch and private root continuation. -/
theorem dispatch_complete_eq_source
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : CorrelatedObserver setup selector.State) (prepared : Prepared setup selector.State)
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
    (observer : CorrelatedObserver setup selector.State) :
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
    (observer : CorrelatedObserver setup selector.State) :
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
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) (observer : CorrelatedObserver setup selector.State) :
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
    (observer : CorrelatedObserver setup selector.State) :
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

end BeaconcryptCore.Computational.PqxdhCorrelatedRootSource

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.sourcePost_interpreter' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.sourcePost_interpreter

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.sourcePost_complete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.sourcePost_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.nativeTarget_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.nativeTarget_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.actualGame_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.actualGame_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.finishTarget_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.finishTarget_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.dispatch_complete_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.dispatch_complete_eq_source

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.filteredSource_eq_sourceMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.filteredSource_eq_sourceMain

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.continuedSource_filtered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.continuedSource_filtered

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.authentication_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.authentication_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.authenticated_correlated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedRootSource.authenticated_correlated_bound
