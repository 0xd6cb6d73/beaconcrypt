import BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix
import BeaconcryptCore.Computational.PqxdhOptionalKemSource

/-!
This concrete typed private-source prefix includes all-candidate optional native encapsulation and the exact 192-byte root input. Honest-key support justifies applying the explicit functional native/total compatibility, which does not follow from IND-CCA. Completed/rejected branches keep their effects, with separate ghost challenger draws. Pending records are built only from the supplied root; the target KEM secret never enters the reduction continuation. The capstone has four coefficient-one terms: joint-use weak-EUF, ordinary IND-CCA, exact joint Extract and HMAC. The actual source experiment explicitly blocks the target ciphertext in its eligible successful post interface. Unrestricted native post-root traffic, pinned-Server Phase2 authentication and global multi-session/reveal composition remain separate obligations.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateRootSource
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
open PqxdhJointKdfGame
open PqxdhSecretInputKdf PqxdhSecretInputInitializer PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- All generated source fields except the target KEM secret remain in the continuation context. -/
def eraseGenerated {setup : StatefulPhase1Setup baseSpec} (generated : Generated setup KemSK) : Generated setup Unit :=
  ⟨generated.before, generated.target, (), generated.after⟩

def eraseRetained {setup : StatefulPhase1Setup baseSpec} {Selection : Type}
    (retained : Retained setup KemSK Selection) : Retained setup Unit Selection :=
  ⟨retained.index, retained.publicIdentity, eraseGenerated retained.generated, retained.bundle, retained.selection⟩

def eraseOutput {setup : StatefulPhase1Setup baseSpec} {Selection : Type}
    (output : Outcome (Retained setup KemSK Selection)) : Outcome (Retained setup Unit Selection) :=
  ⟨eraseRetained output.context, output.candidate, output.accepted⟩

/-- Source identity operations and public HKDF requests remain available beside the exact CCA surface. -/
abbrev PostSourceSpec (baseSpec : OracleSpec ι) := SourceSpec + InitializerPostSpec baseSpec

/-- This private protocol observer cannot receive the target KEM secret: it only gets its erased source context and the declared oracle interface. Root-dependent records are constructed before this continuation. -/
structure Observer (setup : StatefulPhase1Setup baseSpec) (Selection : Type) where
  main : Option (Outcome (Retained setup Unit Selection)) → ServerExecution →
    OracleComp (PostSourceSpec baseSpec) Bool

/-- Local identity-interpretation coins use the explicit ordinary uniform channel. -/
def postCoins {Result : Type} (client : ProbComp Result) : OracleComp (InitializerPostSpec baseSpec) Result :=
  simulateQ (fun coin => ((InitializerPostSpec baseSpec).query (.inl (.inl (.inl coin))) :
    OracleComp (InitializerPostSpec baseSpec) _)) client

/-- The outer CCA interpreter alone owns its target secret; source identity operations retain their actual private state and public log. -/
def postSourceImpl
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) :
    QueryImpl (PostSourceSpec baseSpec) (StateT (BareState count) (OracleComp (InitializerPostSpec baseSpec))) :=
  fun query state => match query with
  | .inl request => postCoins ((bareImpl attachedVerify primitives count request).run state)
  | .inr request => do
      let answer ← (InitializerPostSpec baseSpec).query request
      pure (answer, state)

/-- Preserve all source effects through the observer before projecting its final decision; public KDF evaluations use the actual source function. -/
def observe
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : ServerExecution) (state : BareState count) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  Prod.fst <$> simulateQ (initializerPostRealImpl source kem)
    ((simulateQ (postSourceImpl attachedVerify primitives count) (observer.main output execution)).run state)

/-- All typed accepted identities and candidate KEM keys execute optional native encapsulation in actual source order. -/
noncomputable def acceptedCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  if identity.toList ++ keys.oneTime.toList ∈ server.consumed then
    observe source kem attachedVerify primitives count setup observer output
      ⟨none, none, .error .registrationReplay, server⟩ state
  else
    let ephemeral ← OracleComp.liftComp ephemeralGen (MlKemCCAOracleSpec baseSpec)
    let encapsulated ← OracleComp.liftComp (native.encaps keys.pqKey) (MlKemCCAOracleSpec baseSpec)
    match encapsulated with
    | none =>
        observe source kem attachedVerify primitives count setup observer output
          ⟨some ephemeral, none, .error .badEncoding, server⟩ state
    | some (ciphertext, secret) =>
        let outcome := match rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
          | some failure => (.error failure, server)
          | none => finishFromRoot source.crypto server application identity keys.oneTime ephemeral.toList ciphertext
              (productionHiddenRoot source (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)
        observe source kem attachedVerify primitives count setup observer output
          ⟨some ephemeral, some ciphertext, outcome⟩ state

/-- Source optional verification controls the real continuation, including attacker-owned candidates and all rejection branches. -/
noncomputable def allCandidateCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32)) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  match output.bind (·.accepted) with
  | none => observe source kem attachedVerify primitives count setup observer output
      ⟨none, none, .error .badEncoding, server⟩ state
  | some (identity, keys) => acceptedCommon source kem native attachedVerify primitives count setup observer output
      state server application ephemeralGen identity keys

/-- The one-key CCA reduction generates its own identity/prekey/one-time material, then preserves the entire source selector state. The target KEM secret is absent. -/
def borrowedPrefix
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (target : TargetKemPublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Outcome (Retained setup Unit selector.State) × BareState 1) := do
  let seed ← ccaCoins sampleSeed
  let before ← ccaAmbient (setup.prekey (primitives.publicKeys seed).ed25519)
  let after ← ccaAmbient (setup.oneTime (primitives.publicKeys seed).ed25519 before target)
  let generated : Generated setup Unit := ⟨before, target, (), after⟩
  let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
  let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
  let initial := singletonState primitives 1 seed
  let selected ← (simulateQ (borrowedSelector attachedVerify primitives 1)
    (selector.main (transcript bundle material.context))).run
    (signedGlobalState primitives seed 1 0 material.keyTuple initial.1,
     signedState primitives seed 0 material.keyTuple initial.2)
  pure (⟨⟨0, primitives.publicKeys seed, generated, bundle, selected.1.2⟩,
    ⟨0, selected.1.1⟩, PqxdhJointPhase1Reports.sourceAccept attachedVerify selected.1.1⟩, selected.2)

/-- Evaluating the ordinary borrowed prefix retains all generated source values and the full adaptive source-state result. -/
theorem borrowedPrefix_evaluated
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (target : TargetKemPublicKey) :
    evalKem baseImpl kem secret (borrowedPrefix attachedVerify primitives setup selector target) = (do
      let seed ← sampleSeed
      let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey (primitives.publicKeys seed).ed25519)
      let after ← simulateQ (kemAmbientImpl baseImpl) (setup.oneTime (primitives.publicKeys seed).ed25519 before target)
      let generated : Generated setup Unit := ⟨before, target, (), after⟩
      let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
      let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
      let initial := singletonState primitives 1 seed
      let selected ← (simulateQ (privateImpl attachedVerify primitives 1)
        (simulateQ (localSelector baseImpl kem secret) (selector.main (transcript bundle material.context)))).run
        (signedGlobalState primitives seed 1 0 material.keyTuple initial.1,
         signedState primitives seed 0 material.keyTuple initial.2)
      pure (⟨⟨0, primitives.publicKeys seed, generated, bundle, selected.1.2⟩,
        ⟨0, selected.1.1⟩, PqxdhJointPhase1Reports.sourceAccept attachedVerify selected.1.1⟩, selected.2)) := by
  simp only [borrowedPrefix, evalKem_bind, evalKem_coins, evalKem_ambient,
    ← localSelector_complete]
  rfl

/-- The actual source retains its generated KEM secret solely in the ordinary interpreter; the complete next protocol interface receives only the secret-erased context and source state. -/
def continuedSource {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (next : Outcome (Retained setup Unit selector.State) × BareState 1 →
      OracleComp (MlKemCCAOracleSpec baseSpec) Result) (fallback : Result) : ProbComp Result := do
  let stopped ← privateRun attachedVerify primitives 1 (program baseImpl kem setup selector)
  match stopped.1 with
  | none => pure fallback
  | some output =>
      evalKem baseImpl kem output.context.generated.secret (next (eraseOutput output, stopped.2))

/-- Exact evaluated one-key embedding through the entire next protocol continuation. Source order is preserved on the left; the right moves only the independent KEM key pair and never supplies its secret to the reduction. -/
theorem continuedSource_keyfirst {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (next : Outcome (Retained setup Unit selector.State) × BareState 1 →
      OracleComp (MlKemCCAOracleSpec baseSpec) Result) (fallback : Result) :
    EvalDistEq (continuedSource attachedVerify primitives baseImpl kem setup selector next fallback)
      (do let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
          evalKem baseImpl kem pair.2
            (borrowedPrefix attachedVerify primitives setup selector pair.1 >>= next)) := by
  have commute := generators_complete_continuation baseImpl primitives kem setup
    (fun seed generated => do
      let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
      let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
      let initial := singletonState primitives 1 seed
      let selected ← (simulateQ (privateImpl attachedVerify primitives 1)
        (simulateQ (localSelector baseImpl kem generated.secret)
          (selector.main (transcript bundle material.context)))).run
        (signedGlobalState primitives seed 1 0 material.keyTuple initial.1,
         signedState primitives seed 0 material.keyTuple initial.2)
      evalKem baseImpl kem generated.secret (next
        (⟨⟨0, primitives.publicKeys seed, eraseGenerated generated, bundle, selected.1.2⟩,
          ⟨0, selected.1.1⟩, PqxdhJointPhase1Reports.sourceAccept attachedVerify selected.1.1⟩, selected.2)))
  simpa only [continuedSource, program_complete, bind_assoc, pure_bind, evalKem_bind,
    borrowedPrefix_evaluated, identityPreSample, eraseOutput, eraseRetained, eraseGenerated,
    publicMaterial, setupMaterial] using commute

/-- A public wrapper rejects the challenge ciphertext before forwarding any permitted postchallenge query. It has no secret-key argument. -/
noncomputable def blockChallenge (challenge : MlKem768Ciphertext) :
    QueryImpl (MlKemCCAOracleSpec baseSpec) (OracleComp (MlKemCCAOracleSpec baseSpec))
  | .inl request => (MlKemCCAOracleSpec baseSpec).query (.inl request)
  | .inr ciphertext => if ciphertext = challenge then pure none
      else (MlKemCCAOracleSpec baseSpec).query (.inr ciphertext)

/-- The public blocking wrapper followed by unrestricted interpretation is exactly the ordinary postchallenge interpreter. -/
theorem blockChallenge_interpreter
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) :
    localKemPreChallengeImpl kem secret ∘ₛ blockChallenge challenge =
      kem.IND_CCA_postChallengeImpl secret challenge := by
  funext query
  cases query with
  | inl request =>
      simp only [QueryImpl.compose, blockChallenge, simulateQ_spec_query]
      rfl
  | inr ciphertext =>
      simp only [QueryImpl.compose, blockChallenge]
      split
      · rename_i same
        subst ciphertext
        rw [simulateQ_pure, indCCA_postChallengeImpl_challenge]
      · rename_i different
        rw [simulateQ_spec_query, indCCA_postChallengeImpl_nonchallenge kem secret challenge ciphertext different]
        rfl

/-- Actual server inputs and opaque source generators are fixed independently of the target KEM secret. -/
structure Parameters (baseSpec : OracleSpec ι) where
  source : FixedHkdfSha512NoSaltSource
  native : PqxdhOptionalKemSource.SourceKemInterface baseSpec
  server : Pqxdh.ServerState
  application : Option Pqxdh.Bytes
  ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32)

abbrev Prepared (setup : StatefulPhase1Setup baseSpec) (Selection : Type) :=
  Outcome (Retained setup Unit Selection) × BareState 1

/-- Only fresh, actually accepted, unchanged generated fields target the root replacement. Every other candidate keeps its real continuation. -/
def targetEligible {setup : StatefulPhase1Setup baseSpec} {Selection : Type}
    (parameters : Parameters baseSpec) (prepared : Prepared setup Selection) : Bool :=
  let output := prepared.1
  decide (output.accepted = some (output.context.publicIdentity.ed25519,
      (publicMaterial setup output.context.publicIdentity.ed25519 output.context.generated).keyTuple) ∧
    (0 : Fin 1) ∉ prepared.2.1.reveals ∧
    output.context.publicIdentity.ed25519.toList ++ output.context.generated.after.publicKey.toList ∉ parameters.server.consumed)

/-- The source computes rejection or root-dependent response after encapsulation. Only a successfully initialized target exposes the challenge-blocked post interface. -/
noncomputable def targetAfterEncapsulation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  let output := prepared.1
  let identity := output.context.publicIdentity.ed25519
  let generated := output.context.generated
  match encapsulated with
  | none =>
      observe parameters.source kem attachedVerify primitives 1 setup observer (some output)
        ⟨some ephemeral, none, .error .badEncoding, parameters.server⟩ prepared.2
  | some (ciphertext, secret) =>
      match rootFailure parameters.source.crypto parameters.server.ikSk ephemeral.toList identity
        generated.before.publicKey generated.after.publicKey with
      | some failure =>
          observe parameters.source kem attachedVerify primitives 1 setup observer (some output)
            ⟨some ephemeral, some ciphertext, .error failure, parameters.server⟩ prepared.2
      | none =>
          let root := productionHiddenRoot parameters.source
            (serverCoordinates parameters.source.crypto parameters.server.ikSk ephemeral.toList identity
              generated.before.publicKey generated.after.publicKey) secret
          simulateQ (blockChallenge ciphertext)
            (observe parameters.source kem attachedVerify primitives 1 setup observer (some output)
              ⟨some ephemeral, some ciphertext,
                finishFromRoot parameters.source.crypto parameters.server parameters.application identity
                  generated.after.publicKey ephemeral.toList ciphertext root⟩ prepared.2)

/-- Optional source encapsulation retains ephemeral generation and native failure before every later DH/root operation. -/
noncomputable def nativeTargetContinuation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  let ephemeral ← ccaAmbient parameters.ephemeralGen
  let encapsulated ← ccaAmbient (parameters.native.encaps prepared.1.context.generated.target)
  targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral encapsulated

/-- Ordinary total encapsulation is a separate target-only presentation, justified later by actual generated-key support. -/
noncomputable def totalTargetContinuation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool := do
  let ephemeral ← ccaAmbient parameters.ephemeralGen
  let encapsulated ← ccaAmbient (kem.encaps prepared.1.context.generated.target)
  targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral (some encapsulated)

/-- All accepted, attacker-owned, changed and rejected candidates remain in the same source root game. -/
noncomputable def nativeNext
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
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
    (observer : Observer setup selector.State) : ProbComp Bool :=
  continuedSource attachedVerify primitives baseImpl kem setup selector
    (nativeNext kem parameters attachedVerify primitives setup observer) false

/-- Functional honest-key compatibility is lifted through every target rejection, actual source record construction, and complete observer continuation. -/
theorem nativeTarget_eq_total
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
    (prepared : Prepared setup Selection) (secret : KemSK)
    (supported : (prepared.1.context.generated.target, secret) ∈
      support (simulateQ (kemAmbientImpl baseImpl) kem.keygen)) :
    𝒟[evalKem baseImpl kem secret
      (nativeTargetContinuation kem parameters attachedVerify primitives setup observer prepared)] =
      𝒟[evalKem baseImpl kem secret
        (totalTargetContinuation kem parameters attachedVerify primitives setup observer prepared)] := by
  refine EvalDistEq.evalDist_eq ?_
  simp only [nativeTargetContinuation, totalTargetContinuation, evalKem_bind, evalKem_ambient]
  refine EvalDistEq.bind_right _ fun ephemeral => ?_
  refine ((compatible _ supported).bind_left _).trans ?_
  rw [bind_map_left]

/-- Only the internally recognized unchanged target uses the ordinary total KEM presentation. Arbitrary selected public keys still use the optional source operation. -/
noncomputable def totalNext
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
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
    (observer : Observer setup selector.State) :
    𝒟[actualGame baseImpl kem parameters attachedVerify primitives setup selector observer] =
      𝒟[continuedSource attachedVerify primitives baseImpl kem setup selector
        (totalNext kem parameters attachedVerify primitives setup observer) false] := by
  refine EvalDistEq.evalDist_eq ?_
  simp only [actualGame, continuedSource, program_complete, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun seed => ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun generated generatedSupport => ?_
  refine EvalDistEq.bind_right _ fun selected => ?_
  simp only [nativeNext, totalNext]
  split
  · exact EvalDistEq.of_evalDist_eq
      (nativeTarget_eq_total baseImpl kem parameters compatible attachedVerify primitives setup observer _ _
        (generate_key_support baseImpl kem setup _ generated generatedSupport))
  · rfl

/-- The initializer's observer builds source response records and publication only from the supplied root; the pending context contains no record derived from an old root. -/
noncomputable def finishTarget
    (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (root : RootOutput) :
    OracleComp (InitializerPostSpec baseSpec) Bool :=
  Prod.fst <$> (simulateQ (postSourceImpl attachedVerify primitives 1)
    (observer.main (some prepared.1)
      ⟨some ephemeral, some ciphertext,
        finishFromRoot parameters.source.crypto parameters.server parameters.application
          prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
          ephemeral.toList ciphertext root⟩)).run prepared.2

/-- The source observer and initializer post-observer share exactly the same root-dependent source execution and real public-KDF interpretation. -/
theorem finishTarget_real
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (root : RootOutput) :
    simulateQ (initializerPostRealImpl parameters.source kem)
      (finishTarget parameters attachedVerify primitives setup observer prepared ephemeral ciphertext root) =
      observe parameters.source kem attachedVerify primitives 1 setup observer (some prepared.1)
        ⟨some ephemeral, some ciphertext,
          finishFromRoot parameters.source.crypto parameters.server parameters.application
            prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
            ephemeral.toList ciphertext root⟩ prepared.2 := by
  simp only [finishTarget, observe, simulateQ_map]
  rfl

/-- Completed non-target/abort work is finished before the challenger creates its blocked ciphertext; pending state has no target KEM secret or old-root records. -/
inductive Mode (setup : StatefulPhase1Setup baseSpec) (Selection : Type) where
  | completed (decision : Bool)
  | pending (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)

/-- Filter only the charged fresh changed-acceptance branch. Every other completed branch runs through unrestricted prechallenge oracles in source order. -/
noncomputable def dispatch
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
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
        let decision ← observe parameters.source kem attachedVerify primitives 1 setup observer (some prepared.1)
          ⟨some ephemeral, some encapsulated.1, .error failure, parameters.server⟩ prepared.2
        pure (.completed decision)
  else
    let decision ← allCandidateCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer
      (some prepared.1) prepared.2 parameters.server parameters.application parameters.ephemeralGen
    pure (.completed decision)

/-- The concrete one-key initializer uses the actual private source prefix and optional all-candidate server schedule. All public KDF evaluations remain real. -/
noncomputable def rootInitializer
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Observer setup selector.State) : InitializerAdversary kem where
  State := Mode setup selector.State
  Context := Mode setup selector.State
  preChallenge target := borrowedPrefix attachedVerify primitives setup selector target >>=
    dispatch kem parameters attachedVerify primitives setup observer
  knownCoordinates mode _ _ := match mode with
    | .completed _ => PqxdhAuthenticatedRoot.unusedCoordinates
    | .pending prepared ephemeral =>
        serverCoordinates parameters.source.crypto parameters.server.ikSk ephemeral.toList
          prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
          prepared.1.context.generated.after.publicKey
  publicContext mode _ _ := mode
  main publicTranscript _ root := match publicTranscript.context with
    | .completed decision => pure decision
    | .pending prepared ephemeral =>
        finishTarget parameters attachedVerify primitives setup observer prepared ephemeral publicTranscript.ciphertext root

/-- The pending root input is exactly the source's four DH coordinates and selected KEM contribution, with the FF prefix and total width192. -/
theorem rootInitializer_input
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Observer setup selector.State) (prepared : Prepared setup selector.State)
    (ephemeral : List.Vector UInt8 32) (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (ciphertext : MlKem768Ciphertext)
    (converted : Pqxdh.Bytes)
    (conversion : parameters.source.crypto.xpkConv prepared.1.context.publicIdentity.ed25519.toList = some converted)
    (secret : MlKemSharedSecret) :
    hiddenRootIKM ((rootInitializer kem parameters attachedVerify primitives setup selector observer).knownCoordinates
      (.pending prepared ephemeral) publicKey ciphertext) secret =
      Pqxdh.ikmOf (Pqxdh.serverDHs parameters.source.crypto parameters.server.ikSk ephemeral.toList converted
        prepared.1.context.generated.before.publicKey.toList prepared.1.context.generated.after.publicKey.toList) secret.toList ∧
    (hiddenRootIKM ((rootInitializer kem parameters attachedVerify primitives setup selector observer).knownCoordinates
      (.pending prepared ephemeral) publicKey ciphertext) secret).length = 192 :=
  serverCoordinates_rootInput parameters.source.crypto parameters.server.ikSk ephemeral.toList
    prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
    prepared.1.context.generated.after.publicKey converted conversion secret

/-- Blocking is implemented publicly while the sole secret key stays in the actual CCA interpreter. -/
theorem evalKem_blockChallenge {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (client : OracleComp (MlKemCCAOracleSpec baseSpec) Result) :
    evalKem baseImpl kem secret (simulateQ (blockChallenge challenge) client) =
      simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (kem.IND_CCA_postChallengeImpl secret challenge) client) := by
  simp only [evalKem, ← QueryImpl.simulateQ_compose, blockChallenge_interpreter]
  rfl

/-- The only filtered branch is the changed fresh accepted tuple charged to the joint signature reduction. -/
noncomputable def filteredNext
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type} (observer : Observer setup Selection)
    (prepared : Prepared setup Selection) : OracleComp (MlKemCCAOracleSpec baseSpec) Bool :=
  if changedBit (some prepared.1, prepared.2) then pure false
  else totalNext kem parameters attachedVerify primitives setup observer prepared

/-- Erasing the private KEM secret preserves the exact observable fresh changed-acceptance predicate. -/
theorem erase_changedBit {setup : StatefulPhase1Setup baseSpec} {Selection : Type}
    (output : Outcome (Retained setup KemSK Selection)) (state : BareState 1) :
    changedBit (some (eraseOutput output), state) = changedBit (some output, state) := by
  rfl

/-- Interpreting a local return leaves its exact value unchanged. -/
theorem evalKem_pure {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (value : Result) :
    evalKem baseImpl kem secret (pure value) = pure value := by
  simp only [evalKem, simulateQ_pure]

set_option backward.isDefEq.respectTransparency false in
/-- Standard challenger completion executes exactly the filtered source continuation, including completed-branch ghost draws and pending challenge blocking. -/
theorem dispatch_finish_eq_source
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Observer setup selector.State) (prepared : Prepared setup selector.State)
    (target : TargetKemPublicKey) (secret : KemSK)
    (target_eq : prepared.1.context.generated.target = target) :
    𝒟[do
      let mode ← evalKem baseImpl kem secret
        (dispatch kem parameters attachedVerify primitives setup observer prepared)
      simulateQ (kemAmbientImpl baseImpl)
        (oneKeyFinish kem (runtimeOfImpl (kemAmbientImpl baseImpl))
          (toKemOneKeyAdversary parameters.source kem
            (rootInitializer kem parameters attachedVerify primitives setup selector observer))
          (target, secret, mode) true)] =
      𝒟[evalKem baseImpl kem secret
        (filteredNext kem parameters attachedVerify primitives setup observer prepared)] := by
  refine EvalDistEq.evalDist_eq ?_
  by_cases bad : changedBit (some prepared.1, prepared.2) = true
  · simp [dispatch, filteredNext, bad, evalKem, oneKeyFinish, toKemOneKeyAdversary,
      rootInitializer, runtimeOfImpl_liftProbComp, simulateQ_kemAmbient_liftM_ProbComp, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
    exact (EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.map_const _ _).trans
      (OracleComp.EvalDistEq.bind_const _ _)
  · by_cases eligible : targetEligible parameters prepared = true
    · simp only [dispatch, filteredNext, bad, Bool.false_eq_true, ite_false, eligible, ite_true,
        totalNext, totalTargetContinuation, evalKem_bind, evalKem_ambient, bind_assoc]
      refine EvalDistEq.bind_right _ fun ephemeral => ?_
      cases failure : rootFailure parameters.source.crypto parameters.server.ikSk ephemeral.toList
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
        prepared.1.context.generated.after.publicKey with
      | none =>
          simp only [oneKeyFinish, toKemOneKeyAdversary, rootInitializer,
            runtimeOfImpl_liftProbComp, simulateQ_bind, simulateQ_kemAmbient_liftProbComp,
            evalKem_pure, pure_bind, ite_true, targetAfterEncapsulation, failure,
            evalKem_blockChallenge, finishTarget_real, target_eq]
          refine EvalDistEq.bind_right _ fun encapsulated => ?_
          exact OracleComp.EvalDistEq.bind_const _ _
      | some reason =>
          simp only [evalKem_bind, evalKem_ambient, evalKem_pure, bind_assoc, pure_bind,
            targetAfterEncapsulation, failure]
          refine EvalDistEq.bind_right _ fun encapsulated => ?_
          simp [oneKeyFinish, toKemOneKeyAdversary, rootInitializer,
            runtimeOfImpl_liftProbComp, simulateQ_kemAmbient_liftM_ProbComp, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
          refine (EvalDistEq.bind_right _ fun value =>
            (EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.map_const _ value).trans
              (OracleComp.EvalDistEq.bind_const _ _)).trans ?_
          rw [bind_pure]
    · simp [dispatch, filteredNext, bad, eligible, totalNext, evalKem, oneKeyFinish, toKemOneKeyAdversary,
        rootInitializer, runtimeOfImpl_liftProbComp, simulateQ_kemAmbient_liftM_ProbComp, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
      refine (EvalDistEq.bind_right _ fun value =>
        (EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.map_const _ value).trans
          (OracleComp.EvalDistEq.bind_const _ _)).trans ?_
      rw [bind_pure]

/-- The borrowed prefix retains the challenger public key in the exact generated position through all selector replies. -/
theorem borrowedPrefix_target
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (target : TargetKemPublicKey) (prepared : Prepared setup selector.State)
    (supported : prepared ∈ support (evalKem baseImpl kem secret
      (borrowedPrefix attachedVerify primitives setup selector target))) :
    prepared.1.context.generated.target = target := by
  rw [borrowedPrefix_evaluated] at supported
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, before, _, after, _, selected, _, same⟩ := supported
  subst prepared
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Complete filtered source execution is exactly the ordinary initializer experiment, with the target secret confined to its interpreter. -/
theorem filteredSource_eq_initializerReal
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Observer setup selector.State) :
    𝒟[continuedSource attachedVerify primitives baseImpl kem setup selector
      (filteredNext kem parameters attachedVerify primitives setup observer) false] =
      𝒟[initializerRealGame parameters.source baseImpl kem
        (rootInitializer kem parameters attachedVerify primitives setup selector observer)] := by
  refine EvalDistEq.evalDist_eq ?_
  refine (continuedSource_keyfirst attachedVerify primitives baseImpl kem setup selector _ false).trans ?_
  simp only [initializerRealGame, oneKeyBranchMain, oneKeyPrefix, toKemOneKeyAdversary,
    rootInitializer, simulateQ_bind, bind_assoc, pure_bind, evalKem_bind]
  refine EvalDistEq.bind_right _ fun pair => ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun prepared supported => ?_
  refine EvalDistEq.of_evalDist_eq ?_
  exact (dispatch_finish_eq_source baseImpl kem parameters attachedVerify primitives setup selector
    observer prepared pair.1 pair.2
    (borrowedPrefix_target attachedVerify primitives baseImpl kem pair.2 setup selector pair.1 prepared supported)).symm

/-- The filtered source presentation changes only its named bad branch, preserving the same complete private prefix. -/
theorem continuedSource_filtered
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Observer setup selector.State) :
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

/-- The complete actual optional source-root experiment reaches the ordinary initializer with one concrete joint-use weak-EUF reduction. -/
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
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) (observer : Observer setup selector.State) :
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).boolDistAdvantage
      (initializerRealGame parameters.source baseImpl kem
        (rootInitializer kem parameters attachedVerify primitives setup selector observer)) ≤
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
  simpa only [ProbComp.boolDistAdvantage, VCVioLegacy.evalDist_singleton_eq_probOutput, prEvent_eq_evalDist_singleton,
    actualGame_eq_total baseImpl kem parameters compatible attachedVerify primitives setup selector observer,
    ← filteredSource_eq_initializerReal baseImpl kem parameters attachedVerify primitives setup selector observer] using output

/-- The actual private source-root game has four coefficient-one reductions at its exact joint input distribution and challenge-blocked protocol interface. -/
theorem authenticated_root_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (hmac : HmacSha512) (correct : SourceRootCorrect parameters.source hmac)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) IsSigning) 0)
    (selectorNoCreate : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (observer : Observer setup selector.State) :
    let adversary := rootInitializer kem parameters attachedVerify primitives setup selector observer
    let sample := secretInputSample baseImpl kem adversary
    let postObserver := rootObserver parameters.source baseImpl kem adversary
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).boolDistAdvantage
      (independentInitializerGame parameters.source baseImpl kem adversary) ≤
      (advantage primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (toKemOneKeyAdversary parameters.source kem adversary).toINDCCA +
      (extractRealGame hmac sample (extractReduction hmac postObserver)).boolDistAdvantage
        (extractUniformGame sample (extractReduction hmac postObserver)) +
      (hmacPrfRealGame hmac (expandReduction sample postObserver)).boolDistAdvantage
        (hmacPrfRandomGame (expandReduction sample postObserver)) := by
  dsimp only
  have authenticated := authentication_hop baseImpl kem parameters compatible attachedVerify primitives adapter
    setup selector selectorNoSign selectorNoCreate fallback ordinaryFallback observer
  have initialized := initializerAdvantage_le_kem_add_extract_add_hmac parameters.source hmac correct
    baseImpl kem (rootInitializer kem parameters attachedVerify primitives setup selector observer)
  have combined := (ProbComp.boolDistAdvantage_triangle
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer)
    (initializerRealGame parameters.source baseImpl kem
      (rootInitializer kem parameters attachedVerify primitives setup selector observer))
    (independentInitializerGame parameters.source baseImpl kem
      (rootInitializer kem parameters attachedVerify primitives setup selector observer))).trans
    (add_le_add authenticated initialized)
  simpa only [add_assoc] using combined

end BeaconcryptCore.Computational.PqxdhPrivateRootSource

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.borrowedPrefix_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.borrowedPrefix_evaluated

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.continuedSource_keyfirst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.continuedSource_keyfirst

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.blockChallenge_interpreter' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.blockChallenge_interpreter

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.nativeTarget_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.nativeTarget_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.actualGame_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.actualGame_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.finishTarget_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.finishTarget_real

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.rootInitializer_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.rootInitializer_input

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.evalKem_blockChallenge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.evalKem_blockChallenge

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.erase_changedBit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.erase_changedBit

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.evalKem_pure' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.evalKem_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.dispatch_finish_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.dispatch_finish_eq_source

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.borrowedPrefix_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.borrowedPrefix_target

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.filteredSource_eq_initializerReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.filteredSource_eq_initializerReal

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.continuedSource_filtered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.continuedSource_filtered

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.authentication_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.authentication_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootSource.authenticated_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootSource.authenticated_root_bound
