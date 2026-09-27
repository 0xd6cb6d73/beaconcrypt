import BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot
import BeaconcryptCore.Computational.PqxdhRegistrationInputs
import BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds
import BeaconcryptCore.Computational.FinitePartitionQueryBounds

/-!
The private accepted-root callback executes the already checked actual registration builder before any ideal finish/publication. Actual extracted acceptance derives the original pending-field and RID relations; source consumption retains the prior native map/control/binding/metadata/primitive context. The full original pending stays an interpreter-side source witness through its by-value consuming prepare call. Its root_input and RID are absent from the builder result. Executable construction reads only the four proven-used fields and the supplied root; arbitrary post-derivation root_input bytes do not affect the complete returned/primitive/poststate computation. This is functional non-use, not physical erasure or equality of shortened pending states.

The explicit source game with this private continuation inherits the same joint-use weak-EUF plus coefficient-one ordinary CCA bound and same-secret root correlation. The nine native callback classes each have cap one; exact finite weighted transfer charges each stated callback cost and then the arbitrary continued source work. The initial fixed HKDF64 remains separate local work. Full native/source field and state representations are explicit operational relations: an arbitrary private Plan does not itself prove that relation for a global native scheduler. Consumed-list versus native HashSet, allocation, writer, zeroization, runtime/error and crash contracts, multiple-family/evolving/reveal composition and pinned-Server/global authentication remain separate. No shared-secret bytes are added to a reduction or adversary interface.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Refinement.ProtocolComposition
open BeaconcryptCore.Computational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAcceptedRegistration
open PqxdhServerRegistrationPublication
open PqxdhPrivateAcceptedRoot

/-- Original ciphertext bytes, in the fixed-width extracted representation. -/
def ciphertextArray (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) : Std.Array Std.U8 1088#usize :=
  ⟨ciphertext.toList.map concreteByte, by simp⟩

theorem ciphertextArray_bytes (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) :
    absBytes (ciphertextArray ciphertext) = ciphertext.toList := by
  simp [ciphertextArray, absBytes, List.map_map, Function.comp_def]

/-- The original ephemeral secret stays private; only its actual public mapping is prepared for Phase2. -/
def usedReady (c : Pqxdh.Crypto) (binding : pqxdh.ServerBinding) (ready : Ready) :
    PqxdhRegistrationInputs.UsedInput :=
  ⟨binding, PqxdhRootTableInitialization.rootArray ready.identity,
    PqxdhRootTableInitialization.rootArray ⟨c.xpub ready.ephemeral.toList, c.xpub_length _⟩,
    ciphertextArray ready.ciphertext⟩

/-- Execute from the exact already-consumed source state, without any earlier ideal publication. -/
noncomputable def buildReady {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) :=
  PqxdhRegistrationInputs.build source (usedReady source.crypto binding ready)
    ready.root ready.application metadata state

/-- Actual successful acceptance supplies the builder fields; the full pending value is preserved as witness. -/
theorem accepted_fields (c : Pqxdh.Crypto) (ready : Ready)
    (state acceptedState : pqxdh.ServerState) (registration : pqxdh.VerifiedInitKex)
    (status : pqxdh.RegistrationStatus) (binding : pqxdh.ServerBinding)
    (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (pending : pqxdh.PendingServerRegistration)
    (accepted : pqxdh.server_accept state registration status binding coins secrets =
      ok (.Ok (acceptedState, pending)))
    (identity : absBytes registration.beacon_identity_public_key = ready.identity.toList)
    (ephemeral : absBytes coins.ephemeral_public_key = c.xpub ready.ephemeral.toList)
    (ciphertext : absBytes coins.kem_ciphertext = ready.ciphertext.toList) :
    PqxdhRegistrationInputs.used pending = usedReady c binding ready := by
  rw [(PqxdhRegistrationInputs.accepted_used state acceptedState registration status binding coins secrets
    pending accepted).2]
  unfold usedReady
  congr 1
  · apply BeaconcryptCore.Refinement.PqxdhSurface.bytes_eq_of_abs_eq
    simpa only [PqxdhRootTableInitialization.rootArray_bytes] using identity
  · apply BeaconcryptCore.Refinement.PqxdhSurface.bytes_eq_of_abs_eq
    exact ephemeral.trans (PqxdhRootTableInitialization.rootArray_bytes
      ⟨c.xpub ready.ephemeral.toList, c.xpub_length _⟩).symm
  · apply BeaconcryptCore.Refinement.PqxdhSurface.bytes_eq_of_abs_eq
    simpa only [ciphertextArray_bytes] using ciphertext


/-- Complete source execution agrees for every original pending witness with the established field projection. -/
theorem buildReady_source {Metadata PeerMetadata Consumed PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (pending : pqxdh.PendingServerRegistration)
    (fields : PqxdhRegistrationInputs.used pending = usedReady source.crypto binding ready)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    sourceBuild execute sealReply aux source pending ready.root ready.application metadata state primitive =
      collectState ((simulateQ (functionalImpl execute sealReply aux)
        (buildReady source binding ready metadata state)).run primitive) := by
  rw [PqxdhRegistrationInputs.source_build_exact, fields]
  rfl

/-- Native expansion and arbitrary continuation preserve the identical complete result and primitive poststate. -/
theorem buildReady_complete {Metadata PeerMetadata Consumed PrimitiveState Result ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (pending : pqxdh.PendingServerRegistration)
    (fields : PqxdhRegistrationInputs.used pending = usedReady source.crypto binding ready)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState)
    (next : (RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState) →
      OracleComp base Result) :
    ((simulateQ impl (simulateQ nativeAdapter
        (buildReady source binding ready metadata state))).run primitive >>= next) =
      ((simulateQ impl (simulateQ nativeAdapter
        (PqxdhServerRegistrationPublication.build source pending ready.root ready.application metadata state))).run primitive
        >>= next) := by
  unfold buildReady
  rw [← fields, PqxdhRegistrationInputs.build_exact]

/-- Private interpreter context at the already-consumed boundary; no root-input/shared-secret field is reconstructed. -/
structure Input (Metadata PeerMetadata Consumed PrimitiveState : Type) where
  binding : pqxdh.ServerBinding
  state : State Metadata PeerMetadata Consumed
  metadata : PeerMetadata
  primitive : PrimitiveState

/-- Only ordinary builder results and complete native poststate are passed onward after its pending input is consumed. -/
noncomputable def registrationContinuation {ι Metadata PeerMetadata Consumed PrimitiveState Selection : Type}
    {baseSpec : OracleSpec ι} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (inputs : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit Selection)) →
      Ready → Input Metadata PeerMetadata Consumed PrimitiveState)
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp (CorrelatedSpec baseSpec))))
    (completed : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit Selection)) →
      PqxdhSourceAuthenticatedRoot.ServerExecution → OracleComp (CorrelatedSpec baseSpec) Bool)
    (next : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit Selection)) →
      (RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState) →
      OracleComp (CorrelatedSpec baseSpec) Bool) : Continuation setup Selection where
  completed := completed
  accepted := fun output ready => do
    let input := inputs output ready
    let result ← (simulateQ impl (simulateQ nativeAdapter
      (buildReady source input.binding ready input.metadata input.state))).run input.primitive
    next output result


/-- Source callback caps hold for every accepted-root value, without assuming successful publication. -/
theorem buildReady_bounds {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (kind : CallKind) :
    (buildReady source binding ready metadata state).IsQueryBoundP (fun query => callKind query = kind) 1 :=
  PqxdhRegistrationInputs.build_bound source _ ready.root ready.application metadata state kind

/-- Concrete native KDF/AEAD/hash/writer and auxiliary caps retain every rejected attempt. -/
theorem buildReady_native_bounds {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    let work := simulateQ nativeAdapter (buildReady source binding ready metadata state)
    work.IsQueryBoundP (fun query => leftPredicate Sum.isLeft query = true) 1 ∧
      (∀ kind, work.IsQueryBoundP
        (fun query => leftPredicate (RawCtxSourceSeal.category kind) query = true) 1) ∧
      (∀ kind, work.IsQueryBoundP (fun query => auxPredicate kind query = true) 1) :=
  PqxdhRegistrationInputs.native_build_bounds source _ ready.root ready.application metadata state

/-- Arbitrary typed callback replies produce an ordinary optional source result, never a dropped diagnostic state. -/
theorem buildReady_normal {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    Normal (buildReady source binding ready metadata state) :=
  PqxdhRegistrationInputs.build_normal source _ ready.root ready.application metadata state

/-- Complete primitive-state normality follows from actual source totality, without a losslessness assumption. -/
theorem buildReady_run_normal {Metadata PeerMetadata Consumed PrimitiveState ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : PrimitiveState)
    (result : RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState)
    (supported : result ∈ support ((simulateQ impl (simulateQ nativeAdapter
      (buildReady source binding ready metadata state))).run primitive)) :
    ∃ value, result = (ok value, result.2) := by
  have normal := buildReady_normal source binding ready metadata state
  have member : result.1 ∈ support (buildReady source binding ready metadata state) := by
    rw [← QueryImpl.simulateQ_compose] at supported
    apply OracleComp.support_simulateQ_run'_subset (impl ∘ₛ nativeAdapter) _ primitive
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ supported
  obtain ⟨value, equal⟩ := normal _ member
  exact ⟨value, Prod.ext equal rfl⟩


/-- Interpreter-side plan retains complete source context; its callbacks are private protocol code. -/
structure Plan {ι : Type} (baseSpec : OracleSpec ι)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (Selection : Type)
    (Metadata PeerMetadata Consumed PrimitiveState : Type) where
  inputs : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit Selection)) →
    Ready → Input Metadata PeerMetadata Consumed PrimitiveState
  impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp (CorrelatedSpec baseSpec)))
  completed : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit Selection)) →
    PqxdhSourceAuthenticatedRoot.ServerExecution → OracleComp (CorrelatedSpec baseSpec) Bool
  next : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit Selection)) →
    (RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState) →
    OracleComp (CorrelatedSpec baseSpec) Bool

noncomputable def Plan.continuation {ι Metadata PeerMetadata Consumed PrimitiveState Selection : Type}
    {baseSpec : OracleSpec ι} {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (plan : Plan baseSpec setup Selection Metadata PeerMetadata Consumed PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) : Continuation setup Selection :=
  registrationContinuation source setup plan.inputs plan.impl plan.completed plan.next

/-- At the source boundary, the actual full pending/context is retained until the builder consumes it. -/
theorem Plan.accepted_source {ι Metadata PeerMetadata Consumed PrimitiveState Selection : Type}
    {baseSpec : OracleSpec ι} {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (plan : Plan baseSpec setup Selection Metadata PeerMetadata Consumed PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit Selection)))
    (ready : Ready) (pending : pqxdh.PendingServerRegistration)
    (fields : PqxdhRegistrationInputs.used pending = usedReady source.crypto (plan.inputs output ready).binding ready) :
    (plan.continuation source).accepted output ready =
      ((simulateQ plan.impl (simulateQ nativeAdapter
        (PqxdhServerRegistrationPublication.build source pending ready.root ready.application
          (plan.inputs output ready).metadata (plan.inputs output ready).state))).run
          (plan.inputs output ready).primitive >>= plan.next output) := by
  exact buildReady_complete plan.impl source (plan.inputs output ready).binding ready pending fields
    (plan.inputs output ready).metadata (plan.inputs output ready).state
    (plan.inputs output ready).primitive (plan.next output)

open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhSecretInputInitializer
open PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot PqxdhPrivateRootSource
open PqxdhChallengeSecretRouting

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Same actual private generation and accepted-root source now run the concrete registration tail before the final Boolean. -/
theorem authenticated_registration_bound {Metadata PeerMetadata Consumed PrimitiveState : Type}
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
    (plan : Plan baseSpec setup selector.State Metadata PeerMetadata Consumed PrimitiveState) :
    let observer := plan.continuation parameters.source
    let protocol := rootProtocol kem parameters attachedVerify primitives setup selector observer
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).boolDistAdvantage
      (simulateQ (kemAmbientImpl baseImpl)
        (randomMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)) ≤
      (advantage primitives (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (reduction parameters.source kem protocol).toINDCCA := by
  exact authenticated_correlated_bound baseImpl kem parameters compatible functional correct attachedVerify
    primitives adapter setup selector selectorNoSign selectorNoCreate fallback ordinaryFallback
    (plan.continuation parameters.source)


/-- Retain the complete prior native/primitive context and install only the already-executed consumption mark. -/
def Input.afterReady {Metadata PeerMetadata PrimitiveState : Type}
    (input : Input Metadata PeerMetadata (List Pqxdh.Bytes) PrimitiveState) (execution : Ready) :
    Input Metadata PeerMetadata (List Pqxdh.Bytes) PrimitiveState :=
  { input with state := { input.state with consumed := execution.consumed.consumed } }

/-- Source consumption does not change the current map, allocation control, binding, metadata or primitive state. -/
theorem Input.afterReady_fields {Metadata PeerMetadata PrimitiveState : Type}
    (input : Input Metadata PeerMetadata (List Pqxdh.Bytes) PrimitiveState) (execution : Ready) :
    (input.afterReady execution).state.server = input.state.server ∧
    (input.afterReady execution).state.control = input.state.control ∧
    (input.afterReady execution).state.identityKeyId = input.state.identityKeyId ∧
    (input.afterReady execution).binding = input.binding ∧
    (input.afterReady execution).metadata = input.metadata ∧
    (input.afterReady execution).primitive = input.primitive := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The supplied source acceptance/RID witnesses establish the same actual consumed value before building. -/
theorem Input.actual_consumption {Metadata PeerMetadata PrimitiveState : Type}
    (input : Input Metadata PeerMetadata (List Pqxdh.Bytes) PrimitiveState)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (identity : Ed25519PublicKey) (oneTime : X25519PublicKey)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (root : RootOutput)
    (registration : pqxdh.VerifiedInitKex) (status : pqxdh.RegistrationStatus)
    (binding : pqxdh.ServerBinding) (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (acceptedState : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (accepted : pqxdh.server_accept input.state.control registration status binding coins secrets =
      ok (.Ok (acceptedState, pending)))
    (hidentity : absBytes registration.beacon_identity_public_key = identity.toList)
    (honeTime : absBytes registration.beacon_one_time_public_key = oneTime.toList)
    (history : input.state.consumed = server.consumed) :
    (input.afterReady (ready server application identity oneTime ephemeral ciphertext root)).state =
      { input.state with consumed := absBytes pending.registration_id.bytes :: input.state.consumed } := by
  rw [PqxdhRegistrationInputs.accepted_rid input.state.control acceptedState registration status binding coins secrets
    pending accepted, hidentity, honeTime, history]
  rfl


/-- Actual accepted fields, source consumption and arbitrary post-derivation pending bytes compose through the complete native builder. -/
theorem accepted_native_complete {Metadata PeerMetadata PrimitiveState Result ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Input Metadata PeerMetadata (List Pqxdh.Bytes) PrimitiveState)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (identity : Ed25519PublicKey) (oneTime : X25519PublicKey)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (root : RootOutput)
    (registration : pqxdh.VerifiedInitKex) (status : pqxdh.RegistrationStatus)
    (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (acceptedState : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (afterDerivation : pqxdh.RootKeyInput)
    (accepted : pqxdh.server_accept input.state.control registration status input.binding coins secrets =
      ok (.Ok (acceptedState, pending)))
    (hidentity : absBytes registration.beacon_identity_public_key = identity.toList)
    (honeTime : absBytes registration.beacon_one_time_public_key = oneTime.toList)
    (hephemeral : absBytes coins.ephemeral_public_key = source.crypto.xpub ephemeral.toList)
    (hciphertext : absBytes coins.kem_ciphertext = ciphertext.toList)
    (history : input.state.consumed = server.consumed)
    (next : (RustM (Option Response × State Metadata PeerMetadata (List Pqxdh.Bytes)) × PrimitiveState) →
      OracleComp base Result) :
    let execution := ready server application identity oneTime ephemeral ciphertext root
    ((simulateQ impl (simulateQ nativeAdapter (buildReady source input.binding execution input.metadata
      (input.afterReady execution).state))).run input.primitive >>= next) =
      ((simulateQ impl (simulateQ nativeAdapter
        (PqxdhServerRegistrationPublication.build source { pending with root_key_input := afterDerivation }
          root application input.metadata
          { input.state with consumed := absBytes pending.registration_id.bytes :: input.state.consumed }))).run
        input.primitive >>= next) := by
  dsimp only
  rw [input.actual_consumption server application identity oneTime ephemeral ciphertext root registration status
    input.binding coins secrets acceptedState pending accepted hidentity honeTime history]
  apply buildReady_complete impl source input.binding _ _ _ input.metadata _ input.primitive next
  change PqxdhRegistrationInputs.used pending = _
  exact accepted_fields source.crypto (ready server application identity oneTime ephemeral ciphertext root)
    input.state.control acceptedState registration status input.binding coins secrets pending accepted
    hidentity hephemeral hciphertext


set_option backward.isDefEq.respectTransparency false in
/-- Nine actual native interfaces; the source initializer is separate local fixed-HKDF work. -/
inductive NativeKind where
  | kdf | aead | hash | frameWriter | identity | peerReserve | plaintextReserve | erase | phase2Writer
  deriving DecidableEq, Fintype

def nativeKind : NativeSpec.Domain → NativeKind
  | .inl (.inl _) => .kdf
  | .inl (.inr (.inl _)) => .aead
  | .inl (.inr (.inr (.inl _))) => .hash
  | .inl (.inr (.inr (.inr _))) => .frameWriter
  | .inr (.checkIdentity _) => .identity
  | .inr .reservePeer => .peerReserve
  | .inr (.reservePlaintext _) => .plaintextReserve
  | .inr (.erase _) => .erase
  | .inr (.write _) => .phase2Writer

def nativePredicate (kind : NativeKind) (query : NativeSpec.Domain) : Prop := match kind with
  | .kdf => leftPredicate Sum.isLeft query = true
  | .aead => leftPredicate (RawCtxSourceSeal.category .aead) query = true
  | .hash => leftPredicate (RawCtxSourceSeal.category .hash) query = true
  | .frameWriter => leftPredicate (RawCtxSourceSeal.category .writer) query = true
  | .identity => auxPredicate .identity query = true
  | .peerReserve => auxPredicate .peerReserve query = true
  | .plaintextReserve => auxPredicate .plaintextReserve query = true
  | .erase => auxPredicate .erase query = true
  | .phase2Writer => auxPredicate .writer query = true

instance (kind : NativeKind) : DecidablePred (nativePredicate kind) := fun query => by
  cases kind <;> dsimp [nativePredicate] <;> infer_instance

private theorem nativeKind_iff (kind : NativeKind) (query : NativeSpec.Domain) :
    nativeKind query = kind ↔ nativePredicate kind query := by
  rcases query with ((request | (request | (request | request))) | request)
  all_goals cases kind <;> try cases request
  all_goals simp [nativeKind, nativePredicate, leftPredicate, auxPredicate, auxKind,
    RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate, RawCtxSourceSeal.callKind]

/-- The complete native builder has one-call caps for each of its nine actual callback interfaces. -/
theorem buildReady_native_partition {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (kind : NativeKind) :
    (simulateQ nativeAdapter (buildReady source binding ready metadata state)).IsQueryBoundP
      (fun query => nativeKind query = kind) 1 := by
  apply (isQueryBoundP_congr_pred (p' := nativePredicate kind) (nativeKind_iff kind)).mpr
  have bounds := buildReady_native_bounds source binding ready metadata state
  cases kind
  · exact bounds.1
  · exact bounds.2.1 .aead
  · exact bounds.2.1 .hash
  · exact bounds.2.1 .writer
  · exact bounds.2.2 .identity
  · exact bounds.2.2 .peerReserve
  · exact bounds.2.2 .plaintextReserve
  · exact bounds.2.2 .erase
  · exact bounds.2.2 .writer


/-- Every native callback pays its own stated primitive cost, preserving full state and optional failure. -/
theorem buildReady_weighted {Metadata PeerMetadata Consumed PrimitiveState ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (cost : NativeKind → Nat)
    (step : ∀ query primitive, ((impl query).run primitive).IsQueryBoundP predicate (cost (nativeKind query)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (binding : pqxdh.ServerBinding) (ready : Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : PrimitiveState) :
    ((simulateQ impl (simulateQ nativeAdapter
      (buildReady source binding ready metadata state))).run primitive).IsQueryBoundP predicate (∑ kind, cost kind) := by
  simpa only [Nat.mul_one] using FinitePartitionQueryBounds.weighted_bound nativeKind cost (fun _ => 1)
    impl predicate _ (buildReady_native_partition source binding ready metadata state) step primitive

/-- Exact weighted native work and arbitrary post-publication continuation compose in the original source class. -/
theorem Plan.accepted_bound {ι Metadata PeerMetadata Consumed PrimitiveState Selection : Type}
    {baseSpec : OracleSpec ι} {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (plan : Plan baseSpec setup Selection Metadata PeerMetadata Consumed PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (predicate : (CorrelatedSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (cost : NativeKind → Nat) (qNext : Nat)
    (step : ∀ query primitive, ((plan.impl query).run primitive).IsQueryBoundP predicate (cost (nativeKind query)))
    (next : ∀ output result, (plan.next output result).IsQueryBoundP predicate qNext)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit Selection)))
    (ready : Ready) :
    ((plan.continuation source).accepted output ready).IsQueryBoundP predicate ((∑ kind, cost kind) + qNext) :=
  isQueryBoundP_bind (buildReady_weighted plan.impl predicate cost step source
    (plan.inputs output ready).binding ready (plan.inputs output ready).metadata
    (plan.inputs output ready).state (plan.inputs output ready).primitive) (fun result _ => next output result)

end BeaconcryptCore.Computational.PqxdhAcceptedRegistration

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.ciphertextArray_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.ciphertextArray_bytes

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.accepted_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.accepted_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_source

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_native_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_native_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_run_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_run_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.Plan.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.Plan.accepted_source

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.authenticated_registration_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.authenticated_registration_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.Input.afterReady_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.Input.afterReady_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.Input.actual_consumption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.Input.actual_consumption

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.accepted_native_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.accepted_native_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_native_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_native_partition

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.buildReady_weighted

/--
info: 'BeaconcryptCore.Computational.PqxdhAcceptedRegistration.Plan.accepted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAcceptedRegistration.Plan.accepted_bound
