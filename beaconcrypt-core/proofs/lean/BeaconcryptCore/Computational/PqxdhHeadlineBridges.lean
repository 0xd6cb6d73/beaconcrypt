import BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets
import BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary
import BeaconcryptCore.Computational.PqxdhRegistrationInputs
import BeaconcryptCore.Computational.PqxdhProtocolAcceptance
import BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication
import BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports
import BeaconcryptCore.Computational.RawCtxSourceSeal
import BeaconcryptCore.Computational.RawCtxSourceOpen
import BeaconcryptCore.Computational.RawCtxInterpretedSend
import BeaconcryptCore.Computational.RawCtxNativeFramePrelude
import BeaconcryptCore.Computational.PqxdhInitialGenericPublication
import BeaconcryptCore.Computational.PqxdhInitialPendingBuilder
import BeaconcryptCore.Computational.PqxdhInitialRootEventExperiment
import BeaconcryptCore.Computational.PqxdhInitialRootEventSecrecy
import BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance
import BeaconcryptCore.Refinement.RatchetEffect
import BeaconcryptCore.Refinement.PqxdhCore

/-!
# Headline bridges for the replaced extracted steps of HB-111 and HB-112

The headline experiments HB-111 (`PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound`) and HB-112 (`PqxdhAuthenticatedEvolvingSecrecy.bound`) run hand-written Lean programs in place of several extracted Rust functions. This module adds new statements; it changes no existing theorem.

Bridges B1-B8 and B10 are proved outright, without any hypothesis of the headline theorems; B3 and B6 quantify over representation or width conditions on their own arguments. B1 relates the hand-written consuming prepare and native builder to the extracted `server_prepare_commit`, for every value of the two pending fields that prepare does not read. B2 relates the hand-written Server publications of both experiments to the extracted `server_commit`. B3 relates the hand-written Phase1 control and signed messages to the extracted `beacon_start` on byte arrays that represent the typed keys. B4 relates the hand-written Phase2 publication to the extracted `beacon_commit`. B5 relates the hand-written registration consumption to the extracted `registration_id`. B6 relates the hand-written commitment hash inputs to the extracted `build_commitment_transcript`, for the widths that the hand-written paths check before hashing. B7 relates the hand-written send results to the extracted `SendSeal.finish`. B8 relates the hand-written payload splitter to the extracted `OpenFrameContext.from_frame`. B10 relates the four hand-written Phase1 parsers used by the source acceptance to the extracted `validate_init_kex`; it is exact on fixed-width bundles, and byte strings of other widths are rejected by the parsers and have no extracted representation.

B9 (HB-111) and B11 (HB-112) concern `server_accept`, `registration_id` and the root derivation on the accepted branch. They hold under HB-111's representation premises: a stored secret-identity map and the initial root-field relation of the selected Server. On every stopped source run in the support of the sampled private run, for every eligible candidate whose DH/conversion branch succeeds, the hand-written accepted continuation equals the continuation that executes the extracted acceptance, consumes the returned registration identifier, derives the root from the returned root input and runs the builder on the returned pending token.

The bridged headline theorems conjoin the unchanged statements of HB-111 and HB-112 with these bridges at the same parameters. The `extracted` headline theorems go further for the accepted branch: their experiments execute the extracted `server_accept` (hence `registration_id`) and the extracted `server_prepare_commit` there, and they have the same output distribution as the original experiments under HB-111's representation premises, so the original bounds carry over unchanged. In HB-112's extracted experiment the post-run freshness decision and the origin mark still read the root and ephemeral key of the hand-written accepted-root value; the root equals the one derived from the extracted root input.

Not bridged here: the record-opening phases `record.begin_open`, `record.OpenCommitment.*` and `record.OpenAead.*` (their extracted driver is related to its own source program, not to the hand-written opening used by the experiments), `record.finish_frame_read` (the experiments keep a free frame decoder parameter), and the free route, writer and decoder parameters of the experiments. Apart from the accepted branch of the `extracted` experiments, the experiments still execute the hand-written programs; B1-B8 and B10 state their equality with the extracted functions as conjuncts. The reductions on the right-hand sides still use the hand-written protocol.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhHeadlineBridges
open PqxdhRefinement PqxdhEd25519EufCma PqxdhKemIndCca
open BeaconcryptCore.Refinement.ProtocolComposition (concreteByte absByte_concreteByte)

/-! ## Unconditional bridges B1-B8 -/

/-- B1 (server_prepare_commit): the hand-written consuming prepare equals the extracted prepare on every full pending registration whose four used fields are the given ones, for every value of the two unread fields; the same holds for the complete native builder. -/
def PrepareBridge : Prop :=
  (∀ (state : pqxdh.ServerState) (input : PqxdhRegistrationInputs.UsedInput)
      (registrationId : pqxdh.RegistrationId) (rootInput : pqxdh.RootKeyInput)
      (binding : pqxdh.ServerBinding) (available : pqxdh.KeyIdAvailability),
    PqxdhRegistrationInputs.prepare state input binding available =
      pqxdh.server_prepare_commit state
        ⟨input.server_binding, registrationId, input.beacon_identity_public_key,
          input.ephemeral_public_key, input.kem_ciphertext, rootInput⟩ binding available) ∧
  (∀ (Metadata PeerMetadata Consumed : Type) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
      (input : PqxdhRegistrationInputs.UsedInput)
      (registrationId : pqxdh.RegistrationId) (rootInput : pqxdh.RootKeyInput)
      (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
      (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed),
    PqxdhRegistrationInputs.build source input root data metadata state =
      PqxdhServerRegistrationPublication.build source
        ⟨input.server_binding, registrationId, input.beacon_identity_public_key,
          input.ephemeral_public_key, input.kem_ciphertext, rootInput⟩ root data metadata state)

/-- B1 holds. -/
theorem prepare_bridge : PrepareBridge :=
  ⟨fun state input registrationId rootInput binding available =>
      PqxdhRegistrationInputs.prepare_exact state
        ⟨input.server_binding, registrationId, input.beacon_identity_public_key,
          input.ephemeral_public_key, input.kem_ciphertext, rootInput⟩ binding available,
    fun _ _ _ source input registrationId rootInput root data metadata state =>
      PqxdhRegistrationInputs.build_exact source
        ⟨input.server_binding, registrationId, input.beacon_identity_public_key,
          input.ephemeral_public_key, input.kem_ciphertext, rootInput⟩ root data metadata state⟩

/-- B2 (server_commit): the extracted commit of any candidate returns exactly the control installed by the hand-written publication of HB-111 (native kernels) and of HB-112 (generic kernels), together with the committed key identifier, beacon identity and associated data. -/
def CommitBridge : Prop :=
  (∀ (Metadata PeerMetadata Consumed : Type)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (metadata : PeerMetadata),
    pqxdh.server_commit candidate = ok
      ((PqxdhServerRegistrationPublication.publish state candidate kernel metadata).control,
        ⟨candidate.key_id, candidate.beacon_identity_public_key, candidate.associated_data⟩)) ∧
  (∀ (Kernel Metadata PeerMetadata Consumed : Type)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate) (kernel : Kernel) (metadata : PeerMetadata),
    pqxdh.server_commit candidate = ok
      ((PqxdhInitialGenericPublication.publish state candidate kernel metadata).control,
        ⟨candidate.key_id, candidate.beacon_identity_public_key, candidate.associated_data⟩))

/-- B2 holds. -/
theorem commit_bridge : CommitBridge :=
  ⟨fun _ _ _ state candidate kernel metadata =>
    PqxdhServerRegistrationPublication.publish_commit state candidate kernel metadata,
    fun _ _ _ _ _ _ _ _ => rfl⟩

/-- B3 (beacon_start): for byte arrays representing the typed identity and key tuple, the extracted builder succeeds, installs exactly the hand-written Phase1 control, and emits exactly the four encoded messages that the hand-written signing program signs. -/
def BeaconStartBridge : Prop :=
  ∀ (fresh : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple),
    absBytes inputs.identity_public_key = identity.toList →
    absBytes inputs.prekey_public_key = keys.prekey.toList →
    absBytes coins.one_time_public_key = keys.oneTime.toList →
    absBytes inputs.pq_public_key = keys.pqKey.toList →
    ∃ started : pqxdh.BeaconStart, pqxdh.beacon_start fresh inputs coins = ok started ∧
      started.state = PqxdhBeaconPhase1Publication.control fresh inputs.identity_public_key ∧
      absBytes started.message.identity_key = encodedIdentity identity ∧
      absBytes started.message.prekey = prekeyMessage keys.prekey ∧
      absBytes started.message.one_time_key = oneTimeMessage keys.oneTime ∧
      absBytes started.message.pq_key = pqMessage keys.pqKey

/-- B3 holds. -/
theorem beacon_start_bridge : BeaconStartBridge := by
  intro fresh inputs coins identity keys identityBytes prekeyBytes oneTimeBytes pqBytes
  obtain ⟨started, built, control⟩ := PqxdhBeaconPhase1Publication.core_control fresh inputs coins
  obtain ⟨other, builtOther, _, identityTag, prekeyTag, oneTimeTag, pqTag⟩ :=
    PqxdhJointPhase1SourceWriter.beacon_start_unsigned fresh inputs coins
  have same : other = started := by
    rw [built] at builtOther
    cases builtOther
    rfl
  subst same
  refine ⟨other, built, control, ?_, ?_, ?_, ?_⟩
  · rw [identityTag, identityBytes]; rfl
  · rw [prekeyTag, prekeyBytes]; rfl
  · rw [oneTimeTag, oneTimeBytes]; rfl
  · rw [pqTag, pqBytes]; rfl

/-- B4 (beacon_commit): the extracted commit of the authenticated registration returns exactly the established control that the hand-written Phase2 publication installs, with its assigned key identifier. -/
def BeaconCommitBridge : Prop :=
  ∀ (I D K : Type) (state : PqxdhBeaconPhase2Preparation.State I D K)
    (staged : PqxdhBeaconPhase2Publication.Staged),
    ∃ established : pqxdh.BeaconEstablished,
      pqxdh.beacon_commit staged.authenticated = ok established ∧
      (PqxdhBeaconPhase2Publication.publish state staged).2.beacon.phase =
        .established established staged.associatedData staged.kernel ∧
      (PqxdhBeaconPhase2Publication.publish state staged).2.beacon.identityKeyId =
        established.assigned_key_id

/-- B4 holds. -/
theorem beacon_commit_bridge : BeaconCommitBridge := by
  intro I D K state staged
  obtain ⟨_, _, _, _, keyId, phase, committed⟩ :=
    PqxdhBeaconPhase2Publication.publish_fields state staged
  exact ⟨_, committed, phase, keyId⟩

/-- B5 (registration_id): the extracted registration identifier of the typed verified key tuple succeeds, and the hand-written accepted-root value consumes exactly its bytes on top of the unchanged Server state. -/
def RegistrationIdBridge : Prop :=
  ∀ (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes) (identity : Ed25519PublicKey)
    (keys : Phase1KeyTuple) (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext)
    (root : PqxdhSecretInputKdf.RootOutput),
    ∃ registration : pqxdh.RegistrationId,
      pqxdh.registration_id (PqxdhProtocolAcceptance.verified identity keys) = ok registration ∧
      (PqxdhPrivateAcceptedRoot.ready server application identity keys.oneTime ephemeral ciphertext
        root).consumed = { server with consumed := absBytes registration.bytes :: server.consumed }

/-- B5 holds. -/
theorem registration_id_bridge : RegistrationIdBridge := by
  intro server application identity keys ephemeral ciphertext root
  obtain ⟨registration, computed, bytes⟩ :=
    registration_id_abs (PqxdhProtocolAcceptance.verified identity keys)
  have ridBytes : absBytes registration.bytes = identity.toList ++ keys.oneTime.toList := by
    simpa only [Pqxdh.ValidInit.rid, PqxdhProtocolAcceptance.verified,
      PqxdhRootTableInitialization.rootArray_bytes] using bytes
  refine ⟨registration, computed, ?_⟩
  rw [ridBytes]
  rfl

/-- Every byte string of the right width is represented by a fixed-width extracted byte array. -/
theorem array_of_bytes (n : Std.Usize) (bytes : Pqxdh.Bytes) (width : bytes.length = n.val) :
    ∃ array : Std.Array Std.U8 n, absBytes array = bytes :=
  ⟨⟨bytes.map concreteByte, by simp [width]⟩, by
    simp [absBytes, List.map_map, Function.comp_def, absByte_concreteByte]⟩

/-- B6 (build_commitment_transcript): whenever the hand-written sealing or opening path reaches its hash call (153-byte associated data, 16-byte tag), the hashed bytes are exactly the output of the extracted 229-byte commitment transcript builder on representing arrays. -/
def CommitmentTranscriptBridge : Prop :=
  (∀ (input : RawCtxSourceSend.SealInput) (tagBytes : Pqxdh.Bytes),
    input.context.associatedData.length = 153 → tagBytes.length = 16 →
    ∃ (ad : Std.Array Std.U8 153#usize) (tag : Std.Array Std.U8 16#usize) (transcript : _),
      absBytes ad = input.context.associatedData ∧ absBytes tag = tagBytes ∧
      commitment.build_commitment_transcript input.material.key.bytes input.material.nonce.bytes ad tag
        input.sequence input.context.senderId = ok transcript ∧
      absBytes transcript.bytes = RawCtxSourceSeal.hashInput input tagBytes) ∧
  (∀ (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices),
    input.context.associatedData.length = 153 → slices.tag.length = 16 →
    ∃ (ad : Std.Array Std.U8 153#usize) (tag : Std.Array Std.U8 16#usize) (transcript : _),
      absBytes ad = input.context.associatedData ∧ absBytes tag = slices.tag ∧
      commitment.build_commitment_transcript input.material.key.bytes input.material.nonce.bytes ad tag
        input.sequence input.context.frame.sender = ok transcript ∧
      absBytes transcript.bytes = RawCtxSourceOpen.hashInput input slices)

/-- B6 holds. -/
theorem commitment_transcript_bridge : CommitmentTranscriptBridge := by
  constructor
  · intro input tagBytes adWidth tagWidth
    obtain ⟨ad, adBytes⟩ := array_of_bytes 153#usize _ (by simpa using adWidth)
    obtain ⟨tag, tagArray⟩ := array_of_bytes 16#usize tagBytes (by simpa using tagWidth)
    obtain ⟨transcript, built, bytes⟩ :=
      RawCtxSourceSeal.hashInput_extracted input tagBytes ad tag adBytes tagArray
    exact ⟨ad, tag, transcript, adBytes, tagArray, built, bytes⟩
  · intro input slices adWidth tagWidth
    obtain ⟨ad, adBytes⟩ := array_of_bytes 153#usize _ (by simpa using adWidth)
    obtain ⟨tag, tagArray⟩ := array_of_bytes 16#usize slices.tag (by simpa using tagWidth)
    obtain ⟨transcript, built, bytes⟩ :=
      RawCtxSourceOpen.hashInput_extracted input slices ad tag adBytes tagArray
    exact ⟨ad, tag, transcript, adBytes, tagArray, built, bytes⟩

/-- B7 (SendSeal.finish): the extracted send finish returns exactly the advanced kernel and the unchanged optional sealing reply, which is what the hand-written send programs return; this includes the interpreted native sealing capability. -/
def SendFinishBridge : Prop :=
  (∀ (Context Output : Type) (ready : SendSeal Context) (sealed : Option Output),
    ready.finish sealed = ok (ready.advanced, sealed)) ∧
  (∀ (Context Output : Type) (pending : RawCtxInterpretedSend.Seal RatchetMaterial Context)
      (sealed : Option Output),
    SendSeal.finish (RawCtxInterpretedSend.nativeSeal pending) sealed =
      ok (ConcreteRatchetKernel.mk pending.advanced, sealed))

/-- B7 holds. -/
theorem send_finish_bridge : SendFinishBridge :=
  ⟨fun _ _ ready sealed => SendSeal.finish_returns_interpreter_result ready sealed,
    fun _ _ pending sealed =>
      SendSeal.finish_returns_interpreter_result (RawCtxInterpretedSend.nativeSeal pending) sealed⟩

/-- B8 (OpenFrameContext.from_frame): on every represented payload the extracted payload admission and its three slices equal the hand-written splitter, and every payload no longer than the native size bound is represented by a slice. -/
def FramePayloadBridge : Prop :=
  (∀ (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize) (sender : Std.U64),
    (RawCtxNativeFramePrelude.projectOption RawCtxNativeFramePrelude.contextSlices <$>
        record.OpenFrameContext.from_frame payload ad sender) =
      ok (RawCtxFrameDecoding.fromPayload (RawCtxNativeFramePrelude.sliceBytes payload))) ∧
  (∀ bytes : Pqxdh.Bytes, bytes.length ≤ Std.Usize.max →
    ∃ payload : Slice Std.U8, RawCtxNativeFramePrelude.sliceBytes payload = bytes)

/-- B8 holds. -/
theorem frame_payload_bridge : FramePayloadBridge :=
  ⟨RawCtxNativeFramePrelude.payload_exact, fun bytes width =>
    ⟨⟨bytes.map concreteByte, by simpa using width⟩, by
      simp [RawCtxNativeFramePrelude.sliceBytes, List.map_map, Function.comp_def,
        absByte_concreteByte]⟩⟩

/-! ## B9: native acceptance on the accepted branch of HB-111 -/

section AuthenticatedRoot
open PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource PqxdhPhase2GeneratedDriver
open PqxdhPrivateRootSource PqxdhPrivateAcceptedRoot PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot
open PqxdhAuthenticatedRootExperiment PqxdhJointIdentity PqxdhInitializerSecrecy
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A KemSK : Type} {S B : Nat}

/-- B9 (server_accept and registration_id on the accepted branch): for every stopped source run in the support of the private run that HB-111's experiment samples, every private KEM secret and every ephemeral/encapsulation pair, if the run's candidate is target-eligible and the actual DH/conversion branch succeeds, then the accepted keys are the generated ones and the hand-written accepted continuation equals the one that first runs the extracted acceptance, registration-identifier consumption, root derivation and native builder (`nativeAccept`), followed by the same adaptive schedule. -/
def AcceptBridge {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes) : Prop :=
  ∀ stopped ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
    ∀ output, stopped.1 = some output →
    ∀ (secret : KemSK) (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext)
      (shared : MlKemSharedSecret),
      targetEligible env.parameters (eraseOutput output, stopped.2) = true →
      rootFailure env.source.crypto env.server.ikSk ephemeral.toList
        (eraseOutput output).context.publicIdentity.ed25519
        (eraseOutput output).context.generated.before.publicKey
        (eraseOutput output).context.generated.after.publicKey = none →
      (eraseOutput output).accepted = some ((eraseOutput output).context.publicIdentity.ed25519,
        (publicMaterial setup (eraseOutput output).context.publicIdentity.ed25519
          (eraseOutput output).context.generated).keyTuple) ∧
      PqxdhAuthenticatedRootExperiment.nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program
          post secret (eraseOutput output, stopped.2) ephemeral (some (ciphertext, shared)) =
        (do
          let result ← (PqxdhProtocolNativeAcceptance.nativeAccept env.source env.recordWriter env.aux
            secretIdentity env.senderId env.index env.metadata env.application
            (eraseOutput output).context.publicIdentity.ed25519
            (publicMaterial setup (eraseOutput output).context.publicIdentity.ed25519
              (eraseOutput output).context.generated).keyTuple
            ephemeral ciphertext shared).run (eraseOutput output).context.selection.2
          Prod.fst <$> (simulateQ (PqxdhPhase2PostScheduler.actual attachedVerify primitives 1 env.source
            env.localImpl env.recordWriter env.senderId env.route env.decode baseImpl kem secret ciphertext)
            (post (eraseOutput output).context.selection.1 result.1)).run (result.2, stopped.2))

/-- B9 holds under HB-111's own representation premises: the selected Server's stored secret identity and the initial root-field relation. -/
theorem accept_bridge {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    AcceptBridge env baseImpl kem attachedVerify primitives program post secretIdentity := by
  intro stopped present output stoppedOutput secret ephemeral ciphertext shared eligible valid
  obtain ⟨reached, erased, related⟩ := PqxdhAuthenticatedRootBoundary.reached_root_fields env baseImpl kem
    attachedVerify primitives program secretIdentity initialMatch stopped present
  rw [stoppedOutput, Option.map_some, Option.some.injEq] at erased
  subst reached
  have fields := of_decide_eq_true eligible
  refine ⟨fields.1, ?_⟩
  simp only [PqxdhAuthenticatedRootExperiment.nativeAfterEncapsulation, valid]
  rw [PqxdhAuthenticatedRootExperiment.nativeAccepted,
    PqxdhProtocolNativeAcceptance.native_accept_eq_build env.source env.recordWriter env.aux
    secretIdentity env.senderId env.index env.metadata (eraseOutput output).context.selection.2 env.server related
    env.application _ _ ephemeral ciphertext shared fields.2.2 valid]
  rfl

/-- HB-111's post-encapsulation leaf with the extracted acceptance executed on the accepted branch: identical to `nativeAfterEncapsulation` on the encapsulation-failure and DH/conversion-failure branches; on success it runs `nativeAccept` (extracted `server_accept`, registration-identifier consumption, root derivation from the pending root input, native builder) before the same adaptive schedule. -/
noncomputable def extractedAfterEncapsulation {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes) (secret : KemSK)
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    ProbComp Bool :=
  match encapsulated with
  | none => evalKem baseImpl kem secret (observe env.source none attachedVerify primitives 1 setup
      (commonObserver env program post) (some prepared.1) ⟨some ephemeral, none, .error .badEncoding, env.server⟩
      prepared.2)
  | some (ciphertext, shared) =>
      match rootFailure env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
        prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey with
      | some failure => evalKem baseImpl kem secret (observe env.source none attachedVerify primitives 1 setup
          (commonObserver env program post) (some prepared.1)
          ⟨some ephemeral, some ciphertext, .error failure, env.server⟩ prepared.2)
      | none => do
          let result ← (PqxdhProtocolNativeAcceptance.nativeAccept env.source env.recordWriter env.aux
            secretIdentity env.senderId env.index env.metadata env.application
            prepared.1.context.publicIdentity.ed25519
            (publicMaterial setup prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated).keyTuple
            ephemeral ciphertext shared).run prepared.1.context.selection.2
          Prod.fst <$> (simulateQ (PqxdhPhase2PostScheduler.actual attachedVerify primitives 1 env.source
            env.localImpl env.recordWriter env.senderId env.route env.decode baseImpl kem secret ciphertext)
            (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2)

/-- HB-111's per-run continuation with the extracted-acceptance leaf; every other branch is `nativeNext`'s. -/
noncomputable def extractedNext {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes) (secret : KemSK)
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if targetEligible env.parameters prepared then do
    let ephemeral ← simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (env.native.encaps prepared.1.context.generated.target)
    extractedAfterEncapsulation env baseImpl kem attachedVerify primitives program post secretIdentity secret prepared
      ephemeral encapsulated
  else evalKem baseImpl kem secret (allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
    (commonObserver env program post) (some prepared.1) prepared.2 env.server env.application env.ephemeralGen)

/-- HB-111's experiment in which the accepted branch executes the extracted acceptance. -/
noncomputable def extractedActual {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes) : ProbComp Bool :=
  PqxdhGeneratedNativeContinuation.nativeContinued attachedVerify primitives baseImpl kem setup
    (driver env.toDriverEnvironment program)
    (extractedNext env baseImpl kem attachedVerify primitives program post secretIdentity) false

/-- Under HB-111's representation premises, HB-111's experiment and the experiment executing the extracted acceptance have the same output distribution; on every reachable stopped run their continuations are equal programs. -/
theorem actual_extracted {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    𝒟[actual env baseImpl kem attachedVerify primitives program post] =
      𝒟[extractedActual env baseImpl kem attachedVerify primitives program post secretIdentity] := by
  unfold PqxdhAuthenticatedRootExperiment.actual extractedActual PqxdhGeneratedNativeContinuation.nativeContinued
  apply OracleComp.evalDist_bind_congr_of_support
  intro stopped present
  cases stoppedOutput : stopped.1 with
  | none => rfl
  | some output =>
    simp only
    congr 1
    unfold PqxdhAuthenticatedRootExperiment.nativeNext extractedNext
    split_ifs with eligible
    · congr 1
      funext ephemeral
      congr 1
      funext encapsulated
      rcases encapsulated with _ | ⟨ciphertext, shared⟩
      · rfl
      · cases valid : rootFailure env.source.crypto env.server.ikSk ephemeral.toList
            (eraseOutput output).context.publicIdentity.ed25519
            (eraseOutput output).context.generated.before.publicKey
            (eraseOutput output).context.generated.after.publicKey with
        | some failure =>
          simp only [PqxdhAuthenticatedRootExperiment.nativeAfterEncapsulation, extractedAfterEncapsulation, valid]
        | none =>
          rw [(accept_bridge env baseImpl kem attachedVerify primitives program post secretIdentity initialMatch
            stopped present output stoppedOutput _ ephemeral ciphertext shared eligible valid).2]
          simp only [extractedAfterEncapsulation, valid]
    · rfl

end AuthenticatedRoot

/-! ## validate_init_kex against the hand-written Phase1 parsers -/

section ValidateInit

/-- The typed identity and key tuple represented by a verified extracted bundle. -/
def typedVerified (v : pqxdh.VerifiedInitKex) : Ed25519PublicKey × Phase1KeyTuple :=
  (⟨absBytes v.beacon_identity_public_key, by simp⟩,
    ⟨⟨absBytes v.beacon_prekey_public_key, by simp⟩, ⟨absBytes v.beacon_one_time_public_key, by simp⟩,
      ⟨absBytes v.beacon_pq_public_key, by simp⟩⟩)

/-- Distinct verified extracted bundles represent distinct typed tuples. -/
theorem typedVerified_injective : Function.Injective typedVerified := by
  rintro ⟨identity, prekey, oneTime, pq⟩ ⟨identity', prekey', oneTime', pq'⟩ same
  have identityBytes : absBytes identity = absBytes identity' := congrArg (fun typed => typed.1.toList) same
  have prekeyBytes : absBytes prekey = absBytes prekey' := congrArg (fun typed => typed.2.prekey.toList) same
  have oneTimeBytes : absBytes oneTime = absBytes oneTime' :=
    congrArg (fun typed => typed.2.oneTime.toList) same
  have pqBytes : absBytes pq = absBytes pq' := congrArg (fun typed => typed.2.pqKey.toList) same
  rw [BeaconcryptCore.Refinement.PqxdhSurface.bytes_eq_of_abs_eq identityBytes,
    BeaconcryptCore.Refinement.PqxdhSurface.bytes_eq_of_abs_eq prekeyBytes,
    BeaconcryptCore.Refinement.PqxdhSurface.bytes_eq_of_abs_eq oneTimeBytes,
    BeaconcryptCore.Refinement.PqxdhSurface.bytes_eq_of_abs_eq pqBytes]

/-- The four hand-written Phase1 parsers (identity, prekey, one-time, PQ) applied to four byte strings, in the order and with the result shape used by `PqxdhJointPhase1Reports.sourceAccept`. -/
def parsedBytes (identity prekey oneTime pq : Pqxdh.Bytes) : Option (Ed25519PublicKey × Phase1KeyTuple) := do
  let identity ← parseIdentity identity
  let prekey ← parsePrekeyMessage prekey
  let oneTime ← parseOneTimeMessage oneTime
  let pqKey ← parsePqMessage pq
  pure (identity, ⟨prekey, oneTime, pqKey⟩)

/-- The hand-written parsers applied to the bytes of an extracted bundle. -/
def parsedFields (g : pqxdh.InitKex) : Option (Ed25519PublicKey × Phase1KeyTuple) :=
  parsedBytes (absBytes g.identity_key) (absBytes g.prekey) (absBytes g.one_time_key) (absBytes g.pq_key)

/-- A 32-byte extracted array always parses as a 32-byte vector. -/
theorem vectorOfLength?_absBytes32 (k : Std.Array Std.U8 32#usize) :
    vectorOfLength? 32 (absBytes k) = some ⟨absBytes k, by simp⟩ := by
  unfold vectorOfLength?
  simp

/-- A 1184-byte extracted array always parses as a 1184-byte vector. -/
theorem vectorOfLength?_absBytes1184 (k : Std.Array Std.U8 1184#usize) :
    vectorOfLength? 1184 (absBytes k) = some ⟨absBytes k, by simp⟩ := by
  unfold vectorOfLength?
  simp

/-- Case split of the extracted validator against the hand-written parsers: either both accept with the same typed values, or the extracted validator reports an invalid key encoding and the parsers reject. -/
theorem validate_init_kex_cases (g : pqxdh.InitKex) :
    (∃ v, pqxdh.validate_init_kex g = ok (.Ok v) ∧ parsedFields g = some (typedVerified v)) ∨
    (pqxdh.validate_init_kex g = ok (.Err .InvalidKeyEncoding) ∧ parsedFields g = none) := by
  unfold pqxdh.validate_init_kex
  have hpre := untag_x25519_key_abs g.prekey pqxdh.KEY_ROLE_PREKEY
  have hotk := untag_x25519_key_abs g.one_time_key pqxdh.KEY_ROLE_ONE_TIME
  have hpq := untag_mlkem768_key_abs g.pq_key
  rw [absByte_role_pre] at hpre
  rw [absByte_role_otk] at hotk
  rcases untag_sign_key_abs g.identity_key with ⟨k, hk, hkabs⟩ | ⟨hk, hkabs⟩
  · rcases hpre with ⟨pk, hpk, hpkabs⟩ | ⟨hpk, hpkabs⟩
    · rcases hotk with ⟨otk, hotk1, hotkabs⟩ | ⟨hotk1, hotkabs⟩
      · rcases hpq with ⟨q, hq1, hqabs⟩ | ⟨hq1, hqabs⟩
        · refine Or.inl ⟨⟨k, pk, otk, q⟩, by simp [hk, hpk, hotk1, hq1], ?_⟩
          simp [parsedFields, parsedBytes, parseIdentity, parsePrekeyMessage, parseOneTimeMessage,
            parsePqMessage, hkabs, hpkabs, hotkabs, hqabs, vectorOfLength?_absBytes32,
            vectorOfLength?_absBytes1184, typedVerified]
          rfl
        · refine Or.inr ⟨by simp [hk, hpk, hotk1, hq1], ?_⟩
          simp [parsedFields, parsedBytes, parseIdentity, parsePrekeyMessage, parseOneTimeMessage,
            parsePqMessage, hkabs, hpkabs, hotkabs, hqabs, vectorOfLength?_absBytes32]
      · refine Or.inr ⟨by simp [hk, hpk, hotk1], ?_⟩
        simp [parsedFields, parsedBytes, parseIdentity, parsePrekeyMessage, parseOneTimeMessage,
          hkabs, hpkabs, hotkabs, vectorOfLength?_absBytes32]
    · refine Or.inr ⟨by simp [hk, hpk], ?_⟩
      simp [parsedFields, parsedBytes, parseIdentity, parsePrekeyMessage, hkabs, hpkabs,
        vectorOfLength?_absBytes32]
  · refine Or.inr ⟨by simp [hk], ?_⟩
    simp [parsedFields, parsedBytes, parseIdentity, hkabs]

/-- The extracted validator on any fixed-width bundle: it always returns a Rust `Ok` value; it accepts with `v` exactly when the four hand-written parsers accept the bundle's field bytes with the typed values of `v`; and it returns an error exactly when they reject, the error then being `InvalidKeyEncoding`. -/
theorem validate_init_kex_bridge (g : pqxdh.InitKex) :
    (∃ result, pqxdh.validate_init_kex g = ok result) ∧
    (∀ v, pqxdh.validate_init_kex g = ok (.Ok v) ↔ parsedFields g = some (typedVerified v)) ∧
    (∀ e, pqxdh.validate_init_kex g = ok (.Err e) ↔ e = .InvalidKeyEncoding ∧ parsedFields g = none) := by
  rcases validate_init_kex_cases g with ⟨w, accepted, parsed⟩ | ⟨rejected, parsed⟩
  · refine ⟨⟨_, accepted⟩, fun v => ⟨fun same => ?_, fun same => ?_⟩, fun e => ⟨fun same => ?_, fun same => ?_⟩⟩
    · rw [accepted] at same
      cases same
      exact parsed
    · rw [parsed, Option.some.injEq] at same
      rw [← typedVerified_injective same]
      exact accepted
    · rw [accepted] at same
      cases same
    · rw [parsed] at same
      cases same.2
  · refine ⟨⟨_, rejected⟩, fun v => ⟨fun same => ?_, fun same => ?_⟩, fun e => ⟨fun same => ?_, fun same => ?_⟩⟩
    · rw [rejected] at same
      cases same
    · rw [parsed] at same
      cases same
    · rw [rejected] at same
      cases same
      exact ⟨rfl, parsed⟩
    · rw [same.1, rejected]

/-- The hand-written parsers only accept byte strings of the extracted field widths (33, 34, 34 and 1185 bytes). -/
theorem parsedBytes_widths (identity prekey oneTime pq : Pqxdh.Bytes) (result : Ed25519PublicKey × Phase1KeyTuple)
    (parsed : parsedBytes identity prekey oneTime pq = some result) :
    identity.length = 33 ∧ prekey.length = 34 ∧ oneTime.length = 34 ∧ pq.length = 1185 := by
  simp only [parsedBytes, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at parsed
  obtain ⟨identityKey, identityParsed, prekeyKey, prekeyParsed, oneTimeKey, oneTimeParsed, pqKey, pqParsed, _⟩ :=
    parsed
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(parseIdentity_eq_some_iff identity identityKey).mp identityParsed, encodedIdentity_length]
  · rw [(parsePrekeyMessage_eq_some_iff prekey prekeyKey).mp prekeyParsed, prekeyMessage_length]
  · rw [(parseOneTimeMessage_eq_some_iff oneTime oneTimeKey).mp oneTimeParsed, oneTimeMessage_length]
  · rw [(parsePqMessage_eq_some_iff pq pqKey).mp pqParsed, pqMessage_length]

/-- On arbitrary byte strings, the hand-written parsers accept with `result` exactly when some extracted fixed-width bundle representing these bytes is accepted by `validate_init_kex` with a verified value whose typed tuple is `result`. -/
theorem parsedBytes_accept_iff (identity prekey oneTime pq : Pqxdh.Bytes)
    (result : Ed25519PublicKey × Phase1KeyTuple) :
    parsedBytes identity prekey oneTime pq = some result ↔
      ∃ (g : pqxdh.InitKex) (v : pqxdh.VerifiedInitKex),
        absBytes g.identity_key = identity ∧ absBytes g.prekey = prekey ∧
        absBytes g.one_time_key = oneTime ∧ absBytes g.pq_key = pq ∧
        pqxdh.validate_init_kex g = ok (.Ok v) ∧ typedVerified v = result := by
  constructor
  · intro parsed
    obtain ⟨identityWidth, prekeyWidth, oneTimeWidth, pqWidth⟩ :=
      parsedBytes_widths identity prekey oneTime pq result parsed
    obtain ⟨identityArray, identityBytes⟩ := array_of_bytes 33#usize identity (by simpa using identityWidth)
    obtain ⟨prekeyArray, prekeyBytes⟩ := array_of_bytes 34#usize prekey (by simpa using prekeyWidth)
    obtain ⟨oneTimeArray, oneTimeBytes⟩ := array_of_bytes 34#usize oneTime (by simpa using oneTimeWidth)
    obtain ⟨pqArray, pqBytes⟩ := array_of_bytes 1185#usize pq (by simpa using pqWidth)
    let g : pqxdh.InitKex := ⟨identityArray, prekeyArray, oneTimeArray, pqArray⟩
    have fields : parsedFields g = some result := by
      simp only [parsedFields, g, identityBytes, prekeyBytes, oneTimeBytes, pqBytes]
      exact parsed
    rcases validate_init_kex_cases g with ⟨v, accepted, same⟩ | ⟨_, rejected⟩
    · rw [fields, Option.some.injEq] at same
      exact ⟨g, v, identityBytes, prekeyBytes, oneTimeBytes, pqBytes, accepted, same.symm⟩
    · rw [fields] at rejected
      cases rejected
  · rintro ⟨g, v, rfl, rfl, rfl, rfl, accepted, rfl⟩
    exact ((validate_init_kex_bridge g).2.1 v).mp accepted

/-- On arbitrary byte strings, the hand-written parsers reject exactly when every extracted bundle representing these bytes is rejected by `validate_init_kex` with `InvalidKeyEncoding`; for byte strings of the wrong widths no representing bundle exists and the parsers reject. -/
theorem parsedBytes_reject_iff (identity prekey oneTime pq : Pqxdh.Bytes) :
    parsedBytes identity prekey oneTime pq = none ↔
      ∀ g : pqxdh.InitKex,
        absBytes g.identity_key = identity → absBytes g.prekey = prekey →
        absBytes g.one_time_key = oneTime → absBytes g.pq_key = pq →
        pqxdh.validate_init_kex g = ok (.Err .InvalidKeyEncoding) := by
  constructor
  · rintro rejected g rfl rfl rfl rfl
    exact ((validate_init_kex_bridge g).2.2 _).mpr ⟨rfl, rejected⟩
  · intro rejected
    cases parsed : parsedBytes identity prekey oneTime pq with
    | none => rfl
    | some result =>
      obtain ⟨g, v, identityBytes, prekeyBytes, oneTimeBytes, pqBytes, accepted, _⟩ :=
        (parsedBytes_accept_iff identity prekey oneTime pq result).mp parsed
      rw [rejected g identityBytes prekeyBytes oneTimeBytes pqBytes] at accepted
      cases accepted

/-- The hand-written source acceptance used by the headline experiments is the identity parse and three attached verifications followed by exactly the four-parser block `parsedBytes` on the identity field and the three verified payloads. -/
theorem sourceAccept_parsed (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (candidate : Phase1Candidate) :
    PqxdhJointPhase1Reports.sourceAccept attachedVerify candidate = (do
      let publicKey ← parseIdentity candidate.identityKey
      let pqPayload ← attachedVerify publicKey candidate.pqKey
      let prePayload ← attachedVerify publicKey candidate.preKey
      let onePayload ← attachedVerify publicKey candidate.oneTimeKey
      parsedBytes candidate.identityKey prePayload onePayload pqPayload) := by
  cases identity : parseIdentity candidate.identityKey with
  | none => simp [PqxdhJointPhase1Reports.sourceAccept, identity]
  | some publicKey => simp [PqxdhJointPhase1Reports.sourceAccept, parsedBytes, identity]

/-- B10 (validate_init_kex): the extracted validator agrees with the four hand-written parsers on every fixed-width bundle, the parsers accept arbitrary byte strings exactly when a representing extracted bundle is accepted with the same typed values, and the hand-written source acceptance runs exactly this parser block after its identity parse and three attached verifications. -/
def ValidateInitBridge : Prop :=
  (∀ g : pqxdh.InitKex,
    (∃ result, pqxdh.validate_init_kex g = ok result) ∧
    (∀ v, pqxdh.validate_init_kex g = ok (.Ok v) ↔ parsedFields g = some (typedVerified v)) ∧
    (∀ e, pqxdh.validate_init_kex g = ok (.Err e) ↔ e = .InvalidKeyEncoding ∧ parsedFields g = none)) ∧
  (∀ (identity prekey oneTime pq : Pqxdh.Bytes) (result : Ed25519PublicKey × Phase1KeyTuple),
    parsedBytes identity prekey oneTime pq = some result ↔
      ∃ (g : pqxdh.InitKex) (v : pqxdh.VerifiedInitKex),
        absBytes g.identity_key = identity ∧ absBytes g.prekey = prekey ∧
        absBytes g.one_time_key = oneTime ∧ absBytes g.pq_key = pq ∧
        pqxdh.validate_init_kex g = ok (.Ok v) ∧ typedVerified v = result) ∧
  (∀ (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (candidate : Phase1Candidate),
    PqxdhJointPhase1Reports.sourceAccept attachedVerify candidate = (do
      let publicKey ← parseIdentity candidate.identityKey
      let pqPayload ← attachedVerify publicKey candidate.pqKey
      let prePayload ← attachedVerify publicKey candidate.preKey
      let onePayload ← attachedVerify publicKey candidate.oneTimeKey
      parsedBytes candidate.identityKey prePayload onePayload pqPayload))

/-- B10 holds. -/
theorem validate_init_bridge : ValidateInitBridge :=
  ⟨validate_init_kex_bridge, parsedBytes_accept_iff, sourceAccept_parsed⟩

end ValidateInit

/-! ## Native acceptance on the accepted branch of HB-112 -/

section InitialRootEvent
open PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot PqxdhPrivateAcceptedRoot
variable {ι Chain M P I D K X Response Shared : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The fields of the selected Server in HB-112's generic registration front that root generation, binding, replay admission and allocation read, related to the model Server state; this is the generic-front form of `PqxdhProtocolServerInvariant.RootFields`. -/
def FrontRootFields (c : Pqxdh.Crypto) (secret : M → Pqxdh.Bytes) (senderId : M → Std.U64) (index : Fin S)
    (server : Pqxdh.ServerState) (front : PqxdhInitialPendingPost.Front Chain M P I D K S B) : Prop :=
  secret (front.roles.1.1 index).server.metadata = server.ikSk ∧
    absBytes (front.roles.1.1 index).server.identity = c.edPub server.ikSk ∧
    (senderId (front.roles.1.1 index).server.metadata).val = server.sid ∧
    (front.controls index).last_key_id.val = server.n ∧
    front.consumed index = server.consumed

/-- The extracted acceptance on the typed source values, with a fresh registration and a successful DH/conversion branch, returns a pending token whose root input and registration identifier are the model values; the Server control, consumed list and binding are arbitrary arguments. -/
theorem accept_fresh (c : Pqxdh.Crypto) (control : pqxdh.ServerState) (consumed : List Pqxdh.Bytes)
    (binding : pqxdh.ServerBinding) (seed : Pqxdh.Bytes) (server : Pqxdh.ServerState)
    (seedEq : seed = server.ikSk) (consumedEq : consumed = server.consumed)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret)
    (fresh : identity.toList ++ keys.oneTime.toList ∉ server.consumed)
    (valid : rootFailure c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime = none) :
    ∃ pending, pqxdh.server_accept control (PqxdhProtocolAcceptance.verified identity keys)
        (PqxdhProtocolAcceptance.status identity keys consumed) binding
        (PqxdhProtocolAcceptance.nativeCoins c ephemeral ciphertext)
        (PqxdhProtocolAcceptance.shared
          (serverCoordinates c seed ephemeral.toList identity keys.prekey keys.oneTime) secret) =
        ok (.Ok (control, pending)) ∧
      absBytes pending.root_key_input.bytes = hiddenRootIKM
        (serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret ∧
      absBytes pending.registration_id.bytes = identity.toList ++ keys.oneTime.toList := by
  subst seedEq consumedEq
  obtain ⟨root, rootEq, rootBytes⟩ := (build_root_key_input_abs (PqxdhProtocolAcceptance.shared
    (serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)).1
      (PqxdhProtocolAcceptance.coordinates_valid c server identity keys ephemeral secret valid)
  obtain ⟨rid, ridEq, ridBytes⟩ := registration_id_abs (PqxdhProtocolAcceptance.verified identity keys)
  refine ⟨⟨binding, rid, (PqxdhProtocolAcceptance.verified identity keys).beacon_identity_public_key,
    (PqxdhProtocolAcceptance.nativeCoins c ephemeral ciphertext).ephemeral_public_key,
    (PqxdhProtocolAcceptance.nativeCoins c ephemeral ciphertext).kem_ciphertext, root⟩, ?_, ?_, ?_⟩
  · simp [PqxdhProtocolAcceptance.status, fresh, pqxdh.server_accept, pqxdh.validate_registration_status,
      rootEq, ridEq]
  · simpa only [PqxdhProtocolAcceptance.shared, hiddenRootIKM, PqxdhRootTableInitialization.rootArray_bytes]
      using rootBytes
  · simpa only [Pqxdh.ValidInit.rid, PqxdhProtocolAcceptance.verified,
      PqxdhRootTableInitialization.rootArray_bytes] using ridBytes

/-- HB-112's generic registration builder with the extracted `server_prepare_commit` on the full pending token in place of the hand-written consuming prepare on its four used fields; the allocation check and the candidate tail are those of `PqxdhInitialGenericBuilder.usedBuild`. -/
noncomputable def pendingBuild {Kernel Metadata PeerMetadata Consumed : Type} {m : Type → Type} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) (initial : RustM Kernel)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) :
    m (RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)) :=
  PqxdhInitialGenericBuilder.continueRust (pqxdh.server_next_key_id state.control) fun next =>
    match next with
    | .Err _ => pure (ok (none, state))
    | .Ok next =>
        let availability := if (state.server.peers next).isSome then
          pqxdh.KeyIdAvailability.Occupied else .Available
        PqxdhInitialGenericBuilder.continueRust (pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩ availability) fun prepared =>
          match prepared with
          | .Err _ => pure (ok (none, state))
          | .Ok candidate => PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state

/-- The generic builder on the extracted prepare equals the hand-written one on the pending token's used fields. -/
theorem pendingBuild_used {Kernel Metadata PeerMetadata Consumed : Type} {m : Type → Type} [Monad m]
    [LawfulMonad m] (calls : RawCtxChainOwner.Calls Kernel m)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) (initial : RustM Kernel)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) :
    pendingBuild calls aux initial pending data metadata state =
      PqxdhInitialGenericBuilder.usedBuild calls aux initial (PqxdhRegistrationInputs.used pending) data metadata
        state := rfl

/-- HB-112's registration step with the extracted acceptance: `server_accept` on the selected front Server, consumption of the returned registration identifier, the root derived from the returned root input, and the generic first-send builder running the extracted `server_prepare_commit` on the returned pending token. The initial kernel is supplied as a function of the derived root. -/
noncomputable def frontAccept (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialOf : PqxdhSecretInputKdf.RootOutput → RustM (PqxdhInitialPendingPost.KernelOf Chain))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (application : Option Pqxdh.Bytes)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret) :
    StateT (PqxdhInitialPendingPost.Front Chain M P I D K S B)
      (OracleComp (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B))
      (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun before =>
  match pqxdh.server_accept (before.controls index) (PqxdhProtocolAcceptance.verified identity keys)
      (PqxdhProtocolAcceptance.status identity keys (before.consumed index))
      ⟨(before.roles.1.1 index).server.identity, sender (before.roles.1.1 index).server.metadata⟩
      (PqxdhProtocolAcceptance.nativeCoins source.crypto ephemeral ciphertext)
      (PqxdhProtocolAcceptance.shared (serverCoordinates source.crypto
        (secretIdentity (before.roles.1.1 index).server.metadata) ephemeral.toList identity keys.prekey
        keys.oneTime) secret) with
  | .ok (.Ok (_, pending)) =>
      let consumed := absBytes pending.registration_id.bytes :: before.consumed index
      let current := { before with consumed := Function.update before.consumed index consumed }
      PqxdhInitialPendingBuilder.reinstall index current <$>
        pendingBuild PqxdhInitialPendingPost.calls PqxdhInitialPendingPost.auxForward
          (initialOf (PqxdhProtocolNativeAcceptance.nativeRoot source pending)) pending application metadata
          (PqxdhInitialPendingBuilder.selected sender index current)
  | .ok (.Err _) => pure (.ok none, before)
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)

/-- On a front whose selected Server is represented by the model Server, a fresh registration with a successful DH/conversion branch makes HB-112's hand-written consuming builder on the accepted-root value equal to the extracted-acceptance builder `frontAccept`, including the initial kernel derived from the root. -/
theorem front_accept_eq_build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialOf : PqxdhSecretInputKdf.RootOutput → RustM (PqxdhInitialPendingPost.KernelOf Chain))
    (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (before : PqxdhInitialPendingPost.Front Chain M P I D K S B) (server : Pqxdh.ServerState)
    (related : FrontRootFields source.crypto secretIdentity sender index server before)
    (application : Option Pqxdh.Bytes) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret)
    (fresh : identity.toList ++ keys.oneTime.toList ∉ server.consumed)
    (valid : rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime = none) :
    (frontAccept (extra := extra) (X := X) (Response := Response) (Shared := Shared) source secretIdentity
      initialOf sender index metadata application identity keys ephemeral ciphertext secret).run before =
    (PqxdhInitialPendingBuilder.build source
      (initialOf (productionHiddenRoot source
        (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret))
      sender index metadata
      (ready server application identity keys.oneTime ephemeral ciphertext (productionHiddenRoot source
        (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime)
          secret))).run before := by
  obtain ⟨pending, accepted, rootBytes, ridBytes⟩ := accept_fresh source.crypto (before.controls index)
    (before.consumed index) ⟨(before.roles.1.1 index).server.identity, sender (before.roles.1.1 index).server.metadata⟩
    (secretIdentity (before.roles.1.1 index).server.metadata) server related.1 related.2.2.2.2
    identity keys ephemeral ciphertext secret fresh valid
  have used := (PqxdhRegistrationInputs.accepted_used _ _ _ _ _ _ _ pending accepted).2
  have root : PqxdhProtocolNativeAcceptance.nativeRoot source pending = productionHiddenRoot source
      (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret := by
    simp only [PqxdhProtocolNativeAcceptance.nativeRoot, rootBytes, productionHiddenRoot]
    rfl
  simp only [frontAccept, StateT.run, accepted, pendingBuild_used]
  rw [root, used, ridBytes, related.2.2.2.2]
  rfl

end InitialRootEvent

section InitialRootEventBranch
open PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource PqxdhPhase2GeneratedDriver
open PqxdhPrivateRootSource PqxdhPrivateAcceptedRoot PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot
open PqxdhJointIdentity PqxdhInitializerSecrecy
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A KemSK : Type} {S B : Nat}

/-- HB-112's initial kernel as a function of the root: the real initial KDF response of the root, erased into the refined kernel, exactly as in `PqxdhInitialSourceExperiment.execution`. -/
noncomputable def initialOf (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (root : PqxdhSecretInputKdf.RootOutput) :=
  ConcreteRatchetKernel.refined <$>
    PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialRootLabelService.realInitial source root)

/-- B11 (server_accept and registration_id on the accepted branch of HB-112): for every stopped source run in the support of the private run that HB-112's experiment samples, every private KEM secret and every ephemeral/encapsulation pair, if the candidate is target-eligible and the actual DH/conversion branch succeeds, then the accepted keys are the generated ones and HB-112's accepted continuation equals the one whose registration step is `frontAccept` (extracted acceptance, registration-identifier consumption, root derivation from the pending root input, generic builder on the pending token), followed by the same compiled post schedule, freshness decision and interpretation. -/
def EvolvingAcceptBridge {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) (secretIdentity : M → Pqxdh.Bytes) : Prop :=
  ∀ stopped ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
    ∀ output, stopped.1 = some output →
    ∀ (secret : KemSK) (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext)
      (shared : MlKemSharedSecret),
      let prepared : Prepared setup (driver env.toDriverEnvironment program).State := (eraseOutput output, stopped.2)
      let identity := prepared.1.context.publicIdentity.ed25519
      let keys := (publicMaterial setup identity prepared.1.context.generated).keyTuple
      let readyValue := ready env.server env.application identity keys.oneTime ephemeral ciphertext
        (productionHiddenRoot env.source (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList
          identity keys.prekey keys.oneTime) shared)
      targetEligible env.parameters prepared = true →
      rootFailure env.source.crypto env.server.ikSk ephemeral.toList identity keys.prekey keys.oneTime = none →
      prepared.1.accepted = some (identity, keys) ∧
      PqxdhInitialRootEventExperiment.nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post
          (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program post selected number
            ancestors disclosed) secret prepared ephemeral (some (ciphertext, shared)) =
        simulateQ (PqxdhPhase2PostScheduler.interpretation env.source baseImpl kem secret ciphertext)
          ((fun result => PqxdhInitialRootEventAccepted.decision env readyValue selected number ancestors disclosed
              result.1) <$>
            (simulateQ (PqxdhInitialRootEventCompiler.target env.source env.recordWriter attachedVerify primitives 1
              env.localImpl env.aux ciphertext) (do
                let built ← (frontAccept env.source secretIdentity (initialOf env.source) env.senderId env.index
                  env.metadata env.application identity keys ephemeral ciphertext shared).run
                    (PqxdhInitialRootEventAccepted.front env program prepared)
                (simulateQ (PqxdhInitialOriginPost.compiler (PqxdhInitialSelectedOrigin.mark env.source
                    (PqxdhInitialRootEventAccepted.selectedMessage env program prepared readyValue))
                    env.senderId env.route env.decode)
                  (post prepared.1.context.selection.1 built.1)).run
                    (built.2, PqxdhInitialOriginPost.afterBuilder PqxdhInitialSourcePublication.empty built.2
                      env.index true built.1))).run
              (prepared.1.context.selection.2.primitive, prepared.2))

/-- B11 holds under the same representation premises as HB-111: the selected Server's stored secret identity and the initial root-field relation. -/
theorem evolving_accept_bridge {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    EvolvingAcceptBridge env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
      secretIdentity := by
  intro stopped present output stoppedOutput secret ephemeral ciphertext shared prepared identity keys readyValue
    eligible valid
  obtain ⟨reached, erased, related⟩ := PqxdhAuthenticatedRootBoundary.reached_root_fields env baseImpl kem
    attachedVerify primitives program secretIdentity initialMatch stopped present
  rw [stoppedOutput, Option.map_some, Option.some.injEq] at erased
  subst reached
  have fields := of_decide_eq_true eligible
  have frontRelated : FrontRootFields env.source.crypto secretIdentity env.senderId env.index env.server
      (PqxdhInitialRootEventAccepted.front env program prepared) := related
  have branch : rootFailure env.source.crypto env.server.ikSk ephemeral.toList
      prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
      prepared.1.context.generated.after.publicKey = none := valid
  refine ⟨fields.1, ?_⟩
  simp only [PqxdhInitialRootEventExperiment.nativeAfterEncapsulation, branch]
  rw [front_accept_eq_build env.source secretIdentity (initialOf env.source) env.senderId env.index env.metadata
    (PqxdhInitialRootEventAccepted.front env program prepared) env.server frontRelated env.application
    identity keys ephemeral ciphertext shared fields.2.2 valid]
  rfl

/-- HB-112's post-encapsulation leaf with the extracted acceptance executed on the accepted branch: identical to `PqxdhInitialRootEventExperiment.nativeAfterEncapsulation` with HB-112's accepted continuation on both failure branches; on success its registration step is `frontAccept` instead of the hand-written consuming builder, followed by the same compiled post schedule, freshness decision and interpretation. -/
noncomputable def extractedEvolvingAfterEncapsulation {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) (secretIdentity : M → Pqxdh.Bytes) (secret : KemSK)
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    ProbComp Bool :=
  match encapsulated with
  | none => evalKem baseImpl kem secret (observe env.source none attachedVerify primitives 1 setup
      (PqxdhAuthenticatedRootExperiment.commonObserver env program post) (some prepared.1)
      ⟨some ephemeral, none, .error .badEncoding, env.server⟩ prepared.2)
  | some (ciphertext, shared) =>
      match rootFailure env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
        prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey with
      | some failure => evalKem baseImpl kem secret (observe env.source none attachedVerify primitives 1 setup
          (PqxdhAuthenticatedRootExperiment.commonObserver env program post) (some prepared.1)
          ⟨some ephemeral, some ciphertext, .error failure, env.server⟩ prepared.2)
      | none =>
          let identity := prepared.1.context.publicIdentity.ed25519
          let keys := (publicMaterial setup identity prepared.1.context.generated).keyTuple
          let readyValue := ready env.server env.application identity keys.oneTime ephemeral ciphertext
            (productionHiddenRoot env.source (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList
              identity keys.prekey keys.oneTime) shared)
          simulateQ (PqxdhPhase2PostScheduler.interpretation env.source baseImpl kem secret ciphertext)
            ((fun result => PqxdhInitialRootEventAccepted.decision env readyValue selected number ancestors disclosed
                result.1) <$>
              (simulateQ (PqxdhInitialRootEventCompiler.target env.source env.recordWriter attachedVerify primitives 1
                env.localImpl env.aux ciphertext) (do
                  let built ← (frontAccept env.source secretIdentity (initialOf env.source) env.senderId env.index
                    env.metadata env.application identity keys ephemeral ciphertext shared).run
                      (PqxdhInitialRootEventAccepted.front env program prepared)
                  (simulateQ (PqxdhInitialOriginPost.compiler (PqxdhInitialSelectedOrigin.mark env.source
                      (PqxdhInitialRootEventAccepted.selectedMessage env program prepared readyValue))
                      env.senderId env.route env.decode)
                    (post prepared.1.context.selection.1 built.1)).run
                      (built.2, PqxdhInitialOriginPost.afterBuilder PqxdhInitialSourcePublication.empty built.2
                        env.index true built.1))).run
                (prepared.1.context.selection.2.primitive, prepared.2))

/-- HB-112's per-run continuation with the extracted-acceptance leaf; every other branch is that of `PqxdhInitialRootEventExperiment.nativeNext`. -/
noncomputable def extractedEvolvingNext {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) (secretIdentity : M → Pqxdh.Bytes) (secret : KemSK)
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if targetEligible env.parameters prepared then do
    let ephemeral ← simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (env.native.encaps prepared.1.context.generated.target)
    extractedEvolvingAfterEncapsulation env baseImpl kem attachedVerify primitives program post selected number
      ancestors disclosed secretIdentity secret prepared ephemeral encapsulated
  else evalKem baseImpl kem secret (allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
    (PqxdhAuthenticatedRootExperiment.commonObserver env program post) (some prepared.1) prepared.2 env.server
    env.application env.ephemeralGen)

/-- HB-112's experiment in which the accepted branch executes the extracted acceptance. -/
noncomputable def extractedEvolvingActual {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) (secretIdentity : M → Pqxdh.Bytes) : ProbComp Bool :=
  PqxdhGeneratedNativeContinuation.nativeContinued attachedVerify primitives baseImpl kem setup
    (driver env.toDriverEnvironment program)
    (extractedEvolvingNext env baseImpl kem attachedVerify primitives program post selected number ancestors
      disclosed secretIdentity) false

/-- Under HB-111's representation premises, HB-112's experiment and the experiment executing the extracted acceptance have the same output distribution; on every reachable stopped run their continuations are equal programs. -/
theorem evolving_actual_extracted {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    𝒟[PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number
        ancestors disclosed] =
      𝒟[extractedEvolvingActual env baseImpl kem attachedVerify primitives program post selected number ancestors
        disclosed secretIdentity] := by
  unfold PqxdhInitialRootEventSecrecy.actual PqxdhInitialRootEventExperiment.actual extractedEvolvingActual
    PqxdhGeneratedNativeContinuation.nativeContinued
  apply OracleComp.evalDist_bind_congr_of_support
  intro stopped present
  cases stoppedOutput : stopped.1 with
  | none => rfl
  | some output =>
    simp only
    congr 1
    unfold PqxdhInitialRootEventExperiment.nativeNext extractedEvolvingNext
    split_ifs with eligible
    · congr 1
      funext ephemeral
      congr 1
      funext encapsulated
      rcases encapsulated with _ | ⟨ciphertext, shared⟩
      · rfl
      · cases valid : rootFailure env.source.crypto env.server.ikSk ephemeral.toList
            (eraseOutput output).context.publicIdentity.ed25519
            (eraseOutput output).context.generated.before.publicKey
            (eraseOutput output).context.generated.after.publicKey with
        | some failure =>
          simp only [PqxdhInitialRootEventExperiment.nativeAfterEncapsulation, extractedEvolvingAfterEncapsulation,
            valid]
        | none =>
          rw [(evolving_accept_bridge env baseImpl kem attachedVerify primitives program post selected number
            ancestors disclosed secretIdentity initialMatch stopped present output stoppedOutput _ ephemeral ciphertext
            shared eligible valid).2]
          simp only [extractedEvolvingAfterEncapsulation, valid]
    · rfl

end InitialRootEventBranch

/-! ## Bridged headline statements -/

section Headlines
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPrivateAcceptedRoot
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting PqxdhJointKdfGame
open PqxdhChallengeSecretQueryBounds PqxdhAuthenticatedRootPrepareBounds
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf
open ENNReal
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)

/-- HB-111 with its replaced extracted steps bridged in the statement: the complete statement of `PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound` (bound and reached Server representation, same hypotheses) together with bridges B1-B8 and the accepted-branch acceptance bridge B9 at the same parameters. -/
theorem authenticated_native_root_bound_bridged
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    let p := protocol env kem attachedVerify primitives program post
    ((actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
      ∑ index ∈ Finset.range c.qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    (∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2) ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧
    AcceptBridge env baseImpl kem attachedVerify primitives program post secretIdentity := by
  intro p
  have original := PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound env baseImpl kem
    attachedVerify primitives program post c compatible adapter functional hmac sourceCorrect fallback
    ordinaryFallback secretIdentity initialMatch
  exact ⟨original.1, original.2, prepare_bridge, commit_bridge, beacon_start_bridge, beacon_commit_bridge,
    registration_id_bridge, commitment_transcript_bridge, send_finish_bridge, frame_payload_bridge,
    accept_bridge env baseImpl kem attachedVerify primitives program post secretIdentity initialMatch⟩

/-- HB-111 with every bridge proved here in the statement: `authenticated_native_root_bound_bridged` together with the validate_init_kex bridge B10. -/
theorem authenticated_native_root_bound_bridged_full
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    let p := protocol env kem attachedVerify primitives program post
    ((actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
      ∑ index ∈ Finset.range c.qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    (∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2) ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧
    AcceptBridge env baseImpl kem attachedVerify primitives program post secretIdentity ∧
    ValidateInitBridge := by
  intro p
  have bridged := authenticated_native_root_bound_bridged env baseImpl kem attachedVerify primitives program post c
    compatible adapter functional hmac sourceCorrect fallback ordinaryFallback secretIdentity initialMatch
  exact ⟨bridged.1, bridged.2.1, bridged.2.2.1, bridged.2.2.2.1, bridged.2.2.2.2.1, bridged.2.2.2.2.2.1,
    bridged.2.2.2.2.2.2.1, bridged.2.2.2.2.2.2.2.1, bridged.2.2.2.2.2.2.2.2.1, bridged.2.2.2.2.2.2.2.2.2.1,
    bridged.2.2.2.2.2.2.2.2.2.2, validate_init_bridge⟩

/-- HB-111 for the experiment that executes the extracted acceptance on its accepted branch (`extractedActual`, whose accepted leaf runs `nativeAccept`, hence the extracted `server_accept` and `registration_id`), with the unchanged right-hand side, the reached Server representation and the bridges B1-B8 and B10. It holds under HB-111's own hypotheses. -/
theorem authenticated_extracted_root_bound
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    let p := protocol env kem attachedVerify primitives program post
    ((extractedActual env baseImpl kem attachedVerify primitives program post secretIdentity).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
      ∑ index ∈ Finset.range c.qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    (∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2) ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge := by
  intro p
  have original := PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound env baseImpl kem
    attachedVerify primitives program post c compatible adapter functional hmac sourceCorrect fallback
    ordinaryFallback secretIdentity initialMatch
  have same : (extractedActual env baseImpl kem attachedVerify primitives program post secretIdentity).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) =
      (actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
        (uniformGame (rootReduction env.source baseImpl kem p)) := by
    unfold ProbComp.boolDistAdvantage
    rw [actual_extracted env baseImpl kem attachedVerify primitives program post secretIdentity initialMatch]
  rw [same]
  exact ⟨original.1, original.2, prepare_bridge, commit_bridge, beacon_start_bridge, beacon_commit_bridge,
    registration_id_bridge, commitment_transcript_bridge, send_finish_bridge, frame_payload_bridge,
    validate_init_bridge⟩

variable (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)

/-- HB-112 with its replaced extracted steps bridged in the statement: the bound of `PqxdhAuthenticatedEvolvingSecrecy.bound` (same hypotheses) together with the unconditional bridges B1-B8. -/
theorem evolving_bound_bridged (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number
        ancestors disclosed).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) ≤
      PqxdhAuthenticatedEvolvingSecrecy.loss env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed c hmac fallback ordinaryFallback ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge :=
  ⟨PqxdhAuthenticatedEvolvingSecrecy.bound env baseImpl kem attachedVerify primitives program post selected
      number ancestors disclosed c positive compatible adapter functional hmac correct fallback ordinaryFallback,
    prepare_bridge, commit_bridge, beacon_start_bridge, beacon_commit_bridge, registration_id_bridge,
    commitment_transcript_bridge, send_finish_bridge, frame_payload_bridge⟩

/-- HB-112 with every bridge proved here in the statement: the bound of `PqxdhAuthenticatedEvolvingSecrecy.bound` (same hypotheses) together with B1-B8, the validate_init_kex bridge B10 and the accepted-branch acceptance bridge B11. B11 is stated under the additional representation premises `secretIdentity` and `initialMatch` of HB-111, which the bound itself does not use. -/
theorem evolving_bound_bridged_full (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number
        ancestors disclosed).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) ≤
      PqxdhAuthenticatedEvolvingSecrecy.loss env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed c hmac fallback ordinaryFallback ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge ∧
    EvolvingAcceptBridge env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
      secretIdentity :=
  ⟨PqxdhAuthenticatedEvolvingSecrecy.bound env baseImpl kem attachedVerify primitives program post selected
      number ancestors disclosed c positive compatible adapter functional hmac correct fallback ordinaryFallback,
    prepare_bridge, commit_bridge, beacon_start_bridge, beacon_commit_bridge, registration_id_bridge,
    commitment_transcript_bridge, send_finish_bridge, frame_payload_bridge, validate_init_bridge,
    evolving_accept_bridge env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
      secretIdentity initialMatch⟩

/-- HB-112 for the experiment that executes the extracted acceptance on its accepted branch (`extractedEvolvingActual`, whose registration step is `frontAccept`, hence the extracted `server_accept` and `registration_id`), with the unchanged ideal and loss and the bridges B1-B8 and B10. Besides HB-112's hypotheses it uses HB-111's representation premises `secretIdentity` and `initialMatch`. -/
theorem evolving_extracted_bound (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    (extractedEvolvingActual env baseImpl kem attachedVerify primitives program post selected number ancestors
        disclosed secretIdentity).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) ≤
      PqxdhAuthenticatedEvolvingSecrecy.loss env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed c hmac fallback ordinaryFallback ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge := by
  have original := PqxdhAuthenticatedEvolvingSecrecy.bound env baseImpl kem attachedVerify primitives program post
    selected number ancestors disclosed c positive compatible adapter functional hmac correct fallback ordinaryFallback
  have same : (extractedEvolvingActual env baseImpl kem attachedVerify primitives program post selected number
      ancestors disclosed secretIdentity).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) =
      (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number
        ancestors disclosed).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) := by
    unfold ProbComp.boolDistAdvantage
    rw [evolving_actual_extracted env baseImpl kem attachedVerify primitives program post selected number ancestors
      disclosed secretIdentity initialMatch]
  rw [same]
  exact ⟨original, prepare_bridge, commit_bridge, beacon_start_bridge, beacon_commit_bridge, registration_id_bridge,
    commitment_transcript_bridge, send_finish_bridge, frame_payload_bridge, validate_init_bridge⟩

end Headlines

end BeaconcryptCore.Computational.PqxdhHeadlineBridges

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.prepare_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.prepare_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.commit_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.commit_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.beacon_start_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.beacon_start_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.beacon_commit_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.beacon_commit_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.registration_id_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.registration_id_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.array_of_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.array_of_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.commitment_transcript_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.commitment_transcript_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.send_finish_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.send_finish_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.frame_payload_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.frame_payload_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.accept_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.accept_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.actual_extracted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.actual_extracted

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.typedVerified_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.typedVerified_injective

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.vectorOfLength?_absBytes32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.vectorOfLength?_absBytes32

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.vectorOfLength?_absBytes1184' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.vectorOfLength?_absBytes1184

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.validate_init_kex_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.validate_init_kex_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.validate_init_kex_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.validate_init_kex_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.parsedBytes_widths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.parsedBytes_widths

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.parsedBytes_accept_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.parsedBytes_accept_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.parsedBytes_reject_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.parsedBytes_reject_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.sourceAccept_parsed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.sourceAccept_parsed

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.validate_init_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.validate_init_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.accept_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.accept_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.pendingBuild_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.pendingBuild_used

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.front_accept_eq_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.front_accept_eq_build

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_accept_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_accept_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_actual_extracted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_actual_extracted

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.authenticated_native_root_bound_bridged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.authenticated_native_root_bound_bridged

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.authenticated_native_root_bound_bridged_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.authenticated_native_root_bound_bridged_full

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.authenticated_extracted_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.authenticated_extracted_root_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_bound_bridged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_bound_bridged

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_bound_bridged_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_bound_bridged_full

/-- info: 'BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_extracted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHeadlineBridges.evolving_extracted_bound
