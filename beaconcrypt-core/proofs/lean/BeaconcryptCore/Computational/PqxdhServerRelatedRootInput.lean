import BeaconcryptCore.Computational.PqxdhServerStaticDhSource

/-!
The actual reached Server prefix supplies an executable related-root request containing its received prekey encoding and its locally generated DH2, DH3, DH4 and KEM outputs. The selected static-DH coordinate remains private to the joint primitive interpreter. The request's realized bytes are the exact extracted root builder's 192-byte input; no raw public-key injectivity or independently distributed coordinate is assumed.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open PqxdhRefinement BeaconcryptCore.Refinement.ProtocolComposition
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerRelatedRootInput
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerRootPreparation PqxdhServerStaticDhSource
open PqxdhPhase2GapDhSource (peer)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhPhase2InputBytes (word)
open PqxdhRootTableInitialization (rootArray)

/-- The real selected static reply is determined by its reached public reference, without being part of the executable request. -/
theorem selected_value (joint : Primitives) (domain : PublicDomain joint) (seed : IdentitySeed)
    (reference : PeerEncoding) (admitted : domain.accepts reference = true) :
    joint.staticDh seed reference = some (word (materialize joint seed reference)) := by
  cases actual : joint.staticDh seed reference with
  | none => simpa only [actual, Option.isSome_none, admitted, Bool.false_eq_true] using domain.available seed reference
  | some value => simp only [materialize, actual, Option.getD_some, PqxdhPhase2InputBytes.word_rootArray]

def secrets {Reader E : Type} (input : Inputs Reader E Word32) : pqxdh.PqxdhSharedSecrets :=
  ⟨input.first, input.second, input.third, input.fourth, input.kem⟩

/-- Original prekey bytes and all actual locally held outputs form the ordinary Server-family request. There is no selected seed, hidden output or guessed plaintext in this request. -/
def message {Reader E : Type} (input : Inputs Reader E PeerEncoding) : PqxdhJointDhExtractFamily.Message :=
  PqxdhJointDhExtractRoot.serverMessage (peer (rootArray input.verified.keys.prekey))
    (word input.second) (word input.third) (word input.fourth) (word input.kem)

/-- The complete family address denotes exactly the source core's built192-byte root input, including aliases and all source-local coordinates. -/
theorem source_input (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Reader E : Type} (input : Inputs Reader E PeerEncoding)
    (references : References domain input) (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input (secrets (concreteInputs joint seed input)) = ok (.Ok root)) :
    PqxdhJointDhExtractFamily.input joint dh seed scalar (message input) = some (absBytes root.bytes) := by
  have bytes := PqxdhPhase2InputBytes.root_input _ root built
  have selected := selected_value joint domain seed input.first references.2
  rw [references.1] at selected
  rw [message, PqxdhJointDhExtractRoot.server_input, selected]
  simp only [Option.map_some]
  apply congrArg some
  simpa only [secrets, concreteInputs, PqxdhPhase2InputBytes.coordinates,
    PqxdhHiddenRoot.hiddenRootIKM, Pqxdh.pqxdhIKM, Pqxdh.padFF32, assemble, references.1] using bytes.symm

/-- A complete supported native prefix discharges the exact address references for the existing Extract family. Successful root construction remains the actual source branch test. -/
theorem reached_source_input (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Reader E A : Type}
    (aux : QueryImpl (Spec Reader E Unit) (StateT A ProbComp)) (visit : Word32 → StateT A ProbComp Unit)
    (raw : Pqxdh.Bytes) (initial final : A) (input : Inputs Reader E PeerEncoding)
    (reached : (some input, final) ∈ support ((simulateQ (prefixImpl domain aux visit) (collect raw)).run initial))
    (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input (secrets (concreteInputs joint seed input)) = ok (.Ok root)) :
    PqxdhJointDhExtractFamily.input joint dh seed scalar (message input) = some (absBytes root.bytes) :=
  source_input joint dh domain seed scalar input (collect_references domain aux visit raw initial final input reached) root built

/-- The existing joint primitive/source wiring already rejects an all-zero static-DH reply; this is a functional validity fact, not a security assumption. -/
theorem static_nonzero (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (seed : IdentitySeed) (reference : PeerEncoding) (value : DhOutput)
    (actual : joint.staticDh seed reference = some value) : value.toList ≠ Pqxdh.zero32 := by
  rw [wiring.staticDh, sourceDhReply] at actual
  split at actual
  · contradiction
  · cases Option.some.inj actual
    assumption

/-- Only the three locally generated DH outputs remain in the source nonzero test; the unavailable static output is valid by the reached primitive interface. -/
def localNonzero {Reader E : Type} (input : Inputs Reader E PeerEncoding) : Prop :=
  absBytes input.second ≠ Pqxdh.zero32 ∧ absBytes input.third ≠ Pqxdh.zero32 ∧ absBytes input.fourth ≠ Pqxdh.zero32

/-- The executable local validity test agrees with the actual extracted root-builder admission at every reached private-static input. -/
theorem source_nonzero (c : Pqxdh.Crypto) (joint : Primitives) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (seed : IdentitySeed) {Reader E : Type} (input : Inputs Reader E PeerEncoding)
    (references : References domain input) :
    Pqxdh.dhNonZero (absBytes (materialize joint seed input.first), absBytes input.second,
      absBytes input.third, absBytes input.fourth) ↔ localNonzero input := by
  have valid := static_nonzero c joint secretOfSeed wiring seed input.first
    (word (materialize joint seed input.first)) (selected_value joint domain seed input.first references.2)
  change absBytes (materialize joint seed input.first) ≠ Pqxdh.zero32 at valid
  exact ⟨fun all => all.2, fun known => ⟨valid, known⟩⟩

/-- The existing real root endpoint returns the exact native source root from the extracted input, preserving its full actual PRK/HMAC history and memoization cache. -/
theorem root_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Reader E : Type} (input : Inputs Reader E PeerEncoding)
    (references : References domain input) (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input (secrets (concreteInputs joint seed input)) = ok (.Ok root))
    (state : PqxdhJointDhExtractFamily.State) :
    (simulateQ (PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar)
      (PqxdhJointDhExtractRoot.root (message input))).run state =
      pure (some (PqxdhJointDhExtractRoot.nativeRoot source (absBytes root.bytes)),
        PqxdhJointDhExtractRoot.rootState hmac (message input) (absBytes root.bytes) state) := by
  rw [PqxdhJointDhExtractRoot.root_real source hmac correct]
  simp only [PqxdhJointDhExtractRoot.sourceRoot, StateT.run,
    source_input joint dh domain seed scalar input references root built]


/-- The source tail reads exactly these received/locally generated public fields, independent of the unavailable root input. -/
def metadata {Reader E Shared : Type} (binding : pqxdh.ServerBinding) (input : Inputs Reader E Shared) :
    PqxdhRegistrationInputs.UsedInput :=
  ⟨binding, rootArray input.verified.identity, input.ephemeral.publicKey, input.ciphertext⟩

/-- Actual core acceptance after the prefix's stored Fresh status, using all five actual primitive outputs and original source public coins. -/
def accept {Reader E : Type} (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : Inputs Reader E Word32) :=
  pqxdh.server_accept control (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys)
    .Fresh binding ⟨input.ephemeral.publicKey, input.ciphertext⟩ (secrets input)

/-- Public native availability plus the three actual local nonzero checks derive real extracted acceptance, its precise192-byte root input and registration ID. -/
theorem accept_success (c : Pqxdh.Crypto) (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Reader E : Type} (input : Inputs Reader E PeerEncoding)
    (references : References domain input) (valid : localNonzero input)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) :
    ∃ pending, accept control binding (concreteInputs joint seed input) = ok (.Ok (control, pending)) ∧
      PqxdhRegistrationInputs.used pending = metadata binding input ∧
      PqxdhJointDhExtractFamily.input joint dh seed scalar (message input) = some (absBytes pending.root_key_input.bytes) ∧
      absBytes pending.registration_id.bytes = registrationId input.verified := by
  have nonzero := (source_nonzero c joint domain secretOfSeed wiring seed input references).mpr valid
  obtain ⟨root, built, _⟩ := (build_root_key_input_abs (secrets (concreteInputs joint seed input))).1 nonzero
  obtain ⟨rid, ridEq, ridBytes⟩ := registration_id_abs
    (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys)
  refine ⟨⟨binding, rid, rootArray input.verified.identity, input.ephemeral.publicKey, input.ciphertext, root⟩, ?_, rfl,
    source_input joint dh domain seed scalar input references root built, ?_⟩
  · simp only [concreteInputs] at built
    simp [accept, concreteInputs, pqxdh.server_accept, pqxdh.validate_registration_status, built, ridEq]
    rfl
  · simpa only [Pqxdh.ValidInit.rid, PqxdhProtocolAcceptance.verified,
      PqxdhRootTableInitialization.rootArray_bytes, registrationId] using ridBytes

/-- A rejected local DH test gives the actual extracted InvalidDhOutput branch; it is not converted into a related-root request. -/
theorem accept_failure (c : Pqxdh.Crypto) (joint : Primitives) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (seed : IdentitySeed) {Reader E : Type} (input : Inputs Reader E PeerEncoding)
    (references : References domain input) (invalid : ¬ localNonzero input)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) :
    accept control binding (concreteInputs joint seed input) = ok (.Err pqxdh.RegistrationError.InvalidDhOutput) := by
  have nonzero := mt (source_nonzero c joint domain secretOfSeed wiring seed input references).mp invalid
  have rejected := (build_root_key_input_abs (secrets (concreteInputs joint seed input))).2 nonzero
  simp [accept, pqxdh.server_accept, pqxdh.validate_registration_status, rejected]

/-- The accepted full native pending value runs the existing source response tail through exactly its used public fields, preserving the complete tail program. -/
theorem accepted_tail {Reader E Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (input : Inputs Reader E Word32)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (pending : pqxdh.PendingServerRegistration)
    (accepted : accept control binding input = ok (.Ok (control, pending)))
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes) (peerMetadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhServerRegistrationPublication.build source pending root data peerMetadata state =
      PqxdhRegistrationInputs.build source (metadata binding input) root data peerMetadata state := by
  have fields := (PqxdhRegistrationInputs.accepted_used control control
    (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys) .Fresh binding
    ⟨input.ephemeral.publicKey, input.ciphertext⟩ (secrets input) pending accepted).2
  rw [← PqxdhRegistrationInputs.build_exact, fields]
  rfl


end BeaconcryptCore.Computational.PqxdhServerRelatedRootInput

/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.selected_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.selected_value
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.source_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.source_input
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.reached_source_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.reached_source_input
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.static_nonzero' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.static_nonzero
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.source_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.source_nonzero
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.root_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.accept_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.accept_success
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.accept_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.accept_failure
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.accepted_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootInput.accepted_tail
