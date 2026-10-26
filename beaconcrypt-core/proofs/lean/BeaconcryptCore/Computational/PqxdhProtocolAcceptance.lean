import BeaconcryptCore.Computational.PqxdhProtocolServerInvariant

/-!
Three source-boundary statements derive the actual extracted acceptance token from the same typed verified candidate, source ephemeral/KEM outputs and selected stored Server identity. The source nonzero branch supplies the core check; exact acceptance derives the original 192-byte root input and registration ID. The response builder then consumes that exact ID in the reached state and uses the actual pending fields with a supplied root. The root is arbitrary here to allow comparison worlds; source root derivation is connected in PqxdhProtocolNativeAcceptance. Typed VerifiedInitKex is supplied by the preceding verification path, not an assertion that arbitrary supplied keys are authenticated.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.ProtocolComposition
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhProtocolAcceptance
open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhHiddenRoot PqxdhSourceAuthenticatedRoot
open PqxdhPrivateAcceptedRoot PqxdhRefinement
open PqxdhRootTableInitialization (rootArray)

/-- The accepted typed fields become the same fixed-width core verification result; no key is replaced or normalized. -/
def verified (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) : pqxdh.VerifiedInitKex :=
  ⟨rootArray identity, rootArray keys.prekey, rootArray keys.oneTime,
    ⟨keys.pqKey.toList.map concreteByte, by simp⟩⟩

/-- Source coins retain the exact public ephemeral mapping and original ciphertext. -/
def nativeCoins (c : Pqxdh.Crypto) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) : pqxdh.ServerCoins :=
  ⟨rootArray ⟨c.xpub ephemeral.toList, c.xpub_length _⟩,
    PqxdhAcceptedRegistration.ciphertextArray ciphertext⟩

/-- All five actual primitive outputs retain their bytes and source order in the core acceptance input. -/
def shared (coordinates : KnownPqxdhRootCoordinates) (secret : MlKemSharedSecret) : pqxdh.PqxdhSharedSecrets :=
  ⟨rootArray coordinates.dh1, rootArray coordinates.dh2, rootArray coordinates.dh3,
    rootArray coordinates.dh4, rootArray secret⟩

/-- The source conversion/nonzero branch supplies the actual core nonzero check, independently of the KEM contribution. -/
theorem coordinates_valid (c : Pqxdh.Crypto) (server : Pqxdh.ServerState)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (ephemeral : List.Vector UInt8 32)
    (secret : MlKemSharedSecret)
    (valid : rootFailure c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime = none) :
    Pqxdh.dhNonZero (absDHs (shared
      (serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)) := by
  cases conversion : c.xpkConv identity.toList with
  | none => simp [rootFailure, conversion] at valid
  | some converted =>
      have nonzero : Pqxdh.dhNonZero (Pqxdh.serverDHs c server.ikSk ephemeral.toList converted
          keys.prekey.toList keys.oneTime.toList) := by
        simpa [rootFailure, conversion] using valid
      have coordinatesEq :
          ((serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime).dh1.toList,
            (serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime).dh2.toList,
            (serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime).dh3.toList,
            (serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime).dh4.toList) =
            Pqxdh.serverDHs c server.ikSk ephemeral.toList converted keys.prekey.toList
              keys.oneTime.toList := by
        simp [serverCoordinates, conversion, Pqxdh.serverDHs]
      simp only [absDHs, shared]
      rw [PqxdhRootTableInitialization.rootArray_bytes,
        PqxdhRootTableInitialization.rootArray_bytes,
        PqxdhRootTableInitialization.rootArray_bytes,
        PqxdhRootTableInitialization.rootArray_bytes, coordinatesEq]
      exact nonzero

variable {M P I D K A : Type} {S B : Nat}

/-- The source replay lookup uses the actual reached consumed set before the core accepts any pending registration. -/
def status (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (consumed : List Pqxdh.Bytes) :
    pqxdh.RegistrationStatus :=
  if identity.toList ++ keys.oneTime.toList ∈ consumed then .Consumed else .Fresh

/-- The actual acceptance input reads the selected Server's stored private identity and fixed public binding. -/
def accept (c : Pqxdh.Crypto) (secretIdentity : M → Pqxdh.Bytes) (senderId : M → Std.U64)
    (index : Fin S) (metadata : P) (state : PqxdhRegistrationProtocolState.State M P I D K A S B)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret) :=
  pqxdh.server_accept (state.controls index) (verified identity keys)
    (status identity keys (state.consumed index))
    (PqxdhRegistrationProtocolState.input senderId index metadata state).binding
    (nativeCoins c ephemeral ciphertext)
    (shared (serverCoordinates c (secretIdentity (state.roles.1.1 index).server.metadata)
      ephemeral.toList identity keys.prekey keys.oneTime) secret)

/-- Fresh successful source conversion/DH constructs an actual pending token; acceptance is derived, not assumed. -/
theorem fresh_acceptance (c : Pqxdh.Crypto) (secretIdentity : M → Pqxdh.Bytes) (senderId : M → Std.U64)
    (index : Fin S) (metadata : P) (state : PqxdhRegistrationProtocolState.State M P I D K A S B)
    (server : Pqxdh.ServerState)
    (related : PqxdhProtocolServerInvariant.RootFields c secretIdentity senderId index server state)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret)
    (fresh : identity.toList ++ keys.oneTime.toList ∉ server.consumed)
    (valid : rootFailure c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime = none) :
    ∃ pending, accept c secretIdentity senderId index metadata state identity keys ephemeral ciphertext secret =
        ok (.Ok (state.controls index, pending)) ∧
      absBytes pending.root_key_input.bytes = hiddenRootIKM
        (serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret ∧
      absBytes pending.registration_id.bytes = identity.toList ++ keys.oneTime.toList := by
  obtain ⟨root, rootEq, rootBytes⟩ := (build_root_key_input_abs (shared
    (serverCoordinates c server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)).1
      (coordinates_valid c server identity keys ephemeral secret valid)
  obtain ⟨rid, ridEq, ridBytes⟩ := registration_id_abs (verified identity keys)
  refine ⟨⟨(PqxdhRegistrationProtocolState.input senderId index metadata state).binding, rid,
    (verified identity keys).beacon_identity_public_key, (nativeCoins c ephemeral ciphertext).ephemeral_public_key,
    (nativeCoins c ephemeral ciphertext).kem_ciphertext, root⟩, ?_, ?_, ?_⟩
  case refine_1 =>
    simp [accept, status, related.1, related.2.2.2.2, fresh,
      pqxdh.server_accept, pqxdh.validate_registration_status, rootEq, ridEq]
  case refine_2 =>
    simpa only [shared, hiddenRootIKM, PqxdhRootTableInitialization.rootArray_bytes] using rootBytes
  case refine_3 =>
    simpa only [Pqxdh.ValidInit.rid, verified, PqxdhRootTableInitialization.rootArray_bytes] using ridBytes

/-- Actual source acceptance supplies the pending token, exact root input and fresh consumed update used by the reached native builder. -/
theorem accepted_builder
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (secretIdentity : M → Pqxdh.Bytes) (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) (server : Pqxdh.ServerState)
    (related : PqxdhProtocolServerInvariant.RootFields source.crypto secretIdentity senderId index server state)
    (application : Option Pqxdh.Bytes) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret)
    (root : PqxdhSecretInputKdf.RootOutput)
    (fresh : identity.toList ++ keys.oneTime.toList ∉ server.consumed)
    (valid : rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime = none) :
    ∃ pending,
      accept source.crypto secretIdentity senderId index metadata state identity keys ephemeral ciphertext secret =
        ok (.Ok (state.controls index, pending)) ∧
      absBytes pending.root_key_input.bytes = hiddenRootIKM
        (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret ∧
      PqxdhRegistrationProtocolState.consume index
        (ready server application identity keys.oneTime ephemeral ciphertext root) state =
          { state with
            consumed := Function.update state.consumed index
              (absBytes pending.registration_id.bytes :: state.consumed index) } ∧
      (PqxdhRegistrationProtocolState.build source writer aux senderId index metadata
        (ready server application identity keys.oneTime ephemeral ciphertext root)).run state =
        (PqxdhRegistrationProtocolState.nativeBuild source writer aux senderId index metadata pending root application).run
          { state with
            consumed := Function.update state.consumed index
              (absBytes pending.registration_id.bytes :: state.consumed index) } := by
  obtain ⟨pending, accepted, inputBytes, ridBytes⟩ := fresh_acceptance source.crypto secretIdentity senderId
    index metadata state server related identity keys ephemeral ciphertext secret fresh valid
  have used := (PqxdhRegistrationInputs.accepted_used _ _ _ _ _ _ _ pending accepted).2
  have builder := PqxdhRegistrationProtocolState.build_native source writer aux senderId index metadata
    (ready server application identity keys.oneTime ephemeral ciphertext root) state pending used
  refine ⟨pending, accepted, inputBytes, ?_, ?_⟩
  · simp only [PqxdhRegistrationProtocolState.consume, ready, ridBytes, related.2.2.2.2]
  · simpa only [PqxdhRegistrationProtocolState.consume, ready, ridBytes, related.2.2.2.2] using builder

end BeaconcryptCore.Computational.PqxdhProtocolAcceptance

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolAcceptance.coordinates_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolAcceptance.coordinates_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolAcceptance.fresh_acceptance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolAcceptance.fresh_acceptance

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolAcceptance.accepted_builder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolAcceptance.accepted_builder
