import BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation
import BeaconcryptCore.Computational.PqxdhAcceptedRegistration
import BeaconcryptCore.Computational.RawCtxSourceHkdf
import BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting

/-!
Fixed-width native Phase2 arrays retain the same bytes in the computational KEM and root interfaces. Conversion does not normalize curve encodings, replace DH values or introduce key injectivity. The source root callback remains the original no-salt fixed HKDF evaluated at the actual constructed 192-byte input.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open PqxdhRefinement BeaconcryptCore.Refinement.ProtocolComposition
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2InputBytes
open PqxdhRootTableInitialization (rootArray)
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
open PqxdhKemIndCca PqxdhHiddenRoot PqxdhSecretInputKdf

def word (value : Word32) : List.Vector UInt8 32 :=
  ⟨absBytes value, by simp⟩

def ciphertext (value : Ciphertext) : MlKem768Ciphertext :=
  ⟨absBytes value, by simp⟩

/-- Interpreting an actual native word and returning it to the core preserves every original byte. -/
theorem word_roundtrip (value : Word32) : rootArray (word value) = value := by
  apply Subtype.ext
  apply (absBytes_inj_iff _ _).mp
  rw [PqxdhRootTableInitialization.rootArray_bytes]
  rfl

/-- The computational word is exactly the supplied word when transported through the native array. -/
theorem word_rootArray (value : List.Vector UInt8 32) : word (rootArray value) = value := by
  apply List.Vector.toList_injective
  exact PqxdhRootTableInitialization.rootArray_bytes value

/-- Ciphertext conversion preserves the exact 1088 bytes in both directions, including arbitrary attacker input. -/
theorem ciphertext_roundtrip (value : Ciphertext) (typed : MlKem768Ciphertext) :
    PqxdhAcceptedRegistration.ciphertextArray (ciphertext value) = value ∧
      ciphertext (PqxdhAcceptedRegistration.ciphertextArray typed) = typed := by
  constructor
  · apply Subtype.ext
    apply (absBytes_inj_iff _ _).mp
    exact PqxdhAcceptedRegistration.ciphertextArray_bytes (ciphertext value)
  · apply List.Vector.toList_injective
    exact PqxdhAcceptedRegistration.ciphertextArray_bytes typed

/-- These four coordinates are the actual native DH replies in source order. -/
def coordinates (dh1 dh2 dh3 dh4 : Word32) : KnownPqxdhRootCoordinates :=
  ⟨word dh1, word dh2, word dh3, word dh4⟩

/-- Actual successful source construction identifies the full 192-byte input used by the private root family. -/
theorem root_input (secrets : pqxdh.PqxdhSharedSecrets) (input : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input secrets = ok (.Ok input)) :
    absBytes input.bytes = hiddenRootIKM
      (coordinates secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4) (word secrets.kem_shared_secret) := by
  classical
  by_cases valid : Pqxdh.dhNonZero (absBytes secrets.dh1, absBytes secrets.dh2,
      absBytes secrets.dh3, absBytes secrets.dh4)
  · obtain ⟨actual, generated, bytes⟩ := (build_root_key_input_abs secrets).1 valid
    rw [built] at generated
    cases generated
    exact bytes
  · have rejected := (build_root_key_input_abs secrets).2 valid
    rw [built] at rejected
    cases rejected

/-- The native fixed-HKDF root callback is exactly the root-family function at that same successful source input. -/
theorem root_response (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (secrets : pqxdh.PqxdhSharedSecrets) (input : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input secrets = ok (.Ok input)) :
    RawCtxSourceHkdf.rootResponse source.crypto input =
      rootArray (productionHiddenRoot source
        (coordinates secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4) (word secrets.kem_shared_secret)) := by
  apply Subtype.ext
  apply (absBytes_inj_iff _ _).mp
  rw [RawCtxSourceHkdf.rootResponse_law, PqxdhRootTableInitialization.rootArray_bytes,
    root_input secrets input built]
  rfl

open PqxdhPhase2DecapsulationRouting
open PqxdhChallengeSecretRouting
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Mathematical native interpretation of the retained private handle and original DH values. -/
def secrets (supplied : MlKemSharedSecret) (shared : Shared) (dh1 dh2 dh3 dh4 : Word32) :
    pqxdh.PqxdhSharedSecrets :=
  ⟨dh1, dh2, dh3, dh4, rootArray (materialize supplied shared)⟩

/-- Private root invocation receives only its opaque handle and actual four source coordinates. -/
noncomputable def rootCall (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (shared : Shared) (dh1 dh2 dh3 dh4 : Word32) :
    OracleComp (LocalPostSpec baseSpec) (Option Word32) :=
  Option.map rootArray <$> derive source challenge shared (coordinates dh1 dh2 dh3 dh4)

/-- The typed private root request returns the actual source fixed-HKDF response at the constructed input. -/
theorem rootCall_native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (shared : Shared) (dh1 dh2 dh3 dh4 : Word32) (input : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input (secrets supplied shared dh1 dh2 dh3 dh4) = ok (.Ok input)) :
    simulateQ (actualImpl source kem secret challenge) (rootCall source challenge shared dh1 dh2 dh3 dh4) =
      pure (some (RawCtxSourceHkdf.rootResponse source.crypto input)) := by
  rw [rootCall, simulateQ_map, derive_native source kem secret challenge supplied agreement,
    map_pure, Option.map_some, root_response source _ input built]
  simp only [secrets, word_rootArray]

/-- Native ciphertext bytes select the private decapsulation callback without a new parse or normalization. -/
noncomputable def decapCall (challenge : MlKem768Ciphertext) (value : Ciphertext) :
    OracleComp (LocalPostSpec baseSpec) (Option Shared) :=
  decapsulate challenge (ciphertext value)

/-- The original native optional KEM result is retained through exact byte transport. -/
theorem decapCall_native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied)) (value : Ciphertext) :
    Option.map (fun shared => rootArray (materialize supplied shared)) <$>
      simulateQ (actualImpl source kem secret challenge) (decapCall challenge value) =
        Option.map rootArray <$> kem.decaps secret (ciphertext value) := by
  simpa only [decapCall, Functor.map_map, Option.map_map, Function.comp_def] using
    congrArg (Functor.map (Option.map rootArray))
      (decapsulate_native source kem secret challenge supplied agreement (ciphertext value))

/-- The ordinary CCA reduction produces the same typed root while keeping the supplied challenge secret inside its interpreter. -/
theorem rootCall_reduction (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (shared : Shared) (dh1 dh2 dh3 dh4 : Word32) :
    simulateQ (route (baseSpec := baseSpec) source challenge supplied)
      (rootCall source challenge shared dh1 dh2 dh3 dh4) =
        pure (some (rootArray (productionHiddenRoot source (coordinates dh1 dh2 dh3 dh4)
          (materialize supplied shared)))) := by
  rw [rootCall, simulateQ_map, derive_reduction, map_pure, Option.map_some]

/-- Typed byte transport adds no oracle request and retains the exact selected decapsulation allowance. -/
theorem decapCall_bound (challenge : MlKem768Ciphertext) (value : Ciphertext)
    (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    (decapCall (baseSpec := baseSpec) challenge value).IsQueryBoundP predicate
      (if ciphertext value = challenge then 0 else if predicate (.inl (.inr (ciphertext value))) then 1 else 0) :=
  decapsulate_bound challenge (ciphertext value) predicate

/-- Exactly one matching private-root request is charged; byte transport preserves every query class. -/
theorem rootCall_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (shared : Shared) (dh1 dh2 dh3 dh4 : Word32)
    (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    (rootCall (baseSpec := baseSpec) source challenge shared dh1 dh2 dh3 dh4).IsQueryBoundP predicate
      (match shared with
       | .challenge => if predicate (.inr ⟨challenge, coordinates dh1 dh2 dh3 dh4⟩) then 1 else 0
       | .known _ => 0) := by
  exact (isQueryBoundP_map_iff (p := predicate) _ (Option.map rootArray) _).mpr
    (derive_bound source challenge shared (coordinates dh1 dh2 dh3 dh4) predicate)

end BeaconcryptCore.Computational.PqxdhPhase2InputBytes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.word_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.word_roundtrip

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.word_rootArray' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.word_rootArray

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.ciphertext_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.ciphertext_roundtrip

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.root_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.root_input

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.root_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.root_response

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.rootCall_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.rootCall_native

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.decapCall_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.decapCall_native

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.rootCall_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.rootCall_reduction

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.decapCall_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.decapCall_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2InputBytes.rootCall_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2InputBytes.rootCall_bound
