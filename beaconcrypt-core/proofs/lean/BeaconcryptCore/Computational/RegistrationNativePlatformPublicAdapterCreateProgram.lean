-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint
/-! The current constructor selects the complete supplied Server pin purely, then performs its Ed, X25519 and KEM sampler stages. This free query tree retains the exact caller RNG and private KEM receipt and interprets to the existing joint constructor. It is analysis syntax for the physical source proof. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateProgram
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Prepared)
variable [material : PublicWrapperPlatform.Material]
variable {R : Type} {source : RegistrationNativeMldsa.Source}

abbrev Spec (R : Type) :=
  (R →ₒ (PqxdhJointIdentity.IdentitySeed × R)) +
  ((R →ₒ (PqxdhJointGapDh.ScalarBytes × R)) + (R →ₒ AdapterBeaconConstructorKem.Receipt R))

def prepare (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    OracleComp (Spec R) (Option (Prepared source) × R) := do
  let identity ← (Spec R).query (.inl rng)
  let prekey ← (Spec R).query (.inr (.inl identity.2))
  pure (some ⟨RegistrationNativeBeaconCreateProgram.pin edPin mlPin keyId, identity.1, prekey.1⟩, prekey.2)

def program (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    OracleComp (Spec R) (Option (AdapterBeaconConstructorJoint.Capture source R) × R) := do
  let prepared ← prepare (source := source) edPin mlPin keyId rng
  match prepared.1 with
  | none => pure (none, prepared.2)
  | some ready =>
    let kem ← (Spec R).query (.inr (.inr prepared.2))
    pure (some (ready, kem), kem.rng)

variable {m : Type → Type} [Monad m] [LawfulMonad m]
def handler
    (ed : R → m (PqxdhJointIdentity.IdentitySeed × R))
    (kx : R → m (PqxdhJointGapDh.ScalarBytes × R))
    (kem : R → m (AdapterBeaconConstructorKem.Receipt R)) : QueryImpl (Spec R) m
  | .inl rng => ed rng
  | .inr (.inl rng) => kx rng
  | .inr (.inr rng) => kem rng

variable [primitive : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (AdapterPublicWrapperRustT.RustT m)]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT m)]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT m)]
variable {KemSK Error : Type}
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (jointKeys : PqxdhJointIdentity.Primitives) (edSample : m PqxdhJointIdentity.IdentitySeed)
variable (ed : AdapterBeaconConstructorGeneration.EdContract generator view jointKeys edSample)
variable (kxPublic : PqxdhJointGapDh.ScalarBytes → Std.Array U8 32#usize) (kxSample : m PqxdhJointGapDh.ScalarBytes)
variable (kx : AdapterBeaconConstructorGeneration.KxContract generator view kxPublic kxSample)
variable (kem : R → m (AdapterBeaconConstructorKem.Receipt R))

omit children in
theorem prepare_source (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    simulateQ (handler ed.joint kx.joint kem) (prepare (source := source) edPin mlPin keyId rng) =
      AdapterBeaconConstructorPrepare.joint generator view jointKeys edSample ed kxPublic kxSample kx edPin mlPin keyId rng := by
  simp only [prepare, AdapterBeaconConstructorPrepare.joint, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, handler]
  rfl

omit children in
theorem joint_source (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    simulateQ (handler ed.joint kx.joint kem) (program (source := source) edPin mlPin keyId rng) =
      AdapterBeaconConstructorJoint.joint generator view jointKeys edSample ed kxPublic kxSample kx kem edPin mlPin keyId rng := by
  unfold program AdapterBeaconConstructorJoint.joint
  rw [simulateQ_bind, prepare_source generator view jointKeys edSample ed kxPublic kxSample kx kem]
  apply bind_congr
  rintro ⟨prepared, afterPrepare⟩
  cases prepared <;> simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, handler]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateProgram.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateProgram.prepare_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateProgram.joint_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateProgram.joint_source
