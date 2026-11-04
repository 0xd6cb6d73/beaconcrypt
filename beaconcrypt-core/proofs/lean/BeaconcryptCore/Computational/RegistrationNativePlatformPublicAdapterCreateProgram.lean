-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint
/-! The constructor's five individual primitive stages form a small free query tree. Its interpretation is the existing joint constructor, including the original caller RNG on ML rejection and the actual private KEM receipt on success. This tree is only analysis syntax for proving the physical source interpreter; it does not replace a runtime method. -/
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

abbrev Spec (source : RegistrationNativeMldsa.Source) (R : Type) :=
  (R →ₒ (Option (RegistrationNativeMldsa.Credential source) × R)) +
  ((registration.HashRequest →ₒ CtxRomAuth.CtxDigest) +
  ((R →ₒ (PqxdhJointIdentity.IdentitySeed × R)) +
  ((R →ₒ (PqxdhJointGapDh.ScalarBytes × R)) + (R →ₒ AdapterBeaconConstructorKem.Receipt R))))

def prepare (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    OracleComp (Spec source R) (Option (Prepared source) × R) := do
  let generated ← (Spec source R).query (.inl rng)
  match generated.1 with
  | none => pure (none,generated.2)
  | some credentials =>
    let digest ← (Spec source R).query (.inr (.inl (.Single (Std.Array.to_slice mlPin))))
    let identity ← (Spec source R).query (.inr (.inr (.inl generated.2)))
    let prekey ← (Spec source R).query (.inr (.inr (.inr (.inl identity.2))))
    pure (some ⟨credentials,RegistrationNativeBeaconCreateProgram.pin edPin mlPin keyId digest,identity.1,prekey.1⟩,prekey.2)

def program (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    OracleComp (Spec source R) (Option (AdapterBeaconConstructorJoint.Capture source R) × R) := do
  let prepared ← prepare edPin mlPin keyId rng
  match prepared.1 with
  | none => pure (none,prepared.2)
  | some ready =>
    let kem ← (Spec source R).query (.inr (.inr (.inr (.inr prepared.2))))
    pure (some (ready,kem),kem.rng)

variable {m : Type → Type} [Monad m] [LawfulMonad m]
def handler (ml : R → m (Option (RegistrationNativeMldsa.Credential source) × R))
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (ed : R → m (PqxdhJointIdentity.IdentitySeed × R))
    (kx : R → m (PqxdhJointGapDh.ScalarBytes × R))
    (kem : R → m (AdapterBeaconConstructorKem.Receipt R)) : QueryImpl (Spec source R) m
  | .inl rng => ml rng
  | .inr (.inl request) => hash request
  | .inr (.inr (.inl rng)) => ed rng
  | .inr (.inr (.inr (.inl rng))) => kx rng
  | .inr (.inr (.inr (.inr rng))) => kem rng

variable [primitive : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (AdapterPublicWrapperRustT.RustT m)]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT m)]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT m)]
variable {KemSK Error : Type}
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (mlSample : m (Option (RegistrationNativeMldsa.Credential source)))
variable (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view mlSample)
variable (jointKeys : PqxdhJointIdentity.Primitives) (edSample : m PqxdhJointIdentity.IdentitySeed)
variable (ed : AdapterBeaconConstructorGeneration.EdContract generator view jointKeys edSample)
variable (kxPublic : PqxdhJointGapDh.ScalarBytes → Std.Array U8 32#usize) (kxSample : m PqxdhJointGapDh.ScalarBytes)
variable (kx : AdapterBeaconConstructorGeneration.KxContract generator view kxPublic kxSample)
variable (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
variable (kem : R → m (AdapterBeaconConstructorKem.Receipt R))

omit children in
theorem prepare_source (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    simulateQ (handler ml.joint hash ed.joint kx.joint kem) (prepare edPin mlPin keyId rng) =
      AdapterBeaconConstructorPrepare.joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash edPin mlPin keyId rng := by
  unfold prepare AdapterBeaconConstructorPrepare.joint
  simp only [simulateQ_bind,simulateQ_spec_query,handler]
  apply bind_congr
  rintro ⟨generated,afterMl⟩
  cases generated <;> simp only [simulateQ_pure,simulateQ_bind,simulateQ_spec_query,handler]
  rfl

omit children in
theorem joint_source (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    simulateQ (handler ml.joint hash ed.joint kx.joint kem) (program edPin mlPin keyId rng) =
      AdapterBeaconConstructorJoint.joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash kem edPin mlPin keyId rng := by
  unfold program AdapterBeaconConstructorJoint.joint
  rw [simulateQ_bind,prepare_source generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash kem]
  apply bind_congr
  rintro ⟨prepared,afterPrepare⟩
  cases prepared <;> simp only [simulateQ_pure,simulateQ_bind,simulateQ_spec_query,handler]
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
