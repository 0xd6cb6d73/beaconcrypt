-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorJoint
import BeaconcryptCore.Refinement.AdapterPublicWrapperPin
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The explicit post-constructor source getter/fingerprint continuation uses the actual shared identity and its selected key views. The source constructor alone does not perform this hash. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorPin
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT m)]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]
variable {mlSource : RegistrationNativeMldsa.Source} {KemSK R Error : Type}

theorem source (generator : rand_core.TryCryptoRng R Error)
    (view : MaterialView mlSource KemSK) (views : Views) (objects : AdapterServerConstructorObjects.Leaves views)
    (jointKeys : PqxdhJointIdentity.Primitives) (edSample : m (Option PqxdhJointIdentity.IdentitySeed))
    (ed : AdapterServerConstructorJoint.EdContract generator view jointKeys edSample)
    (mlSample : m (Option (RegistrationNativeMldsa.Credential mlSource)))
    (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view mlSample)
    (identifier : U64) (prepared : AdapterServerConstructorJoint.Prepared mlSource)
    (hash : QueryImpl RegistrationNativeServerPinRecompute.Spec m)
    (edGetter : ∀key,(crypto.edPublicBytes key).run=pure (.ok (view.edPublic key)))
    (mlGetter : ∀identity,(localOps.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))
    (hashLeaf : ∀request,(children.executeHash request).run=hash request) :
    (beaconcrypt_public_request.server.Server.authentication_pin (m:=RustT m)
      (AdapterServerConstructorJoint.object generator view views objects jointKeys edSample ed mlSample ml identifier prepared)).run=
      simulateQ hash (RegistrationNativeServerPinRecompute.program
        ⟨PqxdhRootTableInitialization.rootArray (jointKeys.publicKeys prepared.seed).ed25519,identifier⟩
        prepared.credential.publicKey) := by
  have key : platform.arcView (AdapterServerConstructorJoint.object generator view views objects jointKeys edSample ed mlSample ml identifier prepared).identity=
      (⟨ed.realize prepared.seed,ml.realize prepared.credential,identifier⟩ : beaconcrypt_public_wrapper.server.ServerIdentity) :=
    objects.shared_view _
  rw [AdapterPublicWrapperPin.server_program _
    (PqxdhRootTableInitialization.rootArray (jointKeys.publicKeys prepared.seed).ed25519)
    prepared.credential.publicKey hash]
  · simp only [key]
  · simpa only [key,ed.publicView] using edGetter (ed.realize prepared.seed).public_key
  · simpa only [key,ml.privateView] using mlGetter (ml.realize prepared.credential)
  · exact hashLeaf
end BeaconcryptCore.Refinement.AdapterServerConstructorPin

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorPin.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorPin.source
