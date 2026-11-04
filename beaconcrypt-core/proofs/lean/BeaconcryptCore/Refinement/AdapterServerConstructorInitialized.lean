-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorPin
import BeaconcryptCore.Refinement.AdapterServerConstructorStartup
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! This explicit source initialization continuation reifies only the Server-row metadata, then executes the actual source authentication_pin getter/hash program. The actual returned source object and RNG remain joint with the complete native startup state. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorInitialized
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK R Error : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations
  (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [localOps : LocalOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [crypto : CryptoOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [children : ChildOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
local notation "World" => PqxdhRecordLiftWorld.State n
local notation "M" => StateT World ProbComp

structure Ready (n : Nat) (KemSK R : Type) (mlSource : RegistrationNativeMldsa.Source) where
  stored : beaconcrypt_public_wrapper.server.Server
  rng : R
  initial : RegistrationNativeExperiment.Initial n KemSK mlSource

def created (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : MaterialView mlSource KemSK) (identityIndex : Nat) (identifier : U64)
    (self : beaconcrypt_public_wrapper.server.Server) : PqxdhLiveServerConstruction.Created Unit :=
  PqxdhLiveServerConstruction.initialized setup.joint identityIndex identifier .generated
    (view.edSecret (platform.arcView self.identity).identity_key.secret_key)

def credential (view : MaterialView mlSource KemSK) (self : beaconcrypt_public_wrapper.server.Server) :
    RegistrationNativeMldsa.Credential mlSource := view.mldsa (platform.arcView self.identity).mldsa_identity

def initial (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : MaterialView mlSource KemSK) (identityIndex : Nat) (identifier : U64)
    (self : beaconcrypt_public_wrapper.server.Server) (pin : session.ServerAuthenticationPin) (world : World) :
    RegistrationNativeExperiment.Initial n KemSK mlSource :=
  ⟨created setup view identityIndex identifier self,credential view self,
    ⟨⟨self.control,pin,[],[],⟨RegistrationServerRoleBackend.empty,[],[],(world,[])⟩⟩,[],PqxdhLiveKemBirth.empty,0⟩⟩

noncomputable def finish (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : MaterialView mlSource KemSK) (identityIndex : Nat) (identifier : U64)
    (self : beaconcrypt_public_wrapper.server.Server) (rng : R) : M (Option (Ready n KemSK R mlSource)) := fun before=>do
  let installed←(PqxdhRecordLiftWorld.initializeServer (created setup view identityIndex identifier self)).run before
  let pinned←((beaconcrypt_public_request.server.Server.authentication_pin (m:=RustT M) self).run).run installed.2
  pure ((match pinned.1 with
    | .ok (.Some pin)=>some ⟨self,rng,initial setup view identityIndex identifier self pin pinned.2⟩
    | _=>none),pinned.2)

theorem native (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (generator : rand_core.TryCryptoRng R Error) (view : MaterialView mlSource KemSK)
    (views : Views) (objects : AdapterServerConstructorObjects.Leaves views)
    (edSample : M (Option PqxdhJointIdentity.IdentitySeed))
    (ed : AdapterServerConstructorJoint.EdContract generator view setup.joint edSample)
    (mlSample : M (Option (RegistrationNativeMldsa.Credential mlSource)))
    (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view mlSample)
    (identityIndex : Nat) (identifier : U64) (prepared : AdapterServerConstructorJoint.Prepared mlSource)
    (rng : R) (before : World)
    (edGetter : ∀key,(crypto.edPublicBytes key).run=pure (.ok (view.edPublic key)))
    (mlGetter : ∀identity,(localOps.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))
    (hashLeaf : ∀request,(children.executeHash request).run=RegistrationNativeServerPinRecompute.nativeHash request) :
    (fun result=>(result.1.map Ready.initial,result.2)) <$>
      (finish setup view identityIndex identifier
        (AdapterServerConstructorJoint.object generator view views objects setup.joint edSample ed mlSample ml identifier prepared) rng).run before=
      (AdapterServerConstructorStartup.finish setup mlSource identityIndex identifier prepared).run before := by
  unfold finish
  rw [AdapterServerConstructorPin.source generator view views objects setup.joint edSample ed mlSample ml identifier prepared
    RegistrationNativeServerPinRecompute.nativeHash edGetter mlGetter hashLeaf]
  have shared : platform.arcView (AdapterServerConstructorJoint.object generator view views objects setup.joint edSample ed mlSample ml identifier prepared).identity=
      (⟨ed.realize prepared.seed,ml.realize prepared.credential,identifier⟩ : beaconcrypt_public_wrapper.server.ServerIdentity) := objects.shared_view _
  simp only [created,shared,ed.privateView,AdapterServerConstructorStartup.finish,
    RegistrationWorldServerFrontend.start,StateT.run,map_bind,map_pure,bind_assoc,pure_bind]
  apply bind_congr
  intro installed
  simp only [PqxdhLiveServerConstruction.initialized]
  have nativePin:=RegistrationWorldServerFrontend.initializePin_native
    (⟨PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys prepared.seed).ed25519,identifier⟩ : pqxdh.ServerBinding)
    prepared.credential.publicKey
    ((PqxdhJointDhExtractFamily.empty,
      ⟨RegistrationServerRoleBackend.empty,[],[],(installed.2,[])⟩) :
      RegistrationWorldServerReplay.Global n RegistrationServerRoleBackend.State)
  simp only [StateT.run] at nativePin
  rw [nativePin]
  have pinRun:=RegistrationNativeServerPinRecompute.native_run
    (⟨PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys prepared.seed).ed25519,identifier⟩ : pqxdh.ServerBinding)
    prepared.credential.publicKey installed.2
  change (simulateQ RegistrationNativeServerPinRecompute.nativeHash
    (RegistrationNativeServerPinRecompute.program
      ⟨PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys prepared.seed).ed25519,identifier⟩ prepared.credential.publicKey)).run installed.2=_ at pinRun
  simp only [StateT.run] at pinRun
  rw [pinRun]
  simp only [RegistrationWorldServerCompletion.capability,StateT.run,bind_map_left,bind_assoc,pure_bind]
  apply bind_congr
  intro hashed
  simp only [initial,created,credential,shared,ed.privateView,ml.privateView,
    RegistrationServerFrontendCompiler.erase,Option.map_some]
  rfl
end BeaconcryptCore.Refinement.AdapterServerConstructorInitialized

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorInitialized.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorInitialized.native
