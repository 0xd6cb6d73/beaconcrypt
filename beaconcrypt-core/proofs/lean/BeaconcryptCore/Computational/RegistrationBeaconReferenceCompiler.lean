-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
import BeaconcryptCore.Computational.RegistrationAuthenticationCompiler

/-! The selected-owner Beacon prefix has no selected scalar, root32 or record kernel in its executable state. Ordinary identity/one-time operations are evaluated locally, actual decapsulation uses its generated opaque handle, and the reached related-root message is prepared before material is demanded. Other owners require their ordinary source path; this compiler is explicitly for the chosen owner. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceRoot (Ready)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}

structure SelectedOwner (mlSource : RegistrationNativeMldsa.Source) where
  pin : session.ServerAuthenticationPin
  identitySeed : IdentitySeed
  prekeyPublic : Std.Array U8 32#usize
  kemHandle : Nat
  kemPublic : PqxdhKemIndCca.MlKem768PublicKey
  worldOwner : Nat
  phase : RegistrationNativeBeaconFrontend.Phase
  edHistory : PqxdhJointIdentity.History

def eraseOwner {mlSource : RegistrationNativeMldsa.Source} (owner : RegistrationNativeBeaconFrontend.Owner mlSource) : SelectedOwner mlSource :=
  ⟨owner.pin, owner.identitySeed, owner.prekeyPublic, owner.kemHandle, owner.kemPublic, owner.worldOwner, owner.phase, owner.edHistory⟩

def restoreOwner {mlSource : RegistrationNativeMldsa.Source} (scalar : ScalarBytes) (owner : SelectedOwner mlSource) :
    RegistrationNativeBeaconFrontend.Owner mlSource :=
  ⟨owner.pin, owner.identitySeed, scalar, owner.prekeyPublic, owner.kemHandle, owner.kemPublic, owner.worldOwner, owner.phase, owner.edHistory⟩

theorem restore_erase {mlSource : RegistrationNativeMldsa.Source} (owner : RegistrationNativeBeaconFrontend.Owner mlSource) :
    restoreOwner owner.prekeyScalar (eraseOwner owner) = owner := by cases owner; rfl

theorem erase_restore {mlSource : RegistrationNativeMldsa.Source} (scalar : ScalarBytes) (owner : SelectedOwner mlSource) :
    eraseOwner (restoreOwner scalar owner) = owner := by cases owner; rfl

abbrev Spec (n : Nat) (KemSK : Type) := RegistrationServerReferenceRoot.PrepareSpec +
  (RegistrationNativePairedServerService.PublicSpec n +
    RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK)
abbrev M (n : Nat) (KemSK Auxiliary Value : Type) := StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK)) Value

def effect (query : (EnvEffects n).Domain) : OracleComp (Spec n KemSK) ((EnvEffects n).Range query) :=
  (Spec n KemSK).query (.inr (.inl (.inr (.inr query))))

def prepare (message : RegistrationNativeRelatedFamily.Message) : OracleComp (Spec n KemSK) (Option RegistrationNativeRelatedFamily.Message) :=
  (Spec n KemSK).query (.inl message)

def indexed (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    OracleComp (Spec n KemSK) ((RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Range query) :=
  (Spec n KemSK).query (.inr (.inr query))

def sample {Value : Type} (work : ProbComp Value) : OracleComp (Spec n KemSK) Value :=
  simulateQ (fun query => effect (.inl query)) work

def trustedLift : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (OracleComp (Spec n KemSK))
  | .inl query => effect query
  | .inr query => indexed query

def trustedSample {Value : Type} (work : ProbComp Value) :
    OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value :=
  simulateQ (fun query => (RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl (.inl query))) work

/-- Local source operations have only ordinary identity and one-time material. The prekey conversion is its typed opaque role; prekey DH values are supplied by the related-root prefix. -/
noncomputable def other (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationNativeKemInterface.OtherSpec (OracleComp (Spec n KemSK)) := fun query =>
  sample (Prod.fst <$> (RegistrationBeaconRoleBackend.localBackend setup query.primitive).run
    ⟨owner.identitySeed, some oneTime, none⟩)

noncomputable def trustedOther (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) : QueryImpl RegistrationNativeKemInterface.OtherSpec
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) := fun query =>
  trustedSample (Prod.fst <$> (RegistrationBeaconRoleBackend.localBackend setup query.primitive).run
    ⟨owner.identitySeed, some oneTime, none⟩)

noncomputable def trustedPrimitive (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) : QueryImpl RegistrationAgreementShared.PrimitiveSpec
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) := fun query =>
  simulateQ (fun lower => match lower with
    | .inl query => trustedOther setup owner oneTime query
    | .inr query => (RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inr (.inr query)))
    (RegistrationNativeKemInterface.beacon (some owner.kemHandle) query)

noncomputable def primitive (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationAgreementShared.PrimitiveSpec (OracleComp (Spec n KemSK)) := fun query =>
  simulateQ (fun lower => match lower with
    | .inl query => other setup owner oneTime query
    | .inr query => indexed (.inr query))
    (RegistrationNativeKemInterface.beacon (some owner.kemHandle) query)

noncomputable def backendCore (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Spec n KemSK))
  | .convertPublic key => primitive setup owner oneTime (.convertPublic key)
  | .convertSecret role => primitive setup owner oneTime (.convertSecret role)
  | .generate role => primitive setup owner oneTime (.generate role)
  | .encapsulate key => primitive setup owner oneTime (.encapsulate key)
  | .decapsulate ciphertext => primitive setup owner oneTime (.decapsulate ciphertext)
  | .dh request => primitive setup owner oneTime (.dh request)
  | .root _ => pure .None

noncomputable def trustedBackendCore (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK))
  | .convertPublic key => trustedPrimitive setup owner oneTime (.convertPublic key)
  | .convertSecret role => trustedPrimitive setup owner oneTime (.convertSecret role)
  | .generate role => trustedPrimitive setup owner oneTime (.generate role)
  | .encapsulate key => trustedPrimitive setup owner oneTime (.encapsulate key)
  | .decapsulate ciphertext => trustedPrimitive setup owner oneTime (.decapsulate ciphertext)
  | .dh request => trustedPrimitive setup owner oneTime (.dh request)
  | .root _ => pure .None

noncomputable def trustedBackend (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec
      (StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK))) := fun query => do
  modify fun env => { env with requests := env.requests ++ RegistrationWorldAgreement.recorded query }
  StateT.lift (trustedBackendCore setup owner oneTime query)

noncomputable def backend (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (M n KemSK Auxiliary) := fun query => do
  modify fun env => { env with requests := env.requests ++ RegistrationWorldAgreement.recorded query }
  StateT.lift (backendCore setup owner oneTime query)

def visit (point : PqxdhBeaconPhase2Preparation.Word32) : M n KemSK Auxiliary Unit :=
  modify fun env => { env with requests := env.requests ++ [.dh ⟨.BeaconPrekey, point⟩] }

def trustedVisit (point : PqxdhBeaconPhase2Preparation.Word32) :
    StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Unit :=
  modify fun env => { env with requests := env.requests ++ [.dh ⟨.BeaconPrekey, point⟩] }

noncomputable def trustedCollect (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK))
      (Option (PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)) :=
  simulateQ (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
    (RegistrationBeaconRootInterpreter.auxImpl (trustedBackend setup owner oneTime) authenticated) trustedVisit)
    (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () [])

noncomputable def collect (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    M n KemSK Auxiliary (Option (PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)) :=
  simulateQ (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
    (RegistrationBeaconRootInterpreter.auxImpl (backend setup owner oneTime) authenticated) visit)
    (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () [])

noncomputable def agreement (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) : M n KemSK Auxiliary (RustM (Option Ready)) := do
  match ← collect setup owner oneTime authenticated with
  | none => pure (.ok none)
  | some pending => StateT.lift (simulateQ prepare (RegistrationBeaconReferenceRoot.client authenticated pending))

/-- Terminal consumption occurs before the optional decoder result is inspected; only successful authentication can reach root preparation. -/
noncomputable def finishPreparation (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) :
    StateT (SelectedOwner mlSource) (M n KemSK Auxiliary) (RustM (Option Ready)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending oneTime =>
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok aborted => do
          set ({ owner with phase := .aborted aborted } : SelectedOwner mlSource)
          let accepted ← StateT.lift (StateT.lift (simulateQ effect
            (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify)
              (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some packet => .Some packet)))))
          match accepted with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.Err _) => pure (.ok none)
          | .ok (.Ok authenticated) => StateT.lift (agreement setup owner oneTime authenticated)
  | _ => pure (.ok none)

end BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler.restore_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler.restore_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler.erase_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler.erase_restore
