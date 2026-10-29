-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRoleBackend
import BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter

/-! Native agreement KEM requests use the actual fixed-width getters and an indexed private generated-key service. The non-KEM interface excludes both KEM constructors. Creation exposes only an index and public key; neither the executable native callback nor its cut receives a selected secret. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemInterface
open RegistrationAgreementShared (PrimitiveRequest PrimitiveSpec)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret MlKemScheme)
variable {κ ι KemSK Auxiliary Result : Type} {base : OracleSpec ι}

inductive OtherRequest where
  | convertPublic (key : Std.Array U8 32#usize)
  | convertSecret (role : agreement.DhSecretRole)
  | generate (role : agreement.EphemeralRole)
  | dh (request : agreement.DhRequest)

def OtherRequest.primitive : OtherRequest → PrimitiveRequest
  | .convertPublic key => .convertPublic key
  | .convertSecret role => .convertSecret role
  | .generate role => .generate role
  | .dh request => .dh request

abbrev OtherSpec : OracleSpec OtherRequest := fun query => PrimitiveSpec (query.primitive)
abbrev EncapsulationSpec := MlKem768PublicKey →ₒ (MlKem768Ciphertext × MlKemSharedSecret)
abbrev Spec (ambient : OracleSpec κ) (KemSK : Type) := ambient + (PqxdhLiveKemBirth.PoolSpec KemSK + EncapsulationSpec)

/-- Actual local primitive work and private generated keys have separate state coordinates. -/
noncomputable def source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (ambient : OracleSpec κ) (other : QueryImpl ambient (StateT Auxiliary ProbComp)) :
    QueryImpl (Spec ambient KemSK) (StateT (Auxiliary × PqxdhLiveKemBirth.Pool KemSK) ProbComp)
  | .inl query => fun before => (fun result => (result.1, (result.2, before.2))) <$> (other query).run before.1
  | .inr (.inl query) => fun before => (fun result => (result.1, (before.1, result.2))) <$>
      (PqxdhLiveKemBirth.poolImpl baseImpl kem query).run before.2
  | .inr (.inr key) => StateT.lift (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key))

def other (query : OtherSpec.Domain) : OracleComp (Spec OtherSpec KemSK) (OtherSpec.Range query) :=
  (Spec OtherSpec KemSK).query (.inl query)

def encapsulate (key : MlKem768PublicKey) : OracleComp (Spec OtherSpec KemSK)
    (core.option.Option (Std.Array U8 1088#usize × Std.Array U8 32#usize)) :=
  (fun result => .Some (PqxdhAcceptedRegistration.ciphertextArray result.1,
    PqxdhRootTableInitialization.rootArray result.2)) <$> (Spec OtherSpec KemSK).query (.inr (.inr key))

/-- The actual Server encapsulation getter is exposed only after its existing native key check. -/
noncomputable def server (checks : PqxdhServerAuthExperiment.Checks) :
    QueryImpl PrimitiveSpec (OracleComp (Spec OtherSpec KemSK))
  | .convertPublic key => other (.convertPublic key)
  | .convertSecret role => other (.convertSecret role)
  | .generate role => other (.generate role)
  | .dh request => other (.dh request)
  | .encapsulate .None => pure .None
  | .encapsulate (.Some key) =>
      if checks.kemKey (RegistrationRootInput.pqKey key) then encapsulate (RegistrationRootInput.pqKey key)
      else pure .None
  | .decapsulate _ => pure .None

/-- The owner handle is a private creation index, independent of public-key byte aliases. -/
noncomputable def beacon (handle : Option Nat) : QueryImpl PrimitiveSpec (OracleComp (Spec OtherSpec KemSK))
  | .convertPublic key => other (.convertPublic key)
  | .convertSecret role => other (.convertSecret role)
  | .generate role => other (.generate role)
  | .dh request => other (.dh request)
  | .encapsulate _ => pure .None
  | .decapsulate .None => pure .None
  | .decapsulate (.Some ciphertext) => match handle with
    | none => pure .None
    | some handle => (fun reply => RegistrationAgreementRoot.nativeOption
        (reply.map PqxdhRootTableInitialization.rootArray)) <$>
        (Spec OtherSpec KemSK).query (.inr (.inl (.decapsulate handle (PqxdhPhase2InputBytes.ciphertext ciphertext))))

/-- The source birth returns the actual generated index and public bytes, retaining the complete private pool and its history. -/
theorem create_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (ambient : OracleSpec κ) (implementation : QueryImpl ambient (StateT Auxiliary ProbComp))
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    (source baseImpl kem ambient implementation (.inr (.inl .create))).run before =
      (fun pair => ((before.2.keys.length, pair.1), (before.1, (PqxdhLiveKemBirth.created before.2 pair).2))) <$>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen := by
  simp only [source, PqxdhLiveKemBirth.poolImpl, StateT.run, Functor.map_map]
  rfl

/-- Every newly created private pair belongs to the actual KEM generator's support. -/
theorem create_generated (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (ambient : OracleSpec κ) (implementation : QueryImpl ambient (StateT Auxiliary ProbComp))
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK)
    (result : (Nat × MlKem768PublicKey) × (Auxiliary × PqxdhLiveKemBirth.Pool KemSK))
    (reached : result ∈ support ((source baseImpl kem ambient implementation (.inr (.inl .create))).run before)) :
    ∃ pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen),
      result.1 = (before.2.keys.length, pair.1) ∧ result.2.2.keys = before.2.keys ++ [pair] := by
  rw [create_source, support_map] at reached
  obtain ⟨pair, generated, rfl⟩ := reached
  exact ⟨pair, generated, rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeKemInterface

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemInterface.create_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemInterface.create_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemInterface.create_generated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemInterface.create_generated
