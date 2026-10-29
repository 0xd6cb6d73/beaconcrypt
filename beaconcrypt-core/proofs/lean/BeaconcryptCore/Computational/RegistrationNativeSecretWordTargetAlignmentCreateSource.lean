-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateNative
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment

/-! The complete typed symbolic constructor is the actual native birth AST under the same early provider. Only the selected scalar view is packed afterward; retained KEM handle/PQ metadata is literal. The source equation retains the complete reached environment and interpreter state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetPublication (key pack_keys restore_keys)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer
local notation "trusted" => RegistrationNativeSecretWordTargetAlignmentCreateQuery.trusted (n := n)
  setup wire route sign input inside selected pairs publicKey challenge outer
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

/-- Actual local controller lowering keeps the complete current native environment and early-provider state. -/
theorem local_run (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    (simulateQ implementation (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false)
      (((RegistrationNativeSecretWordOwners.executeLocal selectedOwner publicPrekey work).run owners).run env))).run before =
      (fun result => (((result.1.1.1, RegistrationNativePublicOwners.pack selectedOwner publicPrekey result.1.1.2), result.1.2), result.2)) <$>
        (simulateQ trusted ((work.run (owners.map RegistrationNativePublicOwners.restore)).run env)).run before := by
  simp only [RegistrationNativeSecretWordOwners.executeLocal, RegistrationNativePublicOwners.executeLocal,
    StateT.run, simulateQ_map, map_apply,
    RegistrationNativeSecretWordTargetAlignmentCreateQuery.trusted,
    RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler,
    QueryImpl.simulateQ_compose]
  rfl

/-- The actual typed constructor has the exact native birth continuation and scalar-view packing at its reached state. -/
theorem create_run (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source) :
    (typed (.inr (.create edPin mlPin keyId))).run before =
      (fun result => (result.1.1.1,
        ({ before.1 with beacons := RegistrationNativePublicOwners.pack selectedOwner publicPrekey result.1.1.2, environment := result.1.2 }, result.2))) <$>
        (simulateQ trusted
          (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run
            (before.1.beacons.map RegistrationNativePublicOwners.restore)).run before.1.environment)).run before.2 := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run]
  simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.beacon,
    RegistrationNativeSecretWordOwners.create, StateT.run, simulateQ_map, map_apply, Functor.map_map]
  have localSource := local_run setup wire route sign input inside selected pairs publicKey challenge outer selectedOwner publicPrekey
    (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId) before.1.beacons before.1.environment before.2
  simp only [StateT.run] at localSource
  rw [localSource]
  simp only [Functor.map_map]
  rfl

/-- Every typed constructor preserves both ordered metadata and keys or appends exactly the same actual pair. -/
theorem create_shape (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source) (result : RustM (Option Nat) × State n KemSK source)
    (supported : result ∈ support ((typed (.inr (.create edPin mlPin keyId))).run before)) :
    (result.2.2.kem.1.keys = before.2.kem.1.keys ∧ result.2.1.beacons.map key = before.1.beacons.map key) ∨
    ∃ pair, result.2.2.kem.1.keys = before.2.kem.1.keys ++ [pair] ∧
      result.2.1.beacons.map key = before.1.beacons.map key ++ [(before.2.kem.1.keys.length, pair.1)] := by
  rw [create_run, support_map] at supported
  obtain ⟨reached, actual, equal⟩ := supported
  have shape := RegistrationNativeSecretWordTargetAlignmentCreateNative.create_shape setup wire route sign input inside
    selected pairs publicKey challenge outer edPin mlPin keyId
    (before.1.beacons.map RegistrationNativePublicOwners.restore) before.1.environment before.2 reached actual
  cases equal
  rcases shape with same | ⟨pair, keys, owners⟩
  · exact Or.inl ⟨same.1, by rw [pack_keys, same.2, restore_keys]⟩
  · exact Or.inr ⟨pair, keys, by rw [pack_keys, owners, restore_keys]⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource.local_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource.local_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource.create_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource.create_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource.create_shape
