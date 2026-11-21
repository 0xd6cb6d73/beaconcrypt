-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateNative
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
/-! The literal common-platform symbolic constructor executes the genuine native birth program through the same early provider. Platform state is forwarded at every native leaf, and owner packing preserves exactly the separately represented KEM handle and public key. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message zero)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetPublication (key pack_keys restore_keys)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem local_embedding :
    RegistrationNativePlatformSecretWordOwnerRealization.base (n := n) (KemSK := KemSK) zero ∘ₛ
      RegistrationNativePlatformPublicFrontend.localQuery false =
      RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ RegistrationNativeSecretWordServerSource.realize zero := by
  rw [← RegistrationNativeSecretWordCheckedFrontendLift.realization_local]
  funext query
  rcases query with message | common | kem
  · rfl
  · rfl
  · simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.localQuery,
      RegistrationNativePublicFrontend.liftLocal, ← QueryImpl.simulateQ_compose]
    congr 1

private theorem trusted_query (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (previous : Platform) :
    simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base zero)
      ((RegistrationNativePlatformPublicFrontend.trusted query).run previous) =
      (fun value => (value, previous)) <$>
        RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler query := by
  simp only [RegistrationNativePlatformPublicFrontend.trusted, StateT.run_lift, bind_pure_comp, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose, local_embedding]
  simp only [RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler,
    QueryImpl.apply_compose, QueryImpl.simulateQ_compose]

/-- Every genuine native callback program retains the same platform state and the exact old per-query birth interpretation. -/
theorem native_program (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A) (previous : Platform) :
    simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base zero)
      ((simulateQ RegistrationNativePlatformPublicFrontend.trusted work).run previous) =
      (fun value => (value, previous)) <$>
        simulateQ RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler work := by
  induction work using OracleComp.inductionOn generalizing previous with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind, map_bind]
    rw [trusted_query]
    simp only [bind_map_left]
    apply bind_congr
    intro reply
    exact ih reply previous

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer
local notation "trusted" => RegistrationNativeSecretWordTargetAlignmentCreateQuery.trusted (n := n)
  setup wire route sign input inside selected pairs publicKey challenge outer

/-- Actual source owner restoration and packing leave the common platform state beside the same native/private creation result. -/
theorem local_run (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment)
    (previous : Platform) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    (simulateQ implementation (simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base zero)
      ((((RegistrationNativePlatformPublicOwners.executeLocal selectedOwner publicPrekey
        (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformPublicFrontend.trusted work)).run owners).run env).run previous))).run before =
      (fun result => ((((result.1.1.1, RegistrationNativePublicOwners.pack selectedOwner publicPrekey result.1.1.2), result.1.2), previous), result.2)) <$>
        (simulateQ trusted ((work.run (owners.map RegistrationNativePublicOwners.restore)).run env)).run before := by
  simp only [RegistrationNativePlatformPublicOwners.executeLocal, RegistrationNativePlatformGenericBundle.liftLegacy,
    StateT.run, simulateQ_map, map_apply]
  have nativeEq := native_program ((work.run (owners.map RegistrationNativePublicOwners.restore)).run env) previous
  simp only [StateT.run] at nativeEq
  rw [nativeEq]
  simp only [simulateQ_map, map_apply, Functor.map_map,
    RegistrationNativeSecretWordTargetAlignmentCreateQuery.trusted, QueryImpl.simulateQ_compose]
  rfl

variable {E : Type}
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "controller" => RegistrationNativePlatformSecretWordOrdinary.handler (n := n) setup source selectedOwner publicPrekey reserveFrame writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller

/-- The actual new typed constructor has the same genuine private birth and exact platform poststate. -/
theorem create_run (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePlatformSecretWordExecution.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK) :
    (typed (.inr (.create edPin mlPin keyId))).run before =
      (fun result => (result.1.1.1,
        (({ before.1.1 with beacons := RegistrationNativePublicOwners.pack selectedOwner publicPrekey result.1.1.2, environment := result.1.2 }, before.1.2), result.2))) <$>
        (simulateQ trusted (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run
          (before.1.1.beacons.map RegistrationNativePublicOwners.restore)).run before.1.1.environment)).run before.2 := by
  rw [RegistrationNativePlatformSecretWordExecution.typed_run]
  simp only [RegistrationNativePlatformSecretWordOrdinary.handler, RegistrationNativePlatformSecretWordOrdinary.beacon,
    RegistrationNativePlatformPublicOwners.create, StateT.run, simulateQ_map, map_apply, Functor.map_map]
  have localSource := local_run setup wire route sign input inside selected pairs publicKey challenge outer selectedOwner publicPrekey
    (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId) before.1.1.beacons before.1.1.environment before.1.2 before.2
  simp only [StateT.run] at localSource
  rw [localSource]
  simp only [Functor.map_map]
  rfl

/-- All new typed constructor outcomes preserve both rosters or append the same actual private pair and handle. -/
theorem create_shape (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePlatformSecretWordExecution.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK)
    (result : RustM (Option Nat) × RegistrationNativePlatformSecretWordExecution.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK)
    (supported : result ∈ support ((typed (.inr (.create edPin mlPin keyId))).run before)) :
    (result.2.2.kem.1.keys = before.2.kem.1.keys ∧ result.2.1.1.beacons.map key = before.1.1.beacons.map key) ∨
    ∃ pair, result.2.2.kem.1.keys = before.2.kem.1.keys ++ [pair] ∧
      result.2.1.1.beacons.map key = before.1.1.beacons.map key ++ [(before.2.kem.1.keys.length, pair.1)] := by
  rw [create_run, support_map] at supported
  obtain ⟨reached, actual, equal⟩ := supported
  have shape := RegistrationNativeSecretWordTargetAlignmentCreateNative.create_shape setup wire route sign input inside
    selected pairs publicKey challenge outer edPin mlPin keyId (before.1.1.beacons.map RegistrationNativePublicOwners.restore)
    before.1.1.environment before.2 reached actual
  cases equal
  rcases shape with same | ⟨pair, keys, owners⟩
  · exact Or.inl ⟨same.1, by rw [pack_keys, same.2, restore_keys]⟩
  · exact Or.inr ⟨pair, keys, by rw [pack_keys, owners, restore_keys]⟩

/-- New actual typed creation derives owner-index/private-row alignment without public-key injectivity. -/
theorem aligned (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePlatformSecretWordExecution.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK)
    (result : RustM (Option Nat) × RegistrationNativePlatformSecretWordExecution.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK)
    (prior : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.1.beacons before.2.kem.1.keys)
    (supported : result ∈ support ((typed (.inr (.create edPin mlPin keyId))).run before)) :
    RegistrationNativeSecretWordTargetAlignment.Aligned result.2.1.1.beacons result.2.2.kem.1.keys := by
  rcases create_shape setup wire route sign input inside selected pairs publicKey challenge outer selectedOwner publicPrekey reserveFrame writer
      edPin mlPin keyId before result supported with same | ⟨pair, keys, owners⟩
  · rw [same.1]
    exact RegistrationNativeSecretWordTargetAlignment.same _ _ _ prior same.2
  · rw [keys]
    exact RegistrationNativeSecretWordTargetAlignment.append _ _ _ pair prior owners

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.local_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.local_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.create_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.create_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.create_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate.aligned
