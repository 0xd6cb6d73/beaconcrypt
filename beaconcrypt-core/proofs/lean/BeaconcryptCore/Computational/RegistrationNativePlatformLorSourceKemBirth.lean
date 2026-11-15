-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateNative
/-! The genuine native constructor is interpreted through the source Word KEM contract. Every nonbirth prefix retains private rows, while the indexed birth returns and appends the same genuine pair. Source failure and the subsequent total owner append retain their complete reached private state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeKemBirthInvariant (metadata)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Private A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def trusted (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp)) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp) :=
  implementation ∘ₛ RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler

private theorem compiler_free (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .create) 0) :
    (simulateQ RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler work).IsQueryBoundP
      (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  rcases query with effect | other | pool | key
  all_goals try cases pool
  all_goals simp [RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler,QueryImpl.compose,
    RegistrationBeaconReferenceCompiler.trustedLift,RegistrationBeaconReferenceCompiler.effect,
    RegistrationBeaconReferenceCompiler.indexed,RegistrationNativeSecretWordServerSource.realize,
    RegistrationNativeSecretWordInterface.common,RegistrationNativeSecretWordInterface.localKem,
    RegistrationNativeSecretWordInterface.liftLocal,RegistrationNativeSecretWordInterface.route,
    RegistrationNativeSecretWordInterface.routedKem,RegistrationNativeSecretWordTargetPoolFrame.IsCreate,
    RegistrationNativeKemBeaconFootprint.counted,isQueryBoundP_query_iff,isQueryBoundP_map_iff]

variable (setup : Setup base KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))

include contract in
/-- Every genuine native nonbirth prefix preserves the complete private key list through the source leaf contract. -/
theorem native_keys (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .create) 0)
    (before : Private) (result : A × Private)
    (supported : result ∈ support ((simulateQ (trusted implementation) work).run before)) :
    (kem result.2).1.keys = (kem before).1.keys := by
  simp only [trusted,QueryImpl.simulateQ_compose] at supported
  exact RegistrationNativePlatformLorSourceKem.program_keys setup selected pairs publicKey challenge implementation kem input contract
    _ (compiler_free work bounded) before result supported

include contract in
/-- The same genuine native birth leaf returns its old row ordinal and appended public key, retaining the marker. -/
theorem native_birth (before : Private) (result : (Nat × MlKem768PublicKey) × Private)
    (supported : result ∈ support (((trusted implementation) (.inr (.inr (.inl .create)))).run before)) :
    ∃ pair, result.1 = ((kem before).1.keys.length,pair.1) ∧ (kem result.2).1.keys = (kem before).1.keys ++ [pair] ∧
      (kem result.2).2 = (kem before).2 := by
  have compiled : RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler (n := n) (KemSK := KemSK) (.inr (.inr (.inl .create))) =
      (Spec n KemSK).query (.inl (.inr (.inr (.inr (.inl .create))))) := by
    simp only [RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler,QueryImpl.compose,
      RegistrationBeaconReferenceCompiler.trustedLift,RegistrationBeaconReferenceCompiler.indexed,simulateQ_spec_query,
      RegistrationNativeSecretWordServerSource.realize,RegistrationNativeSecretWordInterface.localKem,
      RegistrationNativeSecretWordInterface.liftLocal,RegistrationNativeSecretWordInterface.route,
      RegistrationNativeSecretWordInterface.routedKem]
  simp only [trusted,QueryImpl.compose,compiled,simulateQ_spec_query] at supported
  exact RegistrationNativePlatformLorSourceKem.create_step setup selected pairs publicKey challenge implementation kem input contract before result supported

include contract in
/-- The literal native constructor preserves both rosters or appends exactly its same genuinely born private pair and handle. -/
theorem native_shape (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationServerReferenceCompiler.Environment)
    (before : Private)
    (result : ((RustM (Option Nat) × RegistrationNativeBeaconFrontend.State source) × RegistrationServerReferenceCompiler.Environment) × Private)
    (supported : result ∈ support ((simulateQ (trusted implementation)
      (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run owners).run env)).run before)) :
    ((kem result.2).1.keys = (kem before).1.keys ∧ result.1.1.2.map metadata = owners.map metadata) ∨
    ∃ pair, (kem result.2).1.keys = (kem before).1.keys ++ [pair] ∧
      result.1.1.2.map metadata = owners.map metadata ++ [((kem before).1.keys.length,pair.1)] := by
  rw [RegistrationNativeBeaconBirth.create_program,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨prepared,reached,continued⟩ := supported
  have keys := native_keys setup selected pairs publicKey challenge implementation kem input contract _
    (RegistrationNativeKemBeaconFootprint.prepare_zero .create edPin mlPin keyId owners env) before prepared reached
  have original : prepared.1 ∈ support
      (((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env) := by
    apply OracleComp.support_simulateQ_run'_subset (trusted implementation) _ before
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have retained := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env prepared.1 original
  cases actual : prepared.1.1.1 with
  | fail error | div =>
    simp only [actual,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
    cases continued
    exact Or.inl ⟨keys,by rw [retained]⟩
  | ok reply => cases reply with
    | none =>
      simp only [actual,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
      cases continued
      exact Or.inl ⟨keys,by rw [retained]⟩
    | some ready =>
      simp only [actual] at continued
      obtain ⟨born,middle,worldOwner,after,generated,allocated,terminal⟩ :=
        RegistrationNativeBeaconBirth.append_supported setup source (trusted implementation) edPin keyId
          ready.pin ready.identity ready.prekey prepared.1.1.2 prepared.1.2 prepared.2 _ continued
      obtain ⟨pair,reply,appended,_marker⟩ := native_birth setup selected pairs publicKey challenge implementation kem input contract prepared.2 (born,middle) generated
      have allocationKeys := native_keys setup selected pairs publicKey challenge implementation kem input contract
        ((RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl (.inr (.appendOwner keyId edPin .fresh))) : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Nat)
        (by simp [RegistrationNativeKemBeaconFootprint.counted,isQueryBoundP_query_iff]) middle (worldOwner,after)
        (by simpa only [simulateQ_spec_query] using allocated)
      subst result
      refine Or.inr ⟨pair,allocationKeys.trans (appended.trans (by rw [keys])),?_⟩
      simp only [List.map_append,List.map_singleton,retained]
      congr 2
      change born = ((kem before).1.keys.length,pair.1)
      rw [keys] at reply
      exact reply

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth.native_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth.native_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth.native_birth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth.native_birth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth.native_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth.native_shape
