-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateQuery
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth

/-! The actual native constructor fails only before private KEM birth. After that birth its World owner-allocation callback is total and its local append stores exactly the returned private handle and public key. This source receipt is valid under the concrete early provider and arbitrary outer material replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateNative
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeKemBirthInvariant (metadata)
open RegistrationNativeSecretWordTargetAlignmentCreateQuery (trusted)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "implementation" => trusted (n := n) setup wire route sign input inside selected pairs publicKey challenge outer

/-- Every actual native constructor outcome either preserves both ordered rosters or appends exactly the one returned genuine pair. -/
theorem create_shape (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationServerReferenceCompiler.Environment)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeBeaconFrontend.State source) × RegistrationServerReferenceCompiler.Environment) ×
      RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ implementation
      (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run owners).run env)).run before)) :
    (result.2.kem.1.keys = before.kem.1.keys ∧ result.1.1.2.map metadata = owners.map metadata) ∨
    ∃ pair, result.2.kem.1.keys = before.kem.1.keys ++ [pair] ∧
      result.1.1.2.map metadata = owners.map metadata ++ [(before.kem.1.keys.length, pair.1)] := by
  rw [RegistrationNativeBeaconBirth.create_program, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, reached, continued⟩ := supported
  have keys := RegistrationNativeSecretWordTargetAlignmentCreateQuery.program_keys setup wire route sign input inside
    selected pairs publicKey challenge outer _
    (RegistrationNativeKemBeaconFootprint.prepare_zero .create edPin mlPin keyId owners env) before prepared reached
  have original : prepared.1 ∈ support
      (((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env) := by
    apply OracleComp.support_simulateQ_run'_subset implementation _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have retained := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env prepared.1 original
  cases actual : prepared.1.1.1 with
  | fail error | div =>
      simp only [actual, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at continued
      cases continued
      exact Or.inl ⟨keys, by rw [retained]⟩
  | ok reply => cases reply with
    | none =>
        simp only [actual, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at continued
        cases continued
        exact Or.inl ⟨keys, by rw [retained]⟩
    | some ready =>
        simp only [actual] at continued
        obtain ⟨born, middle, worldOwner, after, generated, allocated, terminal⟩ :=
          RegistrationNativeBeaconBirth.append_supported setup source implementation edPin keyId
            ready.pin ready.identity ready.prekey prepared.1.1.2 prepared.1.2 prepared.2 _ continued
        obtain ⟨pair, reply, appended⟩ := RegistrationNativeSecretWordTargetAlignmentCreateQuery.create_step setup wire route
          sign input inside selected pairs publicKey challenge outer prepared.2 (born, middle) generated
        have allocationKeys := RegistrationNativeSecretWordTargetAlignmentCreateQuery.program_keys setup wire route sign input inside
          selected pairs publicKey challenge outer
          ((RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl (.inr (.appendOwner keyId edPin .fresh))) : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Nat)
          (by simp [RegistrationNativeKemBeaconFootprint.counted, isQueryBoundP_query_iff]) middle (worldOwner, after)
          (by simpa only [simulateQ_spec_query] using allocated)
        subst result
        refine Or.inr ⟨pair, allocationKeys.trans (appended.trans (by rw [keys])), ?_⟩
        simp only [List.map_append, List.map_singleton, retained]
        congr 2
        change born = (before.kem.1.keys.length, pair.1)
        rw [keys] at reply
        exact reply

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateNative
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateNative.create_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateNative.create_shape
