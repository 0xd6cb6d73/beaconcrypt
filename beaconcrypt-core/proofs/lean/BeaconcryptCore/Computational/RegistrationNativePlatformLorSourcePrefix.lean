-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys
/-! A source Word interpretation exposes only its individual preparation, genuine routed KEM and nonrouted KEM-frame receipts. The contract contains no source callback, roster alignment or security conclusion. Actual native birth and source prefix invariants are derived from these leaves separately, retaining arbitrary persistent World state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Private A : Type} {base : OracleSpec I}

variable (setup : Setup base KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
variable (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))


def Prefixed (pairs : List (MlKem768PublicKey × KemSK)) (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (before : Private) : Prop :=
  (kem before).1.keys = pairs.take (kem before).1.keys.length

include contract in
/-- One actual source leaf consumes the next genuine reserved pair exactly on indexed birth and preserves the prefix otherwise. -/
theorem query_prefix (query : (Spec n KemSK).Domain) (before : Private) (prior : Prefixed pairs kem before)
    (room : (kem before).1.keys.length + (if RegistrationNativeSecretWordTargetPoolFrame.IsCreate query then 1 else 0) ≤ pairs.length)
    (result : (Spec n KemSK).Range query × Private) (supported : result ∈ support ((implementation query).run before)) :
    Prefixed pairs kem result.2 ∧ (kem result.2).1.keys.length = (kem before).1.keys.length +
      (if RegistrationNativeSecretWordTargetPoolFrame.IsCreate query then 1 else 0) := by
  by_cases creates : RegistrationNativeSecretWordTargetPoolFrame.IsCreate query
  · rcases query with (message | (message | common) | routed) | record
    all_goals try exact creates.elim
    rcases routed with (other | key) | pool | key
    all_goals try exact creates.elim
    cases pool with
    | decapsulate handle ciphertext | reveal handle => exact creates.elim
    | create =>
      have available : (kem before).1.keys.length < pairs.length := by
        simpa [RegistrationNativeSecretWordTargetPoolFrame.IsCreate] using room
      have found : pairs[(kem before).1.keys.length]? = some pairs[(kem before).1.keys.length] :=
        List.getElem?_eq_some_iff.mpr ⟨available,rfl⟩
      have actual := contract.routed (.inr (.inl .create)) before result supported
      rw [RegistrationNativeSecretWordKemEarlyKeys.create_reserved setup.baseImpl setup.kem selected pairs publicKey challenge (kem before) _ found,
        mem_support_pure_iff] at actual
      have keys := congrArg (fun output => output.2.1.keys) actual
      change (kem result.2).1.keys = (kem before).1.keys ++ [pairs[(kem before).1.keys.length]] at keys
      refine ⟨?_,?_⟩
      · simp only [Prefixed,keys,List.length_append,List.length_singleton]
        rw [List.take_add_one,←prior,found]
        rfl
      · simp only [keys,List.length_append,List.length_singleton,RegistrationNativeSecretWordTargetPoolFrame.IsCreate,ite_true]
  · have keys := RegistrationNativePlatformLorSourceKem.query_keys setup selected pairs publicKey challenge implementation kem input contract query creates before result supported
    refine ⟨?_,?_⟩
    · simpa only [Prefixed,keys] using prior
    · simp only [keys,ite_eq_right creates,Nat.add_zero]

include contract in
/-- The actual adaptive source preserves its genuine reserved prefix under the remaining source-derived birth allowance. -/
theorem program_prefix (work : OracleComp (Spec n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) count)
    (before : Private) (prior : Prefixed pairs kem before) (room : (kem before).1.keys.length + count ≤ pairs.length)
    (result : A × Private) (supported : result ∈ support ((simulateQ implementation work).run before)) :
    Prefixed pairs kem result.2 ∧ (kem result.2).1.keys.length ≤ (kem before).1.keys.length + count := by
  induction work using OracleComp.inductionOn generalizing count before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact ⟨prior,Nat.le_add_right _ _⟩
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    have affordable : (kem before).1.keys.length + (if RegistrationNativeSecretWordTargetPoolFrame.IsCreate query then 1 else 0) ≤ pairs.length := by
      split_ifs with creates
      · have positive := bounded.1.resolve_left (not_not.mpr creates)
        omega
      · omega
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    obtain ⟨prefixed,size⟩ := query_prefix setup selected pairs publicKey challenge implementation kem input contract query before prior affordable middle called
    have currentRoom : (kem middle.2).1.keys.length + (if RegistrationNativeSecretWordTargetPoolFrame.IsCreate query then count-1 else count) ≤ pairs.length := by
      split_ifs at size ⊢ with creates
      · have positive := bounded.1.resolve_left (not_not.mpr creates)
        omega
      · omega
    obtain ⟨kept,finalSize⟩ := ih middle.1 _ (bounded.2 middle.1) middle.2 prefixed currentRoom result continued
    refine ⟨kept,?_⟩
    split_ifs at size finalSize with creates
    · have positive := bounded.1.resolve_left (not_not.mpr creates)
      omega
    · omega

include contract in
/-- The literal full current Word source consumes only its genuine reserved prefix under the original public create budget. -/
theorem run_prefix {Platform E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (frontend : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (before : Private) (empty : (kem before).1.keys=[])
    (result : ((A × RegistrationNativeLedger.State) × RegistrationNativePlatformSecretWordOrdinary.State source Platform) × Private)
    (supported : result ∈ support ((simulateQ implementation
      (RegistrationNativePlatformSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work frontend)).run before)) :
    Prefixed pairs kem result.2 ∧ (kem result.2).1.keys.length ≤ budget.create := by
  have bill := RegistrationNativePlatformSecretWordTargetCreateBounds.run_bound (n := n) setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode work budget bounded frontend
  have initial : Prefixed pairs kem before := by simp only [Prefixed,empty,List.length_nil,List.take_zero]
  have room : (kem before).1.keys.length + budget.create ≤ pairs.length := by simpa only [empty,List.length_nil,Nat.zero_add] using reserved
  simpa only [empty,List.length_nil,Nat.zero_add] using
    program_prefix setup selected pairs publicKey challenge implementation kem input contract _ budget.create bill before initial room result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix.query_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix.query_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix.program_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix.run_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix.run_prefix
