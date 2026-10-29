-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCreateBounds

/-! The complete symbolic native game consumes the reserved key pairs in their actual creation order. The source-derived original public create cap rules out the fallback branch; no extra private-query bound or current-owner activation premise is imposed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordTargetPoolFrame (IsCreate)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def Prefixed (pairs : List (MlKem768PublicKey × KemSK)) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) : Prop :=
  before.kem.1.keys = pairs.take before.kem.1.keys.length

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer

/-- One actual callback retains the reserved prefix, consuming exactly one pair only on genuine indexed birth. -/
theorem query_prefix (query : (Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (prior : Prefixed pairs before)
    (room : before.kem.1.keys.length + (if IsCreate (KemSK := KemSK) query then 1 else 0) ≤ pairs.length)
    (result : (Spec n KemSK).Range query × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((implementation query).run before)) :
    Prefixed pairs result.2 ∧ result.2.kem.1.keys.length = before.kem.1.keys.length + (if IsCreate (KemSK := KemSK) query then 1 else 0) := by
  by_cases creates : IsCreate (KemSK := KemSK) query
  · have native := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
    rcases query with (message | (message | common) | routed) | record
    all_goals try exact creates.elim
    rcases routed with (other | key) | pool | key
    all_goals try exact creates.elim
    cases pool with
    | decapsulate handle ciphertext | reveal handle => exact creates.elim
    | create =>
        have available : before.kem.1.keys.length < pairs.length := by simpa [IsCreate] using room
        have found : pairs[before.kem.1.keys.length]? = some pairs[before.kem.1.keys.length] :=
          List.getElem?_eq_some_iff.mpr ⟨available, rfl⟩
        rw [RegistrationNativeSecretWordInterpreter.kem_run, support_map] at native
        obtain ⟨answer, reached, equal⟩ := native
        have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins _ reached
        rw [RegistrationNativeSecretWordKemEarlyKeys.create_reserved setup.baseImpl setup.kem selected pairs publicKey challenge before.kem _ found,
          mem_support_pure_iff] at actual
        cases actual
        cases equal
        refine ⟨?_, ?_⟩
        · simp only [Prefixed, RegistrationNativeSecretWordKemPool.created, RegistrationNativeSecretWordKemPool.record,
            List.length_append, List.length_singleton]
          rw [List.take_add_one, ← prior, found]
          rfl
        · simp [RegistrationNativeSecretWordKemPool.created, RegistrationNativeSecretWordKemPool.record, IsCreate]
  · have keys := RegistrationNativeSecretWordTargetPoolFrame.query_keys setup wire route sign input inside
      selected pairs publicKey challenge outer query creates before result supported
    refine ⟨?_, ?_⟩
    · simpa only [Prefixed, keys] using prior
    · simp only [keys, ite_eq_right creates, Nat.add_zero]

/-- An adaptive private source program retains the reserved prefix under its actual remaining constructor allowance. -/
theorem program_prefix (work : OracleComp (Spec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) count)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (prior : Prefixed pairs before)
    (room : before.kem.1.keys.length + count ≤ pairs.length)
    (result : Value × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    Prefixed pairs result.2 ∧ result.2.kem.1.keys.length ≤ before.kem.1.keys.length + count := by
  induction work using OracleComp.inductionOn generalizing count before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨prior, Nat.le_add_right _ _⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have affordable : before.kem.1.keys.length + (if IsCreate (KemSK := KemSK) query then 1 else 0) ≤ pairs.length := by
        split_ifs with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      obtain ⟨prefixed, size⟩ := query_prefix setup wire route sign input inside selected pairs publicKey challenge outer query before prior affordable middle called
      have currentRoom : middle.2.kem.1.keys.length + (if IsCreate (KemSK := KemSK) query then count - 1 else count) ≤ pairs.length := by
        split_ifs at size ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      obtain ⟨kept, finalSize⟩ := ih middle.1 _ (bounded.2 middle.1) middle.2 prefixed currentRoom result continued
      refine ⟨kept, ?_⟩
      split_ifs at size finalSize with creates
      · have positive := bounded.1.resolve_left (not_not.mpr creates)
        omega
      · omega

/-- The whole original native game uses only the reserved key prefix under its original public create budget. -/
theorem run_prefix {source : RegistrationNativeMldsa.Source} (checks : Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (frontend : RegistrationNativeSecretWordMessage.State source)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (empty : before.kem.1.keys = [])
    (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativeSecretWordMessage.State source) ×
      RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ implementation
      (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work frontend)).run before)) :
    Prefixed pairs result.2 ∧ result.2.kem.1.keys.length ≤ budget.create := by
  have bill := RegistrationNativeSecretWordTargetCreateBounds.run_bound (n := n) setup checks wire source sign
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work budget bounded frontend
  have initial : Prefixed pairs before := by simp only [Prefixed, empty, List.length_nil, List.take_zero]
  have room : before.kem.1.keys.length + budget.create ≤ pairs.length := by simpa only [empty, List.length_nil, Nat.zero_add] using reserved
  simpa only [empty, List.length_nil, Nat.zero_add] using
    program_prefix setup wire route sign input inside selected pairs publicKey challenge outer _ budget.create bill before initial room result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix.query_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix.query_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix.program_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix.run_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix.run_prefix
