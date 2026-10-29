-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkKey
import BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseOrder

/-! The actual selected open SDK getter receives the exact candidate in the joint whole-run phase. The proof retains the literal suspension, source prestate, complete reply poststate and successful native continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenPhaseOrder (Extends)
open RegistrationNativeKemCut (Cut scan)
open PqxdhKemIndCca
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- The actual first getter at the selected public key stores precisely its returned ciphertext and secret in the private phase. -/
theorem matching_reply (before after : State n mlSource KemSK) (inactive : before.2 = none)
    (reply : MlKem768Ciphertext × MlKemSharedSecret)
    (supported : (some reply, after) ∈ support (((provider (.inr (.inr publicKey))).run).run before)) :
    after.2 = some reply ∧ after.1 = before.1 := by
  rcases before with ⟨first, phase⟩
  change phase = none at inactive
  subst phase
  rw [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchFacts.matching_getter] at supported
  simp only [mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
  obtain ⟨pair, _generated, uniform, _sampled, rfl, rfl⟩ := supported
  exact ⟨rfl, rfl⟩

/-- Every actual first exposed getter establishes a phase, including an unmatched getter's retained dummy challenge. -/
theorem exposed_some (key : MlKem768PublicKey) (before after : State n mlSource KemSK) (inactive : before.2 = none)
    (reply : MlKem768Ciphertext × MlKemSharedSecret)
    (supported : (some reply, after) ∈ support (((provider (.inr (.inr key))).run).run before)) :
    ∃ label, after.2 = some label := by
  by_cases matching : key = publicKey
  · subst key
    exact ⟨reply, (matching_reply setup checks wire route representation created credential selected pairs publicKey real
      before after inactive reply supported).1⟩
  · rcases before with ⟨first, phase⟩
    change phase = none at inactive
    subst phase
    simp only [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchSource.source,
      OptionT.run_mk, StateT.run, matching, ite_false, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq, Option.some.injEq] at supported
    obtain ⟨pair, _generated, uniform, _sampled, _value, _called, _replyEq, stateEq⟩ := supported
    rw [stateEq]
    exact ⟨_, rfl⟩

/-- A successful actual selected SDK call necessarily establishes a private candidate phase before returning its original session. -/
theorem sdk_active (packet : registration.InitPacket) (session : Nat) (before after : State n mlSource KemSK)
    (inactive : before.2 = none)
    (supported : (some (.ok (some session)), after) ∈ support
      (((simulateQ provider (simulateQ (RegistrationNativeKemOpenFrame.lower true)
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run before)) :
    ∃ label, after.2 = some label := by
  obtain ⟨key, next, reached, reply, replied, prefixSupport, called, rest⟩ :=
    RegistrationNativeKemOptionalCut.sdk_pending_reply setup checks packet provider session before after supported
  have noPhase := (RegistrationNativeKemOpenPhaseOrder.scan_phase setup checks wire route representation created credential
    selected pairs publicKey real _ before reached _ prefixSupport).trans inactive
  obtain ⟨label, assigned⟩ := exposed_some setup checks wire route representation created credential selected pairs publicKey real
    key reached replied noPhase reply called
  have continuation := RegistrationNativeKemOpenPhaseOrder.work_extends setup checks wire route representation created credential
    selected pairs publicKey real (next reply) replied after (some (.ok (some session))) rest
  rcases continuation with impossible | retained
  · rw [assigned] at impossible
    cases impossible
  · exact ⟨label, retained.trans assigned⟩

/-- A successful selected SDK call at an inactive phase uses the literal candidate of the same complete run, with the exact getter-zero callback and continuation retained. -/
theorem sdk_reply (packet : registration.InitPacket)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (verified : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys)
    (selectedKey : keys.2.pqKey = publicKey) (session : Nat)
    (before after : State n mlSource KemSK) (inactive : before.2 = none)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (linked : Extends after.2 (some (challenge, candidate)))
    (supported : (some (.ok (some session)), after) ∈ support
      (((simulateQ provider (simulateQ (RegistrationNativeKemOpenFrame.lower true)
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run before)) :
    ∃ next reached replied,
      reached.2 = none ∧
      (some (Cut.pending publicKey next), reached) ∈ support
        (((scan provider (simulateQ (RegistrationNativeKemOpenFrame.lower true)
          (RegistrationNativeKemServerInterface.typedAccept setup checks packet)) 0).run).run before) ∧
      (some (challenge, candidate), replied) ∈ support (((provider (.inr (.inr publicKey))).run).run reached) ∧
      (some (.ok (some session)), after) ∈ support (((simulateQ provider (next (challenge, candidate))).run).run replied) := by
  obtain ⟨key, next, reached, reply, replied, prefixSupport, called, rest⟩ :=
    RegistrationNativeKemOptionalCut.sdk_pending_reply setup checks packet provider session before after supported
  have keyEq := RegistrationNativeKemOpenSdkKey.typed_pending_key setup checks wire route representation created credential
    selected pairs publicKey real packet keys verified key next before reached prefixSupport
  have actualKey : key = publicKey := keyEq.trans selectedKey
  rw [actualKey] at prefixSupport called
  have noPhase := (RegistrationNativeKemOpenPhaseOrder.scan_phase setup checks wire route representation created credential
    selected pairs publicKey real _ before reached _ prefixSupport).trans inactive
  have replyPhase := (matching_reply setup checks wire route representation created credential selected pairs publicKey real
    reached replied noPhase reply called).1
  have continuation := RegistrationNativeKemOpenPhaseOrder.work_extends setup checks wire route representation created credential
    selected pairs publicKey real (next reply) replied after (some (.ok (some session))) rest
  have retained : after.2 = some reply := by
    rcases continuation with impossible | retained
    · rw [replyPhase] at impossible
      cases impossible
    · exact retained.trans replyPhase
  have same : (challenge, candidate) = reply := by
    rcases linked with impossible | same
    · rw [retained] at impossible
      cases impossible
    · exact Option.some.inj (same.trans retained)
  cases same
  exact ⟨next, reached, replied, noPhase, prefixSupport, called, rest⟩

end BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt.matching_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt.matching_reply
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt.exposed_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt.exposed_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt.sdk_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt.sdk_active
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt.sdk_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt.sdk_reply
