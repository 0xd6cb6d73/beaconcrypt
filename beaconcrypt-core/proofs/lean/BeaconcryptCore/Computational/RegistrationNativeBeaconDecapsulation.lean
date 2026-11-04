-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies
import BeaconcryptCore.Computational.RegistrationNativeBeaconCollectorCuts

/-! Native indexed decapsulation is tied to the actual private generated-key row and the underlying KEM reply. The receipt retains real source execution and accounting rather than supplying a peer-secret equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca (MlKem768Ciphertext MlKemSharedSecret)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem sampled_support (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n)
    (result : Value × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) : result.1 ∈ support work := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, called, returned⟩ := supported
  cases returned
  apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin work before.primitive.1.uniform
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst called

private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

/-- A successful private table getter actually uses the secret at the requested row, preserving the complete row list. -/
theorem pool (setup : Setup base KemSK) (handle : Nat) (ciphertext : MlKem768Ciphertext)
    (shared : MlKemSharedSecret) (before after : PqxdhLiveKemBirth.Pool KemSK)
    (supported : (some shared, after) ∈ support
      ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem (.decapsulate handle ciphertext)).run before)) :
    ∃ pair, before.keys[handle]? = some pair ∧
      some shared ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.decaps pair.2 ciphertext)) ∧
      after.keys = before.keys := by
  simp only [PqxdhLiveKemBirth.poolImpl, StateT.run] at supported
  cases row : before.keys[handle]? with
  | none => simp [row] at supported
  | some pair =>
    simp only [row, bind_pure_comp, support_map] at supported
    obtain ⟨answer, called, same⟩ := supported
    have answerEq : answer = some shared := congrArg Prod.fst same
    subst answer
    exact ⟨pair, rfl, called, (congrArg (fun result => result.2.keys) same).symm⟩

/-- The original globally counted native interpreter preserves the same actual table-row decapsulation witness. -/
theorem trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (handle : Nat) (ciphertext : MlKem768Ciphertext) (shared : MlKemSharedSecret)
    (before after : RegistrationNativeExperiment.State n KemSK source)
    (supported : (some shared, after) ∈ support
      ((RegistrationNativeExperiment.trusted setup checks representation created source
        (.inr (.inr (.inl (.decapsulate handle ciphertext))))).run before)) :
    ∃ pair, before.pool.keys[handle]? = some pair ∧
      some shared ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.decaps pair.2 ciphertext)) ∧
      after.pool.keys = before.pool.keys := by
  simp only [RegistrationNativeExperiment.trusted, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have underlying := sampled_support _ _ inner called
  simp only [RegistrationNativeKemInterface.source, StateT.run, support_map] at underlying
  obtain ⟨result, resultCalled, resultEq⟩ := underlying
  have replyEq : result.1 = some shared :=
    (congrArg Prod.fst resultEq).trans (congrArg Prod.fst same)
  have actualSupport : (some shared, result.2) ∈ support
      ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem (.decapsulate handle ciphertext)).run before.pool) := by
    rw [← replyEq]
    exact resultCalled
  obtain ⟨pair, row, decapsulated, keys⟩ := pool setup handle ciphertext shared before.pool result.2 actualSupport
  have keysEq : result.2.keys = after.pool.keys :=
    (congrArg (fun value => value.2.2.keys) resultEq).trans (congrArg (fun value => value.2.pool.keys) same)
  exact ⟨pair, row, decapsulated, keysEq.symm.trans keys⟩

/-- The actual lowered Beacon primitive gets a decapsulation from its own private table handle, without substituting another key. -/
theorem primitive (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (ciphertext : Std.Array U8 1088#usize) (shared : Std.Array U8 32#usize)
    (before after : Local n KemSK source)
    (supported : (.Some shared, after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativeBeaconFrontend.primitive setup owner oneTime (.decapsulate (.Some ciphertext)))).run before)) :
    ∃ pair, before.2.2.pool.keys[owner.kemHandle]? = some pair ∧
      some (PqxdhPhase2InputBytes.word shared) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (setup.kem.decaps pair.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))) ∧
      after.2.2.pool.keys = before.2.2.pool.keys := by
  simp only [lower, RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
    simulateQ_map, simulateQ_spec_query, RegistrationNativeBeaconFrontend.kem,
    StateT.run, state_map_apply, state_lift_apply, simulateQ_map, simulateQ_spec_query, Functor.map_map, support_map] at supported
  obtain ⟨result, called, returned⟩ := supported
  have reply : RegistrationAgreementRoot.nativeOption (result.1.map PqxdhRootTableInitialization.rootArray) = .Some shared :=
    congrArg Prod.fst returned
  have rawReply : result.1 = some (PqxdhPhase2InputBytes.word shared) := by
    cases answer : result.1 with
    | none => simp only [answer, Option.map_none, RegistrationAgreementRoot.nativeOption] at reply; cases reply
    | some secret =>
      have same : PqxdhRootTableInitialization.rootArray secret = shared := by
        exact Option.some.inj (by simpa only [answer, Option.map_some, RegistrationAgreementRoot.nativeOption] using reply)
      have bytes := congrArg PqxdhPhase2InputBytes.word same
      rw [PqxdhPhase2InputBytes.word_rootArray] at bytes
      exact congrArg some bytes
  have rawCalled : (some (PqxdhPhase2InputBytes.word shared), result.2) ∈ support
      ((RegistrationNativeExperiment.trusted setup checks representation created source
        (.inr (.inr (.inl (.decapsulate owner.kemHandle (PqxdhPhase2InputBytes.ciphertext ciphertext)))))).run before.2.2) := by
    rw [← rawReply]
    exact called
  obtain ⟨pair, row, decapsulated, keys⟩ := trusted setup checks representation created _ _ _ _ _ rawCalled
  have nativeEq : result.2 = after.2.2 := congrArg (fun value => value.2.2.2) returned
  exact ⟨pair, row, decapsulated, (congrArg (fun state => state.pool.keys) nativeEq).symm.trans keys⟩

/-- Decapsulation at the actual agreement callback retains the same table-row witness after its ordinary request-ledger append. -/
theorem agreement (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (ciphertext : Std.Array U8 1088#usize) (shared : Std.Array U8 32#usize)
    (before after : Local n KemSK source)
    (supported : (.Some shared, after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativeBeaconFrontend.agreement setup owner oneTime (.decapsulate (.Some ciphertext)))).run before)) :
    ∃ pair, before.2.2.pool.keys[owner.kemHandle]? = some pair ∧
      some (PqxdhPhase2InputBytes.word shared) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (setup.kem.decaps pair.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))) ∧
      after.2.2.pool.keys = before.2.2.pool.keys := by
  rw [RegistrationNativeBeaconFrontend.agreement, RegistrationNativeResponseAuthentication.lower_bind] at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨ignored, current⟩, updated, continued⟩ := supported
  have nativeEq : current.2.2 = before.2.2 := by
    simp only [lower, RegistrationNativeBeaconFrontend.updateEnv, StateT.run, state_lift_apply] at updated
    exact congrArg (fun value => value.2.2.2) updated
  obtain ⟨pair, row, decapsulated, keys⟩ := primitive setup checks representation created owner oneTime ciphertext shared current after continued
  exact ⟨pair, nativeEq ▸ row, decapsulated, keys.trans (congrArg (fun state => state.pool.keys) nativeEq)⟩

end BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation.pool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation.pool

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation.trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation.primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation.primitive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconDecapsulation.agreement
