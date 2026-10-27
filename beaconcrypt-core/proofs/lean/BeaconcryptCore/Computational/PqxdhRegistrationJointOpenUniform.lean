-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands

/-! Every actual native callback in the open registration compiler has an explicit uniform allowance on all states and all typed private-service replies. Primitive/base work is counted through its existing interpreted caps; no opaque ambient callback is declared free. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointOpenBackend (Spec native prefixImpl)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDynamicKemJointBounds (IsUniform)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Local : Type}

/-- Forwarded native work preserves every actual uniform query; this bound holds before replacing any private-service challenger. -/
theorem native_bound (work : StateT Local ProbComp Result) (state : Local) (cost : Nat)
    (bounded : (work.run state).IsTotalQueryBound cost) :
    ((native (KemSK := KemSK) work).run state).IsQueryBoundP (IsUniform (KemSK := KemSK)) cost := by
  change (PqxdhLiveKemBirth.coins (work.run state)).IsQueryBoundP _ _
  rw [PqxdhLiveKemBirth.coins_class]
  simpa only [IsUniform, isQueryBoundP_true_iff] using bounded

/-- Opening the actual collector preserves its weighted scalar/encapsulation bill on every possible static-DH reply. -/
theorem prefix_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain) (consumed : List Pqxdh.Bytes) :
    ((simulateQ (prefixImpl setup codec checks)
      (PqxdhRegistrationJointServerPrefix.compiler (KemSK := KemSK) identityIndex query)).run consumed).IsQueryBoundP
      (IsUniform (KemSK := KemSK))
      (PqxdhServerAuthSourceCosts.serverUniformCost caps (PqxdhServerAuthSourceCosts.serverClass query)) := by
  cases query <;> first | trivial | skip
  case staticDh point =>
    simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    simp [prefixImpl, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
      IsUniform, PqxdhDynamicIdentityPool.IsUniform]
  all_goals simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_spec_query,
    prefixImpl, StateT.run]
  all_goals rw [PqxdhLiveKemBirth.coins_class]
  all_goals simp only [IsUniform, isQueryBoundP_true_iff]
  case generate => exact PqxdhServerAuthSourceCosts.server_step_uniform setup codec checks caps bounded .generate consumed
  case encapsulate key => exact PqxdhServerAuthSourceCosts.server_step_uniform setup codec checks caps bounded (.encapsulate key) consumed

/-- The whole raw collector has at most one scalar sampler and one actual encapsulation, even with arbitrary replacement service replies. -/
theorem prefix_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    ((simulateQ (prefixImpl setup codec checks)
      (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run consumed).IsQueryBoundP
      (IsUniform (KemSK := KemSK)) (32 + caps.encapsCost) := by
  rw [PqxdhRegistrationJointServerPrefix.clientPrefix, ← QueryImpl.simulateQ_compose]
  have result := FinitePartitionQueryBounds.weighted_bound
    (PqxdhServerAuthSourceCosts.serverClass (Reader := Reader) (E := PqxdhJointGapDh.ScalarBytes))
    (PqxdhServerAuthSourceCosts.serverUniformCost caps) PqxdhServerAuthSourceCosts.serverCap
    (prefixImpl setup codec checks ∘ₛ PqxdhRegistrationJointServerPrefix.compiler identityIndex)
    (IsUniform (KemSK := KemSK)) (PqxdhServerRootPreparation.collect raw)
    (PqxdhServerAuthSourceCosts.server_callbacks raw)
    (fun query before => prefix_step setup codec checks caps bounded identityIndex query before) consumed
  simpa only [PqxdhServerAuthSourceCosts.server_bill] using result

/-- The actual post-prefix root/token continuation uses at most its one 64-byte Extract-table sample on all collected inputs and native states. -/
theorem tail_bound (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity)
    (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes)
    (state : NativeState KemSK) :
    ((PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected).run state).IsTotalQueryBound 64 := by
  simp only [PqxdhRegistrationJointServerAccept.tail, nativeSet, StateT.run]
  cases collected.1
  · trivial
  · apply (isTotalQueryBound_bind (PqxdhRegistrationSchedule.server_client_uniform setup.hmac before.sessions
      before.server.control ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩ _ _)
      (n₂ := 0) ?_).mono (by omega)
    rintro ⟨((_ | token) | error | _), after⟩
    all_goals trivial

/-- Native collector state wrapping adds no draws and keeps the complete optional prepared input. -/
theorem prepare_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((PqxdhRegistrationJointOpenBackend.prepare setup codec checks identityIndex raw).run state).IsQueryBoundP
      (IsUniform (KemSK := KemSK)) (32 + caps.encapsCost) := by
  simpa only [PqxdhRegistrationJointOpenBackend.prepare, StateT.run, isQueryBoundP_map_iff] using
    prefix_bound setup codec checks caps bounded identityIndex raw state.2.server.consumed

/-- Actual raw accept retains its full scalar, encapsulation/base and possible root-table bill on arbitrary native states and every private static-DH reply. -/
theorem accept_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((PqxdhRegistrationJointOpenBackend.accept setup codec checks identityIndex publicIdentity raw).run state).IsQueryBoundP
      (IsUniform (KemSK := KemSK)) (96 + caps.encapsCost) := by
  simp only [PqxdhRegistrationJointOpenBackend.accept, StateT.run_bind]
  apply (isQueryBoundP_bind (native_bound nativeGet state 0 (by trivial)) (m := 32 + caps.encapsCost + 64) ?_).mono (by omega)
  intro before _
  apply isQueryBoundP_bind (prepare_bound setup codec checks caps bounded identityIndex raw before.2)
  intro collected _
  exact native_bound _ collected.2 64 (tail_bound setup publicIdentity before.1 collected.1 collected.2)

open PqxdhRegistrationJointServiceCosts (Kind poolClass classify)

/-- Full native uniform allowance per old backend class. The other class includes possible explicit joint coins; charging one also safely covers deterministic missing/reveal requests. -/
def backendCost (caps : KemCaps) : Kind → Nat
  | .uniform | .other => 1
  | .tail | .build | .hmac | .hash => 64
  | .accept => 96 + caps.encapsCost
  | _ => 0

/-- Each open indexed service request retains its explicit uniform cost; private key creation and decapsulation are charged by their eventual interpreters. -/
theorem pool_bound (query : (Spec KemSK).Domain) (state : Local) (caps : KemCaps) :
    ((PqxdhRegistrationJointOpenBackend.pool query).run state).IsQueryBoundP
      (IsUniform (KemSK := KemSK)) (backendCost caps (poolClass (KemSK := KemSK) query)) := by
  simp only [PqxdhRegistrationJointOpenBackend.pool, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  rcases query with (coin | request) | (coin | request)
  case inl.inl => simp [IsUniform, PqxdhDynamicIdentityPool.IsUniform, backendCost, poolClass]
  case inl.inr =>
    cases request <;> simp [IsUniform, PqxdhDynamicIdentityPool.IsUniform, backendCost, poolClass]
  case inr.inl => simp [IsUniform, backendCost, poolClass]
  case inr.inr => cases request <;> simp [IsUniform, backendCost, poolClass]

/-- Every actual backend operation has its full open-client uniform allowance independently of its current native state or the private challenger's previous replies. -/
theorem backend_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) (state : NativeState KemSK) :
    ((PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity query).run state).IsQueryBoundP
      (IsUniform (KemSK := KemSK)) (backendCost caps (classify (KemSK := KemSK) query)) := by
  rcases query with (service | tail) | shared
  case inl.inl => exact pool_bound service state caps
  case inl.inr => exact native_bound _ state 64 (PqxdhRegistrationSchedule.tail_uniform setup codec tail state)
  case inr =>
    cases shared with
    | accept raw => exact accept_bound setup codec checks caps bounded identityIndex publicIdentity raw state
    | build index payload => exact native_bound _ state 64 (PqxdhRegistrationSchedule.build_uniform setup codec checks index payload state)
    | hmac key message => exact native_bound _ state 64 (PqxdhRegistrationJointPublicShared.hmac_uniform setup key message state)
    | hash bytes => exact native_bound _ state 64 (PqxdhRegistrationSchedule.hash_uniform bytes state)
    | reveal keyId => exact native_bound _ state 0 (by trivial)

private instance : Fintype Kind := ⟨{.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate,
  .uniform, .other, .tail, .accept, .build, .hmac, .hash, .read}, by intro kind; cases kind <;> simp⟩

/-- Complete backend compilation charges its weighted actual native bill on every continuation and every typed private-service reply. -/
theorem backend_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (client : OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) Result)
    (budget : Kind → Nat)
    (certified : ∀ source, client.IsQueryBoundP (fun query => classify (KemSK := KemSK) query = source) (budget source))
    (state : NativeState KemSK) :
    ((simulateQ (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity) client).run state).IsQueryBoundP
      (IsUniform (KemSK := KemSK)) (∑ source, backendCost caps source * budget source) :=
  FinitePartitionQueryBounds.weighted_bound (classify (KemSK := KemSK)) (backendCost caps) budget
    (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity)
    (IsUniform (KemSK := KemSK)) client certified
    (fun query before => backend_step setup codec checks caps bounded identityIndex publicIdentity query before) state

/-- Explicit native/local uniform allowance. The two live private-read coordinates carry a conservative one-call allowance because they share the old other-service class with possible joint coin requests. Identity generation and local KEM generation/decapsulation are charged separately by the replacing interpreter. -/
def total (caps : KemCaps) (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) : Nat :=
  budget (.inl 0) + 32 * budget (.inl 1) + 32 * budget (.inl 2) +
    (96 + caps.encapsCost) * budget (.inl 3) + 64 * budget (.inl 4) +
    (64 * 56) * budget (.inl 5) + 64 * budget (.inl 6) + 64 * budget (.inl 7) +
    budget (.inr 0) + budget (.inr 1)

/-- The expanded old service ledger evaluates to the stated native bill, counting every actual attempt rather than only successful publications. -/
theorem total_eq (caps : KemCaps) (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) :
    (∑ source, backendCost caps source * PqxdhRegistrationJointOpenCosts.oldBudget budget source) = total caps budget := by
  change (∑ source ∈ ({.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate,
    .uniform, .other, .tail, .accept, .build, .hmac, .hash, .read} : Finset Kind),
      backendCost caps source * PqxdhRegistrationJointOpenCosts.oldBudget budget source) = _
  simp [backendCost, PqxdhRegistrationJointOpenCosts.oldBudget, PqxdhRegistrationJointServiceLedger.total, total]
  omega

/-- The actual original fourteen-class source program supplies the complete open-client uniform bound without a real-interpreter or honest-owner restriction. All future challenger replies and reached native states are covered. -/
theorem command_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (client : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    (PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity client owners state).IsQueryBoundP
      (IsUniform (KemSK := KemSK)) (total caps budget) := by
  rw [← total_eq caps budget]
  exact backend_program setup codec checks caps bounded identityIndex publicIdentity _
    (PqxdhRegistrationJointOpenCosts.oldBudget budget)
    (fun source => PqxdhRegistrationJointRevealCosts.program_bound setup codec client budget certified owners source) state

end BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.native_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.prefix_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.prefix_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.prefix_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.tail_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.tail_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.prepare_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.accept_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.pool_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.pool_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.backend_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.backend_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.backend_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.total_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.total_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.command_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform.command_program
