-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate

/-! Full emitted uniform accounting remains valid after exposing actual encapsulation. The retained existing allowance is conservative: an exposed request itself draws no coins, and earlier or later real encapsulations must additionally be charged when interpreted by the cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform
open PqxdhRegistrationJointKemEncapsulation PqxdhRegistrationJointKemExposedCounts
open PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServiceCosts (Kind poolClass classify)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhRegistrationJointOpenUniform (backendCost total)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Local : Type}

def Uniform : (Spec KemSK).Domain → Prop
  | .inl query => PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK) query
  | .inr _ => False
instance : DecidablePred (Uniform (KemSK := KemSK)) := fun query => by
  cases query
  · exact inferInstanceAs (Decidable (PqxdhDynamicKemJointBounds.IsUniform _))
  · exact inferInstanceAs (Decidable False)

/-- Local forwarding retains the full previous uniform allowance; no primitive or native work disappears. -/
theorem lift_bound (work : StateT Local (OracleComp (PqxdhLiveKemBirth.Spec KemSK)) Result)
    (state : Local) (cap : Nat)
    (bounded : (work.run state).IsQueryBoundP (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) cap) :
    ((PqxdhRegistrationJointKemEncapsulation.lift work).run state).IsQueryBoundP
      (Uniform (KemSK := KemSK)) cap := forward_bound _ _ cap bounded

/-- Every collector callback retains its source uniform allowance. The exposed encapsulation query itself uses zero coins, conservatively bounded by its prior primitive allowance. -/
theorem prefix_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain) (consumed : List Pqxdh.Bytes) :
    ((simulateQ (prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.compiler (KemSK := KemSK) identityIndex query)).run consumed).IsQueryBoundP
      (Uniform (KemSK := KemSK))
      (PqxdhServerAuthSourceCosts.serverUniformCost caps (PqxdhServerAuthSourceCosts.serverClass query)) := by
  cases query <;> first | trivial | skip
  case staticDh point =>
    simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    simp [prefixImpl, StateT.run, forward, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
      Uniform, PqxdhDynamicKemJointBounds.IsUniform, PqxdhDynamicIdentityPool.IsUniform]
  case encapsulate key =>
    simp [PqxdhRegistrationJointServerPrefix.compiler, prefixImpl,
      StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, Uniform]
  all_goals simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_spec_query,
    prefixImpl, StateT.run]
  all_goals apply forward_bound
  all_goals rw [PqxdhLiveKemBirth.coins_class]
  all_goals simp only [Uniform, PqxdhDynamicKemJointBounds.IsUniform]
  case generate => exact (PqxdhServerAuthSourceCosts.server_step_uniform setup codec checks caps bounded .generate consumed).isQueryBoundP

/-- The complete raw prefix keeps its full original upper bound independently of every replaced callback reply. -/
theorem prefix_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    ((simulateQ (prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run consumed).IsQueryBoundP
      (Uniform (KemSK := KemSK)) (32 + caps.encapsCost) := by
  rw [PqxdhRegistrationJointServerPrefix.clientPrefix, ← QueryImpl.simulateQ_compose]
  have result := FinitePartitionQueryBounds.weighted_bound
    (PqxdhServerAuthSourceCosts.serverClass (Reader := Reader) (E := PqxdhJointGapDh.ScalarBytes))
    (PqxdhServerAuthSourceCosts.serverUniformCost caps) PqxdhServerAuthSourceCosts.serverCap
    (prefixImpl setup codec checks raw ∘ₛ PqxdhRegistrationJointServerPrefix.compiler identityIndex)
    (Uniform (KemSK := KemSK)) (PqxdhServerRootPreparation.collect raw)
    (PqxdhServerAuthSourceCosts.server_callbacks raw)
    (fun query before => prefix_step setup codec checks caps bounded identityIndex raw query before) consumed
  simpa only [PqxdhServerAuthSourceCosts.server_bill] using result

/-- Complete native preparation adds no further uniform work. -/
theorem prepare_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((prepare setup codec checks identityIndex raw).run state).IsQueryBoundP
      (Uniform (KemSK := KemSK)) (32 + caps.encapsCost) := by
  simpa only [prepare, StateT.run, isQueryBoundP_map_iff] using
    prefix_bound setup codec checks caps bounded identityIndex raw state.2.server.consumed

/-- The actual root/token tail and all source scalar work keep their full uniform bill after a challenger supplies encapsulation. -/
theorem accept_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((accept setup codec checks identityIndex publicIdentity raw).run state).IsQueryBoundP
      (Uniform (KemSK := KemSK)) (96 + caps.encapsCost) := by
  simp only [accept, StateT.run_bind]
  apply (isQueryBoundP_bind (lift_bound _ state 0
    (PqxdhRegistrationJointOpenUniform.native_bound nativeGet state 0 (by trivial)))
      (m := 32 + caps.encapsCost + 64) ?_).mono (by omega)
  intro before _
  apply isQueryBoundP_bind (prepare_bound setup codec checks caps bounded identityIndex raw before.2)
  intro collected _
  exact lift_bound _ collected.2 64 (PqxdhRegistrationJointOpenUniform.native_bound _ collected.2 64
    (PqxdhRegistrationJointOpenUniform.tail_bound setup publicIdentity before.1 collected.1 collected.2))

/-- Each actual backend command retains its conservative old uniform allowance after opening encapsulation. -/
theorem backend_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) (state : NativeState KemSK) :
    ((impl setup codec checks identityIndex publicIdentity query).run state).IsQueryBoundP
      (Uniform (KemSK := KemSK)) (backendCost caps (classify (KemSK := KemSK) query)) := by
  rcases query with (service | tail) | shared
  case inl.inl =>
    exact lift_bound _ state _
      (PqxdhRegistrationJointOpenUniform.backend_step setup codec checks caps bounded identityIndex publicIdentity _ state)
  case inl.inr =>
    exact lift_bound _ state _
      (PqxdhRegistrationJointOpenUniform.backend_step setup codec checks caps bounded identityIndex publicIdentity _ state)
  case inr =>
    cases shared <;> first
    | exact accept_bound setup codec checks caps bounded identityIndex publicIdentity _ state
    | exact lift_bound _ state _
        (PqxdhRegistrationJointOpenUniform.backend_step setup codec checks caps bounded identityIndex publicIdentity _ state)

private instance : Fintype Kind := ⟨{.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate,
  .uniform, .other, .tail, .accept, .build, .hmac, .hash, .read}, by intro kind; cases kind <;> simp⟩

/-- Every adaptive source command pays its native uniform allowance before either real or random encapsulation interpretation. No ambient work is declared free. -/
theorem command_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result)
    (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    (commands setup codec checks identityIndex publicIdentity work owners state).IsQueryBoundP
      (Uniform (KemSK := KemSK)) (total caps budget) := by
  rw [← PqxdhRegistrationJointOpenUniform.total_eq caps budget]
  exact FinitePartitionQueryBounds.weighted_bound (classify (KemSK := KemSK)) (backendCost caps)
    (PqxdhRegistrationJointOpenCosts.oldBudget budget) (impl setup codec checks identityIndex publicIdentity)
    (Uniform (KemSK := KemSK)) _
    (fun source => PqxdhRegistrationJointRevealCosts.program_bound setup codec work budget certified owners source)
    (fun query before => backend_step setup codec checks caps bounded identityIndex publicIdentity query before) state

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.lift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.lift_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.prefix_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.prefix_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.prefix_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.prepare_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.accept_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.backend_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.command_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform.command_bound
