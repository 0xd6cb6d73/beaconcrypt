-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts

/-! The source's existing signing, creation, decapsulation and live-read allowances remain valid when an actual encapsulation reply is supplied by a challenger. Every bound holds for all typed replies, including rejection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate
open PqxdhRegistrationJointKemEncapsulation PqxdhRegistrationJointKemExposedCounts
open PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServiceCosts (Kind poolClass classify)
open PqxdhRegistrationJointOpenCosts (serviceCost oldBudget privateTotal)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Local : Type}

def Private (kind : Kind) : (Spec KemSK).Domain → Prop
  | .inl query => poolClass (KemSK := KemSK) query = kind
  | .inr _ => False
instance (kind : Kind) : DecidablePred (Private (KemSK := KemSK) kind) := fun query => by
  cases query
  · exact inferInstanceAs (Decidable (_ = kind))
  · exact inferInstanceAs (Decidable False)

/-- Every lifted source computation preserves the previous private-query cap exactly. -/
theorem lift_bound (work : StateT Local (OracleComp (PqxdhLiveKemBirth.Spec KemSK)) Result)
    (state : Local) (kind : Kind) (cap : Nat)
    (bounded : (work.run state).IsQueryBoundP (fun query => poolClass (KemSK := KemSK) query = kind) cap) :
    ((PqxdhRegistrationJointKemEncapsulation.lift work).run state).IsQueryBoundP (Private (KemSK := KemSK) kind) cap :=
  forward_bound _ _ cap bounded

/-- The exposed prefix still emits only its one possible private static-DH request. The actual encapsulation hook does not become a private decapsulation or signing request. -/
theorem prefix_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain)
    (consumed : List Pqxdh.Bytes) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((simulateQ (prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.compiler (KemSK := KemSK) identityIndex query)).run consumed).IsQueryBoundP
      (Private (KemSK := KemSK) kind) (if kind = .staticDh ∧ PqxdhServerRootQueryBounds.selected query = true then 1 else 0) := by
  cases query
  all_goals simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_map, simulateQ_spec_query,
    PqxdhServerRootQueryBounds.selected, Bool.false_eq_true, and_false, and_true, ite_false, StateT.run_map]
  case staticDh point =>
    by_cases chosen : kind = .staticDh <;>
      simp [prefixImpl, StateT.run, forward, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
        Private, poolClass, chosen, eq_comm]
  case encapsulate key => simp [prefixImpl, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, Private]
  all_goals exact forward_bound _ _ 0 (PqxdhRegistrationJointOpenCosts.coins_nonuniform _ kind nonuniform)

/-- A full raw prefix has the original exact private cap for every arbitrary encapsulation reply. -/
theorem prefix_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((simulateQ (prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run consumed).IsQueryBoundP
      (Private (KemSK := KemSK) kind) (if kind = .staticDh then 1 else 0) := by
  rw [PqxdhRegistrationJointServerPrefix.clientPrefix, ← QueryImpl.simulateQ_compose]
  simpa [Fintype.sum_bool] using
    FinitePartitionQueryBounds.weighted_bound PqxdhServerRootQueryBounds.selected
      (fun selected => if kind = .staticDh ∧ selected = true then 1 else 0)
      (fun selected => if selected then 1 else 21)
      (prefixImpl setup codec checks raw ∘ₛ PqxdhRegistrationJointServerPrefix.compiler identityIndex)
      (Private (KemSK := KemSK) kind) (PqxdhServerRootPreparation.collect raw)
      (fun selected => PqxdhServerRootQueryBounds.collect_class selected raw)
      (fun query before => prefix_step setup codec checks identityIndex raw query before kind nonuniform) consumed

/-- Wrapping the actual prepared inputs preserves the complete native state and the same private cap. -/
theorem prepare_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : NativeState KemSK)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((prepare setup codec checks identityIndex raw).run state).IsQueryBoundP
      (Private (KemSK := KemSK) kind) (if kind = .staticDh then 1 else 0) := by
  simpa only [prepare, StateT.run, isQueryBoundP_map_iff] using
    prefix_bound setup codec checks identityIndex raw state.2.server.consumed kind nonuniform

set_option backward.isDefEq.respectTransparency false in
/-- The complete source acceptance retains its original private-capability allowance with a challenger-controlled encapsulation reply. -/
theorem accept_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((accept setup codec checks identityIndex publicIdentity raw).run state).IsQueryBoundP
      (Private (KemSK := KemSK) kind) (if kind = .staticDh then 1 else 0) := by
  simp only [accept, StateT.run_bind]
  rw [← Nat.zero_add (if kind = .staticDh then 1 else 0)]
  apply isQueryBoundP_bind (lift_bound _ state kind 0 (PqxdhRegistrationJointOpenCosts.native_nonuniform _ state kind nonuniform))
  intro before _
  exact isQueryBoundP_bind (m := 0)
    (prepare_bound setup codec checks identityIndex raw before.2 kind nonuniform)
    (fun collected _ => lift_bound _ collected.2 kind 0
      (PqxdhRegistrationJointOpenCosts.native_nonuniform _ collected.2 kind nonuniform))

/-- Every original backend callback retains the same emitted private-service cap, uniformly over the replaced encapsulation reply. -/
theorem backend_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) (state : NativeState KemSK)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((impl setup codec checks identityIndex publicIdentity query).run state).IsQueryBoundP
      (Private (KemSK := KemSK) kind) (serviceCost kind (classify (KemSK := KemSK) query)) := by
  rcases query with (service | tail) | shared
  case inl.inl =>
    exact lift_bound _ state kind _
      (PqxdhRegistrationJointOpenCosts.backend_step setup codec checks identityIndex publicIdentity _ state kind nonuniform)
  case inl.inr =>
    exact lift_bound _ state kind _
      (PqxdhRegistrationJointOpenCosts.backend_step setup codec checks identityIndex publicIdentity _ state kind nonuniform)
  case inr =>
    cases shared <;> first
    | exact accept_bound setup codec checks identityIndex publicIdentity _ state kind nonuniform
    | exact lift_bound _ state kind _
        (PqxdhRegistrationJointOpenCosts.backend_step setup codec checks identityIndex publicIdentity _ state kind nonuniform)

private instance : Fintype Kind := ⟨{.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate,
  .uniform, .other, .tail, .accept, .build, .hmac, .hash, .read}, by intro kind; cases kind <;> simp⟩

/-- The whole adaptive backend pays its existing complete private ledger with no restriction on the challenger replies. -/
theorem backend_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) Result)
    (budget : Kind → Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => classify (KemSK := KemSK) query = source) (budget source))
    (state : NativeState KemSK) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((simulateQ (impl setup codec checks identityIndex publicIdentity) work).run state).IsQueryBoundP
      (Private (KemSK := KemSK) kind) (∑ source, serviceCost kind source * budget source) :=
  FinitePartitionQueryBounds.weighted_bound (classify (KemSK := KemSK)) (serviceCost kind) budget
    (impl setup codec checks identityIndex publicIdentity) (Private (KemSK := KemSK) kind) work certified
    (fun query before => backend_step setup codec checks identityIndex publicIdentity query before kind nonuniform) state

/-- Exact creation, signing, DH, decapsulation and read caps derive from the actual source14 request budget even after the actual encapsulation callback is exposed. -/
theorem command_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result)
    (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (commands setup codec checks identityIndex publicIdentity work owners state).IsQueryBoundP
      (Private (KemSK := KemSK) kind) (privateTotal budget kind) := by
  rw [← PqxdhRegistrationJointOpenCosts.private_total budget kind nonuniform]
  exact backend_program setup codec checks identityIndex publicIdentity _ (oldBudget budget)
    (fun source => PqxdhRegistrationJointRevealCosts.program_bound setup codec work budget certified owners source)
    state kind nonuniform

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.lift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.lift_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.prefix_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.prefix_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.prefix_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.prepare_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.accept_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.backend_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.backend_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.backend_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.command_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedPrivate.command_bound
