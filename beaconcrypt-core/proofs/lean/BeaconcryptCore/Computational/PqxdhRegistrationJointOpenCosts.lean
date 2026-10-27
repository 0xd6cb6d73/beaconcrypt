-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization

/-! Actual emitted private-service accounting after opening the complete initialized command backend. Locally interpreted source work does not request private capabilities; its evaluated uniform/base work remains charged separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServiceCosts (Kind poolClass classify)
open PqxdhRegistrationJointOpenBackend (Spec Client native prefixImpl)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Local : Type}

/-- Explicit local uniform forwarding cannot create/sign/read a private identity, perform private DH or request a private KEM capability. This says nothing about the number of uniform draws or CPU cost. -/
theorem coins_nonuniform (work : ProbComp Result) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (PqxdhLiveKemBirth.coins (KemSK := KemSK) work).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) 0 := by
  rw [PqxdhLiveKemBirth.coins_class]
  simp only [poolClass, Ne.symm nonuniform, isQueryBoundP_false]

/-- Every local native callback retains its real work while emitting no private capability, on every local state. -/
theorem native_nonuniform (work : StateT Local ProbComp Result) (state : Local)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((native (KemSK := KemSK) work).run state).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) 0 :=
  coins_nonuniform (work.run state) kind nonuniform

/-- Each exact raw collector callback emits at most its selected static-DH request; all native auxiliary work stays local and has no private capability. -/
theorem prefix_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain)
    (consumed : List Pqxdh.Bytes) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((simulateQ (prefixImpl setup codec checks)
      (PqxdhRegistrationJointServerPrefix.compiler (KemSK := KemSK) identityIndex query)).run consumed).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind)
      (if kind = .staticDh ∧ PqxdhServerRootQueryBounds.selected query = true then 1 else 0) := by
  cases query
  all_goals simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_map, simulateQ_spec_query,
    PqxdhServerRootQueryBounds.selected, Bool.false_eq_true, and_false, and_true, ite_false, StateT.run_map]
  case staticDh point =>
    by_cases chosen : kind = .staticDh <;>
      simp [prefixImpl, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, poolClass, chosen, eq_comm]
  all_goals exact coins_nonuniform _ kind nonuniform

/-- One full raw Server prefix emits at most one static-DH request and no other private capability, including every rejecting branch. -/
theorem prefix_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((simulateQ (prefixImpl setup codec checks)
      (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run consumed).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (if kind = .staticDh then 1 else 0) := by
  rw [PqxdhRegistrationJointServerPrefix.clientPrefix, ← QueryImpl.simulateQ_compose]
  simpa [Fintype.sum_bool] using
    FinitePartitionQueryBounds.weighted_bound PqxdhServerRootQueryBounds.selected
      (fun selected => if kind = .staticDh ∧ selected = true then 1 else 0)
      (fun selected => if selected then 1 else 21)
      (prefixImpl setup codec checks ∘ₛ PqxdhRegistrationJointServerPrefix.compiler identityIndex)
      (fun query => poolClass (KemSK := KemSK) query = kind) (PqxdhServerRootPreparation.collect raw)
      (fun selected => PqxdhServerRootQueryBounds.collect_class selected raw)
      (fun query before => prefix_step setup codec checks identityIndex query before kind nonuniform) consumed

/-- The raw collector's exact native-state wrapper adds no private request. -/
theorem prepare_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : NativeState KemSK)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((PqxdhRegistrationJointOpenBackend.prepare setup codec checks identityIndex raw).run state).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (if kind = .staticDh then 1 else 0) := by
  simpa only [PqxdhRegistrationJointOpenBackend.prepare, StateT.run, isQueryBoundP_map_iff] using
    prefix_bound setup codec checks identityIndex raw state.2.server.consumed kind nonuniform

/-- The actual complete acceptance emits at most one static-DH service call and no other private capability. Root and native work retain their separate full evaluated bill. -/
theorem accept_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((PqxdhRegistrationJointOpenBackend.accept setup codec checks identityIndex publicIdentity raw).run state).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (if kind = .staticDh then 1 else 0) := by
  simp only [PqxdhRegistrationJointOpenBackend.accept, StateT.run_bind]
  rw [← Nat.zero_add (if kind = .staticDh then 1 else 0)]
  apply isQueryBoundP_bind (native_nonuniform nativeGet state kind nonuniform)
  intro before _
  exact isQueryBoundP_bind (m := 0) (prepare_bound setup codec checks identityIndex raw before.2 kind nonuniform)
    (fun collected _ => native_nonuniform _ collected.2 kind nonuniform)

/-- Exact private-capability expansion of the previous backend partition. Native macro callbacks contribute zero private calls; acceptance contributes its one possible static DH. -/
def serviceCost (kind : Kind) : Kind → Nat
  | .accept => if kind = .staticDh then 1 else 0
  | .tail | .build | .hmac | .hash | .read => 0
  | source => if source = kind then 1 else 0

/-- A forwarded primitive-service request stays in its original class; it cannot be mistaken for a native macro callback. -/
theorem serviceCost_pool (query : (Spec KemSK).Domain) (kind : Kind) :
    serviceCost kind (poolClass (KemSK := KemSK) query) =
      (if poolClass (KemSK := KemSK) query = kind then 1 else 0) := by
  rcases query with (coin | request) | (coin | request)
  all_goals first | rfl | skip
  case inl.inr =>
    cases request <;> first | rfl | skip
    case service index call => cases call <;> rfl
  case inr.inr => cases request <;> rfl

/-- Every complete source backend callback pays its actual expanded private-service cap on all native states and all possible typed service replies. -/
theorem backend_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) (state : NativeState KemSK)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity query).run state).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (serviceCost kind (classify (KemSK := KemSK) query)) := by
  rcases query with (service | tail) | shared
  case inl.inl =>
    simp only [classify, serviceCost_pool]
    by_cases same : poolClass (KemSK := KemSK) service = kind <;>
      simp [PqxdhRegistrationJointOpenBackend.impl, PqxdhRegistrationJointOpenBackend.pool,
        StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, same]
  case inl.inr => exact native_nonuniform (sourceBeaconTail setup codec tail) state kind nonuniform
  case inr =>
    cases shared <;> first
    | exact accept_bound setup codec checks identityIndex publicIdentity _ state kind nonuniform
    | exact native_nonuniform _ state kind nonuniform

private instance : Fintype Kind := ⟨{.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate,
  .uniform, .other, .tail, .accept, .build, .hmac, .hash, .read}, by intro kind; cases kind <;> simp⟩

/-- The complete adaptive backend expands its actual old capability ledger into the emitted private-service ledger without any restriction on intermediate typed replies. -/
theorem backend_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) Result)
    (budget : Kind → Nat)
    (certified : ∀ source, program.IsQueryBoundP (fun query => classify (KemSK := KemSK) query = source) (budget source))
    (state : NativeState KemSK) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((simulateQ (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity) program).run state).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (∑ source, serviceCost kind source * budget source) := by
  exact FinitePartitionQueryBounds.weighted_bound (classify (KemSK := KemSK)) (serviceCost kind) budget
    (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity)
    (fun query => poolClass (KemSK := KemSK) query = kind) program certified
    (fun query before => backend_step setup codec checks identityIndex publicIdentity query before kind nonuniform) state

def oldBudget (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) (kind : Kind) : Nat :=
  PqxdhRegistrationJointServiceLedger.total (fun source => budget (.inl source)) kind +
    (if kind = .other then budget (.inr 0) + budget (.inr 1) else 0)

/-- Closed form for private capabilities only. The uniform coordinate is deliberately excluded by the theorems below and retains the separate full evaluated bill. -/
def privateTotal (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) : Kind → Nat
  | .identityCreate | .kemCreate => budget (.inl 1)
  | .signing => 3 * budget (.inl 2)
  | .staticDh => budget (.inl 5) + budget (.inl 3)
  | .decapsulate => budget (.inl 5)
  | .other => budget (.inr 0) + budget (.inr 1)
  | _ => 0

/-- Exact expansion adds the Server-accept DH allowance once; it preserves the original creation, signing, decapsulation and live-read caps and removes native macro labels from the private-service partition. -/
theorem private_total (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (∑ source, serviceCost kind source * oldBudget budget source) = privateTotal budget kind := by
  change (∑ source ∈ ({.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate,
    .uniform, .other, .tail, .accept, .build, .hmac, .hash, .read} : Finset Kind),
      serviceCost kind source * oldBudget budget source) = _
  cases kind <;> simp_all [serviceCost, oldBudget, privateTotal, PqxdhRegistrationJointServiceLedger.total]

/-- All attempted source commands compose into the exact private capability caps of this actual open command client. No owner, success, freshness or honest-target premise restricts the adversary. -/
theorem command_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((PqxdhRegistrationJointOpenBackend.compile setup codec checks identityIndex publicIdentity
      (simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) program) owners).run state).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (privateTotal budget kind) := by
  rw [← private_total budget kind nonuniform]
  exact backend_program setup codec checks identityIndex publicIdentity _ (oldBudget budget)
    (fun source => PqxdhRegistrationJointRevealCosts.program_bound setup codec program budget certified owners source)
    state kind nonuniform

end BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.coins_nonuniform' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.coins_nonuniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.native_nonuniform' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.native_nonuniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.prefix_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.prefix_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.prefix_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.prepare_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.accept_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.serviceCost_pool' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.serviceCost_pool

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.backend_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.backend_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.backend_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.private_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.private_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.command_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts.command_program
