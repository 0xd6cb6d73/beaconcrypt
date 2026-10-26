-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule

/-! Explicit attempted-disclosure coordinates extend the complete source/service ledgers. Disclosures have no uniform draws; identity and live KEM reads each emit at most one private request. Native macro work keeps its existing separately evaluated source bill. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationJointLiveRead PqxdhRegistrationJointRevealSchedule
open PqxdhRegistrationJointServiceCosts (Kind classify poolClass)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

def fieldIndex : Field → Fin 5
  | .identity => 0 | .kem => 1 | .prekey => 2 | .oneTime => 3 | .kernel => 4

abbrev SourceKind := Fin 9 ⊕ Fin 5

def sourceKind : (Spec KemSK).Domain → SourceKind
  | .inl query => .inl (PqxdhRegistrationSchedule.sourceKind query)
  | .inr request => .inr (fieldIndex request.2)

def readCap (kind : Kind) : Fin 5 → Nat := ![if kind = .other then 1 else 0, if kind = .other then 1 else 0, 0, 0, 0]

def cost (kind : Kind) : SourceKind → Nat
  | .inl source => PqxdhRegistrationJointServiceCosts.cost kind source
  | .inr field => readCap kind field

set_option backward.isDefEq.respectTransparency false in
/-- The field client emits at most one private identity or KEM read; erased phases and local fields emit no backend request. Every possible typed service reply is included. -/
theorem entry_bound (field : Field) (entry : PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    (entryClient (KemSK := KemSK) field entry).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (readCap kind (fieldIndex field)) := by
  cases field <;> cases kind <;>
    simp [entryClient, readCap, fieldIndex, isQueryBoundP_map_iff, isQueryBoundP_query_iff, poolClass]
  all_goals cases kemHandle entry.2.2 <;>
    simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- Missing addresses add no backend work; each present read keeps its per-field service allowance. -/
theorem read_bound (request : Nat × Field) (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    ((clientStep (KemSK := KemSK) (Response := Response) request).run owners).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (readCap kind (fieldIndex request.2)) := by
  cases found : owners[request.1]? with
  | none => simp only [StateT.run, clientStep, found, isQueryBoundP_pure]
  | some entry => simpa only [StateT.run, clientStep, found, isQueryBoundP_map_iff,
      PqxdhRegistrationJointServiceLedger.pool_queries] using entry_bound (KemSK := KemSK) request.2 entry kind

/-- The extended fourteen-coordinate source partition bounds every attempted request on all replies and every client registry. -/
theorem query_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (query : (Spec KemSK).Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    ((client setup codec query).run owners).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (cost kind (sourceKind (KemSK := KemSK) query)) := by
  cases query with
  | inl query => exact PqxdhRegistrationJointServiceLedger.query_bound setup codec query owners kind
  | inr request => exact read_bound request owners kind

/-- The old closed-form ledger is unchanged except for explicit identity/KEM disclosures in the previously unused private-capability class. Local-field reads contribute zero backend calls. -/
theorem cost_total (budget : SourceKind → Nat) (kind : Kind) :
    (∑ source, cost kind source * budget source) =
      PqxdhRegistrationJointServiceLedger.total (fun source => budget (.inl source)) kind +
        (if kind = .other then budget (.inr 0) + budget (.inr 1) else 0) := by
  simp only [Fintype.sum_sum_type, cost, PqxdhRegistrationJointServiceLedger.cost_total]
  cases kind <;> simp [readCap, Fin.sum_univ_succ]

/-- Every adaptive original operation and disclosure attempt contributes to the full emitted-service bound, including rejection and arbitrary typed replies. -/
theorem program_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp (Spec KemSK) Result) (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    ((simulateQ (client setup codec) program).run owners).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind)
      (PqxdhRegistrationJointServiceLedger.total (fun source => budget (.inl source)) kind +
        (if kind = .other then budget (.inr 0) + budget (.inr 1) else 0)) := by
  rw [← cost_total budget kind]
  exact FinitePartitionQueryBounds.weighted_bound (sourceKind (KemSK := KemSK)) (cost kind) budget
    (client setup codec) (fun query => classify (KemSK := KemSK) query = kind)
    program certified (fun query before => query_bound setup codec query before kind) owners

/-- Native disclosures consume no uniform samples. The original nine operations retain their complete evaluated primitive/base bill. -/
def uniformCost (caps : PqxdhServerAuthSourceCosts.KemCaps) : SourceKind → Nat
  | .inl source => PqxdhRegistrationSchedule.uniformCost caps 0 source
  | .inr _ => 0

/-- Every native request keeps its entire uniform bill on all reached states; current-field reads are deterministic state projections. -/
theorem query_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    ((native setup codec checks serverSeed query).run state).IsTotalQueryBound
      (uniformCost caps (sourceKind (KemSK := KemSK) query)) := by
  cases query with
  | inl query => exact PqxdhRegistrationSchedule.handler_uniform setup codec checks caps bounded serverSeed 0 query state
  | inr request => change (pure _ : ProbComp _).IsTotalQueryBound 0; trivial

/-- The complete executable adaptive client pays every original interpreted uniform cost after current-field reads are admitted. The equality passes through the full source distribution rather than discarding ambient native work. -/
theorem program_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (program : OracleComp (Spec KemSK) Result) (budget : SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    (PqxdhRegistrationJointServiceSchedule.execute setup codec checks serverSeed
      (simulateQ (client setup codec) program) (PqxdhRegistrationJointGeneratedFinish.encodeState setup state)).IsTotalQueryBound
      (∑ source, uniformCost caps source * budget source) := by
  apply (isQueryBoundP_true_iff _ _).mp
  rw [program_source setup codec checks serverSeed program state owned, isQueryBoundP_map_iff]
  rw [← isQueryBoundP_map_iff (f := fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)),
    program_projection setup codec checks serverSeed program state]
  exact FinitePartitionQueryBounds.weighted_bound (sourceKind (KemSK := KemSK)) (uniformCost caps) budget
    (native setup codec checks serverSeed) (fun _ => True) program certified
    (fun query before => (query_uniform setup codec checks serverSeed caps bounded query before).isQueryBoundP)
    (PqxdhRegistrationJointSchedule.source state)

/-- The extended evaluated uniform sum is exactly the old source bill; all five disclosure coordinates remain present with zero random draws. Server/runtime initialization stays outside this typed interface. -/
theorem uniform_bill (caps : PqxdhServerAuthSourceCosts.KemCaps) (budget : SourceKind → Nat) :
    (∑ source, uniformCost caps source * budget source) =
      budget (.inl 0) + (64 + caps.keygenCost) * budget (.inl 1) + 32 * budget (.inl 2) +
      (96 + caps.encapsCost) * budget (.inl 3) + 64 * budget (.inl 4) +
      (69 * max 64 caps.decapsCost) * budget (.inl 5) + 64 * budget (.inl 6) + 64 * budget (.inl 7) := by
  simp only [Fintype.sum_sum_type, uniformCost, zero_mul, Finset.sum_const_zero, Nat.add_zero]
  simpa only [Nat.zero_add] using PqxdhRegistrationSchedule.uniform_bill caps 0 (fun source => budget (.inl source))

end BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.entry_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.entry_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.read_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.read_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.cost_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.cost_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.program_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.query_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.query_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.program_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.uniform_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts.uniform_bill
