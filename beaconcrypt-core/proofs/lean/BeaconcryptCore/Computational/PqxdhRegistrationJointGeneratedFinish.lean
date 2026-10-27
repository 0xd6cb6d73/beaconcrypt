-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointScheduleInvariant
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleResources

/-! The existing compiled finish now consumes an actual dynamically selected owner after any supported generated schedule. Its identity/KEM slot premises follow from source construction and every intervening request. Complete private histories, shared state and all other owners remain in the same execution; this is a representation theorem, not a new primitive security claim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhRegistrationJointOwnership (Entry)
open PqxdhRegistrationJointSchedule (State initial handler finish)
open PqxdhRegistrationJointFinishCompiler (compiler impl)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Next : Type}

abbrev EncodedEntry := Nat × Nat × PqxdhRegistrationJointBundle.Owner

/-- The whole mapped analysis state retains both service histories, shared caches, every owner and both per-owner creation indices. -/
structure EncodedState (KemSK : Type) where
  pool : Pool KemSK
  shared : NativeState KemSK
  owners : List EncodedEntry

def encodeEntry (setup : Setup baseSpec KemSK) (entry : Entry KemSK) : EncodedEntry :=
  (entry.identityIndex, entry.kemIndex,
    PqxdhRegistrationJointBundle.encode setup entry.identityIndex entry.kemIndex entry.owner)

def encodeState (setup : Setup baseSpec KemSK) (state : State KemSK) : EncodedState KemSK :=
  ⟨state.pool, state.shared, state.owners.map (encodeEntry setup)⟩

/-- At any actually reached selected owner, the original complete finish and the existing private-service compiler produce the same full encoded scheduler result. Exact slot ownership is proved from the generated prefix, without a caller-supplied slot assertion or successful-finish premise. -/
theorem generated_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (pool : Pool KemSK) (shared : NativeState KemSK) (reached : Result × State KemSK)
    (supported : reached ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run (initial pool shared)))
    (address : Nat) (entry : Entry KemSK) (found : reached.2.owners[address]? = some entry) (raw : Pqxdh.Bytes) :
    (fun result => (result.1, encodeState setup result.2)) <$> (finish setup codec address raw).run reached.2 =
      (fun result => (result.1.1,
        ({ pool := result.2.1, shared := result.2.2,
           owners := (reached.2.owners.map (encodeEntry setup)).set address
             (entry.identityIndex, entry.kemIndex, result.1.2) } : EncodedState KemSK))) <$>
        (simulateQ (impl setup codec) (simulateQ (compiler setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw
            (PqxdhRegistrationJointBundle.encode setup entry.identityIndex entry.kemIndex entry.owner)))).run
              (reached.2.pool, reached.2.shared) := by
  have slots := PqxdhRegistrationJointSchedule.generated_slots setup codec checks serverSeed program pool shared reached supported address entry found
  rw [PqxdhRegistrationJointCompiledOwner.owner_source setup codec entry.identityIndex entry.kemIndex entry.owner raw
    (reached.2.pool, reached.2.shared) slots.1 slots.2]
  simp [finish, StateT.run, found, encodeState, encodeEntry, Functor.map_map]

/-- Annotation erasure preserves every selective uniform-query certificate for the complete adaptive source schedule, rather than dropping ambient work from the bill. -/
theorem schedule_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (state : State KemSK) (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (handler setup codec checks serverSeed) program).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ (PqxdhRegistrationSchedule.handler setup codec checks serverSeed) program).run
        (PqxdhRegistrationJointSchedule.source state)).IsQueryBoundP predicate budget := by
  rw [← PqxdhRegistrationJointSchedule.program_source setup codec checks serverSeed program state, isQueryBoundP_map_iff]

/-- Each annotated typed-scheduler attempt retains its complete source randomness bill, including declared KEM and interpreted base costs. Runtime initialization is outside this typed interface. -/
theorem query_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (serverSeed : IdentitySeed) (query : PqxdhRegistrationSchedule.Spec.Domain) (state : State KemSK) :
    ((handler setup codec checks serverSeed query).run state).IsTotalQueryBound
      (PqxdhRegistrationSchedule.uniformCost caps 0 (PqxdhRegistrationSchedule.sourceKind query)) := by
  simpa only [← PqxdhRegistrationJointSchedule.query_source setup codec checks serverSeed query state,
    IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhRegistrationSchedule.handler_uniform setup codec checks caps bounded serverSeed 0 query
      (PqxdhRegistrationJointSchedule.source state)

/-- The whole adaptive typed schedule pays its nine all-attempt source classes, including failed writes and finishes and all inherited public cryptographic work. The certificate covers every typed reply. -/
theorem schedule_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (serverSeed : IdentitySeed) (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (budget : Fin 9 → Nat)
    (certified : ∀ kind, program.IsQueryBoundP (fun query => PqxdhRegistrationSchedule.sourceKind query = kind) (budget kind))
    (state : State KemSK) :
    ((simulateQ (handler setup codec checks serverSeed) program).run state).IsTotalQueryBound
      (∑ kind, PqxdhRegistrationSchedule.uniformCost caps 0 kind * budget kind) := by
  exact (isQueryBoundP_true_iff _ _).mp
    (FinitePartitionQueryBounds.weighted_bound PqxdhRegistrationSchedule.sourceKind
      (PqxdhRegistrationSchedule.uniformCost caps 0) budget (handler setup codec checks serverSeed)
      (fun _ => True) program certified
      (fun query before => (query_uniform setup codec checks caps bounded serverSeed query before).isQueryBoundP) state)

/-- The actually reached compiled owner pays one decapsulation, one joint identity DH, at most 56 native-tail requests and zero other service classes, plus the complete evaluated finish allowance. These are per-attempt bounds; prefix work is charged by `schedule_uniform`. -/
theorem generated_compiled_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (pool : Pool KemSK) (shared : NativeState KemSK) (reached : Result × State KemSK)
    (supported : reached ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run (initial pool shared)))
    (address : Nat) (entry : Entry KemSK) (found : reached.2.owners[address]? = some entry) (raw : Pqxdh.Bytes)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) :
    (∀ kind, (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw
        (PqxdhRegistrationJointBundle.encode setup entry.identityIndex entry.kemIndex entry.owner))).IsQueryBoundP
          (fun query => PqxdhRegistrationJointFinishCompiler.classify (KemSK := KemSK) (Response := Response) query = kind)
          (PqxdhRegistrationJointFinishCompiler.cap kind)) ∧
    ((simulateQ (impl setup codec) (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw
        (PqxdhRegistrationJointBundle.encode setup entry.identityIndex entry.kemIndex entry.owner)))).run
          (reached.2.pool, reached.2.shared)).IsTotalQueryBound
            (69 * max 64 (caps.decapsUniform + caps.baseUniform * caps.decapsBase)) := by
  have slots := PqxdhRegistrationJointSchedule.generated_slots setup codec checks serverSeed program pool shared reached supported address entry found
  exact ⟨fun kind => PqxdhRegistrationJointCompiledOwner.owner_queries setup codec raw
    (PqxdhRegistrationJointBundle.encode setup entry.identityIndex entry.kemIndex entry.owner) kind,
    PqxdhRegistrationJointCompiledOwner.owner_uniform setup codec caps bounded entry.identityIndex entry.kemIndex
      entry.owner raw (reached.2.pool, reached.2.shared) slots.1 slots.2⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.generated_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.generated_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.schedule_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.schedule_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.query_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.query_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.schedule_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.generated_compiled_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish.generated_compiled_resources
