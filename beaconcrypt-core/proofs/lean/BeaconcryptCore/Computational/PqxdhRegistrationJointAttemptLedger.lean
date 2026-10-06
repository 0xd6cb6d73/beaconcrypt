-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory

/-! Private analysis of actual constructor fields and all source signing attempts. This ledger is allocated only by the literal source constructor and updated from the same prepared tuple and one-time draw as each bundle operation. It survives native erasure solely as proof bookkeeping and adds no adversary operation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhEd25519EufCma
open PqxdhRegistrationJointOwnership (Entry)
open PqxdhRegistrationJointSigningTranscript (messagesAt)
open PqxdhRegistrationJointIssuedAttempts (history Fixed)
open PqxdhRegistrationJointAttemptTrace (LiveFixed)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- These immutable public constructor fields and their source KEM index are recorded at birth, before any signing attempt. The chronological tuple list includes failed publication. -/
structure Receipt where
  prekey : X25519PublicKey
  pqKey : PqxdhKemIndCca.MlKem768PublicKey
  kemIndex : Nat
  attempts : List Phase1KeyTuple

abbrev Ledger := Nat → Option Receipt
abbrev State (KemSK : Type) := PqxdhRegistrationJointSchedule.State KemSK × Ledger

def initial (state : PqxdhRegistrationJointSchedule.State KemSK) : State KemSK := (state, fun _ => none)

def birth (setup : Setup baseSpec KemSK) (kemIndex : Nat)
    (material : PqxdhRegistrationJointCreation.Material KemSK) : Receipt :=
  ⟨setup.dh.publicKey material.prekey, material.keys.1, kemIndex, []⟩

/-- The original constructor installs its full native result and records exactly its own generated public fields at its actual creation index. -/
def created (setup : Setup baseSpec KemSK) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : State KemSK) (material : PqxdhRegistrationJointCreation.Material KemSK) : Nat × State KemSK :=
  ((PqxdhRegistrationJointSchedule.created setup pin keyId state.1 material).1,
    (PqxdhRegistrationJointSchedule.created setup pin keyId state.1 material).2,
    Function.update state.2 state.1.pool.1.seeds.length (some (birth setup state.1.pool.2.keys.length material)))

def create (setup : Setup baseSpec KemSK) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) : StateT (State KemSK) ProbComp Nat :=
  fun state => created setup pin keyId state <$> PqxdhRegistrationJointCreation.material setup

/-- Missing analysis entries never change native behavior. Under the proved invariant, the present receipt is updated with the exact same source attempt, before observing writer success. -/
def bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat) :
    StateT (State KemSK) ProbComp (Option Pqxdh.Bytes) := fun state =>
  match state.1.owners[address]? with
  | none => pure (none, state)
  | some entry =>
      (fun result => (result.1.1.1,
        { state.1 with
          pool := (result.1.2, state.1.pool.2),
          owners := state.1.owners.set address { entry with owner := result.1.1.2 } },
        Function.update state.2 entry.identityIndex ((state.2 entry.identityIndex).map fun receipt =>
          { receipt with attempts := result.2 }))) <$>
        PqxdhRegistrationJointAttemptTrace.trace setup codec entry.identityIndex entry.owner state.1.pool.1
          (((state.2 entry.identityIndex).map Receipt.attempts).getD [])

/-- Every other actual source operation retains its entire native return state and leaves the historical constructor/attempt bookkeeping unchanged. -/
def lift (work : StateT (PqxdhRegistrationJointSchedule.State KemSK) ProbComp Result) : StateT (State KemSK) ProbComp Result :=
  fun state => (fun result => (result.1, result.2, state.2)) <$> work.run state.1

noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (StateT (State KemSK) ProbComp)
  | .inl (.inr (.create pin keyId)) => create setup pin keyId
  | .inl (.inr (.bundle address)) => bundle setup codec address
  | query => lift (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query)

/-- Forgetting only the private receipt ledger retains the complete actual source bundle outcome and poststate, with the same one-time sample and either writer result. -/
theorem bundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$> (bundle setup codec address).run state =
      (PqxdhRegistrationJointSchedule.bundle setup codec address).run state.1 := by
  cases found : state.1.owners[address]? <;>
    simp only [bundle, PqxdhRegistrationJointSchedule.bundle, StateT.run, found, map_pure, Functor.map_map]
  case some entry =>
    simpa only [Functor.map_map] using congrArg
      (fun work => (fun result : PqxdhRegistrationJointAttemptTrace.NativeResult KemSK =>
        (result.1.1, { state.1 with
          pool := (result.2, state.1.pool.2),
          owners := state.1.owners.set address { entry with owner := result.1.2 } })) <$> work)
      (PqxdhRegistrationJointAttemptTrace.trace_source setup codec entry.identityIndex entry.owner state.1.pool.1
        (((state.2 entry.identityIndex).map Receipt.attempts).getD []))

/-- Receipt creation is bookkeeping on the same actual constructor draw and complete native state. -/
theorem create_source (setup : Setup baseSpec KemSK) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$> (create setup pin keyId).run state =
      (PqxdhRegistrationJointSchedule.create setup pin keyId).run state.1 := by
  simp only [create, created, PqxdhRegistrationJointSchedule.create, StateT.run, Functor.map_map]

/-- Unchanged source callbacks preserve their complete native return distribution when the private ledger is forgotten. -/
theorem lift_source (work : StateT (PqxdhRegistrationJointSchedule.State KemSK) ProbComp Result) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$> (lift work).run state = work.run state.1 := by
  simp only [lift, StateT.run, Functor.map_map, Prod.mk.eta, id_map']

/-- Every actual source command has its exact old reply and complete native poststate after erasing the ledger. No source request or reply is filtered by an invariant. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$> (handler setup codec checks seed identityIndex query).run state =
      (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state.1 := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request <;> first
    | exact create_source setup _ _ state
    | exact bundle_source setup codec _ state
    | exact lift_source _ state
  all_goals exact lift_source _ state

/-- The whole adaptive source execution, including its final decision and every native/private state coordinate, is unchanged after receipt erasure. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler setup codec checks seed identityIndex) work).run state =
        (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex) work).run state.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun result =>
          (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex) (next result.1)).run result.2)
        (query_source setup codec checks seed identityIndex query state)

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.bundle_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.create_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.lift_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.lift_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger.program_source
