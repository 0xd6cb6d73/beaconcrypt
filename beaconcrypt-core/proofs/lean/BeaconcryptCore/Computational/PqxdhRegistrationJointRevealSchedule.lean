-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead

/-! The actual adaptive registration schedule extended with explicit current Beacon field reads. Reads can be interleaved anywhere, including before or after finish. The complete native and private service states remain in one execution; this module proves representation and capability correspondence, not that a revealed target stays fresh. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointLiveRead
open PqxdhRegistrationJointGeneratedFinish (EncodedState encodeState)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

abbrev Spec (KemSK : Type) := PqxdhRegistrationSchedule.Spec + ReadSpec KemSK

noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (Spec KemSK) (PqxdhRegistrationJointServiceSchedule.Client KemSK Response)
  | .inl query => PqxdhRegistrationJointServiceSchedule.handler setup codec query
  | .inr request => clientStep request

noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) :
    QueryImpl (Spec KemSK) (StateT (PqxdhRegistrationJointSchedule.State KemSK) ProbComp)
  | .inl query => PqxdhRegistrationJointSchedule.handler setup codec checks serverSeed query
  | .inr request => fun state => pure (sourceStep request state)

noncomputable def native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) :
    QueryImpl (Spec KemSK) (StateT (PqxdhRegistrationSchedule.State KemSK) ProbComp)
  | .inl query => PqxdhRegistrationSchedule.handler setup codec checks serverSeed query
  | .inr request => fun state => pure (nativeStep request state)

/-- Every original or compromise request has the same reply and complete encoded poststate as its native source execution. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    PqxdhRegistrationJointServiceSchedule.execute setup codec checks serverSeed (client setup codec query) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (source setup codec checks serverSeed query).run state := by
  cases query with
  | inl query => exact PqxdhRegistrationJointServiceSchedule.query_source setup codec checks serverSeed query state owned
  | inr request => simpa only [client, source, StateT.run, map_pure] using read_source setup codec checks serverSeed request state owned

/-- Each supported reply preserves ownership, including every actual disclosure before or after terminal phase changes. -/
theorem query_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (result : (Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (owned : PqxdhRegistrationJointSchedule.Invariant state)
    (supported : result ∈ support ((source setup codec checks serverSeed query).run state)) :
    PqxdhRegistrationJointSchedule.Invariant result.2 := by
  cases query with
  | inl query => exact PqxdhRegistrationJointSchedule.query_owned setup codec checks serverSeed query state result owned supported
  | inr request =>
      have equality : result = sourceStep request state := by
        simpa only [source, StateT.run, support_pure, Set.mem_singleton_iff] using supported
      simpa only [equality] using read_owned request state owned

/-- All adaptive interleavings of original requests and current-field disclosures have the exact full encoded source distribution. Compromise is not silently excluded by the representation invariant. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    PqxdhRegistrationJointServiceSchedule.execute setup codec checks serverSeed
      (simulateQ (client setup codec) program) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (simulateQ (source setup codec checks serverSeed) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [PqxdhRegistrationJointServiceSchedule.execute, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRegistrationJointServiceSchedule.execute_bind,
        query_source setup codec checks serverSeed query state owned, bind_map_left, StateT.run_bind, map_bind]
      apply bind_congr_of_forall_mem_support
      exact fun result supported => ih result.1 result.2
        (query_owned setup codec checks serverSeed query state result owned supported)

/-- The empty owner registry discharges every generated-slot premise for arbitrary subsequent adaptive disclosure schedules. Initial private history may be arbitrary and stays private. -/
theorem generated_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp (Spec KemSK) Result)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (shared : NativeState KemSK) :
    PqxdhRegistrationJointServiceSchedule.execute setup codec checks serverSeed
      (simulateQ (client setup codec) program) ⟨pool, shared, []⟩ =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (simulateQ (source setup codec checks serverSeed) program).run
          (PqxdhRegistrationJointSchedule.initial pool shared) := by
  exact program_source setup codec checks serverSeed program (PqxdhRegistrationJointSchedule.initial pool shared)
    (PqxdhRegistrationJointSchedule.initial_owned pool shared)

/-- Each extended request projects to the same native reply and whole protocol state after forgetting only private analysis annotations. -/
theorem query_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
      (source setup codec checks serverSeed query).run state =
        (native setup codec checks serverSeed query).run (PqxdhRegistrationJointSchedule.source state) := by
  cases query with
  | inl query => exact PqxdhRegistrationJointSchedule.query_source setup codec checks serverSeed query state
  | inr request =>
      simpa only [source, native, StateT.run, map_pure] using
        congrArg (pure (f := ProbComp)) (read_projection request state)

/-- The entire extended adaptive schedule has the exact native distribution, including the current disclosed values and complete protocol state. -/
theorem program_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
      (simulateQ (source setup codec checks serverSeed) program).run state =
        (simulateQ (native setup codec checks serverSeed) program).run (PqxdhRegistrationJointSchedule.source state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun result => (simulateQ (native setup codec checks serverSeed) (next result.1)).run result.2)
        (query_projection setup codec checks serverSeed query state)

end BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.query_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.query_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.generated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.generated_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.query_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.query_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRevealSchedule.program_projection
