-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit

/-! The public log and complete private occurrence audit are retained jointly in one source execution, so the common authentication event refers to the same record publication that the raw API exposes. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhServerAuthRootOccurrences PqxdhServerAuthRootExecution PqxdhServerAuthEntryFactor
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- Logging the public client and reading the private call receipts agree jointly with every private occurrence, original state field and public result. The entire previous journal is retained on both sides. -/
theorem program_journal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (work : OracleComp ServerAuthSpec Result) (before : PqxdhServerAuthRootOccurrences.Audit KemSK) :
    (fun result => ((result.1, result.2.2.map publicCall), result.2)) <$>
      (simulateQ (handler setup codec checks publicValue beaconSeed) work).run before =
      (fun result => ((result.1.1, before.2.map publicCall ++ result.1.2), result.2)) <$>
        (simulateQ (handler setup codec checks publicValue beaconSeed)
          (PqxdhServerAuthApiJournal.record work)).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp [PqxdhServerAuthApiJournal.record]
  | query_bind query next ih =>
      unfold PqxdhServerAuthApiJournal.record
      rw [run_simulateQ_loggingOracle_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind,
        simulateQ_map, StateT.run_map, Functor.map_map]
      simp_rw [ih]
      simp only [handler, StateT.run, bind_map_left, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, publicCall, PqxdhServerAuthApiJournal.record]


/-- The shared primitive-family interpreter preserves the joint public log and complete private occurrence outcome. -/
theorem execution_journal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (work : OracleComp ServerAuthSpec Result) :
    (fun result => (((result.1.1, result.1.2.2.map publicCall), result.1.2), result.2)) <$>
      execution setup codec checks context work =
        execution setup codec checks context (PqxdhServerAuthApiJournal.record work) := by
  have same := congrArg (fun program =>
    (simulateQ (family setup context.seed context.scalar) program).run PqxdhJointDhExtractFamily.empty)
    (program_journal setup codec checks (context.publicValue setup) context.beaconSeed work
      (contextState setup context, []))
  simpa only [execution, simulateQ_map, StateT.run_map, List.map_nil, List.nil_append, Prod.eta, id_map'] using same

/-- Attach the actual public suffix log to the caller's return value while preserving every common-event receipt and local sample. -/
def recorded (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result) :
    PqxdhRegistrationR1RootAudit.RootAudit KemSK (Result × QueryLog ServerAuthSpec) :=
  ((audit.1, audit.2.state.2.map publicCall), audit.2)

/-- Adding the public journal to the source-ordered run keeps the exact same private common-event outcome. It does not independently rerun or reconstruct that outcome. -/
theorem recorded_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result) :
    recorded <$> PqxdhRegistrationR1RootAudit.rootAudited setup codec checks serverSeed work =
      PqxdhRegistrationR1RootAudit.rootAudited setup codec checks serverSeed
        (fun published => PqxdhServerAuthApiJournal.record (work published)) := by
  simp only [PqxdhRegistrationR1RootAudit.rootAudited, map_bind, map_pure]
  refine bind_congr fun value => ?_
  refine bind_congr fun oneTime => ?_
  refine bind_congr fun published => ?_
  rw [← execution_journal]
  simp only [bind_map_left, recorded]

/-- Mapping a final return value changes no source callback, occurrence receipt or primitive state. -/
theorem execution_map {Output : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (work : OracleComp ServerAuthSpec Result) (f : Result → Output) :
    execution setup codec checks context (f <$> work) =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        execution setup codec checks context work := by
  simp only [execution, simulateQ_map, StateT.run_map]

/-- The actual two prefix replies followed by the public projection of this same private callback journal. Every field of the common-event outcome survives. -/
def surfaceRecorded (setup : Setup baseSpec KemSK) (created : Option Nat)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result) :
    PqxdhRegistrationR1RootAudit.RootAudit KemSK (Result × QueryLog PqxdhRegistrationSchedule.SurfaceSpec) :=
  ((audit.1, PqxdhRegistrationR1Journal.prefixLog (contextInput setup false audit.2.context) created ++
      PqxdhRegistrationR1Journal.restrictLog (audit.2.state.2.map publicCall)), audit.2)

/-- The surface journal is attached to the exact full common-event outcome, including all private root receipts. Thus the accepted-record origin and the public publication refer to the same run. -/
theorem recorded_surface (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (created : Option Nat) (work : AuthInput → OracleComp ServerAuthSpec Result) :
    surfaceRecorded setup created <$> PqxdhRegistrationR1RootAudit.rootAudited setup codec checks serverSeed
      (fun published => work ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩) =
      PqxdhRegistrationR1RootAudit.rootAudited setup codec checks serverSeed
        (fun published => PqxdhRegistrationR1Journal.journalWork work created
          ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩) := by
  simp only [PqxdhRegistrationR1RootAudit.rootAudited, map_bind, map_pure]
  refine bind_congr fun value => ?_
  refine bind_congr fun oneTime => ?_
  refine bind_congr fun published => ?_
  have logging (client : OracleComp ServerAuthSpec Result) :
      (simulateQ loggingOracle client).run = PqxdhServerAuthApiJournal.record client := rfl
  simp only [PqxdhRegistrationR1Journal.journalWork, logging, execution_map, bind_map_left]
  rw [← execution_journal]
  simp only [bind_map_left, surfaceRecorded, contextInput, Context.publicValue,
    challenge, Bool.false_eq_true, ite_false]

end BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal


/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.program_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.program_journal
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.execution_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.execution_journal
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.recorded_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.recorded_root
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.execution_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.execution_map
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.recorded_surface' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootJournal.recorded_surface
