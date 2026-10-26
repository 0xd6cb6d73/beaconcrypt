-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationR1Journal
import BeaconcryptCore.Computational.PqxdhServerAuthRootObserved

/-! The singleton registration source and common authentication event share one execution, including its private callback receipts and public journal. No event witness is reconstructed from an erased state. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerAuthEntryFactor
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- Remove only the occurrence journal, retaining the public result and both complete native states. -/
def nativeOf (result : (Result × PqxdhServerAuthRootOccurrences.Audit KemSK) ×
    PqxdhJointDhExtractFamily.State) : Result × NativeState KemSK :=
  (result.1.1, (result.2, result.1.2.1))

set_option backward.isDefEq.respectTransparency false in
/-- The original occurrence execution is the literal native adaptive execution after journal erasure. The generic invariant will be discharged by the actual Phase 1 result. -/
theorem native_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (work : OracleComp ServerAuthSpec Result)
    (invariant : GameInv Reader Response setup (context.publicValue setup) (contextState setup context)) :
    nativeOf <$> PqxdhServerAuthRootExecution.execution setup codec checks context work =
      (simulateQ (nativeHandler setup codec checks context.seed context.scalar context.beaconSeed) work).run
        (PqxdhRegistrationR1Initial.sourceInitial setup context.seed context.scalar context.published.2) := by
  rw [← program_native setup codec checks context.seed context.scalar context.beaconSeed work
    (PqxdhRegistrationR1Initial.sourceInitial setup context.seed context.scalar context.published.2) invariant]
  change (fun result : (Result × PqxdhServerAuthRootOccurrences.Audit KemSK) ×
    PqxdhJointDhExtractFamily.State => (result.1.1, (result.2, result.1.2.1))) <$>
      PqxdhServerAuthRootExecution.execution setup codec checks context work = _
  simpa only [evaluate, PqxdhRegistrationR1Initial.sourceInitial,
    PqxdhServerAuthRootOccurrences.family, Context.publicValue, contextState, Functor.map_map] using
    congrArg (Functor.map (fun result => (result.1.1, (result.2, result.1.2))))
      (PqxdhServerAuthRootExecution.execution_erase setup codec checks context work)

set_option backward.isDefEq.respectTransparency false in
/-- The same occurrence execution retains exactly the original public query/reply journal jointly with both complete native states and the actual result. -/
theorem native_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (work : OracleComp ServerAuthSpec Result)
    (invariant : GameInv Reader Response setup (context.publicValue setup) (contextState setup context)) :
    (fun result => ((result.1.1, result.1.2.2.map PqxdhServerAuthRootExecution.publicCall),
      (result.2, result.1.2.1))) <$>
        PqxdhServerAuthRootExecution.execution setup codec checks context work =
      (simulateQ (nativeHandler setup codec checks context.seed context.scalar context.beaconSeed)
        (PqxdhServerAuthApiJournal.record work)).run
          (PqxdhRegistrationR1Initial.sourceInitial setup context.seed context.scalar context.published.2) := by
  rw [← program_native setup codec checks context.seed context.scalar context.beaconSeed
    (PqxdhServerAuthApiJournal.record work)
    (PqxdhRegistrationR1Initial.sourceInitial setup context.seed context.scalar context.published.2) invariant]
  simpa only [evaluate, PqxdhRegistrationR1Initial.sourceInitial,
    PqxdhServerAuthRootOccurrences.family, Context.publicValue, contextState, Functor.map_map] using
    congrArg (Functor.map (fun result => (result.1.1, (result.2, result.1.2))))
      (PqxdhServerAuthRootObserved.execution_public setup codec checks context work)

/-- The exact lane input equals the authentication game's public context input. No Server seed is revealed. -/
theorem context_input (setup : Setup baseSpec KemSK) (context : Context KemSK) :
    (⟨setup.joint.publicKeys context.seed, setup.serverKeyId, context.published.1, none⟩ : AuthInput) =
      contextInput setup false context := rfl

/-- Full source outcome with the adversary's actual return value retained. The occurrence outcome contains all original local samples, both state components and the chronological private callback receipts. -/
abbrev RootAudit (KemSK Result : Type) := Result × PqxdhServerAuthRootExecution.Outcome KemSK

/-- Forget only the extra occurrence journal and fixed generation marker from the same run. -/
def toAudit (audit : RootAudit KemSK Result) : PqxdhRegistrationR1Initial.Audit KemSK Result :=
  ⟨⟨audit.2.context.beaconSeed, audit.2.context.scalar, audit.2.context.keys⟩,
    audit.2.context.oneTime, audit.2.context.published,
    (audit.1, (audit.2.primitive, audit.2.state.1))⟩

/-- The actual Beacon constructor, optional first bundle and adaptive suffix in source order, with one private occurrence execution. Failed publication is retained without an admission assumption. -/
noncomputable def rootAudited (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result) :
    ProbComp (RootAudit KemSK Result) := do
  let value ← PqxdhRegistrationJointCreation.material setup
  let oneTime ← sampleScalar
  let published ← phase1Run setup codec value.seed
    (challenge setup.joint setup.dh serverSeed value.prekey) oneTime value.keys.1 value.keys.2
  let context : Context KemSK := ⟨serverSeed, value.prekey, value.seed, oneTime, value.keys, published⟩
  let result ← PqxdhServerAuthRootExecution.execution setup codec checks context (work published.1)
  pure (result.1.1, ⟨context, .targetPhase1, result.1.2, result.2⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The original lane audit is the exact projection of this one occurrence execution. The source invariant follows from the actual optional Phase 1 result; no security conclusion, successful writer or honest target is assumed. -/
theorem audited_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result) :
    toAudit <$> rootAudited setup codec checks serverSeed work =
      PqxdhRegistrationR1Initial.audited setup codec checks serverSeed work := by
  simp only [rootAudited, PqxdhRegistrationR1Initial.audited, map_bind, map_pure]
  refine bind_congr fun value => ?_
  refine bind_congr fun oneTime => ?_
  apply OracleComp.bind_congr_of_forall_mem_support
  intro published supported
  simpa only [bind_pure_comp, Functor.map_map, nativeOf, toAudit] using
    congrArg (Functor.map (fun result =>
      (⟨value, oneTime, published, result⟩ : PqxdhRegistrationR1Initial.Audit KemSK Result)))
      (native_root setup codec checks ⟨serverSeed, value.prekey, value.seed, oneTime, value.keys, published⟩
        (work published.1) (inv_initial setup codec value.seed
          (challenge setup.joint setup.dh serverSeed value.prekey) oneTime value.keys.1 value.keys.2
          published supported))

/-- Read the actual public surface journal from the same occurrence outcome, prepending the concrete create and bundle replies. The private receipt fields never become public values. -/
def journalAudit (setup : Setup baseSpec KemSK) (created : Option Nat) (audit : RootAudit KemSK Result) :
    PqxdhRegistrationR1Initial.Audit KemSK (Result × QueryLog PqxdhRegistrationSchedule.SurfaceSpec) :=
  let original := toAudit audit
  { original with result := ((audit.1,
      PqxdhRegistrationR1Journal.prefixLog (contextInput setup false audit.2.context) created ++
        PqxdhRegistrationR1Journal.restrictLog
          (audit.2.state.2.map PqxdhServerAuthRootExecution.publicCall)), original.result.2) }

set_option backward.isDefEq.respectTransparency false in
/-- The common event's publication journal is the literal singleton surface journal in the same run. The entire native audit and its optional Phase 1 publication are preserved jointly with that journal. -/
theorem journal_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (created : Option Nat) (work : AuthInput → OracleComp ServerAuthSpec Result) :
    journalAudit setup created <$> rootAudited setup codec checks serverSeed
      (fun published => work ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩) =
    PqxdhRegistrationR1Initial.audited setup codec checks serverSeed
      (fun published => PqxdhRegistrationR1Journal.journalWork work created
        ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩) := by
  simp only [rootAudited, PqxdhRegistrationR1Initial.audited, map_bind, map_pure]
  refine bind_congr fun value => ?_
  refine bind_congr fun oneTime => ?_
  apply OracleComp.bind_congr_of_forall_mem_support
  intro published supported
  simpa only [PqxdhRegistrationR1Journal.journalWork, PqxdhServerAuthApiJournal.record,
    simulateQ_map, StateT.run_map, bind_map_left, bind_pure_comp, Functor.map_map,
    journalAudit, toAudit, contextInput, Context.publicValue, challenge, Bool.false_eq_true, ite_false] using
    congrArg (Functor.map (fun result =>
      (⟨value, oneTime, published,
        ((result.1.1, PqxdhRegistrationR1Journal.prefixLog
          ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published.1, none⟩ created ++
            PqxdhRegistrationR1Journal.restrictLog result.1.2), result.2)⟩ :
        PqxdhRegistrationR1Initial.Audit KemSK (Result × QueryLog PqxdhRegistrationSchedule.SurfaceSpec))))
      (native_public setup codec checks ⟨serverSeed, value.prekey, value.seed, oneTime, value.keys, published⟩
        (work ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published.1, none⟩)
        (inv_initial setup codec value.seed (challenge setup.joint setup.dh serverSeed value.prekey)
          oneTime value.keys.1 value.keys.2 published supported))

/-- Sampling the Server seed and then the actual Beacon constructor, first bundle and suffix is literally the authentication game's production order. Only the adversary's return value is discarded; the full outcome, context and receipts stay. -/
theorem generated_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (work : AuthInput → OracleComp ServerAuthSpec Result) :
    (do
      let serverSeed ← sampleSeed
      Prod.snd <$> rootAudited setup codec checks serverSeed
        (fun published => work ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩)) =
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false (fun input => (fun _ => ()) <$> work input) := by
  simp only [rootAudited, PqxdhRegistrationJointCreation.material,
    PqxdhServerAuthRootObserved.orderedGame, bind_assoc, pure_bind, map_bind, map_pure,
    PqxdhServerAuthRootExecution.execution, simulateQ_map, StateT.run_map, bind_map_left,
    contextInput, Context.publicValue, challenge, Bool.false_eq_true, ite_false]

end BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.native_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.native_root
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.native_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.native_public
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.context_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.context_input
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.audited_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.audited_root
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.journal_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.journal_public

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.generated_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1RootAudit.generated_order
