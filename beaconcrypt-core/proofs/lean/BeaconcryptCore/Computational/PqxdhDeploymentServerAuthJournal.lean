-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome

/-! The journal of a ServerAuth client in the root-audited singleton execution (CE-8). On every outcome of the occurrence execution, the client's return value is a possible return value of the client program (`execution_client`), and when the client journals its own queries, that journal is the public projection of the private callback receipts of the same run (`execution_log`). The root-audited singleton run is one occurrence execution on its own sampled context (`audited_member`), so on its outcomes the client's return value is a possible return value of the client on the target's published Phase 1 (`audited_client`) and its own journal is the public journal of the outcome (`audited_log`); for every Server seed the generator can draw, its outcome is an outcome of the Server-authentication game of the same client with its return value discarded (`audited_game`). `audited_failure` combines these with `PqxdhDeploymentServerAuthOutcome.game_failure`: a successful finish in the client's own journal, and no session with both an earlier publication of the accepted decoded record and an accept carrying the target's published keys, give the common authentication failure. No security claim is made here. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhJointIdentity
open PqxdhServerAuthRootExecution (Outcome publicCall)
open PqxdhRegistrationR1RootAudit (rootAudited)
open PqxdhDeploymentTranscript (candidateOf acceptedKeys)
open PqxdhDeploymentServerAuthEvent (keysOfBundle)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- On every outcome of the occurrence execution, the client's return value is a possible return value of the client program. -/
theorem execution_client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (client : OracleComp ServerAuthSpec Result)
    (outcome : (Result × PqxdhServerAuthRootOccurrences.Audit KemSK) × PqxdhJointDhExtractFamily.State)
    (member : outcome ∈ support (PqxdhServerAuthRootExecution.execution setup codec checks context client)) :
    outcome.1.1 ∈ support client := by
  have inner : outcome.1 ∈ support ((simulateQ (PqxdhServerAuthRootOccurrences.handler setup codec checks
      (context.publicValue setup) context.beaconSeed) client).run (contextState setup context, [])) := by
    apply support_simulateQ_run'_subset (PqxdhServerAuthRootOccurrences.family setup context.seed context.scalar) _
      PqxdhJointDhExtractFamily.empty
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ member
  apply support_simulateQ_run'_subset (PqxdhServerAuthRootOccurrences.handler setup codec checks
    (context.publicValue setup) context.beaconSeed) client (contextState setup context, [])
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ inner

/-- On every outcome of the occurrence execution of a client that journals its own queries, the client's journal is the public projection of the callback receipts. -/
theorem execution_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (client : OracleComp ServerAuthSpec Result)
    (outcome : ((Result × QueryLog ServerAuthSpec) × PqxdhServerAuthRootOccurrences.Audit KemSK) ×
      PqxdhJointDhExtractFamily.State)
    (member : outcome ∈ support (PqxdhServerAuthRootExecution.execution setup codec checks context
      (PqxdhServerAuthApiJournal.record client))) :
    outcome.1.1.2 = outcome.1.2.2.map publicCall := by
  have inner : outcome.1 ∈ support ((simulateQ (PqxdhServerAuthRootOccurrences.handler setup codec checks
      (context.publicValue setup) context.beaconSeed) (PqxdhServerAuthApiJournal.record client)).run
        (contextState setup context, [])) := by
    apply support_simulateQ_run'_subset (PqxdhServerAuthRootOccurrences.family setup context.seed context.scalar) _
      PqxdhJointDhExtractFamily.empty
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ member
  have projected := PqxdhServerAuthRootExecution.program_public setup codec checks (context.publicValue setup)
    context.beaconSeed (PqxdhServerAuthApiJournal.record client) (contextState setup context, [])
  have mapped := Set.mem_image_of_mem (fun result : ((Result × QueryLog ServerAuthSpec) ×
      PqxdhServerAuthRootOccurrences.Audit KemSK) => ((result.1, result.2.2.map publicCall), result.2.1)) inner
  rw [← support_map, projected, support_map] at mapped
  obtain ⟨other, otherMember, otherEq⟩ := mapped
  have logged : other.1 ∈ support (PqxdhServerAuthApiJournal.record (PqxdhServerAuthApiJournal.record client)) := by
    apply support_simulateQ_run'_subset (authHandler setup codec checks (context.publicValue setup)
      context.beaconSeed) _ (contextState setup context)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ otherMember
  have self := OracleComp.withQueryLog_self_log_eq client (v := other.1.1.1) (l₁ := other.1.1.2) (l₂ := other.1.2)
    logged
  have first := congrArg (fun value => value.1.1) otherEq
  have second := congrArg (fun value => value.1.2) otherEq
  simp only [List.map_nil, List.nil_append] at first second
  rw [← first, ← second, self]

/-- A root-audited singleton outcome is one occurrence execution of the client on the target's published Phase 1, on the outcome's own context. -/
theorem audited_member (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result)
    (member : audit ∈ support (rootAudited setup codec checks serverSeed work)) :
    audit.2.context.seed = serverSeed ∧
    ∃ result ∈ support (PqxdhServerAuthRootExecution.execution setup codec checks audit.2.context
        (work audit.2.context.published.1)),
      audit.1 = result.1.1 ∧ audit.2.state = result.1.2 ∧ audit.2.primitive = result.2 := by
  simp only [rootAudited, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨value, _, oneTime, _, published, _, result, reached, rfl⟩ := member
  exact ⟨rfl, result, reached, rfl, rfl, rfl⟩

/-- On every root-audited singleton outcome, the client's return value is a possible return value of the client on the target's published Phase 1. -/
theorem audited_client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result)
    (member : audit ∈ support (rootAudited setup codec checks serverSeed work)) :
    audit.1 ∈ support (work audit.2.context.published.1) := by
  obtain ⟨_, result, reached, same, _, _⟩ := audited_member setup codec checks serverSeed work audit member
  rw [same]
  exact execution_client setup codec checks _ _ result reached

/-- On every root-audited singleton outcome of a client that journals its own queries, that journal is the public journal of the outcome. -/
theorem audited_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (client : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK (Result × QueryLog ServerAuthSpec))
    (member : audit ∈ support (rootAudited setup codec checks serverSeed
      (fun published => PqxdhServerAuthApiJournal.record (client published)))) :
    audit.1.2 = audit.2.state.2.map publicCall := by
  obtain ⟨_, result, reached, same, state, _⟩ := audited_member setup codec checks serverSeed _ audit member
  rw [same, state]
  exact execution_log setup codec checks _ _ result reached

set_option linter.deprecated false in
/-- For every Server seed the generator can draw, a root-audited singleton outcome is an outcome of the Server-authentication game of the same client with its return value discarded. -/
theorem audited_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (seeded : serverSeed ∈ support sampleSeed)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result)
    (member : audit ∈ support (rootAudited setup codec checks serverSeed
      (fun published => work ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩))) :
    audit.2 ∈ support (PqxdhServerAuthRootExecution.game setup codec checks false
      (fun input => (fun _ => ()) <$> work input)) := by
  have ordered : audit.2 ∈ support (PqxdhServerAuthRootObserved.orderedGame setup codec checks false
      (fun input => (fun _ => ()) <$> work input)) := by
    rw [← PqxdhRegistrationR1RootAudit.generated_order setup codec checks work, mem_support_bind_iff]
    exact ⟨serverSeed, seeded, by rw [support_map]; exact Set.mem_image_of_mem _ member⟩
  have same := congrArg (fun measure => measure {true})
    (PqxdhServerAuthRootObserved.observation_order (Result := Bool) setup codec checks false
      (fun input => (fun _ => ()) <$> work input) (fun outcome => @decide (outcome = audit.2) (Classical.propDecidable _)))
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def,
    decide_eq_true_eq] at same
  have positive : Pr[fun outcome => outcome = audit.2 | PqxdhServerAuthRootObserved.orderedGame setup codec checks false
      (fun input => (fun _ => ()) <$> work input)] ≠ 0 := probEvent_ne_zero_iff.mpr ⟨_, ordered, rfl⟩
  rw [← same] at positive
  obtain ⟨outcome, reached, rfl⟩ := probEvent_ne_zero_iff.mp positive
  exact reached

/-- On a root-audited singleton outcome of a client that journals its own queries, a successful finish in that journal and no session with both an earlier publication of the accepted decoded record and an accept carrying the target's published keys give the common authentication failure. -/
theorem audited_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (serverSeed : IdentitySeed)
    (seeded : serverSeed ∈ support sampleSeed) (client : AuthInput → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK (Result × QueryLog ServerAuthSpec))
    (member : audit ∈ support (rootAudited setup codec checks serverSeed
      (fun published => PqxdhServerAuthApiJournal.record
        (client ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩))))
    (raw payload : Pqxdh.Bytes)
    (finished : (⟨.inr (.finish raw), some payload⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
      audit.1.2)
    (unmatched : ∀ index, PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index audit.1.2 →
      ∀ acceptRaw candidate keys,
        (⟨.inr (.accept acceptRaw), some index⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
          audit.1.2 →
        candidateOf codec acceptRaw = some candidate → acceptedKeys setup.source.crypto candidate = some keys →
        keysOfBundle codec audit.2.context.published.1 ≠ some keys) :
    PqxdhServerAuthCommonProbability.decision setup codec checks audit.2 = true := by
  have logEq := audited_log setup codec checks serverSeed _ audit member
  have game := audited_game setup codec checks serverSeed seeded
    (fun input => PqxdhServerAuthApiJournal.record (client input)) audit member
  rw [logEq] at finished unmatched
  have failure := PqxdhDeploymentServerAuthOutcome.game_failure setup codec checks phase1 _ audit.2 game raw payload
    finished unmatched
  exact @decide_eq_true _ (Classical.propDecidable _) failure

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.execution_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.execution_client

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.execution_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.execution_log

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_member

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_client

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_log

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_failure
