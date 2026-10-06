-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports

/-! Key-list monotonicity and the recorded raw bytes along the report-run continuation after the selected raw accept. In the report run the private KEM pool lives in the local state of the identity compiler, under the public-report extension, the identity router and the report interpreter. Creation appends one key pair and every other KEM, coin, runtime, import or report step keeps the key list, so the key list reached at the cut is a prefix of the final key list of the same execution. The final tag of the coupled execution records exactly the raw bytes suspended at the cut. Both facts are support statements about the literal executions; no probability is involved. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone
open PqxdhServerAuthExperiment
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut)
open PqxdhRegistrationJointAcceptCutTag (Tag tagFinish)
open PqxdhRegistrationJointAcceptCutReports (resume continuation split)
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
open PqxdhRegistrationJointIdentityCompiler (Local)
open PqxdhRegistrationJointReportLift (extend)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response X Y Result : Type}

/-- An oracle interpretation only removes results of an oracle program. -/
theorem simulate_result {κ κ' : Type} {spec : OracleSpec κ} {target : OracleSpec κ'}
    (impl : QueryImpl spec (OracleComp target)) (work : OracleComp spec Result) (result : Result)
    (reached : result ∈ support (simulateQ impl work)) : result ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa using reached
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
    obtain ⟨answer, _, reached⟩ := reached
    exact (mem_support_bind_iff _ _ _).mpr ⟨answer, mem_support_query query answer, ih answer reached⟩

/-- One private KEM pool step keeps the key list as a prefix: creation appends one pair, and decapsulation and reveal only extend the transcript. -/
theorem pool_keys (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (query : PqxdhLiveKemBirth.Query) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (result : PqxdhLiveKemBirth.Range KemSK query × PqxdhLiveKemBirth.Pool KemSK)
    (supported : result ∈ support ((PqxdhLiveKemBirth.poolImpl baseImpl kem query).run pool)) :
    pool.keys <+: result.2.keys := by
  cases query with
  | create =>
    change result ∈ support (PqxdhLiveKemBirth.created pool <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen) at supported
    rw [support_map] at supported
    obtain ⟨pair, _, rfl⟩ := supported
    exact List.prefix_append _ _
  | decapsulate handle ciphertext =>
    dsimp only [PqxdhLiveKemBirth.poolImpl, StateT.run] at supported
    split at supported <;>
    · rw [mem_support_bind_iff] at supported
      obtain ⟨answer, _, supported⟩ := supported
      rw [mem_support_pure_iff] at supported
      subst supported
      exact List.prefix_refl _
  | reveal handle =>
    dsimp only [PqxdhLiveKemBirth.poolImpl, StateT.run] at supported
    rw [mem_support_pure_iff] at supported
    subst supported
    exact List.prefix_refl _

/-- One step of the identity compiler keeps the local key list as a prefix: forwarded identity, coin and import requests and runtime initialization leave the pool unchanged, and KEM requests run the private pool step. -/
theorem impl_keys (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (query : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain) (localState : Local KemSK A)
    (result : (PqxdhRegistrationJointServerBirth.Spec KemSK).Range query × Local KemSK A)
    (supported : result ∈ support
      ((PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit query).run localState)) :
    localState.1.keys <+: result.2.1.keys := by
  rcases query with ((joint | (coin | pool)) | (_ | seed))
  · simp only [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
      StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact List.prefix_refl _
  · simp only [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
      StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact List.prefix_refl _
  · have inner := simulate_result _ _ result supported
    simp only [PqxdhRegistrationJointIdentityCompiler.onKem, support_map, Set.mem_image] at inner
    obtain ⟨step, stepped, rfl⟩ := inner
    exact pool_keys setup.baseImpl setup.kem pool localState.1 step stepped
  · have inner := simulate_result _ _ result supported
    simp only [PqxdhRegistrationJointIdentityCompiler.onRuntime, support_map, Set.mem_image] at inner
    obtain ⟨step, _, rfl⟩ := inner
    exact List.prefix_refl _
  · simp only [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
      StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact List.prefix_refl _

/-- One step of the identity compiler extended with public reports keeps the local key list as a prefix; a public report leaves the local state unchanged. -/
theorem extend_keys (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (query : (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)).Domain)
    (localState : Local KemSK A)
    (result : (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)).Range query ×
      Local KemSK A)
    (supported : result ∈ support
      ((extend (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit) query).run localState)) :
    localState.1.keys <+: result.2.1.keys := by
  rcases query with query | report
  · exact impl_keys setup ensureInit query localState result (simulate_result _ _ result supported)
  · change result ∈ support ((fun _ => ((), localState)) <$> _) at supported
    rw [support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact List.prefix_refl _

/-- Every adaptive program under the extended identity compiler keeps the local key list of its starting state as a prefix of its final local key list. -/
theorem program_keys (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) Result)
    (localState : Local KemSK A) (result : Result × Local KemSK A)
    (supported : result ∈ support
      ((simulateQ (extend (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit)) program).run localState)) :
    localState.1.keys <+: result.2.1.keys := by
  induction program using OracleComp.inductionOn generalizing localState with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst supported
    exact List.prefix_refl _
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, after⟩, stepped, rest⟩ := supported
    exact (extend_keys setup ensureInit query localState (answer, after) stepped).trans (ih answer after rest)

/-- The report-compiler identity reduction keeps the local key list of its starting state as a prefix of the final local key list. -/
theorem reduction_keys (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) Result)
    (localState : Local KemSK A) (registry : PqxdhRegistrationJointIdentityRouting.Registry)
    (result : (Result × Local KemSK A) × PqxdhRegistrationJointIdentityRouting.Registry)
    (supported : result ∈ support
      (PqxdhRegistrationJointReportCompiler.reduction setup ensureInit program localState registry)) :
    localState.1.keys <+: result.1.2.1.keys := by
  have inner : result.1 ∈ support
      ((simulateQ (extend (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit)) program).run localState) := by
    apply support_simulateQ_run'_subset (extend (PqxdhRegistrationJointIdentityRouting.route setup.joint)) _ registry
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ supported
  exact program_keys setup ensureInit program localState result.1 inner

/-- The report-run continuation from a reached outcome keeps the reached private KEM key list as a prefix of the final private KEM key list. -/
theorem continuation_keys (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (count : Nat) (next : X → OracleComp (Spec KemSK) Y)
    (reached : ReportResult KemSK A X count) (final : ReportResult KemSK A Y count)
    (supported : final ∈ support (continuation setup codec checks ensureInit count next reached)) :
    (sourceResult reached).2.1.2.keys <+: (sourceResult final).2.1.2.keys := by
  have inner : final.1 ∈ support (PqxdhRegistrationJointReportCompiler.reduction setup ensureInit
      (resume setup codec checks count next reached.1.1.1) reached.1.1.2 reached.1.2) := by
    apply support_simulateQ_run'_subset (PqxdhJointPhase1Reports.sourceImpl setup.joint count) _ reached.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ supported
  exact reduction_keys setup ensureInit _ reached.1.1.2 reached.1.2 final.1 inner

/-- In the coupling of the cut with the final outcome, the private KEM key list reached at the cut is a prefix of the final private KEM key list of the same execution. -/
theorem resume_keys_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (pair : ReportResult KemSK A (Cut KemSK X) count × ReportResult KemSK A (X × Tag) count)
    (supported : pair ∈ support (split setup codec checks ensureInit supplied count work index runtime)) :
    (sourceResult pair.1).2.1.2.keys <+: (sourceResult pair.2).2.1.2.keys := by
  simp only [split, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reached, _, final, continued, rfl⟩ := supported
  exact continuation_keys setup codec checks ensureInit count tagFinish reached final continued

/-- Every program result of the reported command compiler is a result of the original program. -/
theorem reported_result (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (count : Nat)
    (program : OracleComp (Spec KemSK) Result) (state : PqxdhRegistrationJointReportCommands.State KemSK)
    (result : Result × PqxdhRegistrationJointReportCommands.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointReportCommands.reported setup codec checks identityIndex
      publicIdentity count program).run state)) :
    result.1 ∈ support program := by
  apply simulate_result (PqxdhRegistrationJointRawReports.instrument codec count) program
  apply support_simulateQ_run'_subset (extend fun query => PqxdhRegistrationJointReportCommands.commands setup codec
    checks identityIndex publicIdentity ((Spec KemSK).query query)) _ state
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ supported

/-- In the coupling of the cut with the final outcome, a pending cut on `raw` ends with a final tag that records exactly `raw` together with the public reply of the selected accept. -/
theorem resume_tag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (pair : ReportResult KemSK A (Cut KemSK X) count × ReportResult KemSK A (X × Tag) count)
    (supported : pair ∈ support (split setup codec checks ensureInit supplied count work index runtime))
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (Cut KemSK X))
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) X)
    (finished : (sourceResult pair.1).1 = some encoded) (pending : encoded.2.1 = .pending raw next) :
    ∃ final answer, (sourceResult pair.2).1 = some final ∧ final.2.1.2 = some (raw, answer) := by
  simp only [split, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reached, _, final, continued, rfl⟩ := supported
  dsimp only at finished ⊢
  rcases equation : reached.1.1.1 with _ | outcome
  · simp [sourceResult, PqxdhRegistrationJointIdentityCompiler.initializedResult,
      PqxdhRegistrationJointIdentityCompiler.projectResult, equation] at finished
  · have recorded : outcome.2.1 = .pending raw next := by
      simp only [sourceResult, PqxdhRegistrationJointIdentityCompiler.initializedResult,
        PqxdhRegistrationJointIdentityCompiler.projectResult, equation, Option.map_some, Option.some.injEq] at finished
      rw [← finished] at pending
      exact pending
    have reduced : final.1 ∈ support (PqxdhRegistrationJointReportCompiler.reduction setup ensureInit
        (resume setup codec checks count tagFinish reached.1.1.1) reached.1.1.2 reached.1.2) := by
      apply support_simulateQ_run'_subset (PqxdhJointPhase1Reports.sourceImpl setup.joint count) _ reached.2
      rw [StateT.run'_eq, support_map]
      exact Set.mem_image_of_mem _ continued
    have compiled : final.1.1 ∈ support ((simulateQ (extend (PqxdhRegistrationJointIdentityCompiler.impl setup
        ensureInit)) (resume setup codec checks count tagFinish reached.1.1.1)).run reached.1.1.2) := by
      apply support_simulateQ_run'_subset (extend (PqxdhRegistrationJointIdentityRouting.route setup.joint)) _
        reached.1.2
      rw [StateT.run'_eq, support_map]
      exact Set.mem_image_of_mem _ reduced
    have resumed : final.1.1.1 ∈ support (resume setup codec checks count tagFinish reached.1.1.1) := by
      apply support_simulateQ_run'_subset (extend (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit)) _
        reached.1.1.2
      rw [StateT.run'_eq, support_map]
      exact Set.mem_image_of_mem _ compiled
    rw [equation, resume, support_map] at resumed
    obtain ⟨result, reportedRun, same⟩ := resumed
    have tagged := reported_result setup codec checks _ _ count _ _ result reportedRun
    rw [recorded, tagFinish, mem_support_bind_iff] at tagged
    obtain ⟨answer, _, tagged⟩ := tagged
    rw [support_map] at tagged
    obtain ⟨value, _, recordedResult⟩ := tagged
    simp only [sourceResult, PqxdhRegistrationJointIdentityCompiler.initializedResult,
      PqxdhRegistrationJointIdentityCompiler.projectResult, ← same, Option.map_some]
    exact ⟨_, answer, rfl, by simp only [PqxdhRegistrationJointOpenInitialization.attach, ← recordedResult]⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.simulate_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.simulate_result

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.pool_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.pool_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.impl_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.impl_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.extend_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.extend_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.program_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.program_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.reduction_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.reduction_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.continuation_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.continuation_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.resume_keys_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.resume_keys_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.reported_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.reported_result

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.resume_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone.resume_tag
