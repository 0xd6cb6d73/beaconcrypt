-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple

/-! Published-tuple provenance and replay events on the final transcript of the actual common deployment experiment, including every failed Fresh bundle encoding. These events contain no successful-publication or no-failure premise. The deterministic replay implication uses only actual registration consumption. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents
open PqxdhServerAuthExperiment
open PqxdhDeploymentPublishedTuple (OwnerForgery PublishedForgery DoubleAcceptAt DoubleAccept ownerIdentities
  publishedTuple filterMap_nodup_ne)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

abbrev Outcome (KemSK A X : Type) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A

/-- A successful accept under this created owner's identity carries a tuple other than its final published tuple, including an owner with no successful bundle. -/
def OwnerEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (owner : Nat)
    (outcome : Outcome KemSK A X) : Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    OwnerForgery setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) owner

/-- Published-tuple provenance failure at any created owner, with all rejected Fresh bundle calls retained. -/
def GameEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : Outcome KemSK A X) : Prop :=
  PqxdhDeploymentPublishedTuple.GameHolds setup (PublishedForgery setup.source.crypto codec) outcome

/-- Two distinct successful accepts under this created owner's identity, regardless of bundle encoding failures. -/
def ReplayOwnerEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (owner : Nat)
    (outcome : Outcome KemSK A X) : Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    DoubleAcceptAt setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) owner

/-- Two distinct successful accepts under any created owner's identity, with no bundle-failure filter. -/
def ReplayEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : Outcome KemSK A X) : Prop :=
  PqxdhDeploymentPublishedTuple.GameHolds setup (DoubleAccept setup.source.crypto codec) outcome

/-- The same unrestricted final published-tuple event on the report-instrumented original source execution. -/
def ReportEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : Nat}
    (outcome : PqxdhRegistrationJointInitializedReports.ReportResult KemSK A
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) count) : Prop :=
  PqxdhDeploymentPublishedTuple.ReportHolds (PublishedForgery setup.source.crypto codec) outcome

theorem game_owner (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (outcome : Outcome KemSK A X) :
    GameEvent setup codec outcome ↔ ∃ owner, OwnerEvent setup codec owner outcome := by
  constructor
  · rintro ⟨created, output, final, reached, forged⟩
    obtain ⟨owner, forged⟩ := (PqxdhDeploymentPublishedTuple.published_owner _ _ _ _).mp forged
    exact ⟨owner, created, output, final, reached, forged⟩
  · rintro ⟨owner, created, output, final, reached, forged⟩
    exact ⟨created, output, final, reached,
      (PqxdhDeploymentPublishedTuple.published_owner _ _ _ _).mpr ⟨owner, forged⟩⟩

theorem replay_owner (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (outcome : Outcome KemSK A X) :
    ReplayEvent setup codec outcome ↔ ∃ owner, ReplayOwnerEvent setup codec owner outcome := by
  constructor
  · rintro ⟨created, output, final, reached, doubled⟩
    obtain ⟨owner, doubled⟩ := (PqxdhDeploymentPublishedTuple.double_owner _ _ _ _).mp doubled
    exact ⟨owner, created, output, final, reached, doubled⟩
  · rintro ⟨owner, created, output, final, reached, doubled⟩
    exact ⟨created, output, final, reached,
      (PqxdhDeploymentPublishedTuple.double_owner _ _ _ _).mpr ⟨owner, doubled⟩⟩

/-- Actual one-use registration consumption makes one of two accepts at this owner differ from its final published tuple. Failed bundle encodings do not enter this argument. -/
theorem replay_owner_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Outcome KemSK A X)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime)) (owner : Nat)
    (replayed : ReplayOwnerEvent setup codec owner outcome) : OwnerEvent setup codec owner outcome := by
  obtain ⟨created, output, final, reached, first, second, different, raw, raw', session, session', candidate,
    candidate', identity, keys, keys', firstFound, secondFound, parsed, parsed', accepted, accepted', identityFound⟩ := replayed
  refine ⟨created, output, final, reached, ?_⟩
  by_contra notForged
  have firstTuple : publishedTuple codec final.1.transcript owner = some keys := by
    by_contra other
    exact notForged ⟨raw, session, List.mem_of_getElem? firstFound, candidate, identity, keys, parsed, accepted,
      identityFound, other⟩
  have secondTuple : publishedTuple codec final.1.transcript owner = some keys' := by
    by_contra other
    exact notForged ⟨raw', session', List.mem_of_getElem? secondFound, candidate', identity, keys', parsed',
      accepted', identityFound, other⟩
  have same : keys' = keys := Option.some.inj (secondTuple.symm.trans firstTuple)
  subst same
  have registered := PqxdhDeploymentReplay.registered_game setup codec checks route ensureInit identityIndex bounds mode
    adversary runtime outcome supported created output final reached
  exact filterMap_nodup_ne (PqxdhDeploymentReplay.entryRegistration setup.source.crypto codec) final.1.transcript
    registered.unique first second different _ _ firstFound secondFound
    (identity.toList ++ keys'.oneTime.toList)
    (by simp [PqxdhDeploymentReplay.entryRegistration, PqxdhDeploymentReplay.registrationOf, parsed, accepted])
    (by simp [PqxdhDeploymentReplay.entryRegistration, PqxdhDeploymentReplay.registrationOf, parsed', accepted'])

/-- Unrestricted replay in the actual deployment is contained in unrestricted final published-tuple provenance failure. -/
theorem replay_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Outcome KemSK A X)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime)) (replayed : ReplayEvent setup codec outcome) : GameEvent setup codec outcome := by
  obtain ⟨owner, doubled⟩ := (replay_owner setup codec outcome).mp replayed
  exact (game_owner setup codec outcome).mpr
    ⟨owner, replay_owner_published setup codec checks route ensureInit identityIndex bounds mode adversary runtime
      outcome supported owner doubled⟩

/-- Removing the no-failure filter changes no CE/source correspondence: the unrestricted final event is transported under exactly the original compiler codec contracts. -/
theorem game_report (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (count : Nat) (runtime : A) :
    letI := Classical.propDecidable
    𝒟[(fun outcome => decide (GameEvent setup codec outcome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} =
      𝒟[(fun outcome => decide (ReportEvent setup codec outcome)) <$>
        PqxdhJointPhase1Reports.run setup.joint count
          (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
            (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime)] {true} :=
  PqxdhDeploymentPublishedTuple.game_report_holds setup codec checks route ensureInit phase1 phase2 bounds mode
    adversary count runtime (PublishedForgery setup.source.crypto codec)

/-- The unrestricted replay event has no larger probability than unrestricted published-tuple provenance failure in the same actual experiment. -/
theorem replay_le_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A) :
    letI := Classical.propDecidable
    𝒟[(fun outcome => decide (ReplayEvent setup codec outcome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime] {true} ≤
    𝒟[(fun outcome => decide (GameEvent setup codec outcome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime] {true} := by
  classical
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map, ← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  apply prEvent_mono_of_support
  intro outcome supported happened
  simp only [decide_eq_true_eq] at happened ⊢
  exact replay_published setup codec checks route ensureInit identityIndex bounds mode adversary runtime outcome
    supported happened

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.game_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.game_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.replay_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.replay_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.replay_owner_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.replay_owner_published

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.replay_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.replay_published

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.game_report' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.game_report

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.replay_le_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents.replay_le_published
