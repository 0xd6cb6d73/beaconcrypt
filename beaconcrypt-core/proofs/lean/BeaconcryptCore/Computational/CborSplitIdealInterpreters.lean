-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCompile
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonServices

/-! Established record commands issue only public hashing and addressed kernel reads. This fact remains valid after registration is interpreted through the pooled prefix and the grouped hidden-root services. These equalities keep all source and private states; they do not assume a record-world handoff or a security-event correspondence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborSplitIdealInterpreters
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed PublicIdentity)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhDeploymentInterface (Spec)
open CborSplitCompiler (RecordKind)
open PqxdhRegistrationJointKemPostSkeleton
variable {ι KemSK Reader Response V X : Type} {baseSpec : OracleSpec ι}

/-- Changing registration's codec cannot affect a record-only request in the pooled native prefix. -/
theorem pool_record_query (setup : Setup baseSpec KemSK) (left right : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (pairs : List (PqxdhLiveKemReservation.Pair KemSK))
    (query : (SourceSpec KemSK).Domain) (permitted : RecordKind (sourceKind (KemSK := KemSK) query)) :
    PqxdhDeploymentIdealPool.revealPool setup left checks seed pairs query =
      PqxdhDeploymentIdealPool.revealPool setup right checks seed pairs query := by
  rcases query with (coin | command) | ⟨address, field⟩
  · simp [RecordKind, sourceKind, PqxdhRegistrationSchedule.sourceKind] at permitted
  · cases command
    all_goals try simp [RecordKind, sourceKind, PqxdhRegistrationSchedule.sourceKind] at permitted
    all_goals rfl
  · cases field
    all_goals try simp [RecordKind, sourceKind, PqxdhRegistrationJointRevealCosts.fieldIndex] at permitted
    all_goals rfl

/-- The source14 interpreter of the grouped hidden-root services, retaining both the live owner registry and every private skeleton field. -/
noncomputable def groupedSource (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (selected : Nat) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) :
    QueryImpl (SourceSpec KemSK)
      (StateT ((List PqxdhRegistrationJointGeneratedFinish.EncodedEntry ×
          (Nat → Option PqxdhEd25519EufCma.Phase1Candidate)) × SkelState KemSK V)
        (OracleComp (Enc KemSK + TSpec V))) :=
  ((skelImpl setup codec checks identityIndex publicIdentity services).mapStateTBase
    (groupedClient setup codec selected challenge)).flattenStateT

/-- Hashing and Server kernel disclosure use exactly the existing shared state; an owner kernel read stays local to its current phase. None can call a registration or hidden-entry service. -/
theorem grouped_record_query (setup : Setup baseSpec KemSK) (left right : Codec Reader Response)
    (checks : Checks) (selected : Nat) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (leftServices rightServices : Services V Response) (query : (SourceSpec KemSK).Domain)
    (permitted : RecordKind (sourceKind (KemSK := KemSK) query)) :
    groupedSource setup left checks selected challenge identityIndex publicIdentity leftServices query =
      groupedSource setup right checks selected challenge identityIndex publicIdentity rightServices query := by
  rcases query with (coin | command) | ⟨address, field⟩
  · simp [RecordKind, sourceKind, PqxdhRegistrationSchedule.sourceKind] at permitted
  · cases command
    all_goals try simp [RecordKind, sourceKind, PqxdhRegistrationSchedule.sourceKind] at permitted
    all_goals rfl
  · cases field
    all_goals try simp [RecordKind, sourceKind, PqxdhRegistrationJointRevealCosts.fieldIndex] at permitted
    apply StateT.ext
    rintro ⟨⟨owners, inits⟩, state⟩
    change (groupedSource setup left checks selected challenge identityIndex publicIdentity leftServices
      (.inr (address, .kernel))).run ((owners, inits), state) =
      (groupedSource setup right checks selected challenge identityIndex publicIdentity rightServices
        (.inr (address, .kernel))).run ((owners, inits), state)
    simp only [groupedSource, QueryImpl.flattenStateT_mapStateTBase_apply_run]
    cases present : owners[address]? <;>
      simp [groupedClient,
        liftGrouped, PqxdhRegistrationJointRevealSchedule.client,
        PqxdhRegistrationJointLiveRead.clientStep, present,
        PqxdhRegistrationJointLiveRead.entryClient, StateT.run]

/-- Codec independence passes through every adaptive continuation with a record-only source footprint, before any slot oracle or candidate interpreter is selected. -/
theorem grouped_quiet (setup : Setup baseSpec KemSK) (left right : Codec Reader Response)
    (checks : Checks) (selected : Nat) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (leftServices rightServices : Services V Response)
    (work : OracleComp (SourceSpec KemSK) X)
    (quiet : ∀ kind, ¬RecordKind kind →
      work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = kind) 0) :
    simulateQ (groupedSource setup left checks selected challenge identityIndex publicIdentity leftServices) work =
      simulateQ (groupedSource setup right checks selected challenge identityIndex publicIdentity rightServices) work :=
  CborSplitCompiler.simulate_quiet _ _
    (grouped_record_query setup left right checks selected challenge identityIndex publicIdentity
      leftServices rightServices) work quiet

/-- The actual public raw compiler's record commands retain the existing three-coordinate source footprint, including admission rejection. -/
theorem raw_record_quiet (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (memory : CborAdmissionCompiler.Local) (kind : SourceKind) (forbidden : ¬RecordKind kind) :
    ((CborRawCompile.compileImpl setup wire parse query).run memory).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) 0 := by
  have bound := CborRawCompile.step_bound setup wire parse kind query memory
  have zero : PqxdhDeploymentCompileBudget.cost kind (PqxdhDeploymentCompileBudget.commandKind query) = 0 := by
    rcases query with coin | command
    · simp [CborSplitCompiler.recordCommand] at record
    · cases command
      all_goals try simp [CborSplitCompiler.recordCommand] at record
      all_goals simp only [RecordKind, not_or] at forbidden
      all_goals simp [PqxdhDeploymentCompileBudget.commandKind, PqxdhDeploymentCompileBudget.cost,
        PqxdhDeploymentCompileBudget.unit, forbidden.1, forbidden.2.1, forbidden.2.2]
  simpa only [zero] using bound

/-- The hidden-root interpreter can keep the canonical registration codec while a compiled record step uses its actual decoder and optional native writer. This is an equality of open programs, so every later slot interpretation preserves it. -/
theorem raw_record_grouped (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (selected : Nat) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (identityIndex : Nat)
    (publicIdentity : PublicIdentity) (services : Services V (Aeneas.Std.U64 × Response))
    (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (memory : CborAdmissionCompiler.Local) :
    simulateQ (groupedSource setup (CborRawCompile.sourceCodec wire parse) checks selected challenge
        identityIndex publicIdentity services) ((CborRawCompile.compileImpl setup wire parse query).run memory) =
      simulateQ (groupedSource setup
        (CborSplitCompiler.records (CborRawCompile.sourceCodec wire parse)
          (CborTaggedSimulation.boundaryWire wire parse).frameRead wire.frameWrite)
        checks selected challenge identityIndex publicIdentity services)
          ((CborRawCompile.compileImpl setup wire parse query).run memory) :=
  grouped_quiet setup _ _ checks selected challenge identityIndex publicIdentity services services _
    (raw_record_quiet setup wire parse query record memory)

end BeaconcryptCore.Computational.CborSplitIdealInterpreters

/-- info: 'BeaconcryptCore.Computational.CborSplitIdealInterpreters.raw_record_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitIdealInterpreters.raw_record_grouped

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborSplitIdealInterpreters.pool_record_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitIdealInterpreters.pool_record_query

/-- info: 'BeaconcryptCore.Computational.CborSplitIdealInterpreters.grouped_record_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitIdealInterpreters.grouped_record_query

/-- info: 'BeaconcryptCore.Computational.CborSplitIdealInterpreters.grouped_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitIdealInterpreters.grouped_quiet

/-- info: 'BeaconcryptCore.Computational.CborSplitIdealInterpreters.raw_record_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitIdealInterpreters.raw_record_quiet
