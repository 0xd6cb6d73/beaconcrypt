-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSupport

/-! Actual source14 budgets supply the four bounds needed by the selected KEM cut: generated identity requests, logical decapsulations, all native uniform work and actual encapsulation occurrences. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills
open PqxdhRegistrationJointKemEncapsulation PqxdhRegistrationJointKemCutBounds
open PqxdhRegistrationJointKemExposedCounts
open PqxdhDynamicKemJointBounds (IsIdentityCreate IsDecapsulation IsUniform)
open PqxdhRegistrationJointServiceCosts (Kind poolClass)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The exact all-reply source allowances used by prechallenge and residual postchallenge compilation. -/
structure Bounds (work : OracleComp (Spec KemSK) Result) (qCreate qD qUniform qEncap : Nat) : Prop where
  creates : work.IsQueryBoundP (Count (KemSK := KemSK) IsIdentityCreate) qCreate
  decaps : work.IsQueryBoundP (Count (KemSK := KemSK) IsDecapsulation) qD
  uniform : work.IsQueryBoundP (Count (KemSK := KemSK) IsUniform) qUniform
  encaps : work.IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) qEncap

/-- The source and KEM router refer to the same generated-identity creation request. -/
theorem creates_class : (IsIdentityCreate (KemSK := KemSK)) =
    (fun query => poolClass (KemSK := KemSK) query = .identityCreate) := by
  funext query
  rcases query with (coin | request) | (coin | request)
  case inl.inr =>
    cases request
    case service index call => cases call <;> simp [IsIdentityCreate, PqxdhDynamicIdentityPool.IsCreate, poolClass]
    all_goals simp [IsIdentityCreate, PqxdhDynamicIdentityPool.IsCreate, poolClass]
  case inr.inr => cases request <;> simp [IsIdentityCreate, poolClass]
  all_goals simp [IsIdentityCreate, PqxdhDynamicIdentityPool.IsCreate, poolClass]

/-- The source and ordinary router count exactly the same logical decapsulation attempts, including rejected or missing private handles. -/
theorem decaps_class : (IsDecapsulation (KemSK := KemSK)) =
    (fun query => poolClass (KemSK := KemSK) query = .decapsulate) := by
  funext query
  rcases query with (coin | request) | (coin | request)
  case inl.inl => simp [IsDecapsulation, poolClass]
  case inl.inr =>
    cases request <;> simp only [IsDecapsulation, poolClass]
    case service index call => cases call <;> simp
    all_goals simp
  case inr.inl => simp [IsDecapsulation, poolClass]
  case inr.inr => cases request <;> simp [IsDecapsulation, PqxdhDynamicKemBounds.IsDecapsulation, poolClass]

/-- Forwarded private predicate classes agree on every exposed query; encapsulation remains outside every private class. -/
theorem count_private (kind : Kind) :
    Count (KemSK := KemSK) (fun query => poolClass (KemSK := KemSK) query = kind) =
      PqxdhRegistrationJointKemExposedPrivate.Private (KemSK := KemSK) kind := by
  funext query
  cases query <;> rfl

/-- The actual whole source command compiler provides all four cut-resource certificates, before any replacement oracle is chosen. -/
theorem commands (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result)
    (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : PqxdhServerAuthNative.NativeState KemSK) :
    Bounds (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks identityIndex publicIdentity work owners state)
      (budget (.inl 1)) (budget (.inl 5)) (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)) := by
  constructor
  · simpa only [creates_class, count_private, PqxdhRegistrationJointOpenCosts.privateTotal] using
      PqxdhRegistrationJointKemExposedPrivate.command_bound setup codec checks identityIndex publicIdentity work budget certified owners state .identityCreate (by decide)
  · simpa only [decaps_class, count_private, PqxdhRegistrationJointOpenCosts.privateTotal] using
      PqxdhRegistrationJointKemExposedPrivate.command_bound setup codec checks identityIndex publicIdentity work budget certified owners state .decapsulate (by decide)
  · exact PqxdhRegistrationJointKemExposedUniform.command_bound setup codec checks caps bounded identityIndex publicIdentity work budget certified owners state
  · exact PqxdhRegistrationJointKemExposedCounts.command_bound setup codec checks identityIndex publicIdentity work budget certified owners state

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills.creates_class' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills.creates_class

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills.decaps_class' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills.decaps_class

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills.count_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills.count_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills.commands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemProgramBills.commands
