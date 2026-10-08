-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix
import BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads

/-! Actual initialized source prefix certificates, including closed current tables, available selected parents, and absent dependent children before the selected parent lookup. These are operational facts about the unchanged source sampler. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix
open PqxdhRecordLiftProtocol PqxdhRecordLiftFirstLookup PqxdhRecordLiftFirstLookupPrefix
open PqxdhRecordLiftAvailability PqxdhRecordLiftInterface
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable
variable {n : Nat} {Result : Type}

/-- Scanning preserves the original query-prefix certificate at every executed query, while the selected lookup itself remains suspended. -/
theorem scan_safe (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (predicate : (ServiceSpec n).Domain → Private n → Prop)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (before : Private n)
    (safe : Safe impl predicate client before) :
    Safe impl predicate (scan target client) before := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      cases query with
      | lookup coordinate =>
          change Safe impl predicate (if coordinate = target then pure (.pending next) else
            (((ServiceSpec n).query (.lookup coordinate) : OracleComp (ServiceSpec n) Unit) >>=
              fun reply => scan target (next reply))) before
          split_ifs
          · trivial
          · exact ⟨safe.1, fun result member => ih result.1 result.2 (safe.2 result member)⟩
      | _ =>
          change Safe impl predicate (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => scan target (next reply)) before
          exact ⟨safe.1, fun result member => ih result.1 result.2 (safe.2 result member)⟩

/-- A closed table cannot already contain a noninitial child whose actual predecessor is missing. -/
theorem closed_child_missing {Slot : Type} (table : Table Slot) (closed : Closed table)
    (parent child : Coordinate Slot) (missing : table parent = none)
    (reads : PqxdhRecordLiftMaskedReads.Reads child parent) : table child = none := by
  cases found : table child with
  | none => rfl
  | some output =>
      obtain ⟨_, prior, stored⟩ := (closed child output found).resolve_left reads.1
      rw [reads.2, missing] at stored
      contradiction

/-- At the literal first-parent cut of any initialized adaptive WorldSpec client, the parent is available but absent, the table is closed, and every dependent child is absent. -/
theorem pending_schedule {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (parent : Coordinate (Slot n))
    (next : Unit → OracleComp (ServiceSpec n) (Result × Control n)) (after : Private n)
    (supported : (Cut.pending next, after) ∈ support ((simulateQ
      (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      (scan parent (schedule codec.frameRead route client initialControl))).run initialPrivate)) :
    Closed after.chain ∧ Available after.chain parent ∧ after.chain parent = none ∧
      ∀ child, PqxdhRecordLiftMaskedReads.Reads child parent → after.chain child = none := by
  have ready := pending_query _ Allowed parent _ _
    (initial_schedule_safe setup codec ideal route client) next after supported
  have missing := scan_initial_missing setup.source ideal setup codec parent
    (schedule codec.frameRead route client initialControl) (.pending next, after) supported
  exact ⟨ready.1, ready.2, missing, fun child reads => closed_child_missing after.chain ready.1 parent child missing reads⟩

/-- Every query actually executed while scanning an initialized schedule retains closure and lookup availability at its current private prestate. -/
theorem scan_schedule_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (parent : Coordinate (Slot n)) :
    Safe (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec) Allowed
      (scan parent (schedule codec.frameRead route client initialControl)) initialPrivate :=
  scan_safe _ Allowed parent _ initialPrivate (initial_schedule_safe setup codec ideal route client)

/-- The literal scanner of the complete frozen program has the same actual pre-query certificate in both source modes. -/
theorem scan_program_safe {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (parent : Coordinate (Slot n)) :
    Safe (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec) Allowed
      (scan parent (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)) initialPrivate :=
  scan_safe _ Allowed parent _ initialPrivate (program_safe setup codec ideal route env serverKid bounds mode adversary)

/-- The actual frozen-program pending cut has an available missing parent and no populated KDF child whose input reads that parent. -/
theorem pending_program {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (parent : Coordinate (Slot n))
    (next : Unit → OracleComp (ServiceSpec n)
      (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
        (X × PqxdhDeploymentSecrecy.Ledger) × E) × Control n)) (after : Private n)
    (supported : (Cut.pending next, after) ∈ support ((simulateQ
      (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      (scan parent (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary))).run initialPrivate)) :
    Closed after.chain ∧ Available after.chain parent ∧ after.chain parent = none ∧
      ∀ child, PqxdhRecordLiftMaskedReads.Reads child parent → after.chain child = none :=
  pending_schedule setup codec ideal route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary) parent next after supported

/-- Attaching the already derived miss proof retains these facts for the very same sampled pending schedule cut, without conditioning. -/
theorem sampled_schedule {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (parent : Coordinate (Slot n))
    (result : { result : Cut n (Result × Control n) × Private n // result.2.chain parent = none })
    (supported : result ∈ support (sampledPrefix setup.source ideal setup codec parent
      (schedule codec.frameRead route client initialControl)))
    (next : Unit → OracleComp (ServiceSpec n) (Result × Control n)) (pending : result.val.1 = .pending next) :
    Closed result.val.2.chain ∧ Available result.val.2.chain parent ∧ result.val.2.chain parent = none ∧
      ∀ child, PqxdhRecordLiftMaskedReads.Reads child parent → result.val.2.chain child = none := by
  apply pending_schedule setup codec ideal route client parent next result.val.2
  have actual := sampled_support setup.source ideal setup codec parent
    (schedule codec.frameRead route client initialControl) result supported
  have same : result.val = (.pending next, result.val.2) := Prod.ext pending rfl
  rw [same] at actual
  exact actual

/-- The proof-attached sampler of the actual frozen program has the same available-parent and absent-child facts whenever its cut is pending. -/
theorem sampled_program {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (parent : Coordinate (Slot n))
    (result : { result : Cut n (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × Control n) × Private n // result.2.chain parent = none })
    (supported : result ∈ support (sampledPrefix setup.source ideal setup codec parent
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)))
    (next : Unit → OracleComp (ServiceSpec n)
      (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
        (X × PqxdhDeploymentSecrecy.Ledger) × E) × Control n)) (pending : result.val.1 = .pending next) :
    Closed result.val.2.chain ∧ Available result.val.2.chain parent ∧ result.val.2.chain parent = none ∧
      ∀ child, PqxdhRecordLiftMaskedReads.Reads child parent → result.val.2.chain child = none :=
  sampled_schedule setup codec ideal route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
    parent result supported next pending

end BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.scan_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.scan_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.closed_child_missing' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.closed_child_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.pending_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.pending_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.scan_schedule_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.scan_schedule_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.scan_program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.scan_program_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.pending_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.pending_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.sampled_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.sampled_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.sampled_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix.sampled_program
