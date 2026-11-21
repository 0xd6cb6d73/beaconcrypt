-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocol
import BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords

/-! Suspend the unchanged global source client before the first selected coordinate lookup. All earlier replies and the complete original continuation remain literal. The actual empty-table miss and sampler will be derived from the private interpreter, not assumed from a public transcript. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol
variable {n : Nat} {Result : Type}

inductive Cut (n : Nat) (Result : Type) where
  | complete (result : Result)
  | pending (next : Unit → OracleComp (ServiceSpec n) Result)

noncomputable def scan (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) : OracleComp (ServiceSpec n) (Cut n Result) :=
  OracleComp.recOn client
    (fun result => pure (.complete result))
    (fun query next recurse => match query with
      | .lookup coordinate =>
          if coordinate = target then pure (.pending next) else do
            let reply ← (ServiceSpec n).query (.lookup coordinate)
            recurse reply
      | query => do
          let reply ← (ServiceSpec n).query query
          recurse reply)

noncomputable def finish (target : PqxdhRecordLiftWorldCompiler.Label n) :
    Cut n Result → OracleComp (ServiceSpec n) Result
  | .complete result => pure result
  | .pending next => (ServiceSpec n).query (.lookup target) >>= next

/-- Resuming the first selected source request recovers the entire adaptive client, before any interpreter or observation is chosen. -/
theorem scan_finish (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) :
    (scan target client >>= finish target) = client := by
  induction client using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind query next ih =>
      cases query with
      | lookup coordinate =>
          change ((if coordinate = target then pure (.pending next) else
            (((ServiceSpec n).query (.lookup coordinate) : OracleComp (ServiceSpec n) Unit) >>= fun reply => scan target (next reply))) >>= finish target) = _
          split_ifs with same
          · subst coordinate; rfl
          · simp only [bind_assoc, ih]
      | _ =>
          change ((((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => scan target (next reply)) >>= finish target) = _
          simp only [bind_assoc, ih]

/-- Before the selected request is resumed, no lookup names its coordinate. -/
def Avoids (target : PqxdhRecordLiftWorldCompiler.Label n) : (ServiceSpec n).Domain → Prop
  | .lookup coordinate => coordinate ≠ target
  | _ => True

/-- The actual prefix, including all adaptive branches, never executes the selected lookup. -/
theorem scan_avoids (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) :
    (scan target client).AllQueriesSatisfy (Avoids target) := by
  induction client using OracleComp.inductionOn with
  | pure result => exact (show (pure (Cut.complete result) : OracleComp (ServiceSpec n) _).AllQueriesSatisfy
      (Avoids target) by simp only [allQueriesSatisfy_pure])
  | query_bind query next ih =>
      cases query with
      | lookup coordinate =>
          change OracleComp.AllQueriesSatisfy (if coordinate = target then pure (.pending next) else
            (((ServiceSpec n).query (.lookup coordinate) : OracleComp (ServiceSpec n) Unit) >>=
              fun reply => scan target (next reply))) (Avoids target)
          split_ifs with same <;>
            simp only [allQueriesSatisfy_pure, allQueriesSatisfy_query_bind_iff, Avoids,
              ih, implies_true]
          exact ⟨same, trivial⟩
      | _ =>
          change OracleComp.AllQueriesSatisfy (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => scan target (next reply)) (Avoids target)
          simp only [allQueriesSatisfy_query_bind_iff, Avoids, true_and, ih, implies_true]

/-- The literal mixed private interpreter cannot change a table coordinate except through its own lookup. The predicate is checked on the complete original private execution. -/
theorem query_other {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n) (query : (ServiceSpec n).Domain)
    (avoids : Avoids target query) (secret : Private n)
    (result : (ServiceSpec n).Range query × Private n)
    (supported : result ∈ support ((interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec query).run secret)) :
    result.2.chain target = secret.chain target := by
  cases query with
  | lookup coordinate =>
      simp only [interpreter, withRecord, localInterpreter,
        PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run,
        mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨reply, member, rfl⟩ := supported
      change reply ∈ support (((fun _ => ()) <$>
        PqxdhRecordLiftLoggedAdapters.liftLookup
          (PqxdhRecordLiftChainOracle.lookup source (cachedSeeds secret) ideal) coordinate :
          StateT (RecordState n) ProbComp Unit).run (recordState secret)) at member
      rw [StateT.run_map] at member
      simp only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run,
        Functor.map_map, support_map] at member
      obtain ⟨actual, member, rfl⟩ := member
      exact PqxdhRecordLiftMixedRecords.lookup_other source (cachedSeeds secret) ideal coordinate
        (secret.chain, secret.primitive) actual member target (Ne.symm avoids)
  | _ =>
      simp only [interpreter, sampled, withRecord, primitiveWork, localInterpreter,
        PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run, bind_pure_comp,
        Functor.map_map, support_map, mem_support_pure_iff] at supported
      obtain ⟨reply, member, rfl⟩ := supported
      rfl

/-- Complete adaptive prefixes preserve an untouched table entry under the actual mixed private interpreter. -/
theorem avoids_preserves {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (avoids : client.AllQueriesSatisfy (Avoids target))
    (secret : Private n) (result : Result × Private n)
    (supported : result ∈ support ((simulateQ (interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) client).run secret)) :
    result.2.chain target = secret.chain target := by
  induction client using OracleComp.inductionOn generalizing secret with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at avoids
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      exact (ih middle.1 (avoids.2 middle.1) middle.2 supported).trans
        (query_other source ideal setup codec target query avoids.1 secret middle reached)

/-- Starting from the actual empty protocol table, the suspended prefix reaches a genuine miss whenever it reaches the selected request. This includes every earlier public, known-key and native effect in the sampled state. -/
theorem scan_initial_missing {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (result : Cut n Result × Private n)
    (supported : result ∈ support ((simulateQ (interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (scan target client)).run initialPrivate)) :
    result.2.chain target = none :=
  avoids_preserves source ideal setup codec target (scan target client) (scan_avoids target client)
    initialPrivate result supported

/-- The actual evaluated source prefix carries its derived miss proof. Attaching a support proof executes the same queries and does not condition or reject executions. -/
noncomputable def sampledPrefix {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) :
    ProbComp { result : Cut n Result × Private n // result.2.chain target = none } :=
  (fun reached => ⟨reached.val, scan_initial_missing source ideal setup codec target client reached.val reached.property⟩) <$>
    PFunctor.FreeM.attachSupp ((simulateQ (interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (scan target client)).run initialPrivate)

/-- Forgetting the derived miss certificate recovers the entire original evaluated prefix, with its exact private counters/cache/log and original continuation. -/
theorem prefix_forget {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) :
    Subtype.val <$> sampledPrefix source ideal setup codec target client =
      (simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
        (scan target client)).run initialPrivate := by
  simp only [sampledPrefix, Functor.map_map]
  exact PFunctor.FreeM.map_attachSupp _

/-- The certified prefix followed by its original suspended request and continuation is the same whole evaluated source execution, including early completion. -/
theorem resume_prefix {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) :
    (sampledPrefix source ideal setup codec target client >>= fun reached =>
      (simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
        (finish target reached.val.1)).run reached.val.2) =
      (simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) client).run initialPrivate := by
  have original := congrArg (fun work =>
    (simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) work).run initialPrivate)
    (scan_finish target client)
  rw [simulateQ_bind, StateT.run_bind, ← prefix_forget] at original
  simpa only [bind_map_left] using original

/-- Suspending the actual first request cannot increase any all-reply selective query allowance. -/
theorem scan_bound (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result)
    (predicate : (ServiceSpec n).Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (bounded : client.IsQueryBoundP predicate cap) :
    (scan target client).IsQueryBoundP predicate cap := by
  induction client using OracleComp.inductionOn generalizing cap with
  | pure result => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      cases query with
      | lookup coordinate =>
          change OracleComp.IsQueryBoundP (if coordinate = target then pure (.pending next) else
            (((ServiceSpec n).query (.lookup coordinate) : OracleComp (ServiceSpec n) Unit) >>=
              fun reply => scan target (next reply))) predicate cap
          split_ifs with same
          · trivial
          · rw [isQueryBoundP_query_bind_iff]
            exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
      | _ =>
          change OracleComp.IsQueryBoundP (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => scan target (next reply)) predicate cap
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

/-- The support certificate adds no primitive work: every selective allowance of the literal evaluated prefix is unchanged. -/
theorem sampledPrefix_bound {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
      (scan target client)).run initialPrivate).IsQueryBoundP predicate cap) :
    (sampledPrefix source ideal setup codec target client).IsQueryBoundP predicate cap := by
  rw [← prefix_forget] at bounded
  exact (isQueryBoundP_map_iff _ Subtype.val cap).mp bounded

end BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.scan_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.scan_finish
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.scan_avoids' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.scan_avoids
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.query_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.query_other
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.avoids_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.avoids_preserves
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.scan_initial_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.scan_initial_missing
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.prefix_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.prefix_forget
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.resume_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.resume_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.scan_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.scan_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.sampledPrefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup.sampledPrefix_bound
