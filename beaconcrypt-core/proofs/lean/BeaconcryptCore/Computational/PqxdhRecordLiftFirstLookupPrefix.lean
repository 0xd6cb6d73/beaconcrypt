-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup
import BeaconcryptCore.Computational.PqxdhRecordLiftAvailability

/-! The first selected lookup cut is an actual supported prefix of the unchanged adaptive source client. No continuation, private state or prefix condition is supplied by an adversary. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix
open PqxdhRecordLiftProtocol PqxdhRecordLiftFirstLookup PqxdhRecordLiftAvailability
variable {n : Nat} {Result : Type}

/-- Every supported scan result resumes at an actual reached remainder, including executions that already completed. -/
theorem scan_reaches (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (before : Private n)
    (result : Cut n Result × Private n)
    (supported : result ∈ support ((simulateQ impl (scan target client)).run before)) :
    Reaches impl client before (finish target result.1) result.2 := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value =>
      change result ∈ support (pure (Cut.complete value, before) : ProbComp _) at supported
      simp only [mem_support_pure_iff] at supported
      simpa only [supported, finish] using Reaches.here (impl := impl) (pure value) before
  | query_bind query next ih =>
      cases query with
      | lookup coordinate =>
          change result ∈ support ((simulateQ impl (if coordinate = target then pure (.pending next) else
            (((ServiceSpec n).query (.lookup coordinate) : OracleComp (ServiceSpec n) Unit) >>= fun reply => scan target (next reply)))).run before) at supported
          split_ifs at supported with same
          · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
            subst coordinate
            simpa only [supported, finish] using Reaches.here (impl := impl) (((ServiceSpec n).query (.lookup target) : OracleComp (ServiceSpec n) Unit) >>= next) before
          · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
            obtain ⟨middle, actual, tail⟩ := supported
            exact .later _ _ _ _ _ _ actual (ih middle.1 middle.2 tail)
      | _ =>
          change result ∈ support ((simulateQ impl ((((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>= fun reply => scan target (next reply)))).run before) at supported
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
          exact supported.elim (fun middle reached => .later _ _ _ _ _ _ reached.1 (ih middle.1 middle.2 reached.2))

/-- A source-derived safety certificate holds at the exact cut, for the entire original remainder and private state. -/
theorem scan_safe (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (predicate : (ServiceSpec n).Domain → Private n → Prop)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (before : Private n)
    (safe : Safe impl predicate client before) (result : Cut n Result × Private n)
    (supported : result ∈ support ((simulateQ impl (scan target client)).run before)) :
    Safe impl predicate (finish target result.1) result.2 :=
  safe.reaches (scan_reaches impl target client before result supported)

/-- A pending cut exposes the source predicate before the selected lookup consumes any reply or changes state. -/
theorem pending_query (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (predicate : (ServiceSpec n).Domain → Private n → Prop)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (before : Private n)
    (safe : Safe impl predicate client before)
    (next : Unit → OracleComp (ServiceSpec n) Result) (after : Private n)
    (supported : (Cut.pending next, after) ∈ support ((simulateQ impl (scan target client)).run before)) :
    predicate (.lookup target) after :=
  (scan_safe impl predicate target client before safe (.pending next, after) supported).1

/-- The support-certified sampler reaches the very same literal prefix; its proof attachment does not add a conditioned execution. -/
theorem sampled_support {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result)
    (result : { result : Cut n Result × Private n // result.2.chain target = none })
    (supported : result ∈ support (sampledPrefix source ideal setup codec target client)) :
    result.val ∈ support ((simulateQ (interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (scan target client)).run initialPrivate) := by
  rw [← prefix_forget source ideal setup codec target client, support_map]
  exact ⟨result, supported, rfl⟩

/-- The actual sampler carries an original-prefix certificate in addition to its already derived missing-entry fact. -/
theorem sampled_reaches {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result)
    (result : { result : Cut n Result × Private n // result.2.chain target = none })
    (supported : result ∈ support (sampledPrefix source ideal setup codec target client)) :
    Reaches (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
      client initialPrivate (finish target result.val.1) result.val.2 :=
  scan_reaches _ target client initialPrivate result.val
    (sampled_support source ideal setup codec target client result supported)

end BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.scan_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.scan_reaches
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.scan_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.scan_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.pending_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.pending_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.sampled_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.sampled_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.sampled_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookupPrefix.sampled_reaches
