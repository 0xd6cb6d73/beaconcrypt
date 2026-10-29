-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld
import BeaconcryptCore.Computational.StatefulGoodEvent

/-! The actual canonical known-install and hidden-install World interpreters are identical until a privately audited slot/role is attempted again. A sticky analysis flag records that attempt before either callback runs, including a later callback that refuses. The bound retains the full World output and all actual optional failures; it supplies no cryptographic probability estimate for the flag. The fixed completed seed table and public materialized request program remain explicit proof-game parameters. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3WorldBound
open PqxdhRecordLiftWorld (State)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3AuditedWorld (Spec Seeds seeded repeated step)
open RegistrationNativeG3AuditedInstall (view)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

noncomputable def marked (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (known : Bool) :
    QueryImpl (Spec n) (StateT (State n × Bool) ProbComp) := fun query before =>
  (fun result => (result.1, (view result.2, before.2 || repeated query before.1))) <$>
    (step setup codec route seeds known query).run (seeded seeds before.1)

/-- The first repeated-role attempt is marked before the actual callback, and the analysis flag can never be cleared. -/
theorem sticky (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (known : Bool)
    (query : (Spec n).Domain) (before : State n × Bool) (flagged : before.2 = true)
    (result : (Spec n).Range query × (State n × Bool))
    (supported : result ∈ support ((marked setup codec route seeds known query).run before)) : result.2.2 = true := by
  simp only [marked, StateT.run, support_map] at supported
  obtain ⟨reached, _possible, equal⟩ := supported
  cases equal
  simp only [flagged, Bool.true_or]

/-- Off the actual repetition test, both complete callback distributions agree on every good reply and poststate. -/
theorem agree_good (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (query : (Spec n).Domain) (before after : State n) (reply : (Spec n).Range query) :
    Pr{let result ← (marked setup codec route seeds true query).run (before, false)}[result = (reply, (after, false))] =
      Pr{let result ← (marked setup codec route seeds false query).run (before, false)}[result = (reply, (after, false))] := by
  by_cases bad : repeated query before = true
  · have zero (known : Bool) :
        Pr{let result ← (marked setup codec route seeds known query).run (before, false)}[result = (reply, (after, false))] = 0 := by
      apply prEvent_eq_zero_of_not_mem_support
      intro supported
      simp only [marked, StateT.run, support_map] at supported
      obtain ⟨reached, _possible, equal⟩ := supported
      have impossible := congrArg (fun result => result.2.2) equal
      simp only [Bool.false_or, bad] at impossible
      cases impossible
    rw [zero true, zero false]
  · have fresh : repeated query before = false := Bool.eq_false_iff.mpr bad
    have same := congrArg (fun distribution => (fun result => (result.1, (result.2, false))) <$> distribution)
      (RegistrationNativeG3AuditedWorld.step_eq setup codec route seeds query before fresh)
    have literal : (marked setup codec route seeds true query).run (before, false) =
        (marked setup codec route seeds false query).run (before, false) := by
      simpa only [marked, StateT.run, Functor.map_map, Prod.map_def, id_eq, Bool.false_or, fresh] using same
    rw [literal]

/-- Any adaptive materialized World program differs by at most the original known-side repeated-role attempt probability. No refusal is silently substituted for an earlier native success. -/
theorem distance_le_repeat (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : State n) :
    discreteDistance
      ((simulateQ (marked setup codec route seeds true) work).run (before, false))
      ((simulateQ (marked setup codec route seeds false) work).run (before, false)) ≤
      Pr{let result ← (simulateQ (marked setup codec route seeds true) work).run (before, false)}[result.2.2 = true].toReal := by
  exact StatefulGoodEvent.distance_le_bad _ _
    (fun query current reply final => agree_good setup codec route seeds query current final reply)
    (sticky setup codec route seeds true) (sticky setup codec route seeds false) work (before, false)

end BeaconcryptCore.Computational.RegistrationNativeG3WorldBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3WorldBound.sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3WorldBound.sticky
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3WorldBound.agree_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3WorldBound.agree_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3WorldBound.distance_le_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3WorldBound.distance_le_repeat
