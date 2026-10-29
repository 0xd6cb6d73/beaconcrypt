-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditCallbacks
import BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceInvariant

/-! The actual guarded known-side audit runs below the same selective callback interpreter and literal paired chronology. Its internal state contains the real dictionary, provider and World alongside the observer; no event list is reconstructed from final outcomes. Ordinary callbacks retain audit evidence, while hidden installations connect their marked slot to the descriptor's actual demand receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePairedTrace (step)
open RegistrationNativeG3AuditTraceInvariant (Good)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK ProviderState : Type) := RegistrationNativePairedDictionary.State n KemSK ProviderState ×
  (PqxdhRecordLiftWorld.State n × Bool)

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) :
    QueryImpl (Spec n KemSK) (StateT (State n KemSK ProviderState) ProbComp) := fun query before =>
  (fun reached => (reached.1.1, ((step query reached.1.1 before.1.1, reached.1.2), reached.2))) <$>
    (simulateQ (RegistrationNativeG3AuditQuiet.world setup codec route seeds)
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query).run before.1.2)).run before.2

variable (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
  (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)

local notation "input" => RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar
local notation "selected" => RegistrationNativeSelectiveHiddenService.selected
  (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate

/-- An actual ordinary callback preserves the same chronological audit/dictionary invariant. -/
theorem quiet_query (query : (Spec n KemSK).Domain) (quiet : RegistrationNativeG3AuditCallbacks.Quiet query)
    (before : State n KemSK ProviderState) (valid : Good input selected before.1.1 before.1.2 before.2)
    (result : (Spec n KemSK).Range query × State n KemSK ProviderState)
    (supported : result ∈ support ((handler setup codec route seeds wire sign seed scalar candidate provider query).run before)) :
    Good input selected result.2.1.1 result.2.1.2 result.2.2 := by
  simp only [handler, StateT.run, support_map] at supported
  obtain ⟨reached, actual, rfl⟩ := supported
  have opened : reached.1 ∈ support ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query).run before.1.2) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeG3AuditQuiet.world setup codec route seeds) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst actual
  have paired : (reached.1.1, (step query reached.1.1 before.1.1, reached.1.2)) ∈ support
      ((RegistrationNativePairedDictionary.handler setup wire sign seed scalar candidate provider query).run before.1) := by
    simp only [RegistrationNativePairedDictionary.handler, StateT.run, support_map]
    exact ⟨reached.1, opened, rfl⟩
  have dictionary := RegistrationNativePairedDictionary.query setup wire sign seed scalar candidate provider query before.1 valid.1 _ paired
  have retained := RegistrationNativeSelectiveHiddenDictionaryRun.query setup wire sign seed scalar candidate provider query before.1.2 reached.1 valid.1.1 opened
  have audited := RegistrationNativeG3AuditQuiet.program setup codec route seeds _
    (RegistrationNativeG3AuditCallbacks.query setup wire sign seed scalar candidate provider query before.1.2 quiet) before.2 reached actual
  obtain ⟨suffix, events⟩ := RegistrationNativePairedEvents.query_chunk query reached.1.1 before.1.1
  exact RegistrationNativeG3AuditTraceInvariant.ordinary input selected _ _ _ _ _ _ valid dictionary retained.2 suffix events audited.1 audited.2

private theorem effect_source (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
      (.inl (.inr (.inl (.inr (.inr query)))))).run before =
      (fun reply => (reply, before)) <$> PqxdhRecordLiftInterface.effectLift query := by
  simp only [RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase, StateT.run]
  change (fun result => (result.1, (result.2, before.2))) <$>
    (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider (.inl (.inr (.inl (.inr (.inr query)))))).run before.1 = _
  rw [RegistrationNativeHiddenInterpreter.effect_query]
  simp only [Functor.map_map]

/-- An actual guarded hidden-slot Server attempt connects its used-bit audit to the same chronological native descriptor and actual demand receipt. -/
theorem server_query (keyId : U64) (binding : PqxdhRecordLiftInterface.PeerBinding) (slot : Slot n)
    (before : State n KemSK ProviderState) (valid : Good input selected before.1.1 before.1.2 before.2)
    (result : Bool × State n KemSK ProviderState)
    (supported : result ∈ support ((handler setup codec route seeds wire sign seed scalar candidate provider
      (.inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding (.hidden slot))))))))).run before))
    (clean : result.2.1.1.bad = false) : Good input selected result.2.1.1 result.2.1.2 result.2.2 := by
  simp only [handler, StateT.run, support_map] at supported
  obtain ⟨reached, actual, rfl⟩ := supported
  change reached ∈ support ((simulateQ (RegistrationNativeG3AuditQuiet.world setup codec route seeds)
    ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
      (.inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding (.hidden slot))))))))).run before.1.2)).run before.2) at actual
  rw [effect_source setup wire sign seed scalar candidate provider, simulateQ_map, StateT.run_map, support_map] at actual
  obtain ⟨⟨reply, final⟩, worldActual, equal⟩ := actual
  cases equal
  have marked : (reply, final) ∈ support ((RegistrationNativeG3GuardedWorld.marked setup codec route seeds true
      (.server keyId binding slot)).run before.2) := by
    simpa only [PqxdhRecordLiftInterface.effectLift, simulateQ_spec_query, RegistrationNativeG3AuditQuiet.world,
      QueryImpl.compose, RegistrationNativeG3Materialize.materialize, simulateQ_spec_query] using worldActual
  have used := RegistrationNativeG3AuditHistory.query_used setup codec route seeds (.server keyId binding slot) before.2 (reply, final) marked
  simp only [RegistrationNativeG3AuditHistory.updateUsed] at used
  have flag : final.2 = (before.2.2 || before.2.1.used slot .server) := by
    simp only [RegistrationNativeG3GuardedWorld.marked, StateT.run, support_map] at marked
    obtain ⟨inner, _possible, equal⟩ := marked
    exact (congrArg (fun result => result.2.2) equal).symm
  have fits : RegistrationNativePairedTrace.Fits (KemSK := KemSK)
      (.inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding (.hidden slot)))))))) before.1.1 := by
    by_contra absent
    simp only [step, absent, decide_false, Bool.not_false, Bool.or_true, Bool.true_eq_false] at clean
  change RegistrationNativePairedTrace.FitsKernel before.1.1 (.hidden slot) at fits
  obtain ⟨live, reference, choice, sameSlot⟩ := fits
  cases current : before.1.1.trace.current with
  | none => simp only [current, Option.isSome_none, Bool.false_eq_true] at live
  | some message =>
      have chronological : (step (KemSK := KemSK)
          (.inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding (.hidden slot)))))))) reply before.1.1).trace.events =
          before.1.1.trace.events ++ [.installAttempt .server message] ++ if (show Bool from reply) then [.install .server message] else [] := by
        cases reply <;> simp only [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
          RegistrationNativeG2Trace.attempt, RegistrationNativeG2Trace.installed, current, List.append_assoc,
          List.cons_append, List.nil_append, Bool.false_eq_true, ite_false, ite_true, List.append_nil]
      have dictionary : RegistrationNativeSelectiveHiddenDictionaryRun.Good before.1.2 ∧
          RegistrationNativePairedDictionary.Current input selected
            (step (KemSK := KemSK) (.inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding (.hidden slot)))))))) reply before.1.1) before.1.2.1.keys := by
        refine ⟨valid.1.1, ?_⟩
        intro selectedMessage selectedReference _active impossible
        cases impossible
      exact RegistrationNativeG3AuditTraceInvariant.installed input selected _ _ _ _ _ _ valid dictionary
        (fun _ _ held => held) .server slot reply message reference current choice sameSlot chronological used flag

/-- An actual guarded hidden-slot Beacon attempt connects its used-bit audit to the same chronological native descriptor and actual demand receipt. -/
theorem beacon_query (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell) (slot : Slot n)
    (before : State n KemSK ProviderState) (valid : Good input selected before.1.1 before.1.2 before.2)
    (result : Bool × State n KemSK ProviderState)
    (supported : result ∈ support ((handler setup codec route seeds wire sign seed scalar candidate provider
      (.inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell (.hidden slot))))))))).run before))
    (clean : result.2.1.1.bad = false) : Good input selected result.2.1.1 result.2.1.2 result.2.2 := by
  simp only [handler, StateT.run, support_map] at supported
  obtain ⟨reached, actual, rfl⟩ := supported
  change reached ∈ support ((simulateQ (RegistrationNativeG3AuditQuiet.world setup codec route seeds)
    ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
      (.inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell (.hidden slot))))))))).run before.1.2)).run before.2) at actual
  rw [effect_source setup wire sign seed scalar candidate provider, simulateQ_map, StateT.run_map, support_map] at actual
  obtain ⟨⟨reply, final⟩, worldActual, equal⟩ := actual
  cases equal
  have marked : (reply, final) ∈ support ((RegistrationNativeG3GuardedWorld.marked setup codec route seeds true
      (.beacon owner shell slot)).run before.2) := by
    simpa only [PqxdhRecordLiftInterface.effectLift, simulateQ_spec_query, RegistrationNativeG3AuditQuiet.world,
      QueryImpl.compose, RegistrationNativeG3Materialize.materialize, simulateQ_spec_query] using worldActual
  have used := RegistrationNativeG3AuditHistory.query_used setup codec route seeds (.beacon owner shell slot) before.2 (reply, final) marked
  simp only [RegistrationNativeG3AuditHistory.updateUsed] at used
  have flag : final.2 = (before.2.2 || before.2.1.used slot .beacon) := by
    simp only [RegistrationNativeG3GuardedWorld.marked, StateT.run, support_map] at marked
    obtain ⟨inner, _possible, equal⟩ := marked
    exact (congrArg (fun result => result.2.2) equal).symm
  have fits : RegistrationNativePairedTrace.Fits (KemSK := KemSK)
      (.inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell (.hidden slot)))))))) before.1.1 := by
    by_contra absent
    simp only [step, absent, decide_false, Bool.not_false, Bool.or_true, Bool.true_eq_false] at clean
  change RegistrationNativePairedTrace.FitsKernel before.1.1 (.hidden slot) at fits
  obtain ⟨live, reference, choice, sameSlot⟩ := fits
  cases current : before.1.1.trace.current with
  | none => simp only [current, Option.isSome_none, Bool.false_eq_true] at live
  | some message =>
      have chronological : (step (KemSK := KemSK)
          (.inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell (.hidden slot)))))))) reply before.1.1).trace.events =
          before.1.1.trace.events ++ [.installAttempt .beacon message] ++ if (show Bool from reply) then [.install .beacon message] else [] := by
        cases reply <;> simp only [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
          RegistrationNativeG2Trace.attempt, RegistrationNativeG2Trace.installed, current, List.append_assoc,
          List.cons_append, List.nil_append, Bool.false_eq_true, ite_false, ite_true, List.append_nil]
      have dictionary : RegistrationNativeSelectiveHiddenDictionaryRun.Good before.1.2 ∧
          RegistrationNativePairedDictionary.Current input selected
            (step (KemSK := KemSK) (.inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell (.hidden slot)))))))) reply before.1.1) before.1.2.1.keys := by
        refine ⟨valid.1.1, ?_⟩
        intro selectedMessage selectedReference _active impossible
        cases impossible
      exact RegistrationNativeG3AuditTraceInvariant.installed input selected _ _ _ _ _ _ valid dictionary
        (fun _ _ held => held) .beacon slot reply message reference current choice sameSlot chronological used flag

/-- Every actual guarded callback derives and preserves the chronological dictionary/audit invariant from its clean paired result. -/
theorem query_good (query : (Spec n KemSK).Domain) (before : State n KemSK ProviderState)
    (valid : Good input selected before.1.1 before.1.2 before.2)
    (result : (Spec n KemSK).Range query × State n KemSK ProviderState)
    (supported : result ∈ support ((handler setup codec route seeds wire sign seed scalar candidate provider query).run before))
    (clean : result.2.1.1.bad = false) : Good input selected result.2.1.1 result.2.1.2 result.2.2 := by
  by_cases quiet : RegistrationNativeG3AuditCallbacks.Quiet query
  · exact quiet_query setup codec route seeds wire sign seed scalar candidate provider query quiet before valid result supported
  · rcases query with (prepare | (demand | (publication | environment)) | kem) | record
    · exact False.elim (quiet trivial)
    · exact False.elim (quiet trivial)
    · exact False.elim (quiet trivial)
    · rcases environment with coin | capability
      · exact False.elim (quiet trivial)
      · cases capability with
        | installServer keyId binding kernel => cases kernel with
          | known kernel => exact False.elim (quiet trivial)
          | hidden slot => exact server_query setup codec route seeds wire sign seed scalar candidate provider keyId binding slot before valid result supported clean
        | installBeacon owner shell kernel => cases kernel with
          | known kernel => exact False.elim (quiet trivial)
          | hidden slot => exact beacon_query setup codec route seeds wire sign seed scalar candidate provider owner shell slot before valid result supported clean
        | _ => exact False.elim (quiet trivial)
    · exact False.elim (quiet trivial)
    · exact False.elim (quiet trivial)

end BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace.quiet_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace.quiet_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace.server_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace.server_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace.beacon_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace.beacon_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace.query_good
