-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore

/-! Common World execution retains the entire role-use map. Only its private seed table is projected; hidden installation is the sole excluded callback because it intentionally reads that table and writes the role history. Concrete records, AD, CTX state, every primitive counter and all used-role bits remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec CapabilitySpec EnvEffects)
open RegistrationNativeG3KnownWorldFrameCore (Allowed)
open RegistrationNativeSeedDelayFrames (ReadsSeed)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def view (before : State n) : State n := { before with seeds := PqxdhRecordLiftLazyTable.initial }

private theorem capability_keeps (query : (CapabilitySpec n).Domain) (quiet : ¬ReadsSeed query)
    (before : State n) (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.capability query).run before)) :
    result.2.seeds = before.seeds ∧ result.2.used = before.used := by
  cases query with
  | peerPresent keyId | ownerPresent owner | appendOwner identity keyId phase =>
      simp only [PqxdhRecordLiftWorld.capability, StateT.run, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, rfl⟩
  | advanceOwner owner phase =>
      cases found : before.owners[owner]? with
      | none =>
          simp only [PqxdhRecordLiftWorld.capability, StateT.run, found, mem_support_pure_iff] at supported
          cases supported
          exact ⟨rfl, rfl⟩
      | some current =>
          cases current <;> simp only [PqxdhRecordLiftWorld.capability, StateT.run, found] at supported
          all_goals try split at supported
          all_goals simp only [mem_support_pure_iff] at supported
          all_goals cases supported
          all_goals exact ⟨rfl, rfl⟩
  | installServer keyId binding ref =>
      cases ref with
      | hidden slot => exact False.elim (quiet trivial)
      | known kernel =>
          cases found : before.server with
          | none =>
              simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer,
                StateT.run, found, mem_support_pure_iff] at supported
              cases supported
              exact ⟨rfl, rfl⟩
          | some server =>
              simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer, StateT.run, found] at supported
              split at supported <;>
                simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.markUsed,
                  mem_support_pure_iff] at supported
              all_goals cases supported
              all_goals exact ⟨rfl, rfl⟩
  | installBeacon owner shell ref =>
      cases ref with
      | hidden slot => exact False.elim (quiet trivial)
      | known kernel =>
          simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installBeacon, StateT.run] at supported
          split at supported <;>
            simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.markUsed,
              mem_support_pure_iff] at supported
          all_goals cases supported
          all_goals exact ⟨rfl, rfl⟩
  | hash bytes =>
      simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled, StateT.run,
        bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, _actual, rfl⟩ := supported
      exact ⟨rfl, rfl⟩

private theorem effects_keeps (query : (EnvEffects n).Domain)
    (quiet : match query with | .inr request => ¬ReadsSeed request | _ => True)
    (before : State n) (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.effects query).run before)) :
    result.2.seeds = before.seeds ∧ result.2.used = before.used := by
  cases query with
  | inl coin =>
      simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.sampled, StateT.run,
        bind_pure_comp, support_map] at supported
      obtain ⟨inner, _actual, rfl⟩ := supported
      exact ⟨rfl, rfl⟩
  | inr request => exact capability_keeps request quiet (PqxdhRecordLiftWorld.chargeEffect (.inr request) before) result supported

/-- Every actual common callback retains the complete cached seed table and the full earlier role-use history. -/
theorem keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (quiet : Allowed query)
    (before : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.handler setup codec route query).run before)) :
    result.2.seeds = before.seeds ∧ result.2.used = before.used := by
  cases query with
  | inl created =>
      cases found : before.server <;> simp only [PqxdhRecordLiftWorld.handler,
        PqxdhRecordLiftWorld.initializeServer, StateT.run, found, mem_support_pure_iff] at supported
      all_goals cases supported
      all_goals exact ⟨rfl, rfl⟩
  | inr query => cases query with
    | inl effect => cases effect with
      | inl coin => exact effects_keeps (.inl coin) trivial before result supported
      | inr request => exact effects_keeps (.inr request) quiet before result supported
    | inr record => cases record with
      | inl server =>
          cases server <;> cases found : before.server <;>
            simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.serverStep, StateT.run,
              found, bind_pure_comp, support_map] at supported
          all_goals obtain ⟨inner, _actual, rfl⟩ := supported
          all_goals exact ⟨rfl, rfl⟩
      | inr beacon =>
          rcases beacon with ⟨owner, query⟩
          cases query <;> cases found : before.owners[owner]? <;>
            simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.beaconStep, StateT.run,
              found, bind_pure_comp, support_map] at supported
          all_goals obtain ⟨inner, _actual, rfl⟩ := supported
          all_goals exact ⟨rfl, rfl⟩

/-- The actual common callback preserves every prior private role marker. -/
theorem used_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (quiet : Allowed query)
    (before : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.handler setup codec route query).run before)) :
    result.2.used = before.used := (keeps setup codec route query quiet before result supported).2

private theorem restore_map (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (quiet : Allowed query) (before : State n) :
    (fun result => (result.1, { RegistrationNativeHiddenWorldInstall.view result.2 with used := before.used })) <$>
      (PqxdhRecordLiftWorld.handler setup codec route query).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run before := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  have same := used_keeps setup codec route query quiet before result supported
  simp only [Function.comp_apply, Prod.map_def, id_eq, view, RegistrationNativeHiddenWorldInstall.view, same]

/-- Common execution ignores only the private seed table while retaining its actual input role-use map. -/
theorem handler_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (quiet : Allowed query) (before : State n) :
    Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (view before) := by
  have first := RegistrationNativeG3KnownWorldFrameCore.handler_input setup codec route query quiet before
  have second := RegistrationNativeG3KnownWorldFrameCore.handler_input setup codec route query quiet (view before)
  have twice : RegistrationNativeHiddenWorldInstall.view (view before) = RegistrationNativeHiddenWorldInstall.view before := rfl
  rw [twice] at second
  have same := first.trans second.symm
  have restored := congrArg (fun distribution =>
    Prod.map id (fun world => { world with used := before.used }) <$> distribution) same
  simp only [Functor.map_map, Prod.map_def, id_eq] at restored
  rw [restore_map setup codec route query quiet before] at restored
  exact restored.trans (restore_map setup codec route query quiet (view before))

end BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame.keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame.keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame.used_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame.used_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame.handler_input
