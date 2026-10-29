-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld

/-! An unobserved early completion can be deferred through an arbitrary actual World continuation and then dropped. The observer retains installed concrete kernels, populated AD, every used-role marker, protocol state, shared CTX cache and native/effect bills; only the private seed table and the stated accounting coordinates are removed. No new World or adversary capability is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedDelay
open PqxdhRecordLiftWorld (State SeedSpec)
open PqxdhRecordLiftInterface (WorldSpec Slot)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSeedDelayCore (lens mask)
open RegistrationNativeSeedDelayWorld (handler)
open LazyOracleDiscard (LawEq)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def view (before : State n) : State n :=
  { mask before with seeds := PqxdhRecordLiftLazyTable.initial }

/-- The seed-delay observation retains exact operational state and role-use history. -/
theorem view_fields (before : State n) :
    (view before).server = before.server ∧ (view before).owners = before.owners ∧
    (view before).ownerRaw = before.ownerRaw ∧ (view before).produced = before.produced ∧
    (view before).used = before.used ∧ (view before).primitive.2 = before.primitive.2 ∧
    (view before).primitive.1.native = before.primitive.1.native ∧
    (view before).primitive.1.effects = before.primitive.1.effects :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem view_set (before : State n) (cache : (SeedSpec n).QueryCache) :
    view (lens.set before cache) = view before := rfl

/-- The concrete final observer cannot inspect an otherwise unused completion. -/
theorem view_blind : LazyOracleDiscard.Blind (lens (n := n))
    (fun result : Value × State n => (pure (result.1, view result.2) : ProbComp (Value × State n))) :=
  LazyOracleDiscard.blind_proj lens view view_set

/-- A seed completed at material demand may instead be left lazy throughout any later actual World program, including its original hidden-install guards and all record interactions. -/
theorem program_delay (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (point : Option (Slot n)) (before : State n) :
    LawEq
      (lens.completeOpt point before >>= fun reached =>
        Prod.map id view <$> (simulateQ (handler setup codec route) work).run reached)
      (Prod.map id view <$> (simulateQ (handler setup codec route) work).run before) := by
  have delayed := LazyOracleDiscard.erase_tail lens
    (RegistrationNativeSeedDelayWorld.program_commutes setup codec route work)
    (view_blind (Value := Value)) point before
  simpa only [map_eq_bind_pure_comp, Function.comp_def, Prod.map_def, id_eq] using delayed

end BeaconcryptCore.Computational.RegistrationNativeSeedDelay

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelay.view_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelay.view_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelay.view_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelay.view_set
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelay.view_blind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelay.view_blind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelay.program_delay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelay.program_delay
