-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting
import BeaconcryptCore.Computational.RegistrationNativeSeedDelay

/-! Seed-delay is an equality in law for the original counted World program under its stated observation. The per-query accounting normalization is derived from actual source nonread, not assumed as a whole-game correspondence. Complete operational poststates and all used-role markers remain observable through this law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec Slot)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSeedDelayCore (lens mask)
open RegistrationNativeSeedDelay (view)
open LazyOracleDiscard (LawEq StateLens)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

/-- The concrete semantic view of the original full execution equals the actual normalized interpreter. -/
theorem program_view (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before =
      Prod.map id view <$> (simulateQ (RegistrationNativeSeedDelayWorld.handler setup codec route) work).run (mask before) := by
  have actual := congrArg (fun distribution => Prod.map id view <$> distribution)
    (RegistrationNativeSeedDelayAccounting.program_mask setup codec route work before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, view, mask] using actual

/-- Accounting normalization commutes exactly with an optional private cache completion. -/
theorem complete_mask (point : Option (Slot n)) (before : State n) :
    mask <$> lens.completeOpt point before = lens.completeOpt point (mask before) := by
  cases point with
  | none => simp only [StateLens.completeOpt, map_pure]
  | some slot =>
      simp only [StateLens.completeOpt, StateLens.complete, Functor.map_map,
        lens, mask]

/-- The original actual World execution obeys seed delay through every future adaptive native command. Only the displayed private seed/accounting view is erased; no new capability, unused-role premise or client simulation law is supplied. -/
theorem program_delay (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (point : Option (Slot n)) (before : State n) :
    LawEq
      (lens.completeOpt point before >>= fun reached =>
        Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run reached)
      (Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before) := by
  have first : (lens.completeOpt point before >>= fun reached =>
      Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run reached) =
      (lens.completeOpt point before >>= fun reached =>
        Prod.map id view <$> (simulateQ (RegistrationNativeSeedDelayWorld.handler setup codec route) work).run (mask reached)) := by
    apply bind_congr
    intro reached
    exact program_view setup codec route work reached
  have moved := congrArg (fun distribution => distribution >>= fun reached =>
    Prod.map id view <$> (simulateQ (RegistrationNativeSeedDelayWorld.handler setup codec route) work).run reached)
    (complete_mask point before)
  simp only [bind_map_left] at moved
  exact (LawEq.of_eq (first.trans moved)).trans
    ((RegistrationNativeSeedDelay.program_delay setup codec route work point (mask before)).trans
      (LawEq.of_eq (program_view setup codec route work before).symm))

end BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource.program_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource.program_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource.complete_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource.complete_mask
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource.program_delay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource.program_delay
