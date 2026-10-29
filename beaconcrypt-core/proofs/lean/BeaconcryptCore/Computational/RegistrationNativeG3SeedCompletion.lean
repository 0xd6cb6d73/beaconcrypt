-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource

/-! A finite private completion of the actual World seed cache can be erased before any adaptive actual World program. This extends the concrete one-point delay law to all slots without a new protocol capability. It retains installed kernels, populated AD, shared CTX cache, role-use history and all named semantic fields. Splitting the actual uniform108 service and excluding repeated-role aliases remain separate obligations. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot WorldSpec)
open PqxdhRecordLiftWorld (State SeedSpec)
open RegistrationNativeSeedDelayCore (lens)
open RegistrationNativeSeedDelay (view)
open LazyOracleDiscard (StateLens LawEq)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

noncomputable def complete : List (Slot n) → State n → ProbComp (State n)
  | [], before => pure before
  | point :: rest, before => lens.completeOpt (some point) before >>= complete rest

/-- Completing any fixed list of private slots is removable before the actual counted World execution. -/
theorem program_delay (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (points : List (Slot n)) (before : State n) :
    LawEq
      (complete points before >>= fun reached =>
        Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run reached)
      (Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before) := by
  induction points generalizing before with
  | nil => simp only [complete, pure_bind]; exact LawEq.refl _
  | cons point rest ih =>
      simp only [complete, bind_assoc]
      exact (LawEq.bind (LawEq.refl _) (fun reached => ih reached)).trans
        (RegistrationNativeSeedDelaySource.program_delay setup codec route work (some point) before)

/-- All finite private seed slots may be sampled in a proof game and then erased by the same concrete actual-World law. -/
theorem all_program_delay (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    LawEq
      (complete (List.finRange n) before >>= fun reached =>
        Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run reached)
      (Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before) :=
  program_delay setup codec route work (List.finRange n) before

/-- A private point completion changes only the focused cache in every supported source execution. -/
theorem point_view (point : Slot n) (before after : State n)
    (supported : after ∈ support (lens.completeOpt (some point) before)) : view after = view before := by
  simp only [StateLens.completeOpt, StateLens.complete, support_map] at supported
  obtain ⟨cache, _sampled, equal⟩ := supported
  cases equal
  exact RegistrationNativeSeedDelay.view_set before cache

/-- A complete private slot list preserves every semantic field retained by the actual World observer. -/
theorem complete_view (points : List (Slot n)) (before after : State n)
    (supported : after ∈ support (complete points before)) : view after = view before := by
  induction points generalizing before with
  | nil =>
      simp only [complete, mem_support_pure_iff] at supported
      cases supported
      rfl
  | cons point rest ih =>
      simp only [complete, mem_support_bind_iff] at supported
      obtain ⟨reached, stepped, continued⟩ := supported
      exact (ih reached continued).trans (point_view point before reached stepped)

end BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion.program_delay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion.program_delay
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion.all_program_delay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion.all_program_delay
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion.point_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion.point_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion.complete_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SeedCompletion.complete_view
