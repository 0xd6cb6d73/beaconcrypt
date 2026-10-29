-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelaySource
import BeaconcryptCore.Computational.CborRecordWorldSimulation

/-! Seed delay applies to the actual cursor-aware guarded World. The public record shell ignores the private seed-cache lens, so its exact source compiler converts the guarded continuation to an ordinary World continuation with the same admission state. No guarded-versus-unguarded equality is assumed. The resulting delay retains all role-use markers, installed kernels, shared CTX, counters and protocol state except the already named seed/uniform accounting view. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay
open PqxdhRecordLiftWorld (State SeedSpec)
open PqxdhRecordLiftInterface (WorldSpec Slot)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSeedDelayCore (lens)
open RegistrationNativeSeedDelay (view)
open CborRecordWorldCursor (worldShell)
open LazyOracleDiscard (StateLens LawEq)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

/-- The actual public admission shell retains every cursor and control field when only the private seed-cache cell map is replaced. -/
theorem shell_set (before : State n) (cache : (SeedSpec n).QueryCache) :
    worldShell (lens.set before cache) = worldShell before := rfl

/-- Every supported optional seed completion has the identical actual public admission shell. -/
theorem shell_complete (point : Option (Slot n)) (before after : State n)
    (supported : after ∈ support (lens.completeOpt point before)) : worldShell after = worldShell before := by
  cases point with
  | none =>
      rw [StateLens.completeOpt, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some slot =>
      simp only [StateLens.completeOpt, StateLens.complete, support_map] at supported
      obtain ⟨cache, _possible, rfl⟩ := supported
      exact shell_set before cache

/-- Actual early record-size refusals and every adaptive World continuation obey the derived seed-delay law, with complete role-use and semantic state retained. -/
theorem program_delay (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (point : Option (Slot n)) (before : State n) :
    LawEq
      (lens.completeOpt point before >>= fun reached =>
        Prod.map id view <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run reached)
      (Prod.map id view <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run before) := by
  have first : (lens.completeOpt point before >>= fun reached =>
        Prod.map id view <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run reached) =
      (lens.completeOpt point before >>= fun reached =>
        Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
          (CborRecordWorldClient.client work (worldShell before))).run reached) := by
    apply bind_congr_of_forall_mem_support
    intro reached supported
    rw [← CborRecordWorldSimulation.client_simulation setup codec route work reached,
      shell_complete point before reached supported]
  exact (LawEq.of_eq first).trans
    ((RegistrationNativeSeedDelaySource.program_delay setup codec route
      (CborRecordWorldClient.client work (worldShell before)) point before).trans
        (LawEq.of_eq (congrArg (fun distribution => Prod.map id view <$> distribution)
          (CborRecordWorldSimulation.client_simulation setup codec route work before))))

noncomputable def completeMany : List (Slot n) → State n → ProbComp (State n)
  | [], before => pure before
  | slot :: slots, before => lens.complete slot before >>= completeMany slots

/-- Completing any finite list of actual seed-cache cells can be deferred through the entire original guarded World computation, including repeated cells. -/
theorem program_many (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (slots : List (Slot n)) (before : State n) :
    LawEq
      (completeMany slots before >>= fun reached =>
        Prod.map id view <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run reached)
      (Prod.map id view <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run before) := by
  induction slots generalizing before with
  | nil => exact LawEq.of_eq (pure_bind _ _)
  | cons slot slots ih =>
      have first := (LawEq.refl (lens.complete slot before)).bind (fun reached => ih reached)
      simp only [completeMany, bind_assoc] at first ⊢
      exact first.trans (program_delay setup codec route work (some slot) before)

end BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay.shell_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay.shell_set
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay.shell_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay.shell_complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay.program_delay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay.program_delay
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay.program_many' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedSeedDelay.program_many
