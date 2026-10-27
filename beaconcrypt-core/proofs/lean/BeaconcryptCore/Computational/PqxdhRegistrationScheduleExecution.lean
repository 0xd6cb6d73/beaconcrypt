-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleSurface

/-! The literal Server constructor and the raw dynamic Beacon API share one complete adaptive execution. Runtime initialization state survives every source constructor; public numeric indices retain missing and future requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- Execute the public raw surface after the literal source Server creation. The created private seed remains interpreter input; the adversary receives only the actual public identity and sender ID. -/
noncomputable def surfaceExecute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (adversary : PublicIdentity → Std.U64 → OracleComp SurfaceSpec Result)
    (created : PqxdhLiveServerConstruction.Created Unit) (runtime : A) :
    ProbComp (Result × (A × State KemSK)) :=
  (simulateQ (surfaceHandler setup codec checks created.seed ensureInit)
    (adversary created.publicIdentity created.server.server.metadata.sender)).run (runtime, initial created)

/-- This common registration execution performs the real supplied/generated Server constructor, then arbitrary dynamic Beacon creation and registration scheduling. The full constructor value and final protocol/runtime state are private analysis output. -/
noncomputable def surfaceExperiment (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp SurfaceSpec Result) (runtime : A) :
    ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × (Result × State KemSK)) × A) := do
  let started ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId supplied).run runtime
  match started.1 with
  | none => pure (none, started.2)
  | some created => (fun result => (some (created, result.1, result.2.2), result.2.1)) <$>
      surfaceExecute setup codec checks ensureInit adversary created started.2

/-- A completed common run supplies the exact source constructor reply and the same full subsequent raw-surface continuation. Its intermediate runtime is preserved explicitly rather than conflated with the final runtime. -/
theorem surfaceExperiment_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp SurfaceSpec Result) (runtime afterRuntime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (result : Result × State KemSK)
    (supported : (some (created, result), afterRuntime) ∈ support
      (surfaceExperiment setup codec checks ensureInit supplied adversary runtime)) :
    ∃ initializedRuntime,
      (some created, initializedRuntime) ∈ support
        ((PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId supplied).run runtime) ∧
      (result.1, afterRuntime, result.2) ∈ support
        (surfaceExecute setup codec checks ensureInit adversary created initializedRuntime) := by
  simp only [surfaceExperiment, mem_support_bind_iff] at supported
  rcases supported with ⟨⟨_ | started, nextRuntime⟩, born, continued⟩
  all_goals simp [Set.mem_image] at continued
  rcases continued with ⟨reply, final, executed, rfl, rfl⟩
  exact ⟨nextRuntime, born, executed⟩

/-- Actual source initialization and the complete raw schedule establish consumed-set uniqueness and public all-attempt allocation bounds. Generated and attacker-supplied Server seeds execute the identical source rules; arbitrary runtime effects remain in the execution. -/
theorem surfaceExperiment_ledger (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp SurfaceSpec Result) (qAccept qBuild : Nat)
    (accepts : ∀ identity sender, (adversary identity sender).IsQueryBoundP (SurfaceClass checks IsAccept) qAccept)
    (builds : ∀ identity sender, (adversary identity sender).IsQueryBoundP (SurfaceClass checks IsBuild) qBuild)
    (runtime afterRuntime : A) (created : PqxdhLiveServerConstruction.Created Unit)
    (result : Result × State KemSK)
    (supported : (some (created, result), afterRuntime) ∈ support
      (surfaceExperiment setup codec checks ensureInit supplied adversary runtime)) :
    result.2.shared.2.server.consumed.Nodup ∧
      result.2.shared.2.server.consumed.length ≤ qAccept ∧
      result.2.shared.2.sessions ≤ qAccept ∧
      setup.serverKeyId.val ≤ result.2.shared.2.server.control.last_key_id.val ∧
      result.2.shared.2.server.control.last_key_id.val ≤ setup.serverKeyId.val + qBuild := by
  obtain ⟨initializedRuntime, born, reached⟩ := surfaceExperiment_support setup codec checks ensureInit supplied
    adversary runtime afterRuntime created result supported
  obtain ⟨seed, rfl, _⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit 0 setup.serverKeyId
    supplied runtime initializedRuntime created born
  have consumed := surface_consumed setup codec checks seed ensureInit _ _
    (result.1, afterRuntime, result.2) reached
  refine ⟨consumed.2 (by simp [initial, PqxdhLiveServerConstruction.initialized]), ?_, ?_, ?_, ?_⟩
  · simpa only [initial, PqxdhLiveServerConstruction.initialized, List.length_nil, Nat.zero_add] using
      surface_count setup codec checks seed ensureInit IsAccept
        (fun current => current.shared.2.server.consumed.length)
        (handler_consumed_count setup codec checks seed) _ qAccept (accepts _ _) _
        (result.1, afterRuntime, result.2) reached
  · simpa only [initial, Nat.zero_add] using
      surface_count setup codec checks seed ensureInit IsAccept (fun current => current.shared.2.sessions)
        (handler_sessions setup codec checks seed) _ qAccept (accepts _ _) _
        (result.1, afterRuntime, result.2) reached
  · simpa only [initial, PqxdhLiveServerConstruction.initialized] using
      surface_program_relation setup codec checks seed ensureInit
        (fun before after => before.shared.2.server.control.last_key_id.val ≤ after.shared.2.server.control.last_key_id.val)
        (fun _ => le_refl _) (fun _ _ _ first second => first.trans second)
        (fun query before after member => by
          rcases handler_counter setup codec checks seed query before after member with same | next
          · rw [same]
          · rw [next]; omega)
        _ _ (result.1, afterRuntime, result.2) reached
  · simpa only [initial, PqxdhLiveServerConstruction.initialized] using
      surface_count setup codec checks seed ensureInit IsBuild
        (fun current => current.shared.2.server.control.last_key_id.val)
        (handler_counter_count setup codec checks seed) _ qBuild (builds _ _) _
        (result.1, afterRuntime, result.2) reached

end BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surfaceExperiment_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surfaceExperiment_support
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surfaceExperiment_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surfaceExperiment_ledger
