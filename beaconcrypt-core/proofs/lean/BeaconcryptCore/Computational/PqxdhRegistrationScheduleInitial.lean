-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleLedger
import BeaconcryptCore.Computational.PqxdhLiveServerConstruction

/-! Source Server construction supplies the empty joint registration state. Imported seeds remain caller-owned inputs, and generated seeds retain their actual draw. The obsolete single-Beacon analysis field is a deterministic aborted value, never a generated hidden identity or a public owner slot. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- An erased, deterministic compatibility field for the old single-Beacon interpreter. It contains no private key and is not inserted in the dynamically exposed owner list. -/
def bookkeeping (created : PqxdhLiveServerConstruction.Created Unit) :
    RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK :=
  ⟨⟨(), created.server.server.metadata.sender, created.server.server.identity,
    .aborted ⟨created.server.server.metadata.sender⟩⟩, 0⟩

/-- Retain the actual constructed Server's identity, peers, control and consumed list; erase only its private registry metadata. Both primitive tables and the dynamic owner/pending registries start empty. -/
def initial (created : PqxdhLiveServerConstruction.Created Unit) : State KemSK :=
  { shared := (PqxdhJointDhExtractFamily.empty,
      { ctx := ∅
        server :=
          { server := ⟨created.server.server.identity, created.server.server.peers, ()⟩
            identityKeyId := created.server.server.metadata.sender
            control := created.control
            consumed := created.consumed }
        pending := fun _ => none
        beacon := bookkeeping created
        sessions := 0
        ghost := Ghost.empty })
    owners := [] }

/-- The unused analysis field is literally aborted and the public owner registry is literally empty; no auxiliary honest identity or KEM key is sampled. -/
theorem initial_bookkeeping (created : PqxdhLiveServerConstruction.Created Unit) :
    (initial (KemSK := KemSK) created).shared.2.beacon.beacon.phase =
      .aborted ⟨created.server.server.metadata.sender⟩ ∧
      (initial (KemSK := KemSK) created).owners = [] := by
  exact ⟨rfl, rfl⟩

/-- No joint public operation dispatches a finish to the old single-Beacon analysis coordinate; every finish instead names the separate dynamic owner registry. -/
theorem serverLabel_ne_finish (query : Spec.Domain) (raw : Pqxdh.Bytes) :
    serverLabel query ≠ some (.inr (.finish raw)) := by
  rcases query with coin | request
  · simp [serverLabel]
  · cases request <;> simp [serverLabel]

/-- The old single-Beacon field is not a mutable public owner: all joint operations preserve it exactly, including real finishes directed to dynamically allocated owner addresses. -/
theorem handler_bookkeeping (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : State KemSK) (result : Spec.Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    result.2.shared.2.beacon = state.shared.2.beacon := by
  have unchanged := server_labeled_relation setup codec checks serverSeed
    (fun label before after => (∀ raw, label ≠ some (.inr (.finish raw))) → after.beacon = before.beacon)
    (fun _ _ _ => rfl)
    (fun original before after member unrelated =>
      (authHandler_step (Reader := Reader) (Response := Response) codec checks serverSeed original before after member).2.2.2.2
        (fun raw equal => unrelated raw (congrArg some equal))) query state result supported
  exact unchanged (serverLabel_ne_finish query)

/-- The complete adaptive program preserves the deterministic compatibility field from source initialization; all reached mutable Beacons remain in the separate actual owner registry. -/
theorem program_bookkeeping (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp Spec Result)
    (state : State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    result.2.shared.2.beacon = state.shared.2.beacon := by
  exact run_rel (handler setup codec checks serverSeed)
    (fun before after => after.shared.2.beacon = before.shared.2.beacon)
    (fun _ => rfl) (fun _ _ _ first second => second.trans first)
    (handler_bookkeeping setup codec checks serverSeed) program state result supported

/-- The original adversary receives only the actually constructed Server public identity and public identifier. The private constructor value is retained solely for source interpretation and event provenance. -/
noncomputable def execute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : PublicIdentity → Std.U64 → OracleComp Spec Result)
    (created : PqxdhLiveServerConstruction.Created Unit) : ProbComp (Result × State KemSK) :=
  (simulateQ (handler setup codec checks created.seed)
    (adversary created.publicIdentity created.server.server.metadata.sender)).run (initial created)

/-- One literal source Server constructor precedes the dynamically scheduled registration APIs. Runtime initialization runs even on invalid supplied bytes; no Beacon, KEM or one-time key is precreated. The returned constructor/state pair is private analysis output. -/
noncomputable def experiment (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp Spec Result) (runtime : A) :
    ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × (Result × State KemSK)) × A) := do
  let started ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId supplied).run runtime
  match started.1 with
  | none => pure (none, started.2)
  | some created => (fun result => (some (created, result), started.2)) <$> execute setup codec checks adversary created

/-- Every completed joint run comes from that exact source constructor reply and the identical full adaptive continuation; no successful initialization or key-origin premise is assumed. -/
theorem experiment_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp Spec Result) (runtime afterRuntime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (result : Result × State KemSK)
    (supported : (some (created, result), afterRuntime) ∈ support
      (experiment setup codec checks ensureInit supplied adversary runtime)) :
    (some created, afterRuntime) ∈ support
      ((PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId supplied).run runtime) ∧
      result ∈ support (execute setup codec checks adversary created) := by
  simp only [experiment, mem_support_bind_iff] at supported
  rcases supported with ⟨⟨_ | started, nextRuntime⟩, born, continued⟩
  all_goals simp [Set.mem_image] at continued
  rcases continued with ⟨reply, final, executed, rfl, rfl, rfl⟩
  exact ⟨born, executed⟩

/-- A completed experiment's actual private seed and empty source role come from the literal constructor. Supplied seed bytes are retained exactly and carry imported origin, never a generated-seed label. -/
theorem experiment_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp Spec Result) (runtime afterRuntime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (result : Result × State KemSK)
    (supported : (some (created, result), afterRuntime) ∈ support
      (experiment setup codec checks ensureInit supplied adversary runtime)) :
    ∃ seed, created = PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId
      (if supplied.isNone then .generated else .imported) seed ∧
      (match supplied with | none => True | some bytes => seed.toList = bytes) := by
  have origin := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit 0 setup.serverKeyId supplied
    runtime afterRuntime created
    (experiment_support setup codec checks ensureInit supplied adversary runtime afterRuntime created result supported).1
  cases supplied <;> simpa using origin

/-- The literal source constructor and arbitrary joint schedule supply the actual empty-set invariant and public allocation bounds. Neither imported nor generated identities bypass the same admission or moved-token rules. -/
theorem experiment_ledger (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (adversary : PublicIdentity → Std.U64 → OracleComp Spec Result)
    (qAccept qBuild : Nat)
    (accepts : ∀ identity sender, (adversary identity sender).IsQueryBoundP IsAccept qAccept)
    (builds : ∀ identity sender, (adversary identity sender).IsQueryBoundP IsBuild qBuild)
    (runtime afterRuntime : A) (created : PqxdhLiveServerConstruction.Created Unit)
    (result : Result × State KemSK)
    (supported : (some (created, result), afterRuntime) ∈ support
      (experiment setup codec checks ensureInit supplied adversary runtime)) :
    result.2.shared.2.server.consumed.Nodup ∧
      result.2.shared.2.server.consumed.length ≤ qAccept ∧
      result.2.shared.2.sessions ≤ qAccept ∧
      setup.serverKeyId.val ≤ result.2.shared.2.server.control.last_key_id.val ∧
      result.2.shared.2.server.control.last_key_id.val ≤ setup.serverKeyId.val + qBuild := by
  have reached := (experiment_support setup codec checks ensureInit supplied adversary runtime afterRuntime created result supported).2
  obtain ⟨seed, rfl, _⟩ := experiment_origin setup codec checks ensureInit supplied adversary runtime afterRuntime created result supported
  have consumed := program_consumed setup codec checks seed _ _ result reached
  refine ⟨consumed.2 (by simp [initial, PqxdhLiveServerConstruction.initialized]), ?_, ?_, ?_, ?_⟩
  · simpa only [initial, PqxdhLiveServerConstruction.initialized, List.length_nil, Nat.zero_add] using
      program_consumed_count setup codec checks seed _ qAccept (accepts _ _) _ result reached
  · simpa only [initial, Nat.zero_add] using
      program_sessions setup codec checks seed _ qAccept (accepts _ _) _ result reached
  · simpa only [initial, PqxdhLiveServerConstruction.initialized] using
      program_counter setup codec checks seed _ _ result reached
  · simpa only [initial, PqxdhLiveServerConstruction.initialized] using
      program_counter_bound setup codec checks seed _ qBuild (builds _ _) _ result reached

end BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.initial_bookkeeping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.initial_bookkeeping
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.serverLabel_ne_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.serverLabel_ne_finish
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_bookkeeping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_bookkeeping
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_bookkeeping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_bookkeeping
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.experiment_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.experiment_support
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.experiment_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.experiment_origin
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.experiment_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.experiment_ledger
