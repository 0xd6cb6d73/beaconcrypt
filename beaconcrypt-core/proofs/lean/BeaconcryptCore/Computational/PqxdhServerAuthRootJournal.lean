import BeaconcryptCore.Computational.PqxdhServerAuthRootSession

/-! The actual successful finish and public journal of the complete original annotated source. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootJournal
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Original acceptance allocates and derives a Server token without changing the Beacon acceptance snapshot. All optional and diagnostic branches remain in the same source support. -/
theorem accept_snapshot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (before : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run before)) :
    result.2.ghost.acceptance = before.ghost.acceptance := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨prefixMember, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | some input =>
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨consumed, extra, eq, _, _⟩ := client_run before.sessions (binding setup publicValue) input _ returned derived
      rcases returned with ⟨outcome, after⟩
      rcases outcome with (_ | token) | error | _
      all_goals
        simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        subst result
        change after.ghost.acceptance = before.ghost.acceptance
        dsimp only at eq
        rw [eq]

/-- Every original builder outcome preserves the Beacon snapshot, including writer failure and all native diagnostics. -/
theorem build_snapshot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (payload : Option Pqxdh.Bytes) (before : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks index payload).run before)) :
    result.2.ghost.acceptance = before.ghost.acceptance := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : before.pending index with
  | none =>
      simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | some token =>
      simp only [found, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨tail, lifted, supported⟩ := supported
      obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
      simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      rfl

/-- A rejected original finish creates no acceptance, while retaining its actual preparation, opening, cache and abort effects. -/
theorem finish_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (before after : GameState KemSK)
    (supported : (none, after) ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run before)) :
    after.ghost.acceptance = before.ghost.acceptance := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases active : before.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [active, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨staged, stageRun, supported⟩ := supported
      obtain ⟨cache, extra, stageEq, _⟩ := stage_run setup codec beaconSeed publicValue control
        before.beacon.beacon.identity oneTime kem raw before staged stageRun
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, _, rfl, same⟩ := supported
      have resultEq := congrArg Prod.fst same
      have stateEq := congrArg Prod.snd same
      dsimp only at resultEq stateEq
      rw [stateEq]
      simp only [← resultEq, acceptedOf, Option.isSome_none, Bool.false_eq_true, ite_false, Ghost.accept]
      rw [stageEq]
  | _ =>
      simp only [active, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
      exact congrArg (fun state => state.ghost.acceptance) supported.2

/-- Only an actual successful finish reply can change the original acceptance snapshot. This follows from every literal API branch, not from a final acceptance or parser premise. -/
theorem handler_snapshot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (before : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run before)) :
    result.2.ghost.acceptance = before.ghost.acceptance ∨ ∃ raw payload,
      (⟨query, result.1⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) =
        ⟨.inr (.finish raw), some payload⟩ := by
  rcases query with coin | query
  · left
    rw [forward_support _ _ _ supported]
  cases query with
  | accept raw => exact Or.inl (accept_snapshot setup codec checks publicValue raw before result supported)
  | build index data => exact Or.inl (build_snapshot setup codec checks index data before result supported)
  | finish raw =>
      rcases result with ⟨_ | payload, after⟩
      · exact Or.inl (finish_none setup codec publicValue beaconSeed raw before after supported)
      · exact Or.inr ⟨raw, payload, rfl⟩
  | hash bytes =>
      obtain ⟨_, same⟩ := hashOracle_step bytes before result supported
      exact Or.inl (by rw [same])
  | reveal keyId =>
      simp only [authHandler] at supported
      subst result
      exact Or.inl rfl
  | hmac key message =>
      left
      simp only [authHandler, hmacOracle] at supported
      split_ifs at supported
      · obtain ⟨middle, first, rest⟩ := run_bind_support _ _ _ _ supported
        rw [record_run, support_pure, Set.mem_singleton_iff] at first
        subst middle
        rw [forward_support _ _ _ rest]
      · rw [forward_support _ _ _ supported]

/-- A nonempty acceptance snapshot in the actual source path requires a completed successful finish call. The original empty snapshot discharges occurrence provenance. -/
theorem path_finish_exists (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after)
    (empty : before.1.ghost.acceptance = none) (snap : Snapshot)
    (accepted : after.1.ghost.acceptance = some snap) :
    ∃ call ∈ calls, ∃ raw payload,
      PqxdhServerAuthRootExecution.publicCall call = ⟨.inr (.finish raw), some payload⟩ := by
  induction path with
  | nil state primitive => simp_all
  | cons call primitive middle suffix final reached rest ih =>
      have original := interpreted_source setup seed scalar _ _ _
        (callback_source setup codec checks publicValue beaconSeed seed scalar call primitive middle reached)
      rcases handler_snapshot setup codec checks publicValue beaconSeed call.query call.before
        (call.reply, call.after) original with same | success
      · obtain ⟨found, member, raw, payload, actual⟩ := ih (same.trans empty) accepted
        exact ⟨found, List.mem_cons_of_mem call member, raw, payload, actual⟩
      · obtain ⟨raw, payload, actual⟩ := success
        exact ⟨call, List.mem_cons_self, raw, payload, actual⟩

end BeaconcryptCore.Computational.PqxdhServerAuthRootJournal

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.accept_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.accept_snapshot

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.build_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.build_snapshot

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.finish_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.finish_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.handler_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.handler_snapshot

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.path_finish_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootJournal.path_finish_exists
