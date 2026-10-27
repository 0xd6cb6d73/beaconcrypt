import BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences

/-! Actual root callback values passed to the original native initializer continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
open PqxdhRootTableInitialization (rootArray)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- A successful actual Beacon stage retains its reached metadata and the literal root callback value used by the complete original post-root initializer/getter/receive program. No root is inferred from an installed kernel. -/
theorem stage_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes) (publicValue : PublicChallenge)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes)
    (kem : KemSK) (raw : Pqxdh.Bytes)
    (before : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (after : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : (some staged, after) ∈ support
      ((interp (family setup seed scalar) (simulateQ (stageImpl setup codec beaconSeed)
        (PqxdhPhase2DhStage.stage publicValue codec.frameRead control identity oneTime kem raw))).run before)) :
    ∃ pending root,
      some pending ∈ support ((beaconPrefix setup codec beaconSeed control identity oneTime kem raw).run' ()) ∧
      (some root, after.2) ∈ support ((family setup seed scalar
        (.inr (.derive (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)))).run before.2) ∧
      RootAt setup seed scalar after.2.cache
        (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected) root ∧
      (some staged, ((), after.1.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (rootArray root))).run ((), before.1.ctx)) ∧
      after.1 = { before.1 with ctx := after.1.ctx, ghost := { before.1.ghost with
        touches := before.1.ghost.touches ++
          [.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)] } } := by
  have forward : CoinForward (family setup seed scalar) :=
    rom_coinForward setup.hmac setup.joint setup.dh seed scalar
  rw [stage_game] at supported
  simp only [interp_bind, StateT.run_bind, interp_run_liftCoins _ forward,
    bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨prepared, preparedRun, continued⟩ := supported
  cases prepared with
  | none =>
      simp only [interp_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
        false_and] at continued
  | some pending =>
      simp only [recordTouch, interp_bind, StateT.run_bind, interp_run_modify, pure_bind,
        interp_run_forward, bind_map_left, mem_support_bind_iff] at continued
      obtain ⟨derived, rootRun, continued⟩ := continued
      cases reply : derived.1 with
      | none =>
          simp only [reply, interp_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            reduceCtorEq, false_and] at continued
      | some root =>
          simp only [reply, interp_run_onCtx_simulateQ _ forward, support_map] at continued
          obtain ⟨opened, openedRun, same⟩ := continued
          have resultEq : opened.1 = some staged := congrArg Prod.fst same
          have stateEq := congrArg Prod.snd same
          dsimp only at stateEq
          rw [← stateEq]
          have actualRoot : (some root, derived.2) ∈ support
              ((family setup seed scalar (.inr (.derive
                (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)))).run before.2) := by
            rw [← reply]
            exact rootRun
          refine ⟨pending, root, preparedRun, actualRoot,
            root_at setup seed scalar _ before.2 derived.2 root actualRoot, ?_, rfl⟩
          have unitEq : opened.2.1 = () := Subsingleton.elim _ _
          rw [← resultEq, ← unitEq]
          exact openedRun

/-- A successful original Server acceptance stores exactly the root returned at this attempt's reached source descriptor. Its complete prefix, allocation coordinate and native pending fields come from the same run. -/
theorem accept_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (publicValue : PublicChallenge) (raw : Pqxdh.Bytes)
    (before : GameState KemSK × PqxdhJointDhExtractFamily.State) (index : Nat)
    (after : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : (some index, after) ∈ support
      ((interp (family setup seed scalar) (acceptOracle setup codec checks publicValue raw)).run before)) :
    ∃ input root consumed,
      index = before.1.sessions ∧
      (some input, consumed) ∈ support ((serverPrefix setup codec checks raw).run before.1.server.consumed) ∧
      PqxdhServerRelatedRootInput.localNonzero input ∧
      (some root, after.2) ∈ support ((family setup seed scalar
        (.inr (.derive (PqxdhServerRelatedRootInput.message input)))).run before.2) ∧
      RootAt setup seed scalar after.2.cache (PqxdhServerRelatedRootInput.message input) root ∧
      after.1.pending index = some ⟨root, PqxdhServerClearedRoot.pending (binding setup publicValue) input⟩ ∧
      after.1.ghost.touches = before.1.ghost.touches ++
        [.session index (PqxdhServerRelatedRootInput.message input) (some root)] := by
  classical
  have forward : CoinForward (family setup seed scalar) :=
    rom_coinForward setup.hmac setup.joint setup.dh seed scalar
  unfold acceptOracle at supported
  simp only [interp_bind, StateT.run_bind, interp_run_get, interp_run_liftCoins _ forward,
    interp_run_set, pure_bind, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨collected, prefixRun, continued⟩ := supported
  rcases collected with ⟨_ | input, consumed⟩
  · simp only [interp_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
      false_and] at continued
  · simp only [interp_bind, StateT.run_bind, interp_simulateQ, client_run_flat] at continued
    by_cases valid : PqxdhServerRelatedRootInput.localNonzero input
    · simp only [valid, ite_true, bind_assoc, mem_support_bind_iff] at continued
      obtain ⟨derived, rootRun, continued⟩ := continued
      cases reply : derived.1 with
      | none =>
          simp only [reply, support_pure, Set.mem_singleton_iff, exists_eq_left,
            interp_run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at continued
      | some root =>
          simp only [reply, support_pure, Set.mem_singleton_iff, exists_eq_left,
            interp_bind, StateT.run_bind, interp_run_modify, interp_run_pure, pure_bind,
            Prod.mk.injEq, Option.some.injEq] at continued
          obtain ⟨indexEq, stateEq⟩ := continued
          rw [indexEq, stateEq]
          have actualRoot : (some root, derived.2) ∈ support
              ((family setup seed scalar (.inr (.derive
                (PqxdhServerRelatedRootInput.message input)))).run before.2) := by
            rw [← reply]
            exact rootRun
          exact ⟨input, root, consumed, rfl, prefixRun, valid, actualRoot,
            root_at setup seed scalar _ before.2 derived.2 root actualRoot, by simp only [Function.update_self], rfl⟩
    · simp only [valid, ite_false, pure_bind, interp_run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, reduceCtorEq, false_and] at continued

/-- A successful original build consumes its actual present token, runs the native builder with that token's root, and installs the kernel produced from that same root. The complete native log and cache effects remain in the support receipt. -/
theorem build_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (index : Nat) (payload : Option Pqxdh.Bytes)
    (before : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (response : PqxdhServerRegistrationPublication.Response)
    (after : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : (some response, after) ∈ support
      ((interp (family setup seed scalar) (buildOracle setup codec checks index payload)).run before)) :
    ∃ token candidate kernel logged cache,
      before.1.pending index = some token ∧
      after.2 = before.2 ∧
      after.1.pending = Function.update before.1.pending index none ∧
      after.1.server = PqxdhServerRegistrationPublication.publish before.1.server candidate kernel () ∧
      Installed setup.source token.root kernel ∧
      (ok (some response, PqxdhServerRegistrationPublication.publish before.1.server candidate kernel ()),
        (logged, cache)) ∈ support ((simulateQ (tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () before.1.server)).run
            ([], before.1.ctx)) ∧
      after.1.ctx = cache ∧
      after.1.ghost.seals = before.1.ghost.seals ++ logged.map (fun entry => (index, entry)) := by
  have forward : CoinForward (family setup seed scalar) :=
    rom_coinForward setup.hmac setup.joint setup.dh seed scalar
  unfold buildOracle at supported
  simp only [interp_bind, StateT.run_bind, interp_run_get, pure_bind] at supported
  cases lookup : before.1.pending index with
  | none =>
      simp only [lookup, interp_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at supported
  | some token =>
      simp only [lookup, interp_bind, StateT.run_bind, interp_run_liftCoins _ forward,
        bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨tail, tailRun, continued⟩ := supported
      rcases build_support (tailImpl setup codec checks) setup.source (tailImpl_kdf setup codec checks)
        token.pending token.root payload () before.1.server ([], before.1.ctx) tail tailRun with failed |
          ⟨candidate, kernel, output, completed, installed, _⟩
      · simp only [failed, settle, interp_run_set, interp_run_pure,
          support_pure, Set.mem_singleton_iff, exists_eq_left, Prod.mk.injEq, reduceCtorEq, false_and] at continued
      · simp only [completed, settle, interp_run_set, interp_run_pure,
          support_pure, Set.mem_singleton_iff, exists_eq_left, Prod.mk.injEq, Option.some.injEq] at continued
        obtain ⟨outputEq, stateEq⟩ := continued
        rw [outputEq, stateEq]
        refine ⟨token, candidate, kernel, tail.2.1, tail.2.2, rfl, rfl, rfl, rfl, installed, ?_, rfl, rfl⟩
        rw [← completed]
        exact tailRun

/-- A successful original finish reaches an actual InitSent stage, retains that stage's full primitive state, and publishes precisely its staged kernel after the original outer pin checks. -/
theorem finish_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (raw payload : Pqxdh.Bytes) (before after : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : (some payload, after) ∈ support
      ((interp (family setup seed scalar) (finishOracle setup codec publicValue beaconSeed raw)).run before)) :
    ∃ control prekey oneTime kem staged middle,
      before.1.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
      (some staged, middle) ∈ support ((interp (family setup seed scalar)
        (simulateQ (stageImpl setup codec beaconSeed)
          (PqxdhPhase2DhStage.stage publicValue codec.frameRead control before.1.beacon.beacon.identity
            oneTime kem raw))).run before) ∧
      control.expected_server_binding.identity_key_id = staged.authenticated.candidate.server_binding.identity_key_id ∧
      absBytes middle.1.beacon.beacon.serverIdentity =
        absBytes staged.authenticated.candidate.server_binding.identity_public_key ∧
      payload = staged.opened.plaintext.drop 8 ∧
      after = ({ middle.1 with
        beacon := (PqxdhBeaconPhase2Publication.publish middle.1.beacon staged).2
        ghost := middle.1.ghost.accept (some (Accepted.ofStaged staged)) }, middle.2) := by
  unfold finishOracle at supported
  simp only [interp_bind, StateT.run_bind, interp_run_get, pure_bind] at supported
  cases active : before.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [active, interp_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reached, stagedRun, continued⟩ := supported
      simp only [interp_run_get, interp_run_set, interp_run_pure, support_pure, Set.mem_singleton_iff,
        exists_eq_left, Prod.mk.injEq] at continued
      obtain ⟨staged, stageEq, pinned, identity, published⟩ :=
        PqxdhBeaconPhase2Publication.finish_success control reached.2.1.beacon
          (PqxdhBeaconPhase2Publication.finish control reached.2.1.beacon reached.1).2
          reached.1 payload (Prod.ext continued.1.symm rfl)
      refine ⟨control, prekey, oneTime, kem, staged, reached.2, rfl, ?_, pinned, identity,
        (congrArg Prod.fst published).symm, ?_⟩
      · rw [← stageEq]
        exact stagedRun
      · rw [continued.2, ← congrArg Prod.snd published, ← continued.1]
        simp only [stageEq, acceptedOf, Option.isSome_some, ite_true, Option.map_some]

  | _ =>
      simp only [active, interp_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at supported

/-- The actual successful finish carries one continuous receipt from its literal root callback through native initialization/opening to the published Beacon kernel. The root is retained at the final real cache, independently of kernel representations. -/
theorem finish_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (raw payload : Pqxdh.Bytes) (before after : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : (some payload, after) ∈ support
      ((interp (family setup seed scalar) (finishOracle setup codec publicValue beaconSeed raw)).run before)) :
    ∃ control prekey oneTime kem pending root staged,
      before.1.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
      some pending ∈ support ((beaconPrefix setup codec beaconSeed control before.1.beacon.beacon.identity
        oneTime kem raw).run' ()) ∧
      (some root, after.2) ∈ support ((family setup seed scalar
        (.inr (.derive (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)))).run before.2) ∧
      RootAt setup seed scalar after.2.cache
        (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected) root ∧
      (some staged, ((), after.1.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (rootArray root))).run ((), before.1.ctx)) ∧
      after.1.beacon.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel ∧
      payload = staged.opened.plaintext.drop 8 ∧
      control.expected_server_binding.identity_key_id = staged.authenticated.candidate.server_binding.identity_key_id ∧
      after.1.ghost.touches = before.1.ghost.touches ++
        [.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)] := by
  obtain ⟨control, prekey, oneTime, kem, staged, middle, active, reached, pinned, _, plaintext, stateEq⟩ :=
    finish_receipt setup codec publicValue beaconSeed seed scalar raw payload before after supported
  obtain ⟨pending, root, prepared, derived, rooted, initialized, stageState⟩ :=
    stage_receipt setup codec beaconSeed seed scalar publicValue control before.1.beacon.beacon.identity
      oneTime kem raw before staged middle reached
  rw [stateEq]
  refine ⟨control, prekey, oneTime, kem, pending, root, staged, active, prepared, derived, rooted,
    initialized, rfl, plaintext, pinned, ?_⟩
  exact (Ghost.accept_touches _ _).trans (congrArg (fun state => state.ghost.touches) stageState)

end BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.stage_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.stage_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.accept_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.accept_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.build_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.build_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.finish_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.finish_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.finish_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization.finish_root
