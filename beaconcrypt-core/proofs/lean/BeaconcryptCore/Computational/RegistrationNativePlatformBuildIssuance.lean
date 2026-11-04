-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames

/-! New receipt entries in the complete source SDK build force an earlier reached first-record completion. Moved-token consumption, pin recomputation, occupancy, reservation and control commitment preserve the signing log. Later failed signing, encoding and installation retain the actual earlier source cut and final-cache anchor. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBuildIssuance
open BeaconcryptCore.Refinement
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformCompletionSdk (Completion)
variable {n : Nat} {Platform Encoded Value : Type}

abbrev history (before : State n) := before.world.world.2
abbrev cache (before : State n) := before.world.world.1.primitive.2

private def Quiet (work : StateT (State n) (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result next, (result, next) ∈ support ((work.run before).run previous) → history result.2 = history before

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := bind_pure_comp _ _

private theorem pure_state {S X : Type} (value : X) (before : S) (previous : Platform)
    (result : X × S) (next : Platform)
    (supported : (result, next) ∈ support (((pure value : StateT S (StateT Platform ProbComp) X).run before).run previous)) :
    result.2 = before ∧ next = previous := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  exact ⟨congrArg Prod.snd supported.1, supported.2⟩

private theorem early {X : Type} (value : X) (current : State n) (previous : Platform)
    (result : X × State n) (next : Platform) (old : List RegistrationSigningShared.Receipt)
    (unchanged : history current = old) (changed : history result.2 ≠ old)
    (supported : (result, next) ∈ support (((pure value : StateT (State n) (StateT Platform ProbComp) X).run current).run previous)) : False := by
  have same := (pure_state value current previous result next supported).1
  exact changed ((congrArg history same).trans unchanged)

private theorem take_history (handle : Nat) (before : State n) :
    history (RegistrationServerSdkSource.take handle before).2 = history before := by
  unfold RegistrationServerSdkSource.take
  cases before.sessions[handle]? with
  | none => rfl
  | some selected => cases selected <;> rfl

private theorem commit_frame (reply : RustM (RegistrationWorldServerCompletion.Result Encoded))
    (before : State n) (previous : Platform)
    (result : RustM (Option (U64 × Encoded)) × State n) (next : Platform)
    (supported : (result, next) ∈ support (((RegistrationNativePlatformServerSdk.commit (m := StateT Platform ProbComp) reply).run before).run previous)) :
    history result.2 = history before ∧ cache result.2 = cache before ∧ next = previous := by
  cases reply with
  | fail error | div =>
      simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, state_pure_apply,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
      have same := congrArg Prod.snd supported.1
      rw [same]
      exact ⟨rfl, rfl, supported.2⟩
  | ok answer => cases answer <;>
      simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, state_pure_apply,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported <;>
      obtain ⟨returned, platform⟩ := supported <;>
      have same := congrArg Prod.snd returned <;>
      rw [same] <;>
      exact ⟨rfl, rfl, platform⟩

private theorem fromInitial_reached
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before : State n) (previous : Platform)
    (result : RustM (Option (U64 × Encoded)) × State n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformCompletionSdk.fromInitial finish control initial).run before).run previous)) :
    ∃ reply completed,
      ((reply, completed), next) ∈ support (((finish control initial).run before.world).run previous) ∧
      history result.2 = completed.world.2 ∧ cache result.2 = completed.world.1.primitive.2 := by
  simp only [RegistrationNativePlatformCompletionSdk.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨reply, current⟩, platform⟩, reached, returned⟩ := supported
  obtain ⟨historyEq, cacheEq, platformEq⟩ := commit_frame reply current platform result next returned
  cases platformEq
  simp only [RegistrationNativePlatformServerSdk.world, StateT.run, state_map_apply, support_map] at reached
  obtain ⟨⟨⟨answer, completed⟩, platform⟩, called, equal⟩ := reached
  have stateEq := congrArg (fun value => value.1.2) equal
  have answerEq := congrArg (fun value => value.1.1) equal
  have platformEq := congrArg Prod.snd equal
  cases answerEq
  cases platformEq
  change { before with world := completed } = current at stateEq
  rw [← stateEq] at historyEq cacheEq
  exact ⟨reply, completed, called, historyEq, cacheEq⟩

structure Reached
    (pin : StateT (State n) (StateT Platform ProbComp) (RustM (Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) (StateT Platform ProbComp) Bool)
    (present : U64 → StateT (State n) (StateT Platform ProbComp) Bool)
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (handle : Nat) (application : Option (Slice U8)) (before : State n) (previous : Platform)
    (result : RustM (Option (U64 × Encoded)) × State n) (next : Platform) where
  token : peer.ConsumedRegistration
  current : State n
  plaintext : Slice U8
  pinned : session.ServerAuthenticationPin
  pinnedState : State n
  pinPlatform : Platform
  lookup : peer.CompletionLookup
  keyId : U64
  occupied : Bool
  located : State n
  lookupPlatform : Platform
  initial : registration.ServerInitialKdf
  reserved : State n
  reservePlatform : Platform
  reply : RustM (RegistrationWorldServerCompletion.Result Encoded)
  completed : Local n
  tokenTaken : RegistrationServerSdkSource.take handle before = (some token, current)
  applicationSome : application = some plaintext
  pinCalled : ((.ok (some pinned), pinnedState), pinPlatform) ∈ support ((pin.run current).run previous)
  lookupStarted : peer.begin_completion_lookup current.control pinned token plaintext = .ok (.Ok lookup)
  keyRequested : lookup.request = .ok keyId
  preflight : RegistrationServerSdkSource.preflight plaintext keyId = true
  occupancyCalled : ((occupied, located), lookupPlatform) ∈ support (((present keyId).run pinnedState).run pinPlatform)
  occupancyResumed : lookup.resume occupied = .ok (.Ok initial)
  reserveCalled : ((true, reserved), reservePlatform) ∈ support ((reserve.run located).run lookupPlatform)
  finishCalled : ((reply, completed), next) ∈ support (((finish current.control initial).run reserved.world).run reservePlatform)
  historyBefore : reserved.world.world.2 = history before
  historyAfter : completed.world.2 = history result.2
  cacheAfter : completed.world.1.primitive.2 = cache result.2

private theorem reached
    (pin : StateT (State n) (StateT Platform ProbComp) (RustM (Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) (StateT Platform ProbComp) Bool)
    (present : U64 → StateT (State n) (StateT Platform ProbComp) Bool)
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (pinQuiet : Quiet pin) (reserveQuiet : Quiet reserve) (presentQuiet : ∀ keyId, Quiet (present keyId))
    (handle : Nat) (application : Option (Slice U8)) (before : State n) (previous : Platform)
    (result : RustM (Option (U64 × Encoded)) × State n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application).run before).run previous))
    (changed : history result.2 ≠ history before) :
    Nonempty (Reached pin reserve present finish handle application before previous result next) := by
  have retained := take_history handle before
  simp only [RegistrationNativePlatformCompletionSdk.build, StateT.run] at supported
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk selected current =>
      rw [taken] at supported retained
      cases selected with
      | none => exact False.elim (early _ current previous result next (history before) retained changed supported)
      | some token =>
          cases application with
          | none => exact False.elim (early _ current previous result next (history before) retained changed supported)
          | some plaintext =>
              change (result, next) ∈ support
                (((RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token plaintext).run current).run previous) at supported
              simp only [RegistrationNativePlatformCompletionSdk.complete, StateT.run_bind, StateT.run_get, pure_bind] at supported
              rw [mem_support_bind_iff] at supported
              obtain ⟨⟨⟨pinReply, pinnedState⟩, pinPlatform⟩, pinCalled, continued⟩ := supported
              have pinnedSame := (pinQuiet current previous (pinReply, pinnedState) pinPlatform pinCalled).trans retained
              cases pinReply with
              | fail error | div => exact False.elim (early _ pinnedState pinPlatform result next _ pinnedSame changed continued)
              | ok optional => cases optional with
                | none => exact False.elim (early _ pinnedState pinPlatform result next _ pinnedSame changed continued)
                | some pinned =>
                    unfold RegistrationNativePlatformCompletionSdk.afterPin at continued
                    dsimp only at continued
                    cases started : peer.begin_completion_lookup current.control pinned token plaintext with
                    | fail error | div =>
                        rw [started] at continued
                        exact False.elim (early _ pinnedState pinPlatform result next _ pinnedSame changed continued)
                    | ok answer => cases answer with
                      | Err prior =>
                          rw [started] at continued
                          exact False.elim (early _ pinnedState pinPlatform result next _ pinnedSame changed continued)
                      | Ok lookup =>
                          rw [started] at continued
                          dsimp only at continued
                          cases requested : lookup.request with
                          | fail error | div =>
                              rw [requested] at continued
                              exact False.elim (early _ pinnedState pinPlatform result next _ pinnedSame changed continued)
                          | ok keyId =>
                              rw [requested] at continued
                              dsimp only at continued
                              split at continued
                              next preflight =>
                                simp only [StateT.run_bind, mem_support_bind_iff] at continued
                                obtain ⟨⟨⟨occupied, located⟩, lookupPlatform⟩, occupancyCalled, continued⟩ := continued
                                have locatedSame := (presentQuiet keyId pinnedState pinPlatform (occupied, located) lookupPlatform occupancyCalled).trans pinnedSame
                                unfold RegistrationNativePlatformCompletionSdk.afterOccupancy at continued
                                dsimp only at continued
                                cases resumed : lookup.resume occupied with
                                | fail error | div =>
                                    rw [resumed] at continued
                                    exact False.elim (early _ located lookupPlatform result next _ locatedSame changed continued)
                                | ok answer => cases answer with
                                  | Err prior =>
                                      rw [resumed] at continued
                                      exact False.elim (early _ located lookupPlatform result next _ locatedSame changed continued)
                                  | Ok initial =>
                                      rw [resumed] at continued
                                      dsimp only at continued
                                      simp only [StateT.run_bind, mem_support_bind_iff] at continued
                                      obtain ⟨⟨⟨admitted, reserved⟩, reservePlatform⟩, reserveCalled, continued⟩ := continued
                                      have reservedSame := (reserveQuiet located lookupPlatform (admitted, reserved) reservePlatform reserveCalled).trans locatedSame
                                      cases admitted with
                                      | false => exact False.elim (early _ reserved reservePlatform result next _ reservedSame changed continued)
                                      | true =>
                                          obtain ⟨reply, completed, finishCalled, historyEq, cacheEq⟩ :=
                                            fromInitial_reached finish current.control initial reserved reservePlatform result next continued
                                          exact ⟨⟨token, current, plaintext, pinned, pinnedState, pinPlatform, lookup, keyId,
                                            occupied, located, lookupPlatform, initial, reserved, reservePlatform, reply, completed,
                                            taken, rfl, pinCalled, started, requested, preflight, occupancyCalled, resumed,
                                            reserveCalled, finishCalled, reservedSame, historyEq.symm, cacheEq.symm⟩⟩
                              next rejected => exact False.elim (early _ pinnedState pinPlatform result next _ pinnedSame changed continued)

private theorem pin_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp)) :
    Quiet (RegistrationNativePlatformSourceBuild.pin (n := n) coins) := by
  intro before previous result next supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, state_map_apply, support_map] at supported
  obtain ⟨inner, _hashed, equal⟩ := supported
  have same := congrArg (fun value => history value.1.2) equal
  exact same.symm

private theorem reserve_quiet (reservation : StateT Platform ProbComp Bool) :
    Quiet (n := n) (StateT.lift reservation) := by
  intro before previous result next supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _reserved, equal⟩ := supported
  have same := congrArg (fun value => history value.1.2) equal
  exact same.symm

private theorem capability_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (query : PqxdhRecordLiftInterface.Capability n) (before : Local n) (previous : Platform)
    (result : (PqxdhRecordLiftInterface.CapabilitySpec n).Range query × Local n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformServerCompletion.capability coins query).run before).run previous)) :
    result.2.world.2 = before.world.2 := by
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
  obtain ⟨inner, _queried, equal⟩ := actual
  have same := congrArg (fun value => value.2.world.2) equal
  exact same.symm

private theorem present_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (keyId : U64) :
    Quiet (RegistrationNativePlatformCompletionSdk.nativePresent (n := n) coins keyId) := by
  intro before previous result next supported
  simp only [RegistrationNativePlatformCompletionSdk.nativePresent,
    RegistrationNativePlatformServerSdk.world, StateT.run, state_map_apply, support_map] at supported
  obtain ⟨⟨inner, platform⟩, called, equal⟩ := supported
  have same := congrArg (fun value => history value.1.2) equal
  rw [← same]
  exact capability_quiet coins (.peerPresent keyId) before.world previous inner platform called

variable {E ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : AdapterSealPrimitive.Operations]
open PqxdhServerAuthExperiment (Setup Codec)

/-- Every complete source build which adds a signing receipt has an earlier actual successful source first-record cut, anchored at the actual final cache even after later failure. -/
theorem source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before : State n) (previous : Platform)
    (result : RustM (Option (U64 × alloc.vec.Vec U8)) × State n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer sign helper writer
        handle application).run before).run previous))
    (changed : history result.2 ≠ history before) :
    ∃ cut : Reached (RegistrationNativePlatformSourceBuild.pin coins) (StateT.lift reservePeer)
      (RegistrationNativePlatformCompletionSdk.nativePresent coins)
      (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer)
      handle application before previous result next,
    ∃ hashed current platform,
      ((.ok (.Ok hashed), current), platform) ∈ support
        (((RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper cut.initial).run cut.reserved.world).run cut.reservePlatform) ∧
      RegistrationServerRecordExecutor.Path cut.initial hashed ∧
      current.world.1.primitive.2 ≤ cache result.2 ∧
      ((cut.reply, cut.completed), next) ∈ support
        (((RegistrationNativePlatformSourceBuildCut.afterRecord coins sign writer cut.current.control hashed).run current).run platform) := by
  obtain ⟨cut⟩ := reached (RegistrationNativePlatformSourceBuild.pin coins) (StateT.lift reservePeer)
    (RegistrationNativePlatformCompletionSdk.nativePresent coins)
    (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer)
    (pin_quiet coins) (reserve_quiet reservePeer) (present_quiet coins)
    handle application before previous result next supported changed
  have changedLocal : cut.completed.world.2 ≠ cut.reserved.world.world.2 := by
    intro same
    exact changed ((cut.historyAfter.symm.trans same).trans cut.historyBefore)
  obtain ⟨hashed, current, platform, called, path, cached, continued⟩ := RegistrationNativePlatformSourceFrames.new_receipts
    coins setup codec view failure allocation erased sign helper writer cut.current.control cut.initial
    cut.reserved.world cut.reservePlatform (cut.reply, cut.completed) next cut.finishCalled changedLocal
  rw [cut.cacheAfter] at cached
  exact ⟨cut, hashed, current, platform, called, path, cached, continued⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformBuildIssuance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildIssuance.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildIssuance.source
