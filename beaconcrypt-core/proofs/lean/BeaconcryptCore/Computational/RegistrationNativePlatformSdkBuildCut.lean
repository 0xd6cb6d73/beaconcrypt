-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk

/-! A successful adaptive SDK build supplies its literal moved token, recomputed pin, lookup, public occupancy, reservation and local completion cuts. Every prefix uses its actual shared native/platform poststate. No completion or installation conclusion is a premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildCut
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformCompletionSdk (AdHash Completion)
variable {n : Nat} {Platform Encoded : Type}

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := bind_pure_comp _ _

structure Cut
    (deriveAd : AdHash n (StateT Platform ProbComp))
    (pin : StateT (State n) (StateT Platform ProbComp) (RustM (Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) (StateT Platform ProbComp) Bool)
    (present : U64 → StateT (State n) (StateT Platform ProbComp) Bool)
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (handle : Nat) (application : Option (Slice U8)) (assigned : U64) (encoded : Encoded)
    (before after : State n) (previous next : Platform) where
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
  pendingAd : registration.ServerAdHash
  hashed : State n
  hashPlatform : Platform
  initial : registration.ServerInitialKdf
  reserved : State n
  reservePlatform : Platform
  published : peer.PublishedPeer Encoded
  completed : Local n
  tokenTaken : RegistrationServerSdkSource.take handle before = (some token, current)
  applicationSome : application = some plaintext
  pinCalled : ((.ok (some pinned), pinnedState), pinPlatform) ∈ support ((pin.run current).run previous)
  lookupStarted : peer.begin_completion_lookup current.control pinned token plaintext = .ok (.Ok lookup)
  keyRequested : lookup.request = .ok keyId
  preflight : RegistrationServerSdkSource.preflight plaintext keyId = true
  occupancyCalled : ((occupied, located), lookupPlatform) ∈ support (((present keyId).run pinnedState).run pinPlatform)
  occupancyResumed : lookup.resume occupied = .ok (.Ok pendingAd)
  adHashCalled : ((.ok (.Ok initial), hashed), hashPlatform) ∈ support (((deriveAd pendingAd).run located).run lookupPlatform)
  reserveCalled : ((true, reserved), reservePlatform) ∈ support ((reserve.run hashed).run hashPlatform)
  finishCalled : ((.ok (.Ok published), completed), next) ∈ support (((finish current.control initial).run reserved.world).run reservePlatform)
  assignedExact : published.key_id = assigned
  encodedExact : published.encoded = encoded
  afterExact : after = { reserved with world := completed, control := published.control }

private theorem fromInitial_cut
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (assigned : U64) (encoded : Encoded) (before after : State n) (previous next : Platform)
    (supported : ((.ok (some (assigned, encoded)), after), next) ∈ support
      (((RegistrationNativePlatformCompletionSdk.fromInitial finish control initial).run before).run previous)) :
    ∃ published completed,
      ((.ok (.Ok published), completed), next) ∈ support (((finish control initial).run before.world).run previous) ∧
      published.key_id = assigned ∧ published.encoded = encoded ∧
      after = { before with world := completed, control := published.control } := by
  simp only [RegistrationNativePlatformCompletionSdk.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨reply, current⟩, platform⟩, reached, returned⟩ := supported
  cases reply with
  | fail error | div => simp [RegistrationNativePlatformServerSdk.commit, StateT.run, state_pure_apply] at returned
  | ok result => cases result with
    | Err prior => simp [RegistrationNativePlatformServerSdk.commit, StateT.run, state_pure_apply] at returned
    | Ok published =>
        simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, state_pure_apply, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at returned
        obtain ⟨⟨⟨assignedEq, encodedEq⟩, stateEq⟩, platformEq⟩ := returned
        cases platformEq
        simp only [RegistrationNativePlatformServerSdk.world, StateT.run, state_map_apply, support_map] at reached
        obtain ⟨⟨⟨answer, completed⟩, platform⟩, called, equal⟩ := reached
        obtain ⟨nativeEq, platformEq⟩ := Prod.mk.inj equal
        obtain ⟨answerEq, currentEq⟩ := Prod.mk.inj nativeEq
        cases answerEq
        cases platformEq
        cases currentEq
        exact ⟨published, completed, called, assignedEq.symm, encodedEq.symm, stateEq⟩

/-- Literal success of the complete SDK build supplies every actual reached source prefix and completion call. -/
theorem build
    (deriveAd : AdHash n (StateT Platform ProbComp))
    (pin : StateT (State n) (StateT Platform ProbComp) (RustM (Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) (StateT Platform ProbComp) Bool)
    (present : U64 → StateT (State n) (StateT Platform ProbComp) Bool)
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (handle : Nat) (application : Option (Slice U8)) (assigned : U64) (encoded : Encoded)
    (before after : State n) (previous next : Platform)
    (supported : ((.ok (some (assigned, encoded)), after), next) ∈ support
      (((RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application).run before).run previous)) :
    Nonempty (Cut deriveAd pin reserve present finish handle application assigned encoded before after previous next) := by
  simp only [RegistrationNativePlatformCompletionSdk.build, StateT.run] at supported
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk selected current =>
      rw [taken] at supported
      cases selected with
      | none => simp [state_pure_apply] at supported
      | some token =>
          cases application with
          | none => simp [state_pure_apply] at supported
          | some plaintext =>
              change ((.ok (some (assigned, encoded)), after), next) ∈ support
                (((RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token plaintext).run current).run previous) at supported
              simp only [RegistrationNativePlatformCompletionSdk.complete, StateT.run_bind, StateT.run_get,
                pure_bind] at supported
              rw [mem_support_bind_iff] at supported
              obtain ⟨⟨⟨pinReply, pinnedState⟩, pinPlatform⟩, pinCalled, continued⟩ := supported
              cases pinReply with
              | fail error | div => simp [RegistrationNativePlatformCompletionSdk.afterPin, StateT.run_pure] at continued
              | ok optional => cases optional with
                | none => simp [RegistrationNativePlatformCompletionSdk.afterPin, StateT.run_pure] at continued
                | some pinned =>
                    unfold RegistrationNativePlatformCompletionSdk.afterPin at continued
                    dsimp only at continued
                    cases started : peer.begin_completion_lookup current.control pinned token plaintext with
                    | fail error | div => simp [started, StateT.run_pure] at continued
                    | ok result => cases result with
                      | Err prior => simp [started, StateT.run_pure] at continued
                      | Ok lookup =>
                          rw [started] at continued
                          dsimp only at continued
                          cases requested : lookup.request with
                          | fail error | div => simp [requested, StateT.run_pure] at continued
                          | ok keyId =>
                              rw [requested] at continued
                              dsimp only at continued
                              split at continued
                              next preflight =>
                                simp only [StateT.run_bind, mem_support_bind_iff] at continued
                                obtain ⟨⟨⟨occupied, located⟩, lookupPlatform⟩, occupancyCalled, continued⟩ := continued
                                unfold RegistrationNativePlatformCompletionSdk.afterOccupancy at continued
                                dsimp only at continued
                                cases resumed : lookup.resume occupied with
                                | fail error | div => simp [resumed, StateT.run_pure] at continued
                                | ok result => cases result with
                                  | Err prior => simp [resumed, StateT.run_pure] at continued
                                  | Ok pendingAd =>
                                      rw [resumed] at continued
                                      dsimp only at continued
                                      simp only [StateT.run_bind, mem_support_bind_iff] at continued
                                      obtain ⟨⟨⟨hashReply, hashed⟩, hashPlatform⟩, hashCalled, continued⟩ := continued
                                      cases hashReply with
                                      | fail error | div => simp [StateT.run_pure] at continued
                                      | ok result => cases result with
                                        | Err prior => simp [StateT.run_pure] at continued
                                        | Ok initial =>
                                          simp only [StateT.run_bind, mem_support_bind_iff] at continued
                                          obtain ⟨⟨⟨admitted, reserved⟩, reservePlatform⟩, reserveCalled, continued⟩ := continued
                                          cases admitted with
                                          | false => simp [StateT.run_pure] at continued
                                          | true =>
                                              obtain ⟨published, completed, finishCalled, assignedEq, encodedEq, stateEq⟩ :=
                                                fromInitial_cut finish current.control initial assigned encoded reserved after reservePlatform next continued
                                              exact ⟨⟨token, current, plaintext, pinned, pinnedState, pinPlatform, lookup, keyId,
                                                occupied, located, lookupPlatform, pendingAd, hashed, hashPlatform,
                                                initial, reserved, reservePlatform, published, completed,
                                                taken, rfl, pinCalled, started, requested, preflight, occupancyCalled, resumed, hashCalled,
                                                reserveCalled, finishCalled, assignedEq, encodedEq, stateEq⟩⟩
                              next rejected => simp [StateT.run_pure] at continued

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildCut.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildCut.build
