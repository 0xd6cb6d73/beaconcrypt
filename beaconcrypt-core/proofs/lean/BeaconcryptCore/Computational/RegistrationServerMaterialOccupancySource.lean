-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialAdmittedSource

/-! Actual current-pin/occupancy and peer-reservation decisions precede material demand. Private root restoration changes only the source initializer's consumed KDF input; the public gate and every refusal are the native ones. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationPublicationKernelErasure (mapOk)
open RegistrationServerMaterialSourceState (State close project restore nativeView service)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

private theorem rust_map_eq {Input Output : Type} (f : Input → Output) (action : RustM Input) :
    f <$> action = (match (generalizing := false) action with
      | .fail error => .fail error
      | .div => .div
      | .ok value => .ok (f value)) := by
  cases action <;> rfl

noncomputable def continuation (wire : RegistrationNativeWire.Wire) (reserve : Bool) (control : pqxdh.ServerState)
    (message : RegistrationNativeRelatedFamily.Message) :
    RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState) →
      StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n))
        RegistrationServerMaterialFrontend.Result
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok initial) =>
      if reserve then RegistrationServerMaterialAdmittedSource.admitted wire control initial message
      else pure (.ok none)

noncomputable def hashThen (wire : RegistrationNativeWire.Wire) (reserve : Bool) (control : pqxdh.ServerState)
    (message : RegistrationNativeRelatedFamily.Message) (pending : registration.ServerAdHash) :
    StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n))
      RegistrationServerMaterialFrontend.Result := do
  let hashedPublic ← StateT.lift
    ((fun result => mapOk RegistrationBoundKeySchedule.publicInitial <$> result) <$>
      RegistrationServerMaterialFrontend.adHash (n := n) pending)
  continuation wire reserve control message hashedPublic

noncomputable def after (wire : RegistrationNativeWire.Wire) (reserve : Bool) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (message : RegistrationNativeRelatedFamily.Message) (occupied : Bool) :
    StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n))
      RegistrationServerMaterialFrontend.Result :=
  match lookup.resume occupied with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok pending) => hashThen (n := n) wire reserve control message pending

private theorem restore_public_ad (pending : registration.ServerAdHash) :
    RegistrationBoundKeySchedule.restoreAd (RegistrationBoundKeySchedule.publicAd pending)
      (RegistrationBoundSource.rootValue pending.root.bytes) = pending := by
  cases pending with
  | mk candidate binding root application input =>
      cases root
      simp only [RegistrationBoundKeySchedule.restoreAd, RegistrationBoundKeySchedule.publicAd,
        RegistrationBoundSource.root_value_array]

private theorem ad_hash_public (left right : registration.ServerAdHash)
    (same : RegistrationBoundKeySchedule.publicAd left = RegistrationBoundKeySchedule.publicAd right) :
    (fun result => mapOk RegistrationBoundKeySchedule.publicInitial <$> result) <$>
        RegistrationServerMaterialFrontend.adHash (n := n) left =
      (fun result => mapOk RegistrationBoundKeySchedule.publicInitial <$> result) <$>
        RegistrationServerMaterialFrontend.adHash right := by
  have requested : left.request = right.request := by
    have inputs := congrArg RegistrationBoundKeySchedule.PublicAd.input same
    change left.input = right.input at inputs
    simp only [registration.ServerAdHash.request, inputs]
  unfold RegistrationServerMaterialFrontend.adHash
  rw [requested]
  cases right.request with
  | fail error | div => rfl
  | ok request =>
      simp only [map_bind, map_pure]
      apply bind_congr
      intro digest
      apply congrArg pure
      have leftRun := RegistrationBoundGate.ad_resume_public_root
        (RegistrationBoundKeySchedule.publicAd left) (RegistrationBoundSource.rootValue left.root.bytes)
        (.Some (RegistrationAuthenticationShared.digestArray digest))
      have rightRun := RegistrationBoundGate.ad_resume_public_root
        (RegistrationBoundKeySchedule.publicAd right) (RegistrationBoundSource.rootValue right.root.bytes)
        (.Some (RegistrationAuthenticationShared.digestArray digest))
      rw [restore_public_ad left] at leftRun
      rw [restore_public_ad right] at rightRun
      rw [same] at leftRun
      exact leftRun.trans rightRun.symm

private theorem hash_source (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (pending : registration.ServerAdHash) :
    simulateQ (service hkdf writer sign roots) (RegistrationServerMaterialFrontend.adHash (n := n) pending) =
      RegistrationWorldServerCompletion.adHash pending := by
  unfold RegistrationServerMaterialFrontend.adHash RegistrationWorldServerCompletion.adHash
  cases pending.request with
  | fail error | div => simp only [simulateQ_pure]
  | ok request =>
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, RegistrationServerMaterialFrontend.effect,
        service, RegistrationServerKnownStageWorldSource.common]
      rfl

private theorem bind_apply {S A B : Type} (work : StateT S ProbComp A)
    (next : A → StateT S ProbComp B) (before : S) :
    (work >>= next) before = (do let reached ← work before; next reached.1 reached.2) := rfl

private theorem pure_apply {S A : Type} (value : A) (before : S) :
    (pure value : StateT S ProbComp A) before = pure (value, before) := rfl

private theorem result (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (control : pqxdh.ServerState)
    (message : RegistrationNativeRelatedFamily.Message)
    (action : RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState))
    (role : ∀ initial, action = .ok (.Ok initial) → initial.pending =
      PqxdhInitialRatchetComplementarity.serverPending (PqxdhRootTableInitialization.rootArray (roots message)))
    (before : State n) :
    Prod.map id (project roots) <$>
      (close setup.source wire.frameWrite sign roots
        (continuation wire checks.reservePeer control message
          (mapOk RegistrationBoundKeySchedule.publicInitial <$> action))).run before =
      Prod.map id nativeView <$>
        ((match (generalizing := false) action with
        | .fail error => pure (.fail error)
        | .div => pure .div
        | .ok (.Err _) => pure (.ok none)
        | .ok (.Ok initial) =>
            if checks.reservePeer then RegistrationServerSdkSource.fromInitial setup
              (RegistrationNativeWire.ledgerCodec wire) sign wire.encodeResponse control initial
            else pure (.ok none)) : StateT (RegistrationServerFrontendCompiler.State n) ProbComp
              RegistrationServerMaterialFrontend.Result).run (restore roots before) := by
  cases action with
  | fail error | div =>
      simp only [rust_map_eq, continuation, RegistrationServerMaterialSourceLift.pure_run, map_pure]
      rfl
  | ok answer => cases answer with
    | Err previous =>
        simp only [rust_map_eq, mapOk, continuation, RegistrationServerMaterialSourceLift.pure_run, map_pure]
        rfl
    | Ok initial =>
        simp only [rust_map_eq, mapOk, continuation]
        by_cases reserved : checks.reservePeer = true
        · simp only [reserved, ite_true]
          exact RegistrationServerMaterialAdmittedSource.native setup wire sign roots control initial message
            (role initial rfl) before
        · have refused : checks.reservePeer = false := Bool.eq_false_iff.mpr reserved
          simp only [refused, Bool.false_eq_true, ite_false, RegistrationServerMaterialSourceLift.pure_run, map_pure]
          rfl

/-- The actual native lookup supplies the public gate and root-role receipt needed by the real material service; failed reservation reaches no service. -/
theorem native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (message : RegistrationNativeRelatedFamily.Message)
    (occupied : Bool) (before : State n) :
    Prod.map id (project roots) <$>
      (close setup.source wire.frameWrite sign roots (after wire checks.reservePeer control lookup message occupied)).run before =
      Prod.map id nativeView <$>
        (RegistrationServerSdkSource.afterOccupancy setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse
          control (RegistrationServerReferenceSourceLookup.withRoot lookup (roots message)) occupied).run (restore roots before) := by
  have publicEq := RegistrationServerReferenceSourceLookup.resume_public lookup (roots message) occupied
  unfold after RegistrationServerSdkSource.afterOccupancy
  cases selectedRun : lookup.resume occupied with
  | fail error | div =>
      simp only [selectedRun, rust_map_eq] at publicEq
      cases actual : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots message)).resume occupied <;>
        simp_all only [reduceCtorEq, RustM.fail.injEq]
      all_goals simp only [RegistrationServerMaterialSourceLift.pure_run, map_pure]; rfl
  | ok selectedResult => cases selectedResult with
    | Err previous =>
      cases actual : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots message)).resume occupied with
      | fail error | div => simp [actual, selectedRun, rust_map_eq] at publicEq
      | ok answer => cases answer with
        | Ok pending => simp [actual, selectedRun, rust_map_eq, mapOk] at publicEq
        | Err previous => simp only [RegistrationServerMaterialSourceLift.pure_run, map_pure]; rfl
    | Ok pending =>
      cases actual : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots message)).resume occupied with
      | fail error | div => simp [actual, selectedRun, rust_map_eq] at publicEq
      | ok answer => cases answer with
        | Err previous => simp [actual, selectedRun, rust_map_eq, mapOk] at publicEq
        | Ok restored =>
          have same : RegistrationBoundKeySchedule.publicAd pending = RegistrationBoundKeySchedule.publicAd restored := by
            simpa only [selectedRun, actual, RawCtxMaterialInterpretation.rust_map_ok, mapOk,
              RustM.ok.injEq, core.result.Result.Ok.injEq] using publicEq.symm
          dsimp only
          unfold hashThen
          rw [ad_hash_public pending restored same]
          rw [RegistrationServerMaterialSourceLift.bind_run, RegistrationServerMaterialSourceLift.lift_run]
          simp only [simulateQ_map, hash_source, StateT.run_map, Functor.map_map, map_bind, bind_map_left]
          unfold RegistrationServerSdkSource.adHash RegistrationWorldServerCompletion.adHash
          cases requested : restored.request with
          | fail error | div =>
            simp only [StateT.run, bind_apply, pure_apply, pure_bind,
              RegistrationServerSdkSource.world, map_pure]
            exact result setup checks wire sign roots control message _
              (by intro initial impossible; cases impossible) before
          | ok request =>
            simp only [StateT.run, bind_apply, pure_apply, pure_bind, bind_assoc,
              RegistrationServerSdkSource.world, map_bind, bind_map_left]

            apply bind_congr
            rintro ⟨digest, current⟩
            apply result setup checks wire sign roots control message _ ?_
              (before.1, current)
            intro initial resumed
            exact RegistrationServerReferenceSourceLookup.resume_role lookup (roots message) occupied restored
              (RegistrationAuthenticationShared.digestArray digest) initial actual resumed

end BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource.native
