-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque
/-! The same genuine KEM profile, candidate and private tables can precede the actual complete World startup. This distribution law retains the complete original record event and persistent platform result. Reduction-owned independent draws on startup failure are discarded only by their proved lossless law; no source counter equality is inferred from that reordering. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueGame
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)


noncomputable def draws (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) := do
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ PqxdhKemIndCca.MlKemSharedSecret
  let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
  pure (profile,candidate,materials)

noncomputable def game (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ProbComp (Bool × Platform) := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let _unused ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
  let sample ← draws setup budget selected
  RegistrationNativePlatformG3UniformOpaqueNative.actual setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val sample.1.pairs sample.1.publicKey sample.1.challenge sample.2.1) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar sample.2.1 sample.2.2 previous ensureInit identityIndex

/-- Independent private draws can be ordered before the genuine World startup without changing the original complete event or persistent platform result. -/
theorem game_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) :
    RegistrationNativePlatformG3UniformOpaque.hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous =ᵈ
      game setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous := by
  unfold RegistrationNativePlatformG3UniformOpaque.hidden RegistrationNativePlatformG3UniformOpaque.warmPrior
    RegistrationNativePlatformPublicRecordOpaqueInitialized.prior game
  simp only [bind_assoc,pure_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  apply _root_.EvalDistEq.bind_right
  intro unused
  let start := (RegistrationNativePublicStartupFrame.startup (n := budget.cap 4 + budget.cap 5) setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed)).run PqxdhRecordLiftWorld.initial
  let nextWork := fun (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
      (sample : RegistrationNativeSecretWordAliasOuter.Profile KemSK × PqxdhKemIndCca.MlKemSharedSecret × RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) =>
    RegistrationNativePlatformG3UniformOpaqueAfter.hidden setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val sample.1.pairs sample.1.publicKey sample.1.challenge sample.2.1) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar sample.2.1 sample.2.2 previous initialized
  have normalized :
      (start >>= fun initialized => do
        let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
        let candidate ← $ᵗ PqxdhKemIndCca.MlKemSharedSecret
        RegistrationNativePlatformG3UniformOpaque.hiddenAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
          budget selected previous ((seed,scalar,unused,initialized),profile,candidate)) =ᵈ
        (start >>= fun initialized => draws setup budget selected >>= nextWork initialized) := by
    apply _root_.EvalDistEq.bind_right
    intro initialized
    unfold draws
    simp only [bind_assoc,pure_bind]
    apply _root_.EvalDistEq.bind_right
    intro profile
    apply _root_.EvalDistEq.bind_right
    intro candidate
    cases success : initialized.1 with
    | none =>
      simpa only [RegistrationNativePlatformG3UniformOpaque.hiddenAt,nextWork,RegistrationNativePlatformG3UniformOpaqueAfter.hidden,success] using
        (OracleComp.EvalDistEq.bind_const ($ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5))
          (pure (false,previous) : ProbComp (Bool × Platform))).symm
    | some started =>
      simp only [RegistrationNativePlatformG3UniformOpaque.hiddenAt,nextWork,success]
      exact .rfl
  have switched := OracleComp.EvalDistEq.bind_bind_swap start (draws setup budget selected) nextWork
  refine normalized.trans (switched.trans ?_)
  apply _root_.EvalDistEq.bind_right
  intro sample
  have fixed := RegistrationNativePlatformG3UniformOpaqueNative.after_source setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val sample.1.pairs sample.1.publicKey sample.1.challenge sample.2.1) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar sample.2.1 sample.2.2 previous ensureInit identityIndex
  simpa only [RegistrationNativePlatformG3UniformOpaqueNative.after,start,nextWork] using (show _ =ᵈ _ from fixed ▸ _root_.EvalDistEq.rfl)
end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueGame.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueGame.game_source
