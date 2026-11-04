-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountNative

/-! The actual reified Init program retains its complete signing history, mutable owner/Env state and optional failures under free ML count normalization. Primitive requests and replies remain literal; only explicitly named private accounting coordinates are projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaShared (Local)
open RegistrationNativeMldsaCountLower (localProject)
open RegistrationNativeMldsaCountRules (Correct)
open RegistrationNativeMldsaCountMap (transform)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private def nativeLens (work : StateT (RegistrationNativeExperiment.State n KemSK source) (OracleComp (Spec source)) Value) :
    StateT (Local n KemSK source) (OracleComp (Spec source)) Value := fun before =>
  (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$> work.run before.2.2

private theorem nativeLens_correct
    (work : StateT (RegistrationNativeExperiment.State n KemSK source) (OracleComp (Spec source)) Value)
    (good : Correct RegistrationNativeMldsaMainView.project work) : Correct localProject (nativeLens work) := by
  constructor
  · intro before
    have same := congrArg (fun computation => (fun result =>
      (result.1, (before.1, (RegistrationNativeBeaconEnvView.erase before.2.1, result.2)))) <$> computation) (good.1 before.2.2)
    simp only [nativeLens, StateT.run, Functor.map_map, Prod.map, id_eq, localProject] at same ⊢
    exact same
  · intro before
    have same := congrArg (fun computation => (fun result =>
      (result.1, (before.1, (RegistrationNativeBeaconEnvView.erase before.2.1, result.2)))) <$> computation) (good.2 before.2.2)
    simp only [nativeLens, StateT.run, transform, simulateQ_map, Functor.map_map, Prod.map, id_eq, localProject] at same ⊢
    exact same

private def append (receipt : RegistrationSigningShared.Receipt) :
    StateT (Local n KemSK source) (OracleComp (Spec source)) Unit :=
  modify fun before => (before.1, ({ before.2.1 with receipts := before.2.1.receipts ++ [receipt] }, before.2.2))

private theorem append_correct (receipt : RegistrationSigningShared.Receipt) :
    Correct (localProject (n := n) (KemSK := KemSK) (source := source)) (append receipt) := by
  constructor <;> intro before <;>
    simp only [append, StateT.run_modify, transform, simulateQ_pure, map_pure, Prod.map, id_eq,
      localProject, RegistrationNativeBeaconEnvView.erase, RegistrationNativeMldsaMainView.idempotent]

private theorem outgoing_sign (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) :
    RegistrationNativeMldsaBundle.outgoing (n := n) setup checks representation created index owner (.inl (.sign request payload digest)) = (do
      let reply ← nativeLens (RegistrationNativeMldsaCreation.world (RegistrationNativeMldsaProgram.call .environment (.sign owner.mldsa request)))
      append ⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes reply⟩, digest⟩
      pure reply) := by
  funext before
  simp only [RegistrationNativeMldsaBundle.outgoing, nativeLens, RegistrationNativeMldsaCreation.world,
    append, StateT.run, StateT.monad_bind_def, StateT.bind,
    Functor.map_map, bind_map_left, bind_pure_comp]
  rfl

/-- Every actual outgoing Init callback has both count-normalized and original free continuation laws for all optional signing replies. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Correct (localProject (n := n)) (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request =>
        exact RegistrationNativeMldsaCountLower.native setup checks representation created _
          (RegistrationNativeBeaconEnvBundle.outgoing_stable setup index owner _)
    | sign request payload digest =>
        rw [outgoing_sign]
        apply RegistrationNativeMldsaCountRules.bind localProject _ _
          (nativeLens_correct _ (RegistrationNativeMldsaCountNative.call .environment (.sign owner.mldsa request)))
        intro reply
        exact RegistrationNativeMldsaCountRules.bind localProject _ _ (append_correct _)
          (fun _ => RegistrationNativeMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent reply)
  | inr request =>
      exact RegistrationNativeMldsaCountLower.native setup checks representation created _
        (RegistrationNativeBeaconEnvBundle.outgoing_stable setup index owner _)

private theorem afterPublished (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Correct (localProject (n := n))
      (RegistrationNativeMldsaBundle.afterPublished setup checks representation created index owner oneTime published) := by
  cases published with
  | fail error | div => exact RegistrationNativeMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
    | Ok completed =>
        exact RegistrationNativeMldsaCountRules.bind localProject _ _
          (RegistrationNativeMldsaCountLower.native setup checks representation created _
            (RegistrationNativeBeaconEnvCallbacks.phase_stable index (.initSent completed.pending oneTime)))
          (fun _ => RegistrationNativeMldsaCountRules.bind localProject _ _
            (RegistrationNativeMldsaCountLower.native setup checks representation created _
              (RegistrationNativeBeaconEnvCallbacks.effect_stable _))
            (fun _ => RegistrationNativeMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _))

/-- The whole actual free Init bundle preserves optional publication and consumed-owner behavior when named ML private counts are normalized. -/
theorem bundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) :
    Correct (localProject (n := n) (source := source))
      (RegistrationNativeMldsaBundle.bundle setup checks wire representation created index) := by
  unfold RegistrationNativeMldsaBundle.bundle
  apply RegistrationNativeMldsaCountRules.bind localProject _ _
    (RegistrationNativeMldsaCountLower.native setup checks representation created _ RegistrationNativeBeaconEnvView.get_stable)
  intro owners
  cases found : owners[index]? with
  | none => exact RegistrationNativeMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
  | some owner =>
      have continuation (oneTime : PqxdhJointGapDh.ScalarBytes) :
          Correct (localProject (n := n)) (do
            let published ← simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner)
              (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
                (RegistrationNativeBeaconFrontend.inputs setup owner)
                ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
            RegistrationNativeMldsaBundle.afterPublished setup checks representation created index owner oneTime published) :=
        RegistrationNativeMldsaCountRules.bind localProject _ _
          (RegistrationNativeMldsaCountRules.simulate localProject RegistrationNativeMldsaCountLower.idempotent _
            (outgoing setup checks representation created index owner) _)
          (afterPublished setup checks representation created index owner oneTime)
      cases phase : owner.phase <;> simp only [phase]
      all_goals first
        | exact RegistrationNativeMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
        | exact RegistrationNativeMldsaCountRules.bind localProject _ _
            (RegistrationNativeMldsaCountLower.native setup checks representation created _
              (RegistrationNativeBeaconEnvCallbacks.sample_stable _)) continuation
        | exact RegistrationNativeMldsaCountRules.bind localProject _ _
            (RegistrationNativeMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _) continuation

private def openState (before : RegistrationNativeExperiment.State n KemSK source) : Local n KemSK source :=
  (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))

private theorem open_project (before : RegistrationNativeExperiment.State n KemSK source) :
    localProject (openState before) = openState (RegistrationNativeMldsaMainView.project before) := rfl

private theorem close_project (before : Local n KemSK source) :
    RegistrationNativeMldsaShared.close (localProject before) =
      RegistrationNativeMldsaMainView.project (RegistrationNativeMldsaShared.close before) := rfl

/-- The complete unchanged native Init wrapper has checked original and normalized free continuation equations, including final shared-cache and signing state. -/
theorem sourceBundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) :
    Correct (RegistrationNativeMldsaMainView.project (n := n) (source := source))
      (RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index) := by
  constructor
  · intro before
    have same := congrArg (fun computation => Prod.map id RegistrationNativeMldsaShared.close <$> computation)
      ((bundle (source := source) setup checks wire representation created index).1 (openState before))
    simp only [Functor.map_map, Prod.map, id_eq, close_project, open_project] at same
    simp only [RegistrationNativeMldsaBundle.sourceBundle, StateT.run, Functor.map_map, Prod.map, id_eq]
    exact same
  · intro before
    have same := congrArg (fun computation => Prod.map id RegistrationNativeMldsaShared.close <$> computation)
      ((bundle (source := source) setup checks wire representation created index).2 (openState before))
    simp only [Functor.map_map, Prod.map, id_eq, close_project, open_project] at same
    simp only [RegistrationNativeMldsaBundle.sourceBundle, StateT.run, transform, simulateQ_map,
      Functor.map_map, Prod.map, id_eq]
    exact same

end BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle.sourceBundle
