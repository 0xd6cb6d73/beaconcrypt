-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicInitPublication
/-! All three actual source Ed signing stages and the actual Core begin/Init driver fold to the stateful publication program. Immutable Ed public-key getters and actual primitive signing/hash contracts are explicit. No fixed reply function, source-loop fuel assumption, allocation-success premise or encoder law is used; common monadic poststates and source writer failures remain observable. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicInitEdPublication
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
open AdapterPublicInitPublication

private theorem ed_shapes (pending : registration.BeaconEd25519Signing) (reply : Option (Slice U8)) :
    ∃ effect, pending.resume reply = .ok effect ∧
      (effect = .Rejected pending.state.original_control ∨
        (∃ next, effect = .Ed25519SigningRequested next ∧
          next.state.original_control = pending.state.original_control ∧
          RegistrationBeaconInitExecutor.edRank pending = RegistrationBeaconInitExecutor.edRank next + 1) ∨
        ∃ next, effect = .HashRequested next ∧
          next.state.original_control = pending.state.original_control ∧
          RegistrationBeaconInitExecutor.edRank pending = 1) := by
  obtain ⟨effect, resumed, progress⟩ := RegistrationSigning.ed_resume_refines pending reply
  refine ⟨effect, resumed, ?_⟩
  cases effect with
  | Rejected original =>
      exact .inl (congrArg registration.BeaconInitEffect.Rejected progress)
  | Ed25519SigningRequested next =>
      refine .inr (.inl ⟨next, rfl, ?_⟩)
      cases stage : pending.stage <;> simp only [RegistrationSigning.EdReplyTransition, stage] at progress
      · exact ⟨by simpa only using congrArg registration.BeaconInitState.original_control progress.2.2.2,
          by simp only [RegistrationBeaconInitExecutor.edRank, stage, progress.2.1]⟩
      · exact ⟨by simpa only using congrArg registration.BeaconInitState.original_control progress.2.2.2,
          by simp only [RegistrationBeaconInitExecutor.edRank, stage, progress.2.1]⟩
      · cases progress.2
  | HashRequested next =>
      refine .inr (.inr ⟨next, rfl, ?_, ?_⟩)
      · simpa only using congrArg registration.BeaconInitState.original_control progress.2.2.2
      · simp only [RegistrationBeaconInitExecutor.edRank, progress.2.1]
  | _ => cases progress

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m] {Encoded : Type}
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]

omit platform localOps in
private theorem ed_fold (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconEd25519Signing)
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (ed : registration.Ed25519SigningRequest → m RegistrationSigningShared.SignReply)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request)
    (edLeaf : ∀ request, (AdapterPublicInitReady.ed (m := m) beacon request).run = RustM.ok <$> ed request) :
    publication pending.state.original_control encode
      (beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) (.Ed25519SigningRequested pending) beacon) =
    RegistrationNativePlatformBeaconPublication.fromEd (outgoing hash ed) encode pending := by
  rw [AdapterPublicInitReady.loop_source, RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  simp only [AdapterPublicInitSourceLoop.rank]
  rw [publication_step]
  simp only [AdapterPublicInitReady.step, RustT.run_bind, RustT.run_liftRust, RustT.run_pure]
  cases requested : pending.request with
  | fail error | div => simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith]
  | ok request =>
      simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith,
        edLeaf, outgoing, bind_map_left, bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨effect, resumed, shapes⟩ := ed_shapes pending reply
      rw [resumed]
      rcases shapes with rfl | ⟨next, rfl, original, ranks⟩ | ⟨next, rfl, original, ranks⟩
      · simp only [pure_bind, AdapterPublicWrapperLiftFunction.loopFuel, AdapterPublicInitReady.step,
          RustT.run_pure, publication]
      · change AdapterPublicInitSourceLoop.edRank pending = AdapterPublicInitSourceLoop.edRank next + 1 at ranks
        simp only [pure_bind]
        have continued := ed_fold beacon next hash ed encode hashLeaf edLeaf
        rw [AdapterPublicInitReady.loop_source] at continued
        simp only [AdapterPublicInitSourceLoop.rank, original] at continued
        convert continued using 1
        congr 2
        omega
      · change AdapterPublicInitSourceLoop.edRank pending = 1 at ranks
        simp only [pure_bind]
        have continued := hash_source beacon next hash ed encode hashLeaf
        rw [AdapterPublicInitReady.loop_source] at continued
        simp only [AdapterPublicInitSourceLoop.rank, original] at continued
        convert continued using 1
        congr 2
        omega
termination_by RegistrationBeaconInitExecutor.edRank pending


omit platform localOps in
theorem ed_source (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconEd25519Signing)
    (publicKey : Std.Array U8 32#usize)
    (edSign : Slice U8 → m (core.result.Result (alloc.vec.Vec U8) primitive.Error))
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (getter : (crypto.edPublicBytes beacon.identity_key.public_key).run = pure (.ok publicKey))
    (edSignLeaf : ∀ message, (crypto.edSign message beacon.identity_key.secret_key).run = RustM.ok <$> edSign message)
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request) :
    publication pending.state.original_control encode
      (beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) (.Ed25519SigningRequested pending) beacon) =
    RegistrationNativePlatformBeaconPublication.fromEd (outgoing hash (edMethod publicKey edSign)) encode pending :=
  ed_fold beacon pending hash (edMethod publicKey edSign) encode hashLeaf
    (ed_leaf beacon publicKey edSign getter edSignLeaf)


omit material platform primitive localOps crypto children in
private theorem publication_lift {Input : Type}
    (control : pqxdh.BeaconFresh)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (action : RustM Input) (next : Input → RustT m (core.option.Option registration.BeaconInitReady)) :
    publication control encode (do let value ← liftRust action; next value) =
      (match action with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok value => publication control encode (next value)) := by
  cases action <;> simp only [publication, RustT.run_bind, RustT.run_liftRust, pure_bind]

omit platform localOps in
theorem begin_source (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (publicKey : Std.Array U8 32#usize)
    (edSign : Slice U8 → m (core.result.Result (alloc.vec.Vec U8) primitive.Error))
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (getter : (crypto.edPublicBytes beacon.identity_key.public_key).run = pure (.ok publicKey))
    (edSignLeaf : ∀ message, (crypto.edSign message beacon.identity_key.secret_key).run = RustM.ok <$> edSign message)
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request) :
    publication control encode (do
      let effect ← liftRust (registration.begin_beacon_init control inputs coins pin)
      beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) effect beacon) =
    RegistrationNativePlatformBeaconPublication.begin (outgoing hash (edMethod publicKey edSign)) encode control inputs coins pin := by
  rw [publication_lift]
  unfold RegistrationNativePlatformBeaconPublication.begin
  obtain ⟨started, _startedRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin
  rw [beginRun]
  split_ifs
  · simp only [RegistrationNativePlatformBeaconPublication.continueWith, AdapterPublicInitReady.loop_source,
      AdapterPublicInitSourceLoop.rank, AdapterPublicWrapperLiftFunction.loopFuel, AdapterPublicInitReady.step,
      publication, RustT.run_pure, pure_bind]
  · simp only [RegistrationNativePlatformBeaconPublication.continueWith]
    exact ed_source beacon _ publicKey edSign hash encode getter edSignLeaf hashLeaf

end BeaconcryptCore.Refinement.AdapterPublicInitEdPublication

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitEdPublication.ed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitEdPublication.ed_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitEdPublication.begin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitEdPublication.begin_source
