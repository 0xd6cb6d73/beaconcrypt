-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishTranscript
import BeaconcryptCore.Refinement.AdapterPublicFinishBody
/-! The actual public Beacon first-open loop and its initial HKDF compose with the native record request program in one shared monad. Individual primitive functional contracts preserve optional hash/AEAD failure, the actual mutable transcript result, exact comparison and complete object installation. Recursion uses the actual Core rank; no fixed reply, success or caller fuel premise is needed by the source endpoints. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishRecord
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [children : ChildOperations (RustT m)]

structure Primitives (m : Type → Type) where
  initial : ratchet.SymmetricRatchetKdfRequest → m (Std.Array U8 64#usize)
  kdf : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse
  hash : commitment.CommitmentTranscript → m (core.option.Option (Std.Array U8 64#usize) × commitment.CommitmentTranscript)
  aead : record.AeadRequest → m (core.option.Option (alloc.vec.Vec U8))

def handler (primitive : Primitives m) : QueryImpl RegistrationRecordPrimitives.Spec m
  | .ratchetKdf request => core.option.Option.Some <$> primitive.kdf request
  | .hash request => Prod.fst <$> primitive.hash request
  | .openAead request => AdapterPublicInitPublication.borrowed <$> primitive.aead request
  | .rootKdf _ => pure .None
  | .initialKdf request => (fun bytes => core.option.Option.Some (⟨bytes⟩ : pqxdh.concrete.InitialRatchetKdfResponse)) <$> primitive.initial request
  | .seal _ => pure .None
  | .write _ => pure .None

structure Contract (primitive : Primitives m) : Prop where
  kdf : ∀ request, (children.ratchetHkdf request).run = RustM.ok <$> primitive.kdf request
  hash : ∀ transcript, (children.commitmentHash transcript).run = RustM.ok <$> primitive.hash transcript
  aead : ∀ request, (children.openRequest request).run = RustM.ok <$>
    (match request with | .none => pure .none | .some request => primitive.aead request)
  compare : ∀ left right, (children.compare left right).run =
    pure (.ok (decide (TranscriptAuthParts.absSlice left = TranscriptAuthParts.absSlice right)))

omit children [Monad m] [LawfulMonad m] in
def result (identifier : U64) : RustM RegistrationBeaconRecordExecutor.Result → RustM AdapterPublicFinishReady.Result
  | .fail error => .fail error
  | .div => .div
  | .ok (.Err control) => .ok (.None, identifier, .Aborted control)
  | .ok (.Ok completed) => AdapterPublicWrapperCopy.install completed

private theorem kdf (primitive : Primitives m) (contract : Contract primitive) (identifier : U64)
    (fuel : Nat) (pending : registration.BeaconRecordKdf)
    (continued : ∀ response next, pending.resume (.Some response) = .ok (.Ok next) →
      (AdapterPublicWrapperLiftFunction.loopFuel fuel (AdapterPublicFinishReady.step identifier) next).run =
        result identifier <$> simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program next)) :
    (AdapterPublicWrapperLiftFunction.loopFuel (fuel + 1) (AdapterPublicFinishReady.step identifier) (.KdfRequested pending)).run =
      result identifier <$> simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program (.KdfRequested pending)) := by
  rw [AdapterPublicWrapperLiftFunction.loopFuel, RegistrationBeaconRecordExecutor.program.eq_def]
  simp only [AdapterPublicFinishReady.step, AdapterPublicFinishReady.resume, RustT.run_bind,
    RustT.run_liftRust, bind_assoc]
  cases requested : pending.request with
  | fail error | div => simp only [pure_bind, RegistrationBeaconRecordExecutor.continueWith, simulateQ_pure, map_pure, result]
  | ok request =>
      simp only [pure_bind, contract.kdf, bind_map_left, RegistrationBeaconRecordExecutor.continueWith,
        simulateQ_bind, simulateQ_spec_query, handler, map_bind]
      apply bind_congr
      intro response
      cases resumed : pending.resume (.Some response) with
      | fail error | div => simp only [simulateQ_pure, map_pure, result]
      | ok answer => cases answer with
        | Err control => simp only [pure_bind, RustT.run_pure, simulateQ_pure, map_pure, result]
        | Ok next =>
            simp only [RustT.run_pure, pure_bind]
            exact continued response next resumed

private theorem aead (primitive : Primitives m) (contract : Contract primitive) (identifier : U64)
    (fuel : Nat) (pending : registration.BeaconRecordAead) :
    (AdapterPublicWrapperLiftFunction.loopFuel (fuel + 1) (AdapterPublicFinishReady.step identifier) (.AeadRequested pending)).run =
      result identifier <$> simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program (.AeadRequested pending)) := by
  rw [AdapterPublicWrapperLiftFunction.loopFuel, RegistrationBeaconRecordExecutor.program.eq_def]
  simp only [AdapterPublicFinishReady.step, RustT.run_bind, RustT.run_liftRust, bind_assoc]
  cases requested : pending.request with
  | fail error | div => simp only [pure_bind, RegistrationBeaconRecordExecutor.continueWith, simulateQ_pure, map_pure, result]
  | ok optional =>
      cases optional with
      | none =>
          simp only [pure_bind, contract.aead, map_pure, AdapterPublicInitPublication.borrowed_source,
            RegistrationBeaconRecordExecutor.continueWith, simulateQ_pure, AdapterPublicInitPublication.borrowed]
          cases finished : pending.finish .None with
          | fail error | div => simp only [result]
          | ok answer => cases answer with
            | Err control => simp only [pure_bind, RustT.run_pure, result]
            | Ok completed => simp only [pure_bind, RustT.run_bind, RustT.run_liftRust, RustT.run_pure,
                AdapterPublicWrapperCopy.install_exact, result]
      | some request =>
          simp only [pure_bind, contract.aead, bind_map_left, AdapterPublicInitPublication.borrowed_source,
            RegistrationBeaconRecordExecutor.continueWith, simulateQ_bind,
            simulateQ_spec_query, handler, map_bind]
          apply bind_congr
          intro plaintext
          cases finished : pending.finish (AdapterPublicInitPublication.borrowed plaintext) with
          | fail error | div => simp only [simulateQ_pure, map_pure, result]
          | ok answer => cases answer with
            | Err control => simp only [pure_bind, RustT.run_pure, simulateQ_pure, map_pure, result]
            | Ok completed => simp only [pure_bind, RustT.run_bind, RustT.run_liftRust, RustT.run_pure,
                AdapterPublicWrapperCopy.install_exact, simulateQ_pure, map_pure, result]

omit material children [Monad m] [LawfulMonad m] in
private theorem slice_bytes {width : Usize} (bytes : Std.Array U8 width) :
    TranscriptAuthParts.absSlice (Std.Array.to_slice bytes) = PqxdhRefinement.absBytes bytes := rfl

private theorem commitment (primitive : Primitives m) (contract : Contract primitive) (identifier : U64)
    (fuel : Nat) (pending : registration.BeaconRecordCommitment)
    (continued : ∀ matched next, pending.resume matched = .ok (.Ok next) →
      (AdapterPublicWrapperLiftFunction.loopFuel fuel (AdapterPublicFinishReady.step identifier) next).run =
        result identifier <$> simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program next)) :
    (AdapterPublicWrapperLiftFunction.loopFuel (fuel + 1) (AdapterPublicFinishReady.step identifier) (.CommitmentRequested pending)).run =
      result identifier <$> simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program (.CommitmentRequested pending)) := by
  have transcriptRun : pending.transcript = .ok pending.pending.pending.transcript := rfl
  obtain ⟨supplied, suppliedRun⟩ : ∃ supplied, pending.supplied_commitment = .ok supplied := ⟨_, rfl⟩
  rw [AdapterPublicWrapperLiftFunction.loopFuel, RegistrationBeaconRecordExecutor.program.eq_def]
  simp only [AdapterPublicFinishReady.step, AdapterPublicFinishTranscript.borrowed, RustT.run_bind,
    RustT.run_liftRust, pure_bind, transcriptRun, RegistrationBeaconRecordExecutor.continueWith,
    contract.hash, bind_map_left, simulateQ_bind, simulateQ_spec_query, handler, map_bind, bind_assoc]
  apply bind_congr
  intro hashed
  rcases hashed with ⟨digest, erased⟩
  cases digest with
  | none =>
      simp only [AdapterPublicFinishReady.resume, AdapterPublicFinishTranscript.resume, suppliedRun,
        RegistrationBeaconRecordExecutor.commitmentMatches,
        RustT.run_bind, RustT.run_liftRust]
      cases resumed : pending.resume false with
      | fail error | div => simp only [pure_bind, simulateQ_pure, map_pure, result]
      | ok answer => cases answer with
        | Err control => simp only [pure_bind, RustT.run_pure, simulateQ_pure, map_pure, result]
        | Ok next =>
            simp only [pure_bind, RustT.run_pure]
            exact continued false next resumed
  | some digest =>
      simp only [AdapterPublicFinishTranscript.supplied, suppliedRun, RustT.run_bind, RustT.run_liftRust,
        pure_bind, contract.compare,
        RegistrationBeaconRecordExecutor.commitmentMatches, AdapterPublicFinishReady.resume, AdapterPublicFinishTranscript.resume]
      rw [slice_bytes, slice_bytes]
      cases resumed : pending.resume (decide (PqxdhRefinement.absBytes digest = PqxdhRefinement.absBytes supplied)) with
      | fail error | div => simp only [pure_bind, simulateQ_pure, map_pure, result]
      | ok answer => cases answer with
        | Err control => simp only [pure_bind, RustT.run_pure, simulateQ_pure, map_pure, result]
        | Ok next =>
            simp only [pure_bind, RustT.run_pure]
            exact continued _ next resumed

theorem finite (primitive : Primitives m) (contract : Contract primitive) (identifier : U64)
    (fuel : Nat) (effect : registration.BeaconInitialOpen) (enough : RegistrationBeaconRecordExecutor.rank effect < fuel) :
    (AdapterPublicWrapperLiftFunction.loopFuel fuel (AdapterPublicFinishReady.step identifier) effect).run =
      result identifier <$> simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program effect) := by
  induction fuel generalizing effect with
  | zero => omega
  | succ fuel ih =>
      cases effect with
      | KdfRequested pending =>
          apply kdf primitive contract identifier fuel pending
          intro response next resumed
          have progress := RegistrationBeaconRecordExecutor.kdf_rank pending (.Some response) next resumed
          exact ih next (by omega)
      | CommitmentRequested pending =>
          apply commitment primitive contract identifier fuel pending
          intro matched next resumed
          have progress := RegistrationBeaconRecordExecutor.commitment_rank pending matched next resumed
          exact ih next (by omega)
      | AeadRequested pending => exact aead primitive contract identifier fuel pending

/-- The actual source first-open loop has its native record result in the same shared monad, with no caller fuel or fixed-reply premise. -/
theorem source (primitive : Primitives m) (contract : Contract primitive) (identifier : U64)
    (effect : registration.BeaconInitialOpen) :
    (beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop (m := RustT m) effect identifier).run =
      result identifier <$> simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program effect) := by
  rw [AdapterPublicFinishReady.loop_source]
  exact finite primitive contract identifier _ effect (by omega)

variable [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.CryptoOperations]

omit children [Monad m] [LawfulMonad m] in
def wrap (self : beaconcrypt_public_wrapper.beacon.Beacon) (answer : RustM AdapterPublicFinishReady.Result) : RustM AdapterPublicFinishBody.Result := do
  let (plaintext, identifier, state) ← answer
  .ok (plaintext, { self with identity_key_kid := identifier, state := state })

variable [localOps : LocalOperations (RustT m)]

omit platform [PublicWrapperPlatform.CryptoOperations] localOps in
private theorem loop_wrap (primitive : Primitives m) (contract : Contract primitive)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : registration.BeaconInitialOpen) :
    (do let (plaintext, identifier, state) ←
          beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop (m := RustT m) effect self.identity_key_kid
        pure (plaintext, { self with identity_key_kid := identifier, state := state })).run =
      (fun answer => wrap self (result self.identity_key_kid answer)) <$>
        simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program effect) := by
  simp only [RustT.run_bind]
  rw [source primitive contract]
  simp only [bind_map_left]
  rw [← bind_pure_comp]
  apply bind_congr
  intro answer
  cases answer with
  | fail error | div => rfl
  | ok answer => cases answer with
    | Err control => rfl
    | Ok completed => simp only [result, AdapterPublicWrapperCopy.install_exact, RustT.run_pure, wrap, bind_tc_ok]; rfl

omit [PublicWrapperPlatform.CryptoOperations] in
theorem initial (primitive : Primitives m) (contract : Contract primitive)
    (initialLeaf : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run = RustM.ok <$> primitive.initial request)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (agreement : agreement.BeaconAgreement) :
    (AdapterPublicFinishBody.beginOpen (m := m) self agreement).run =
      (fun answer => wrap self (result self.identity_key_kid answer)) <$>
        simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.begin agreement) := by
  unfold AdapterPublicFinishBody.beginOpen RegistrationBeaconRecordExecutor.begin
  simp only [RustT.run_bind, RustT.run_liftRust]
  cases begun : registration.begin_beacon_completion agreement with
  | fail error | div => simp only [pure_bind, RegistrationBeaconRecordExecutor.continueWith, simulateQ_pure, map_pure, result, wrap]; rfl
  | ok pending =>
      simp only [pure_bind, RegistrationBeaconRecordExecutor.continueWith, RegistrationBeaconRecordExecutor.fromInitial]
      cases requested : pending.request with
      | fail error | div => simp only [simulateQ_pure, map_pure, result, wrap]; rfl
      | ok request =>
          simp only [initialLeaf, bind_map_left, simulateQ_bind, simulateQ_spec_query, handler, map_bind, pqxdh.concrete.InitialRatchetKdfResponse.from_bytes]
          apply bind_congr
          intro bytes
          cases resumed : pending.resume (.Some ⟨bytes⟩) with
          | fail error | div => simp only [simulateQ_pure, map_pure, result, wrap]; rfl
          | ok answer => cases answer with
            | Err control => simp only [RustT.run_pure, simulateQ_pure, map_pure, result, wrap, bind_tc_ok]; rfl
            | Ok effect => exact loop_wrap primitive contract self effect
end BeaconcryptCore.Refinement.AdapterPublicFinishRecord

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecord.finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecord.finite

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecord.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecord.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecord.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecord.initial
