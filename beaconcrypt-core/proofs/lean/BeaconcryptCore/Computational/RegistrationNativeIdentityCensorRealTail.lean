-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicHashSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame

/-! The actual ML/Ready/writer suffix has no CTX query or indexed Ed service. Its canonical operational realization erases to the literal original source with every current reply, shared native state, mutable writer state and true counter retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorRealSigning (NoHash)
variable {n : Nat} {I KemSK Platform E A B : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] registration.BeaconFingerprint.resume registration.BeaconInitHash.resume registration.BeaconMldsaSigning.resume

private def Safe (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) : Prop :=
  ∀ before, (work.run before).AllQueriesSatisfy NoHash

private theorem pure_safe (value : A) : Safe (pure value : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) := by
  intro before
  simp only [StateT.run_pure]
  trivial

private theorem bind_safe (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (next : A → RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource B)
    (first : Safe work) (later : ∀ value, Safe (next value)) : Safe (work >>= next) := by
  intro before
  rw [StateT.run_bind]
  exact allQueriesSatisfy_bind (first before) (fun result => later result.1 result.2)

private theorem continue_safe {X : Type} (action : RustM X)
    (next : X → RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource (RustM (RegistrationBeaconInitExecutor.Result A)))
    (later : ∀ value, Safe (next value)) : Safe (RegistrationNativePlatformBeaconPublication.continueWith action next) := by
  cases action with
  | fail error | div => exact pure_safe _
  | ok value => exact later value

private theorem coin_noHash (query : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain)
    (coin : RegistrationNativePlatformIdentityCtxMldsaCoins.Coin query) : NoHash query := by
  rcases query with ((coin | request) | report) | bytes
  · trivial
  · exact False.elim coin
  · exact False.elim coin
  · exact False.elim coin

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
variable (writer : registration.SignedInitView → StateT Platform ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "callback" => (fun query => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query)))
local notation "encoder" => (fun fields => Main (RegistrationNativePlatformIdentityProgram.external (writer fields)))

private theorem encode_safe (fields : registration.SignedInitView) : Safe (encoder fields) := by
  intro before
  exact (RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer fields) before).mono coin_noHash

private theorem ready_safe (pending : registration.BeaconInitReady) :
    Safe (RegistrationNativePlatformBeaconPublication.ready encoder pending) := by
  unfold RegistrationNativePlatformBeaconPublication.ready
  apply continue_safe
  intro fields
  exact bind_safe _ _ (encode_safe setup checks representation created writer fields) (fun _ => pure_safe _)

/-- The literal original ML-to-Ready source suffix contains only protocol uniform queries after all actual request/resume branches are evaluated. -/
theorem signing_safe (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    Safe (RegistrationNativePlatformBeaconPublication.fromSigning callback encoder payload digest pending) := by
  unfold RegistrationNativePlatformBeaconPublication.fromSigning
  apply continue_safe
  intro request
  apply bind_safe
  · intro before
    exact (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before).mono coin_noHash
  · intro signature
    apply continue_safe
    intro effect
    cases effect with
    | Ready selected => exact ready_safe setup checks representation created writer selected
    | _ => exact pure_safe _

private abbrev TailSpec := RegistrationBeaconInitExecutor.Spec +
  (registration.SignedInitView →ₒ RustM (core.option.Option (alloc.vec.Vec U8)))

private noncomputable def dictionary : QueryImpl TailSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource)
  | .inl query => callback query
  | .inr fields => encoder fields

private theorem factor (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    simulateQ (dictionary setup checks representation created index owner writer)
      (RegistrationNativePlatformBeaconPublication.fromSigning
        (fun query => TailSpec.query (.inl query)) (fun fields => TailSpec.query (.inr fields)) payload digest pending) =
      RegistrationNativePlatformBeaconPublication.fromSigning callback encoder payload digest pending := by
  simpa only [simulateQ_spec_query, dictionary] using
    RegistrationNativePlatformBeaconPublication.signing_interpret
      (dictionary setup checks representation created index owner writer)
      (fun query => TailSpec.query (.inl query)) (fun fields => TailSpec.query (.inr fields)) payload digest pending

private theorem original_program {Q : Type} {queries : OracleSpec Q}
    (joint : PqxdhJointIdentity.Primitives)
    (impl : QueryImpl queries (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (work : OracleComp queries A) :
    RegistrationNativePlatformIdentityCtxMain.interpret joint (simulateQ impl work) =
      simulateQ (fun query => RegistrationNativePlatformIdentityCtxMain.interpret joint (impl query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value =>
    simp only [simulateQ_pure]
    exact RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure joint value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query,
      RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, ih]

private theorem source_factor (selected : Nat) (placeholder : Ed25519Signature)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning) :
    interpret setup.joint selected placeholder false
      (RegistrationNativePlatformBeaconPublication.fromSigning callback encoder payload digest pending) =
      RegistrationNativePlatformBeaconPublication.fromSigning
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) payload digest pending := by
  rw [← factor setup checks representation created index owner writer payload digest pending,
    RegistrationNativeIdentityCensorSourceFold.program, RegistrationNativePlatformBeaconPublication.signing_interpret]
  simp only [simulateQ_spec_query, dictionary]

private theorem original_factor (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformBeaconPublication.fromSigning callback encoder payload digest pending) =
      RegistrationNativePlatformBeaconPublication.fromSigning
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) payload digest pending := by
  rw [← factor setup checks representation created index owner writer payload digest pending,
    original_program, RegistrationNativePlatformBeaconPublication.signing_interpret]
  simp only [simulateQ_spec_query, dictionary]

/-- The complete literal ML/Ready/encoder continuation erases to the original honest source. All optional signing replies, source failures, mutable writer results, pool observations and true counters remain in the same joint run. -/
theorem signing (selected : Nat) (placeholder : Ed25519Signature)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromSigning
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) payload digest pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromSigning
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) payload digest pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  rw [← source_factor setup checks representation created index owner writer selected placeholder payload digest pending,
    ← original_factor setup checks representation created index owner writer payload digest pending]
  exact RegistrationNativeIdentityCensorRealSigning.main setup.joint selected placeholder _ before
    (signing_safe setup checks representation created index owner writer payload digest pending before.1.1)

private def hashNext {m : Type → Type} [Monad m]
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : registration.BeaconInitHash) (request : registration.HashRequest) (digest : CtxRomAuth.CtxDigest) :
    m (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformBeaconPublication.continueWith
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .MldsaSigningRequested next => RegistrationNativePlatformBeaconPublication.fromSigning impl encode
          ⟨.beacon, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩ digest next
      | _ => pure .div

/-- The actual hidden Init hash and complete ML/Ready suffix erase to the ordinary source once the reached private memo reconstructs that exact current hash input. -/
theorem hash (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconInitHash) (request : registration.HashRequest) (requested : pending.request = .ok request)
    (signature : Ed25519Signature)
    (literal : BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request =
      (RegistrationNativeIdentityCensorOperational.parts (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)).1 ++ signature.toList ++
      (RegistrationNativeIdentityCensorOperational.parts (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)).2)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (stored : before.2.canonical = some signature) (active : before.1.2.active = true) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromHash
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromHash
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  obtain ⟨actualRequest, actualRequested, _bytes, routed⟩ := RegistrationNativeIdentityHashRoute.transcript pending
  have same : actualRequest = request := RustM.ok.inj (actualRequested.symm.trans requested)
  subst actualRequest
  simp only [RegistrationNativePlatformBeaconPublication.fromHash, requested, RegistrationNativePlatformBeaconPublication.continueWith]
  simp only [StateT.run_bind, map_bind]
  have current := RegistrationNativeIdentityCensorActualHashSource.hidden setup checks representation created selected placeholder request before
    signature stored active routed literal
  change Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
    (interpret setup.joint selected placeholder false (callback (.inl (.hash request)))).run before =
    (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback (.inl (.hash request)))).run
      (RegistrationNativeIdentityCensorActualHashSource.project before) at current
  rw [← current, bind_map_left]
  apply bind_congr
  rintro ⟨digest, after⟩
  change Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
    (hashNext (fun query => interpret setup.joint selected placeholder false (callback query))
      (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending request digest).run after =
    (hashNext (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
      (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending request digest).run
        (RegistrationNativeIdentityCensorActualHashSource.project after)
  unfold hashNext
  cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | ok effect => cases effect with
    | MldsaSigningRequested next =>
      exact signing setup checks representation created index owner writer selected placeholder
        ⟨.beacon, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩ digest next after
    | _ =>
      simp only [RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_pure, map_pure, Prod.map_apply, id_eq]

private def fingerprintNext {m : Type → Type} [Monad m]
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : registration.BeaconFingerprint) (digest : CtxRomAuth.CtxDigest) :
    m (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformBeaconPublication.continueWith
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .HashRequested next => RegistrationNativePlatformBeaconPublication.fromHash impl encode next
      | _ => pure .div

/-- Actual fingerprint resume derives the precise hidden input framing from its retained canonical attachment; the full fingerprint/hash/ML/writer source marginal follows with no hash-coverage or controller equation supplied. -/
theorem fingerprint (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconFingerprint) (signature : Ed25519Signature) (message : Pqxdh.Bytes)
    (attached : PqxdhRefinement.absBytes pending.state.one_time_key = signature.toList ++ message)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (stored : before.2.canonical = some signature) (active : before.1.2.active = true) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.fromFingerprint
        (fun query => interpret setup.joint selected placeholder false (callback query))
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromFingerprint
        (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  obtain ⟨request, requested, bytes, _routed⟩ := RegistrationNativeIdentityHashRoute.fingerprint pending
  have width : (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request).length = 1952 := by
    rw [bytes, PqxdhRefinement.absBytes_length]
    rfl
  simp only [RegistrationNativePlatformBeaconPublication.fromFingerprint, requested, RegistrationNativePlatformBeaconPublication.continueWith,
    StateT.run_bind, map_bind]
  have current := RegistrationNativeIdentityCensorPublicHashSource.fingerprint setup checks representation created selected placeholder request before width
  change Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
    (interpret setup.joint selected placeholder false (callback (.inl (.hash request)))).run before =
    (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback (.inl (.hash request)))).run
      (RegistrationNativeIdentityCensorActualHashSource.project before) at current
  rw [← current, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨digest, after⟩ reached
  have frame := RegistrationNativeIdentityCensorHashFrame.outgoing setup checks representation created selected placeholder request false before (digest, after) reached
  have stillStored : after.2.canonical = some signature := (congrArg (fun value => value.2.2.2) frame).trans stored
  have stillActive : after.1.2.active = true := (congrArg (fun value => value.1.active) frame).trans active
  obtain ⟨next, nextRequest, resumed, nextRequested, _framing, literal⟩ := RegistrationNativeIdentityPublicHashTemplate.source pending
    (RegistrationAuthenticationShared.digestArray digest) signature message attached
  change Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
    (fingerprintNext (fun query => interpret setup.joint selected placeholder false (callback query))
      (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending digest).run after =
    (fingerprintNext (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (callback query))
      (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending digest).run
        (RegistrationNativeIdentityCensorActualHashSource.project after)
  unfold fingerprintNext
  rw [resumed]
  exact hash setup checks representation created index owner writer selected placeholder next nextRequest nextRequested signature literal after stillStored stillActive

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.signing_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.signing_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.fingerprint
