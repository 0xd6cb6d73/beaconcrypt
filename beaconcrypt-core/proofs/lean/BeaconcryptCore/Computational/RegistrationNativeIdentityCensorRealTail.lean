-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicHashSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame

/-! The actual Ready/writer suffix has no CTX query or indexed Ed service. Its canonical operational realization erases to the literal original source with every current reply, shared native state, mutable writer state and true counter retained. -/
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
attribute [local irreducible] registration.BeaconInitHash.resume

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
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
variable (writer : registration.InitView → StateT Platform ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "callback" => (fun query => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query)))
local notation "encoder" => (fun fields => Main (RegistrationNativePlatformIdentityProgram.external (writer fields)))

private theorem encode_safe (fields : registration.InitView) : Safe (encoder fields) := by
  intro before
  exact (RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer fields) before).mono coin_noHash

private theorem ready_safe (pending : registration.BeaconInitReady) :
    Safe (RegistrationNativePlatformBeaconPublication.ready encoder pending) := by
  unfold RegistrationNativePlatformBeaconPublication.ready
  apply continue_safe
  intro fields
  exact bind_safe _ _ (encode_safe setup checks representation created writer fields) (fun _ => pure_safe _)

private abbrev TailSpec := registration.InitView →ₒ RustM (core.option.Option (alloc.vec.Vec U8))

private noncomputable def dictionary : QueryImpl TailSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource) :=
  fun fields => encoder fields

private theorem factor (pending : registration.BeaconInitReady) :
    simulateQ (dictionary setup checks representation created writer)
      (RegistrationNativePlatformBeaconPublication.ready (fun fields => TailSpec.query fields) pending) =
      RegistrationNativePlatformBeaconPublication.ready encoder pending := by
  simpa only [simulateQ_spec_query,dictionary] using
    RegistrationNativePlatformBeaconPublication.ready_interpret
      (dictionary setup checks representation created writer) (fun fields => TailSpec.query fields) pending

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

private theorem source_factor (selected : Nat) (placeholder : Ed25519Signature) (pending : registration.BeaconInitReady) :
    interpret setup.joint selected placeholder false (RegistrationNativePlatformBeaconPublication.ready encoder pending) =
      RegistrationNativePlatformBeaconPublication.ready
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending := by
  rw [← factor setup checks representation created writer pending,
    RegistrationNativeIdentityCensorSourceFold.program,RegistrationNativePlatformBeaconPublication.ready_interpret]
  simp only [simulateQ_spec_query,dictionary]

private theorem original_factor (pending : registration.BeaconInitReady) :
    RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (RegistrationNativePlatformBeaconPublication.ready encoder pending) =
      RegistrationNativePlatformBeaconPublication.ready
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending := by
  rw [← factor setup checks representation created writer pending,
    original_program,RegistrationNativePlatformBeaconPublication.ready_interpret]
  simp only [simulateQ_spec_query,dictionary]

/-- The actual Ready/encoder continuation erases to the original source with every writer outcome and full state. -/
theorem ready (selected : Nat) (placeholder : Ed25519Signature) (pending : registration.BeaconInitReady)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (RegistrationNativePlatformBeaconPublication.ready
        (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending).run before =
      (RegistrationNativePlatformBeaconPublication.ready
        (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending).run
          (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  rw [← source_factor setup checks representation created writer selected placeholder pending,
    ← original_factor setup checks representation created writer pending]
  exact RegistrationNativeIdentityCensorRealSigning.main setup.joint selected placeholder _ before
    (ready_safe setup checks representation created writer pending before.1.1)

private def hashNext {m : Type → Type} [Monad m]
    (encode : registration.InitView → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : registration.BeaconInitHash) (digest : CtxRomAuth.CtxDigest) :
    m (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformBeaconPublication.continueWith
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .Ready next => RegistrationNativePlatformBeaconPublication.ready encode next
      | _ => pure .div

/-- The actual hidden Init hash and complete Ready suffix erase to the ordinary source once the reached private memo reconstructs that exact current hash input. -/
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
    (hashNext (fun fields => interpret setup.joint selected placeholder false (encoder fields)) pending digest).run after =
    (hashNext (fun fields => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (encoder fields)) pending digest).run
        (RegistrationNativeIdentityCensorActualHashSource.project after)
  unfold hashNext
  cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | ok effect => cases effect with
    | Ready next =>
      exact ready setup checks representation created writer selected placeholder next after
    | _ =>
      simp only [RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_pure, map_pure, Prod.map_apply, id_eq]

/-- The actual canonical request receipt supplies the selected hidden address directly. -/
theorem request_hash (selected : Nat) (placeholder : Ed25519Signature)
    (pending : registration.BeaconInitHash) (canonical : RegistrationNativeInitStageContents.Canonical pending)
    (signature : Ed25519Signature) (message : Pqxdh.Bytes)
    (attached : PqxdhRefinement.absBytes pending.state.one_time_key = signature.toList ++ message)
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
  obtain ⟨request,requested,_framing,literal⟩ := RegistrationNativeIdentityPublicHashTemplate.source pending canonical signature message attached
  exact hash setup checks representation created index owner writer selected placeholder pending request requested signature literal before stored active

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail



/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.ready

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.request_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealTail.request_hash
