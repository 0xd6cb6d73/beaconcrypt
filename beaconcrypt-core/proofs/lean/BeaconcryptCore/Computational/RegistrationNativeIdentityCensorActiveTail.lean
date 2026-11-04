-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStaleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame

/-! Actual later publication leaves preserve the public current-callback active flag. This supplies the operational stopping condition rather than assuming successful publication is recognizable from a private source event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A B : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)

private def Keeps (work : StateT FullState ProbComp A) : Prop :=
  ∀ before result, result ∈ support (work.run before) → result.2.1.2.active = before.1.2.active

private theorem pure_keeps (value : A) : Keeps (pure value : StateT FullState ProbComp A) := by
  intro before result possible
  rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at possible
  subst result
  rfl

private theorem bind_keeps (work : StateT FullState ProbComp A) (next : A → StateT FullState ProbComp B)
    (first : Keeps work) (later : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before result possible
  rw [StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨middle, reached, continued⟩ := possible
  exact (later middle.1 middle.2 result continued).trans (first before middle reached)

private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → StateT FullState ProbComp (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))))
    (later : ∀ input, Keeps (next input)) : Keeps (RegistrationNativePlatformBeaconPublication.continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps _
  | ok input => exact later input

private theorem uniform_keeps (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (allowed : ∀ before, (work.run before).AllQueriesSatisfy RegistrationNativePlatformIdentityCtxMldsaCoins.Coin) :
    Keeps (interpret joint selected placeholder censored work) := by
  intro before result possible
  have opened : (interpret joint selected placeholder censored work).run before =
      (fun returned => (returned.1.1.1, ((returned.1.1.2, returned.1.2), returned.2))) <$>
        RegistrationNativeIdentityCensorMldsaOutgoingSource.run joint selected placeholder censored (work.run before.1.1) before.1.2 before.2 := by
    simp only [interpret, StateT.run, RegistrationNativeIdentityCensorMldsaOutgoingSource.run, bind_pure_comp]
  rw [opened, support_map] at possible
  obtain ⟨returned, reached, rfl⟩ := possible
  exact congrArg (fun state => state.1.active)
    (RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_frame joint selected placeholder censored _ (allowed before.1.1) before.1.2 before.2 returned reached)

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "callback(" censored ")" => (fun query => source(censored, Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))))
local notation "encoder(" censored ")" => (fun fields => source(censored, Main (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields))))

private theorem crypto_keeps (censored : Bool) (query : RegistrationSigningShared.Spec.Domain) :
    Keeps (callback(censored) (.inl query)) := by
  intro before result possible
  cases query with
  | hash request =>
    exact congrArg (fun state => state.1.active)
      (RegistrationNativeIdentityCensorHashFrame.outgoing setup checks representation created selected placeholder request censored before result possible)
  | sign request payload digest =>
    exact congrArg (fun state => state.1.active)
      (RegistrationNativeIdentityCensorMldsaOutgoingSource.frame setup checks representation created selected index owner request placeholder censored payload digest before result possible)

private theorem encoder_keeps (censored : Bool) (fields : registration.SignedInitView) : Keeps (encoder(censored) fields) :=
  uniform_keeps setup.joint selected placeholder censored _
    (fun before => RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created _ before)

private theorem ready_keeps (censored : Bool) (pending : registration.BeaconInitReady) :
    Keeps (RegistrationNativePlatformBeaconPublication.ready (encoder(censored)) pending) := by
  unfold RegistrationNativePlatformBeaconPublication.ready
  apply continue_keeps
  intro fields
  exact bind_keeps _ _ (encoder_keeps setup checks representation created selected placeholder reserve censored fields) (fun _ => pure_keeps _)

private theorem signing_keeps (censored : Bool) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    Keeps (RegistrationNativePlatformBeaconPublication.fromSigning (callback(censored)) (encoder(censored)) payload digest pending) := by
  unfold RegistrationNativePlatformBeaconPublication.fromSigning
  apply continue_keeps
  intro request
  apply bind_keeps _ _ (crypto_keeps setup checks representation created selected index owner placeholder censored _)
  intro signature
  apply continue_keeps
  intro effect
  cases effect with
  | Ready next => exact ready_keeps setup checks representation created selected placeholder reserve censored next
  | _ => exact pure_keeps _

private theorem hash_keeps (censored : Bool) (pending : registration.BeaconInitHash) :
    Keeps (RegistrationNativePlatformBeaconPublication.fromHash (callback(censored)) (encoder(censored)) pending) := by
  unfold RegistrationNativePlatformBeaconPublication.fromHash
  apply continue_keeps
  intro request
  apply bind_keeps _ _ (crypto_keeps setup checks representation created selected index owner placeholder censored _)
  intro digest
  apply continue_keeps
  intro effect
  cases effect with
  | MldsaSigningRequested next => exact signing_keeps setup checks representation created selected index owner placeholder reserve censored _ digest next
  | _ => exact pure_keeps _

/-- All actual fingerprint/hash/ML/writer outcomes preserve the current public source-selection flag, including every rejection and failed allocation. -/
theorem fingerprint (censored : Bool) (pending : registration.BeaconFingerprint)
    (before : FullState) (result : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × FullState)
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromFingerprint (callback(censored)) (encoder(censored)) pending).run before)) :
    result.2.1.2.active = before.1.2.active := by
  apply (show Keeps (RegistrationNativePlatformBeaconPublication.fromFingerprint (callback(censored)) (encoder(censored)) pending) from ?_) before result possible
  unfold RegistrationNativePlatformBeaconPublication.fromFingerprint
  apply continue_keeps
  intro request
  apply bind_keeps _ _ (crypto_keeps setup checks representation created selected index owner placeholder censored _)
  intro digest
  apply continue_keeps
  intro effect
  cases effect with
  | HashRequested next => exact hash_keeps setup checks representation created selected index owner placeholder reserve censored next
  | _ => exact pure_keeps _

/-- After selection, the source's role-separated PQ service and every later original publication branch keep the selected callback active. -/
theorem pq (censored : Bool) (pending : registration.BeaconEd25519Signing) (stage : pending.stage = .PqKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : FullState) (target : Pqxdh.Bytes) (held : before.1.2.target = some target)
    (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (result : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × FullState)
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromEd (callback(censored)) (encoder(censored)) pending).run before)) :
    result.2.1.2.active = before.1.2.active := by
  obtain ⟨request, requested, role⟩ := RegistrationNativeIdentitySigningRole.request pending tagged
  have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = false := by
    simpa only [RegistrationNativeIdentitySigningRole.slot, stage] using role
  rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def] at possible
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨⟨reply, middle⟩, called, later⟩ := possible
  have current := RegistrationNativeIdentityCensorEdForwardSource.frame setup checks representation created selected index owner request placeholder censored before target held targetRole currentRole (reply, middle) called
  have active : middle.1.2.active = before.1.2.active := congrArg (fun state => state.1.active) current
  obtain ⟨effect, resumed, facts⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_resume_refines pending reply
  rw [resumed] at later
  cases effect <;> simp only [BeaconcryptCore.Refinement.RegistrationSigning.EdReplyTransition, stage] at facts
  case Rejected previous =>
    change result ∈ support (pure (.ok (.Err previous), middle) : ProbComp _) at later
    rw [support_pure, Set.mem_singleton_iff] at later
    subst result
    exact active
  case Ed25519SigningRequested next => exact facts.2.elim
  case FingerprintRequested next =>
    exact (fingerprint setup checks representation created selected index owner placeholder reserve censored next middle result later).trans active

private theorem selected_current (censored : Bool) (request : registration.Ed25519SigningRequest)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : TranscriptAuthParts.absSlice request.message ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    (callback(censored) (.inr request)).run before =
      pure (RegistrationAuthenticationShared.openedBytes (some ((if censored then placeholder else setup.joint.sign seed (TranscriptAuthParts.absSlice request.message)).toList ++ TranscriptAuthParts.absSlice request.message)),
        RegistrationNativeIdentityCensorEdOutgoingSource.after selected index (TranscriptAuthParts.absSlice request.message)
          (setup.joint.sign seed (TranscriptAuthParts.absSlice request.message))
          (if censored then placeholder else setup.joint.sign seed (TranscriptAuthParts.absSlice request.message))
          (RegistrationNativeIdentityCensorFirstSource.chosenFull (TranscriptAuthParts.absSlice request.message) before)) := by
  rw [RegistrationNativeIdentityCensorFirstSource.current_equal setup checks representation created selected index owner placeholder censored request before seed handle publicKey role armed held sourceTarget fresh found]
  cases censored with
  | false =>
    exact RegistrationNativeIdentityCensorEdOutgoingSource.real setup checks representation created selected index owner request placeholder
      (RegistrationNativeIdentityCensorFirstSource.chosenFull (TranscriptAuthParts.absSlice request.message) before) seed handle publicKey rfl rfl role found
  | true =>
    exact RegistrationNativeIdentityCensorEdOutgoingSource.censored setup checks representation created selected index owner request placeholder
      (RegistrationNativeIdentityCensorFirstSource.chosenFull (TranscriptAuthParts.absSlice request.message) before) seed handle publicKey rfl rfl role found

/-- Every reached result after the first actual selected one-time call retains active=true. The current key gate, genuine source row, adaptive selection and all later primitive/writer leaves are discharged from their literal bodies. -/
theorem one_time (censored : Bool) (pending : registration.BeaconEd25519Signing) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) (stage : pending.stage = .OneTimeKey)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (before : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (publicKey : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519)
    (armed : before.1.2.armed = true) (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : PqxdhRefinement.absBytes pending.state.started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed)
    (result : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × FullState)
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromEd (callback(censored)) (encoder(censored)) pending).run before)) :
    result.2.1.2.active = true := by
  obtain ⟨actual, run, _key, _role, bytes⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_request_exact pending
  cases RustM.ok.inj (run.symm.trans requested)
  have messageEq : TranscriptAuthParts.absSlice request.message = PqxdhRefinement.absBytes pending.state.started.message.one_time_key :=
    congrArg (List.map PqxdhRefinement.absByte) (by simpa only [BeaconcryptCore.Refinement.RegistrationSigning.signingMessageValues, stage] using bytes)
  have role : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
    rw [messageEq]
    exact tagged.2.1
  have current := selected_current setup checks representation created selected index owner placeholder censored request before seed handle publicKey role armed held sourceTarget (messageEq.symm ▸ fresh) found
  rw [messageEq] at current
  let signature := if censored then placeholder else setup.joint.sign seed (PqxdhRefinement.absBytes pending.state.started.message.one_time_key)
  have admitted := RegistrationNativeIdentityCensorReply.admitted pending signature stage
  obtain ⟨next, resumed, nextStage, _copied, _restored⟩ := RegistrationNativeIdentityEdProgress.one_time pending
    (RegistrationNativeIdentityCensorReply.buffer signature pending.state.started.message.one_time_key).to_slice stage admitted.1 admitted.2
  have nextTagged := RegistrationNativeIdentitySigningRole.preserved pending tagged _ _ resumed
  change RegistrationNativeIdentitySigningRole.Tagged next.state.started at nextTagged
  rw [← RegistrationNativeIdentityCensorReply.packed signature _] at resumed
  rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def] at possible
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind] at possible
  rw [current] at possible
  simp only [pure_bind] at possible
  rw [resumed] at possible
  exact pq setup checks representation created selected index owner placeholder reserve censored next nextStage nextTagged
    (RegistrationNativeIdentityCensorEdOutgoingSource.after selected index (PqxdhRefinement.absBytes pending.state.started.message.one_time_key)
      (setup.joint.sign seed (PqxdhRefinement.absBytes pending.state.started.message.one_time_key)) signature
      (RegistrationNativeIdentityCensorFirstSource.chosenFull (PqxdhRefinement.absBytes pending.state.started.message.one_time_key) before))
    (PqxdhRefinement.absBytes pending.state.started.message.one_time_key) rfl tagged.2.1 result possible

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail.fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail.fingerprint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail.pq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail.pq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTail.one_time
