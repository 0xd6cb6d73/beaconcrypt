-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache
import BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin

/-! Actual source acceptance uses the reached cached stored pin and mandatory authentication. Its literal replay/reservation/agreement suffix keeps the authentication summary, so protected unsigned-origin failure is a same-cut weak forgery or a retained shared-cache collision. This is a statement about the corrected source callback, with every platform poststate retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInitOrigin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeInitAuthentication (withWorld)
open RegistrationNativeInitFinal (summary)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationWorldAuthentication.begin RegistrationServerNativeSource.authenticate
  RegistrationAuthenticationShared.begin
  RegistrationNativePlatformSourceAccept.accept RegistrationSigningShared.historyFor RegistrationAuthenticationNative.trial

/-- The original displayed-key origin event is covered at the actual returned source acceptance cut. -/
theorem accept (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (before after : State n) (previous next : Platform) (handle : Nat)
    (supported : ((.ok (some handle), after), next) ∈ support
      (((RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route source.verify representation created packet).run before).run previous))
    (pinned : RegistrationNativeServerPinRecompute.Cached before.pin before.world.world.1.primitive.2)
    (cached : RegistrationSigningShared.Cached (summary before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial true before.pin packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before)))) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash after.world.world.1.primitive.2) source.verify
      (RegistrationAuthenticationNative.trial true before.pin packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before))) ∨
      CacheHasCollision after.world.world.1.primitive.2 := by
  obtain ⟨cut⟩ := RegistrationNativePlatformAcceptCut.accept coins setup codec checks reserve route source.verify representation created
    packet before after previous next handle supported
  have pinCalled := cut.pinCalled
  rw [RegistrationNativePlatformSourceBuild.pin_hit coins before pinned] at pinCalled
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at pinCalled
  have pinSummary : summary cut.pinned = summary before := congrArg (fun result => summary result.1.2) pinCalled
  have stored := (RegistrationNativePlatformAcceptCut.pin_fields coins setup codec checks reserve route source.verify representation created
    packet before after previous next handle cut pinned).2
  have authenticated := RegistrationNativePlatformAcceptCut.authentication coins setup codec checks reserve route source.verify
    representation created packet before after previous next handle cut pinned
  rw [RegistrationNativeInitAuthentication.authenticate setup codec route source.verify created packet cut.pinned, support_map] at authenticated
  obtain ⟨⟨reply, middle⟩, called, same⟩ := authenticated
  have replyEq : reply = .ok (cut.events, .Accepted cut.authenticated) := congrArg Prod.fst same
  cases replyEq
  have checked : cut.checked = withWorld cut.pinned middle := (congrArg Prod.snd same).symm
  have finalSummary := RegistrationNativePlatformAcceptCache.afterAuthentication coins setup checks reserve representation created packet
    cut.authenticated cut.checked cut.authPlatform ((.ok (some handle), after), next) cut.continued
  have finalCache : after.world.world.1.primitive.2 = middle.primitive.2 := by
    exact (congrArg Prod.snd finalSummary).trans (congrArg (fun state => (summary state).2) checked)
  rw [finalCache]
  have historyCached := RegistrationSigningShared.history_cached (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before) cached
  have pinCache : cut.pinned.world.world.1.primitive.2 = before.world.world.1.primitive.2 := congrArg (fun value : RegistrationSigningShared.State => value.2) pinSummary
  change MldsaSharedAuthentication.HistoryCached before.world.world.1.primitive.2 _ at historyCached
  rw [← pinCache] at historyCached
  rw [stored] at called
  exact RegistrationAuthenticationNative.begin_origin_split setup.source.crypto source.verify codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) before.pin packet
    (RegistrationWorldAuthentication.project cut.pinned.world.world.1) (RegistrationWorldAuthentication.project middle)
    cut.events cut.authenticated
    (RegistrationWorldAuthentication.begin_native_support setup codec route source.verify before.pin packet cut.pinned.world.world.1 middle
      cut.events cut.authenticated called) true rfl
    (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before))
    historyCached absent

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The literal corrected typed accept is covered using its reached stored-pin cache receipt. -/
theorem typed {E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (packet : registration.InitPacket) (before after : RegistrationNativeExperiment.State n KemSK source)
    (previous next : Platform) (handle : Nat)
    (supported : ((.ok (some handle), after), next) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer (.inr (.accept packet))).run before).run previous))
    (pinned : RegistrationNativeServerPinRecompute.Cached before.server.pin before.server.world.world.1.primitive.2)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial true before.server.pin packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (RegistrationNativeMldsaShared.nativeProject before)))) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash after.server.world.world.1.primitive.2) source.verify
      (RegistrationAuthenticationNative.trial true before.server.pin packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (RegistrationNativeMldsaShared.nativeProject before))) ∨
      CacheHasCollision after.server.world.world.1.primitive.2 := by
  simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at supported
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at supported
  obtain ⟨⟨⟨reply, current⟩, platform⟩, called, same⟩ := supported
  have replyEq : reply = .ok (some handle) := congrArg (fun result => result.1.1) same
  have stateEq : current = after.server := congrArg (fun result => result.1.2.server) same
  cases replyEq
  have actual := accept coins setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration route representation created packet
    before.server current previous platform handle called pinned cached absent
  have summaryEq : summary before.server = RegistrationNativeMldsaShared.nativeProject before := rfl
  rw [summaryEq] at actual
  simpa only [stateEq] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformInitOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitOrigin.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitOrigin.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitOrigin.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitOrigin.typed
