-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptPoolFrame
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {S P T A B : Type}
private def Keeps (project : S→T) (work : StateT S (StateT P ProbComp) A) : Prop :=
  ∀before previous result,result∈support ((work.run before).run previous)→project result.1.2=project before
private theorem pure_keeps (project : S→T) (value : A) : Keeps (P:=P) project (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  subst result
  rfl
private theorem bind_keeps (project : S→T) (work : StateT S (StateT P ProbComp) A)
    (next : A→StateT S (StateT P ProbComp) B)
    (first : Keeps project work) (later : ∀value,Keeps project (next value)) : Keeps project (work >>=next) := by
  intro before previous result supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  exact (later middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)
private theorem map_keeps (project : S→T) (work : StateT S (StateT P ProbComp) A)
    (f : A→B) (held : Keeps project work) : Keeps project (f <$>work) := by
  intro before previous result supported
  rw [StateT.run_map,StateT.run_map,support_map] at supported
  obtain ⟨middle,called,rfl⟩ := supported
  exact held before previous middle called
private theorem lift_keeps (project : S→T) (work : StateT P ProbComp A) : Keeps project (StateT.lift work) := by
  intro before previous result supported
  simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at supported
  obtain ⟨middle,called,rfl⟩ := supported
  rfl
variable {n : Nat} {KemSK I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "NativeM" => StateT Native (StateT P ProbComp)
private def pool (before : Native) := before.pool
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))]
omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] localOps containers in
private theorem captured (coins : QueryImpl unifSpec (StateT P ProbComp)) {R Error Value : Type}
    (generator : rand_core.TryCryptoRng R Error) (keys : AdapterPublicAgreementFields.Keys)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (rng : R) :
    Keeps pool (AdapterPublicAgreementNativePlatformInterpreter.captured (n:=n) (KemSK:=KemSK) (source:=mlSource)
      coins generator keys work rng).run := by
  intro before previous result supported
  rw [AdapterPublicAgreementNativePlatformInterpreter.captured_run] at supported
  have called := RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 supported
  rw [AdapterPublicAgreementNativeWorldInterpreter.captured_run,support_map] at called
  obtain ⟨middle,_called,returned⟩ := called
  have same := congrArg Prod.snd returned
  rw [←same]
  rfl
omit original localOps in
private theorem replay {R : Type} (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server)
    (standard : AdapterPublicServerAgreementRetention.Standard (n:=n) (KemSK:=KemSK) (mlSource:=mlSource)
      (m:=StateT P ProbComp) views self) (receipt : AdapterPublicServerAgreementReceipt.Receipt R) :
    Keeps pool (AdapterPublicServerAgreementReceipt.replay (n:=n) (KemSK:=KemSK) (source:=mlSource) (m:=StateT P ProbComp) self receipt) := by
  cases receipt with
  | fail error | div => exact pure_keeps _ _
  | ok pair =>
    rcases pair with ⟨⟨effect,journal⟩,capture⟩
    cases effect with
    | fail error =>
      simpa only [AdapterPublicServerAgreementReceipt.replay,RustT.run_bind,RustT.run_liftRust,pure_bind] using
        (pure_keeps (P:=P) (pool (n:=n) (KemSK:=KemSK) (mlSource:=mlSource)) (.fail error :RustM (AdapterPublicServerAgreementReceipt.Word R)))
    | div =>
      simpa only [AdapterPublicServerAgreementReceipt.replay,RustT.run_bind,RustT.run_liftRust,pure_bind] using
        (pure_keeps (P:=P) (pool (n:=n) (KemSK:=KemSK) (mlSource:=mlSource)) (.div :RustM (AdapterPublicServerAgreementReceipt.Word R)))
    | ok effect =>
      cases effect <;> try { exact pure_keeps _ _ }
      case ServerComplete completed =>
        rcases standard with ⟨insertion⟩
        obtain ⟨reply,operation,_footprint⟩ := insertion completed
        simp only [AdapterPublicServerAgreementReceipt.replay,RustT.run_bind,RustT.run_liftRust,pure_bind]
        rw [AdapterPublicServerToken.record,operation,pure_bind]
        exact pure_keeps _ _
omit localOps in
private theorem agreement (coins : QueryImpl unifSpec (StateT P ProbComp)) {R Error : Type}
    (generator : rand_core.TryCryptoRng R Error) (keys : AdapterPublicAgreementFields.Keys)
    (views : AdapterPublicWrapperStorage.Views) (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect)) (rng : R)
    (standard : AdapterPublicServerAgreementRetention.Standard (n:=n) (KemSK:=KemSK) (mlSource:=mlSource)
      (m:=StateT P ProbComp) views self) :
    Keeps pool (AdapterPublicServerAgreementReceipt.program (n:=n) (KemSK:=KemSK) (source:=mlSource)
      coins generator keys self work rng) := by
  unfold AdapterPublicServerAgreementReceipt.program
  apply bind_keeps _ _ _ (captured coins generator keys work rng)
  intro receipt
  apply bind_keeps _ _ _ (replay views self standard receipt)
  intro returned
  exact pure_keeps _ _
omit localOps in
private theorem reservation (coins : QueryImpl unifSpec (StateT P ProbComp)) {R Error : Type}
    (generator : rand_core.TryCryptoRng R Error) (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server) (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) (rng : R)
    (allocated : StateT P ProbComp AdapterPublicServerReservationNative.AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve (m:=NativeM) self.consumed_registrations).run =
      RustM.ok <$>StateT.lift allocated)
    (insertion : ∀history,AdapterPublicServerAgreementRetention.Standard (n:=n) (KemSK:=KemSK) (mlSource:=mlSource)
      (m:=StateT P ProbComp) views {self with consumed_registrations:=history}) :
    Keeps pool (AdapterPublicServerReservationReceipt.program (n:=n) (KemSK:=KemSK) (mlSource:=mlSource)
      coins generator self control authenticated rng) := by
  unfold AdapterPublicServerReservationReceipt.program
  rw [operation]
  apply bind_keeps _ _ _ (map_keeps _ _ _ (lift_keeps _ allocated))
  intro returned
  cases returned with
  | fail error | div => exact pure_keeps _ _
  | ok pair =>
    rcases pair with ⟨allocation,history⟩
    cases allocation with
    | Err error => exact pure_keeps _ _
    | Ok value => exact map_keeps _ _ _ (agreement coins generator _ views _ _ rng (insertion history))
omit localOps in
private theorem lookup (coins : QueryImpl unifSpec (StateT P ProbComp)) {R Error : Type}
    (generator : rand_core.TryCryptoRng R Error) (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup) (rng : R)
    (membership : ∀identifier,AdapterPublicServerReplayPrefix.contains (m:=NativeM)
      self.consumed_registrations identifier=pure (views.replay self.consumed_registrations identifier))
    (allocated : StateT P ProbComp AdapterPublicServerReservationNative.AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve (m:=NativeM) self.consumed_registrations).run =
      RustM.ok <$>StateT.lift allocated)
    (insertion : ∀history,AdapterPublicServerAgreementRetention.Standard (n:=n) (KemSK:=KemSK) (mlSource:=mlSource)
      (m:=StateT P ProbComp) views {self with consumed_registrations:=history}) :
    Keeps pool (AdapterPublicServerLookupReceipt.program (n:=n) (KemSK:=KemSK) (mlSource:=mlSource)
      coins generator self pending rng) := by
  rw [AdapterPublicServerLookupReceipt.member coins generator self pending rng _ (membership _)]
  split
  · exact pure_keeps _ _
  · exact reservation coins generator views self pending.control pending.authenticated rng allocated operation insertion

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] original localOps containers in
private theorem world {Value : Type} (work : StateT (PqxdhRecordLiftWorld.State n) (StateT P ProbComp) Value) :
    Keeps (pool (KemSK:=KemSK) (mlSource:=mlSource)) (AdapterPublicServerWorldLens.world work) := by
  intro before previous result supported
  rw [AdapterPublicServerWorldLens.world_run,StateT.run_map,support_map] at supported
  obtain ⟨middle,called,returned⟩ := supported
  have same := congrArg (fun reached=>reached.1.2) returned
  rw [←same]
  rfl
-- The Server pin is now selected purely (no fingerprint hash query), so elaboration-time whnf of the concrete authentication prefix would evaluate `begin_server_pin`; `world` only needs it as an opaque work. Proof terms are unchanged and kernel-checked.
attribute [local irreducible] AdapterPublicServerAuthenticationPrefix.program in
theorem run {E R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before after : Native) (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT Native (StateT P ProbComp)) self.consumed_registrations identifier =
        pure (views.replay self.consumed_registrations identifier))
    (allocated : StateT P ProbComp AdapterPublicServerReservationNative.AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT Native (StateT P ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := StateT P ProbComp) views {self with consumed_registrations := history})
    (receipt : AdapterPublicServerReservationReceipt.Receipt R) (word : RustM (AdapterPublicServerAgreementReceipt.Word R)) (previous next : P)
    (supported : (((receipt, word), after), next) ∈ support
      (((RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous)) : after.pool=before.pool := by
  let charged:=AdapterPublicServerAcceptDispatch.charged input before
  have held:=AdapterPublicServerAcceptDispatch.material_retained view views created credential self before related input
  change (((receipt,word),after),next)∈support (((AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng).run charged).run previous) at supported
  rw [AdapterPublicServerEntryReceipt.source_joint coins setup codec route verify edLaws recording writer generator self input rng
    view views created credential charged held edGetter mlGetter] at supported
  have chargedPool : charged.pool=before.pool := by
    unfold charged AdapterPublicServerAcceptDispatch.charged
    cases RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) <;> rfl
  cases decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none =>
    rw [decoded] at supported
    simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq] at supported
    exact supported.1.2 ▸ chargedPool
  | some packet =>
    rw [decoded] at supported
    simp only [StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨⟨⟨checked,current⟩,middle⟩,called,continued⟩ := supported
    have kept : current.pool=before.pool := (world _ charged previous _ called).trans chargedPool
    cases checked with
    | fail error | div =>
      simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq] at continued
      exact continued.1.2 ▸ kept
    | ok optional => cases optional with
      | none =>
        simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq] at continued
        exact continued.1.2 ▸ kept
      | some pending => exact (lookup coins generator views self pending rng membershipOperation allocated operation insertion current middle _ continued).trans kept
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptPoolFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptPoolFrame.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptPoolFrame.run
