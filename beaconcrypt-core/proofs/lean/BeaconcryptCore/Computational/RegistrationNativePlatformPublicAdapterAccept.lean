-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptLookup
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptInstrumentedSource
/-! Acceptance executes the actual instrumented SDK body on the retained physical backend. Source object getters and replay containers use the same persistent platform leaves; authentication and agreement share the actual physical cache. The source receipt is retained jointly with the original SDK word and full backend/platform state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterLeaves (localOperations containerOperations)
variable {n : Nat} {I KemSK Reader Response P : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable (locals : LocalOperations (RustT (StateT P ProbComp)))
variable (containers : ContainerOperations (RustT (StateT P ProbComp)))
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "NativeM"=>StateT Native (StateT P ProbComp)

noncomputable def binding (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (self : beaconcrypt_public_wrapper.server.Server) : pqxdh.ServerBinding :=
  ⟨view.edPublic (platform.arcView self.identity).identity_key.public_key,
    (platform.arcView self.identity).identity_key_kid⟩

noncomputable def program {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R) :
    StateT (Backend n KemSK) (StateT P ProbComp)
      (AdapterPublicServerReservationReceipt.Receipt R×RustM (AdapterPublicServerAgreementReceipt.Word R)) :=
  match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>pure (none,.ok (.None,self,rng))
  | some packet=>do
    let checked←fun before=>simulateQ coins
      ((RegistrationNativePlatformPublicAdapterAuthentication.prefixProgram setup checks representation created verify
        self.control (binding view self) (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey packet).run before)
    match checked with
    | .fail error=>pure (none,.fail error)
    | .div=>pure (none,.div)
    | .ok .None=>pure (none,.ok (.None,self,rng))
    | .ok (.Some pending)=>RegistrationNativePlatformPublicAdapterAcceptLookup.lookup containers coins generator self pending rng

theorem program_source {E R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R) (before : Native)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀key,(@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run=pure (.ok (view.edPublic key)))
    (mlGetter : ∀identity,(locals.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey)) :
    let : LocalOperations (RustT NativeM):=localOperations locals
    let : ContainerOperations (RustT NativeM):=containerOperations containers
    Prod.map id backend <$>
      (AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng).run before=
      (program containers coins setup checks verify representation created generator view self input rng).run (backend before) := by
  let : LocalOperations (RustT NativeM):=localOperations locals
  let : ContainerOperations (RustT NativeM):=containerOperations containers
  have getter : ∀identity,((localOperations (S:=Native) locals).auth_MldsaIdentity_public_key identity).run=
      pure (.ok (view.mldsa identity).publicKey) := by
    intro identity
    change StateT.lift (locals.auth_MldsaIdentity_public_key identity).run=_
    rw [mlGetter]
    apply StateT.ext
    intro state
    simp only [StateT.run_lift,StateT.run_pure,pure_bind]
  have bound : before.server.pin.binding=binding view self := by
    exact congrArg₂ pqxdh.ServerBinding.mk
      (related.pinIdentity.trans related.identity.publicKey.symm)
      (related.pinIdentifier.trans related.identity.identifier.symm)
  have publicKey : before.server.pin.public_key=(view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey:=
    related.pinMldsa.trans (congrArg RegistrationNativeMldsa.Credential.publicKey related.identity.mldsa).symm
  dsimp only
  rw [AdapterPublicServerEntryReceipt.source_joint coins setup codec route verify edLaws recording writer generator
    self input rng view views created credential before related edGetter getter]
  unfold program
  cases decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>simp only [map_pure,StateT.run_pure];rfl
  | some packet=>
    simp only [StateT.run_bind,map_bind]
    dsimp only [StateT.run]
    rw [bound,publicKey]
    have prefixLaw:=RegistrationNativePlatformPublicAdapterAuthentication.prefix_source
      setup checks representation created coins codec route verify edLaws self.control (binding view self)
      (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey packet before
    dsimp only [StateT.run] at prefixLaw
    rw [←prefixLaw,bind_map_left]
    apply bind_congr
    rintro ⟨checked,current⟩
    cases checked with
    | fail error | div=>simp only [map_pure];rfl
    | ok optional=>cases optional with
      | none=>simp only [map_pure];rfl
      | some pending=>exact RegistrationNativePlatformPublicAdapterAcceptLookup.lookup_source containers coins generator self pending rng current

theorem instrumented_source {E R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R)
    (before : Native) (previous : P)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀key,(@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run=pure (.ok (view.edPublic key)))
    (mlGetter : ∀identity,(locals.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey)) :
    let : LocalOperations (RustT NativeM):=localOperations locals
    let : ContainerOperations (RustT NativeM):=containerOperations containers
    Prod.map id (Prod.map backend id) <$>
      RegistrationNativePlatformSdkAcceptInstrumentedSource.source coins setup codec route verify edLaws recording writer
        generator self input rng before previous=
      (fun result=>(RegistrationNativePlatformSdkAcceptInstrumentedSource.reply result.1.1.1 result.1.1.2,(result.1.2,result.2))) <$>
        ((program containers coins setup checks verify representation created generator view self input rng).run (backend before)).run previous := by
  let : LocalOperations (RustT NativeM):=localOperations locals
  let : ContainerOperations (RustT NativeM):=containerOperations containers
  have relatedCharged:=AdapterPublicServerAcceptDispatch.material_retained view views created credential self before related input
  have law:=program_source locals containers coins setup codec checks route verify representation created generator edLaws
    recording writer view views credential self input rng (AdapterPublicServerAcceptDispatch.charged input before) relatedCharged edGetter mlGetter
  have mapped:=congrArg (fun computation=>(fun result=>(RegistrationNativePlatformSdkAcceptInstrumentedSource.reply
      result.1.1.1 result.1.1.2,(result.1.2,result.2))) <$>computation.run previous) law
  have kept : backend (AdapterPublicServerAcceptDispatch.charged input before)=backend before := by
    unfold AdapterPublicServerAcceptDispatch.charged
    cases RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) <;> rfl
  dsimp only
  unfold RegistrationNativePlatformSdkAcceptInstrumentedSource.source
    RegistrationNativePlatformExtractedSdkServer.Accept.run AdapterPublicServerAcceptDispatch.entry
  dsimp only [StateT.run]
  simp only [StateT.run_map,Functor.map_map,kept] at mapped
  simpa only [Functor.map_map,Prod.map,id_eq,StateT.run] using mapped

noncomputable def committed {R : Type}
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (returned : RegistrationNativePlatformSdkAcceptInstrumentedSource.Word R) (raw : Backend n KemSK×P) : Backend n KemSK×P :=
  let auxiliary:=match returned.1 with
    | some (.ok ((_,_),capture))=>AdapterPublicAgreementServerWorld.project view capture
    | _=>raw.1.auxiliary
  let attempts:=(raw.1.world.server.map (fun records=>records.records.rawAttempts)).getD 0
  let server:=AdapterPublicOrdinaryServerReifier.server view views returned.2.2.1 attempts
  (⟨auxiliary,raw.1.pool,RegistrationNativePlatformSdkReification.worldBackend {raw.1.world with server:=some server}⟩,raw.2)

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] original in
theorem snapshot_source {R : Type}
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (input : Slice U8) (before : Native)
    (returned : RegistrationNativePlatformSdkAcceptInstrumentedSource.Word R) (raw : Native×P) :
    RegistrationNativePlatformSdkReification.persistent
      (RegistrationNativePlatformSdkAcceptInstrumentedSource.sourceSnapshot view views input before returned raw).committed=
      committed view views returned (RegistrationNativePlatformSdkReification.persistent raw) := by
  rcases returned with ⟨receipt,word⟩
  cases receipt with
  | none=>
    simp only [RegistrationNativePlatformSdkAcceptInstrumentedSource.sourceSnapshot,
      RegistrationNativePlatformSdkServerReification.snapshot,RegistrationNativePlatformSdkServerReification.acceptEnvironment,
      RegistrationNativePlatformSdkServerReification.rawAttempts,
      RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot.committed,committed,
      RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
      RegistrationNativePlatformSdkReification.worldBackend,Function.update_idem]
  | some receipt=>
    cases receipt with
    | fail error | div=>
      simp only [RegistrationNativePlatformSdkAcceptInstrumentedSource.sourceSnapshot,
        RegistrationNativePlatformSdkServerReification.snapshot,RegistrationNativePlatformSdkServerReification.acceptEnvironment,
        RegistrationNativePlatformSdkServerReification.rawAttempts,
        RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot.committed,committed,
        RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
        RegistrationNativePlatformSdkReification.worldBackend,Function.update_idem]
    | ok captured=>
      simp only [RegistrationNativePlatformSdkAcceptInstrumentedSource.sourceSnapshot,
        RegistrationNativePlatformSdkServerReification.snapshot,RegistrationNativePlatformSdkServerReification.acceptEnvironment,
        RegistrationNativePlatformSdkServerReification.rawAttempts,
        RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot.committed,committed,
        RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
        RegistrationNativePlatformSdkReification.commitEnvironment,RegistrationWorldAgreementCompiler.join,
        RegistrationNativePlatformSdkReification.worldBackend,Function.update_idem]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept.instrumented_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept.instrumented_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept.snapshot_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept.snapshot_source
