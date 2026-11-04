-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
/-! The selected concrete SDK constructor commits the actual returned object, RNG and captured source backend. This joins the complete source primitive execution to the same supported Carrier continuation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

variable {n : Nat} {I KemSK R Error P : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto : CryptoOperations (RustT ProbComp)]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
local notation "SourceM" => AdapterBeaconConstructorNative.M n KemSK mlSource RegistrationServerRoleBackend.State (StateT P ProbComp)
local notation "PhysicalM" => StateT (Backend n KemSK) (StateT P ProbComp)


variable (sourcePrevious : ChildOperations (RustT (AdapterBeaconConstructorNative.M n KemSK mlSource RegistrationServerRoleBackend.State (StateT P ProbComp))))
variable (physicalPrevious : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (generator : rand_core.TryCryptoRng R Error) (kem : AdapterBeaconConstructorKem.Representation view R)
variable (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view (RegistrationNativeMldsa.generate mlSource))
variable (signing : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint PqxdhJointIdentity.sampleSeed)
variable (prekey : AdapterBeaconConstructorGeneration.KxContract generator view
  (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
variable (kemContract : RegistrationNativePlatformPublicAdapterCreateKem.Contract view setup kem generator)
variable (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential mlSource)
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
open RegistrationNativePlatformPublicAdapterStore (Store erase)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep returned returned_exact store)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (strongPhysical)

include coins checks representation physicalPrevious generator in
noncomputable def run (keyId : U64) (identityKey mlKey : Slice U8) (before : Store n KemSK R P) :
    ProbComp (RustM (Option Nat × Store n KemSK R P) × (Backend n KemSK × P)) :=
  RegistrationNativePlatformPublicAdapterCreateStore.run
    (RegistrationNativePlatformPublicAdapterCreateSource.physical coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey before.rng) before

include coins checks representation sourcePrevious generator kem ml signing prekey kemContract in
noncomputable abbrev active (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize)
    (identityKey mlKey : Slice U8)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey=.ok (.Ok serverId))
    (parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mlKey=.ok (.Ok mlPin))
    (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (Prod.map RegistrationNativeRawAdapter.resultOption id <$>
        (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
          (((RegistrationNativePlatformExperiment.liftNative coins
            (RegistrationNativeExperiment.beacon setup checks representation created
              (RegistrationNativeBeaconFrontend.create setup mlSource (view.edPublic serverId) mlPin keyId))).run current.1).run current.2))) :=
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceGenerators coins setup checks representation created view
  let : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
  let : ChildOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children sourcePrevious (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
  let leaves := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceLeaves coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract
  RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
    (RegistrationNativePlatformSdkStrongCreateStep.total coins setup checks representation created generator view kem leaves views credential
      keyId serverId mlPin identityKey mlKey parsed parsedMl current.1 current.2 before)

omit material platform ed original originalCrypto in
private theorem source_eq {N Reply S : Type} {Private : N → Type} {model : ProbComp (Reply × N)}
    (call : TotalStep Private model) (first : {packet //packet∈support call.step.sample} → S)
    (update : RustM call.step.sourceType × N → S)
    (retained : ∀packet,first packet=update (call.step.sourceReply packet.val,call.step.sourceState packet.val)) :
    first <$> PFunctor.FreeM.attachSupp call.step.sample = update <$> call.step.sourceCall := by
  rw [← call.step.source_exact,Functor.map_map]
  have law := congrArg (fun work => (fun packet => update (call.step.sourceReply packet,call.step.sourceState packet)) <$> work)
    (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
  simp only [Functor.map_map] at law
  rw [← law]
  congr 1
  funext packet
  exact retained packet

theorem active_stored (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize)
    (identityKey mlKey : Slice U8)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey=.ok (.Ok serverId))
    (parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mlKey=.ok (.Ok mlPin))
    (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    let call := active coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential keyId serverId mlPin identityKey mlKey parsed parsedMl current before
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (strongPhysical setup view views created credential) call =
      (fun result => RegistrationNativePlatformPublicAdapterCreateStore.finish (erase before.base.objects) result.1
        (RegistrationNativePlatformSdkReification.persistent result.2)) <$> call.step.sourceCall := by
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceGenerators coins setup checks representation created view
  let : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
  let : ChildOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children sourcePrevious (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
  let leaves := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceLeaves coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract
  let call := active coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential keyId serverId mlPin identityKey mlKey parsed parsedMl current before
  unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
  apply source_eq call
  intro packet
  have normal := returned_exact call packet
  change RustM.ok packet.val.1.1.1.1.outcome=RustM.ok (returned call packet) at normal
  have actual : returned call packet=packet.val.1.1.1.1.outcome := (RustM.ok.inj normal).symm
  have kept : (store call packet).base.objects = RegistrationNativePlatformExtractedSdkCarrierCreate.update
      before.base.objects packet.val.1.1.1.1.outcome (.direct (packet.val.1.1.1.1.sourceAfter,packet.val.2)) := by
    change (RegistrationNativePlatformExtractedSdkCarrierCreate.putPacket coins setup checks representation created generator view kem leaves views credential
      keyId serverId mlPin current.1 current.2 before.base packet.val packet.property).objects = _
    exact RegistrationNativePlatformExtractedSdkCarrierCreate.putPacket_objects coins setup checks representation created generator view kem leaves views credential
      keyId serverId mlPin current.1 current.2 before.base packet.val packet.property
  change (RustM.ok (call.observe (returned call packet),erase (store call packet).base.objects),
    (erase (store call packet).base.objects).backend) = _
  rw [actual,kept,RegistrationNativePlatformPublicAdapterStore.create_update]
  change (RustM.ok (RegistrationNativeRawAdapter.resultOption
    (RegistrationNativePlatformExtractedSdkCreateCommit.observe current.1.beacons.length packet.val.1.1.1.1.outcome),
      RegistrationNativePlatformPublicAdapterStore.create (erase before.base.objects) packet.val.1.1.1.1.outcome
        (RegistrationNativePlatformSdkReification.persistent (packet.val.1.1.1.1.sourceAfter,packet.val.2))),
    (RegistrationNativePlatformPublicAdapterStore.create (erase before.base.objects) packet.val.1.1.1.1.outcome
      (RegistrationNativePlatformSdkReification.persistent (packet.val.1.1.1.1.sourceAfter,packet.val.2))).backend) = _
  have payload : call.step.sourceReply packet.val=.ok packet.val.1.1.1.1.outcome := rfl
  have captured : call.step.sourceState packet.val=(packet.val.1.1.1.1.sourceAfter,packet.val.2) := rfl
  rw [payload,captured]
  have count := before.base.ownerCount
  change before.base.objects.nextOwner=current.1.beacons.length at count
  simp only [RegistrationNativePlatformPublicAdapterCreateStore.finish,RegistrationNativePlatformExtractedSdkCreateCommit.observe,
    RegistrationNativeRawAdapter.resultOption,RegistrationNativePlatformPublicAdapterStore.create,
    RegistrationNativePlatformPublicAdapterStore.erase,count]
  rfl

theorem active_source (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize)
    (identityKey mlKey : Slice U8)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey=.ok (.Ok serverId))
    (parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mlKey=.ok (.Ok mlPin))
    (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    let call := active coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential keyId serverId mlPin identityKey mlKey parsed parsedMl current before
    Prod.map id RegistrationNativePlatformSdkReification.persistent <$> call.step.sourceCall =
      (fun result : (RustM (AdapterBeaconConstructorBody.Outcome R) × Backend n KemSK) × P => (result.1.1,(result.1.2,result.2))) <$>
        ((RegistrationNativePlatformPublicAdapterCreateSource.physical coins setup checks representation created view physicalPrevious generator
          keyId identityKey mlKey before.base.objects.rng).run.run (backend current.1)).run current.2 := by
  have law := RegistrationNativePlatformPublicAdapterCreateSource.full_platform coins setup checks representation created view generator kem ml signing prekey kemContract
    sourcePrevious physicalPrevious keyId identityKey mlKey before.base.objects.rng current.1 current.2
  have packed := congrArg (fun work => (fun result => (result.1.1,(result.1.2,result.2))) <$> work) law
  simpa only [active,RegistrationNativePlatformPublicAdapterReply.map,RegistrationNativePlatformSdkStrongCreateStep.total,
    RegistrationNativePlatformExtractedSdkCreateStep.total,RegistrationNativePlatformPublicAdapterCreateSource.source,
    Functor.map_map,RegistrationNativePlatformExtractedSdkAdaptive.pack,
    RegistrationNativePlatformSdkReification.persistent,Prod.map_def,id_eq] using packed

theorem active_physical (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize)
    (identityKey mlKey : Slice U8)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey=.ok (.Ok serverId))
    (parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mlKey=.ok (.Ok mlPin))
    (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    let call := active coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential keyId serverId mlPin identityKey mlKey parsed parsedMl current before
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (strongPhysical setup view views created credential) call =
      run coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey (erase before.base.objects) := by
  dsimp only
  refine (active_stored coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential
    keyId serverId mlPin identityKey mlKey parsed parsedMl current before).trans ?_
  have law := active_source coins setup checks representation created view sourcePrevious physicalPrevious generator kem ml signing prekey kemContract views credential
    keyId serverId mlPin identityKey mlKey parsed parsedMl current before
  have mapped := congrArg (fun work => (fun result => RegistrationNativePlatformPublicAdapterCreateStore.finish (erase before.base.objects) result.1 result.2) <$> work) law
  simp only [Functor.map_map,Prod.map_def,id_eq] at mapped
  conv_rhs at mapped => erw [Functor.map_map]
  have basis : (erase before.base.objects).backend=RegistrationNativePlatformSdkReification.persistent current := before.base.backend
  unfold run RegistrationNativePlatformPublicAdapterCreateStore.run
  rw [basis]
  simpa only [Functor.map_map,RegistrationNativePlatformPublicAdapterStore.erase,RegistrationNativePlatformSdkReification.persistent] using mapped


noncomputable abbrev refused
    (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (keyId : U64) (identityKey mlKey : Slice U8) (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bad : PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=none ∨
      RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=none) :=
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceGenerators coins setup checks representation created view
  let : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
  let : ChildOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children sourcePrevious (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
  RegistrationNativePlatformPublicAdapterCreateDispatch.refused setup created generator view views credential parsing keyId identityKey mlKey current before bad

theorem refused_physical
    (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (keyId : U64) (identityKey mlKey : Slice U8) (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bad : PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=none ∨
      RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=none) :
    let call := refused coins setup checks representation created view sourcePrevious generator views credential parsing keyId identityKey mlKey current before bad
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (strongPhysical setup view views created credential) call =
      run coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey (erase before.base.objects) := by
  let call := refused coins setup checks representation created view sourcePrevious generator views credential parsing keyId identityKey mlKey current before bad
  have stored : RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (strongPhysical setup view views created credential) call =
      (fun result => RegistrationNativePlatformPublicAdapterCreateStore.finish (erase before.base.objects) result.1
        (RegistrationNativePlatformSdkReification.persistent result.2)) <$> call.step.sourceCall := by
    unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
    apply source_eq call
    intro packet
    change (RustM.ok (none,erase before.base.objects),(erase before.base.objects).backend) =
      RegistrationNativePlatformPublicAdapterCreateStore.finish (erase before.base.objects) (.ok (.Err (),before.base.objects.rng))
        (RegistrationNativePlatformSdkReification.persistent before.base.objects.snapshot.committed)
    exact (RegistrationNativePlatformPublicAdapterCreateStore.rejected (erase before.base.objects)).symm
  have called : pure (RustM.ok ((.Err (),before.base.objects.rng) : AdapterBeaconConstructorBody.Outcome R),before.base.objects.snapshot.committed) = call.step.sourceCall := by
    have law := call.step.source_exact
    simpa only [call,refused,RegistrationNativePlatformPublicAdapterCreateDispatch.refused,map_pure] using law
  have normalRaw : RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (strongPhysical setup view views created credential) call =
      pure (.ok (none,erase before.base.objects),(erase before.base.objects).backend) := by
    rw [stored,←called]
    erw [map_pure]
    exact congrArg pure (RegistrationNativePlatformPublicAdapterCreateStore.rejected (erase before.base.objects))
  refine normalRaw.trans ?_
  symm
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.physicalGenerators coins setup checks representation created view
  let : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created)
  let : ChildOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children physicalPrevious (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created)
  exact RegistrationNativePlatformPublicAdapterCreateStore.invalid view parsing generator keyId identityKey mlKey (erase before.base.objects) bad


omit material platform ed original originalCrypto in
private noncomputable def modelCast {N Reply : Type} {Private : N → Type}
    {left right : ProbComp (Reply × N)} (same : left=right) (call : TotalStep Private left) : TotalStep Private right :=
  same ▸ call

omit original originalCrypto in
private theorem raw_cast {N Reply : Type} {Private : N → Type}
    {left right : ProbComp (Reply × N)} (same : left=right) (call : TotalStep Private left)
    (physical : ∀current,Private current → Store n KemSK R P) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical (modelCast same call) =
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical call := by
  cases same
  rfl

def Valid (identityKey mlKey : Slice U8) : Prop :=
  ∃identity : Std.Array U8 32#usize, ∃ml : Std.Array U8 1952#usize,
    PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=some identity ∧
    RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=some ml

omit material platform ed original originalCrypto in
private theorem invalid (identityKey mlKey : Slice U8) (bad : ¬Valid identityKey mlKey) :
    PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=none ∨
      RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=none := by
  cases identity : PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey) with
  | none => exact Or.inl rfl
  | some bytes =>
    cases ml : RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey) with
    | none => exact Or.inr rfl
    | some mlBytes => exact False.elim (bad ⟨bytes,mlBytes,identity,ml⟩)

omit platform original originalCrypto in
private theorem command_selected (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (keyId : U64) (identityKey mlKey : Slice U8) (current : Native × P)
    (identity : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize)
    (parsed : PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=some identity)
    (parsedMl : RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=some mlPin) :
    (Prod.map RegistrationNativeRawAdapter.resultOption id <$>
      (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
        (((RegistrationNativePlatformExperiment.liftNative coins
          (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeBeaconFrontend.create setup mlSource (view.edPublic (parsing.object identity)) mlPin keyId))).run current.1).run current.2))) =
    RegistrationNativePlatformPublicAdapterCreateDispatch.command coins setup checks representation created keyId identityKey mlKey current := by
  unfold RegistrationNativePlatformPublicAdapterCreateDispatch.command
  rw [parsed,parsedMl,parsing.publicBytes]

noncomputable def dispatch (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (keyId : U64) (identityKey mlKey : Slice U8) (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (RegistrationNativePlatformPublicAdapterCreateDispatch.command coins setup checks representation created keyId identityKey mlKey current) := by
  classical
  exact if valid : Valid identityKey mlKey then
    let identity := Classical.choose valid
    let mlPin := Classical.choose (Classical.choose_spec valid)
    let fields := Classical.choose_spec (Classical.choose_spec valid)
    let call := active coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential
      keyId (parsing.object identity) mlPin identityKey mlKey
      (RegistrationNativePlatformPublicAdapterPinParsing.ed_decoded view parsing identityKey identity fields.1)
      (RegistrationNativePlatformPublicAdapterPinParsing.ml_decoded mlKey mlPin fields.2) current before
    modelCast (command_selected coins setup checks representation created view parsing keyId identityKey mlKey current identity mlPin fields.1 fields.2) call
  else
    let bad := invalid identityKey mlKey valid
    let call := refused coins setup checks representation created view sourcePrevious generator views credential parsing keyId identityKey mlKey current before bad
    modelCast (by
      symm
      unfold RegistrationNativePlatformPublicAdapterCreateDispatch.command
      rcases bad with identity | ml
      · rw [identity]
      · rw [ml]
        cases PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey) <;> rfl) call

theorem query (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (keyId : U64) (identityKey mlKey : Slice U8) (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (strongPhysical setup view views created credential)
      (dispatch coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential parsing keyId identityKey mlKey current before) =
    run coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey (erase before.base.objects) := by
  classical
  by_cases valid : Valid identityKey mlKey
  · simp only [dispatch,dite_eq_left valid,raw_cast]
    exact active_physical coins setup checks representation created view sourcePrevious physicalPrevious generator kem ml signing prekey kemContract views credential
      keyId (parsing.object (Classical.choose valid)) (Classical.choose (Classical.choose_spec valid)) identityKey mlKey
      (RegistrationNativePlatformPublicAdapterPinParsing.ed_decoded view parsing identityKey (Classical.choose valid) (Classical.choose_spec (Classical.choose_spec valid)).1)
      (RegistrationNativePlatformPublicAdapterPinParsing.ml_decoded mlKey (Classical.choose (Classical.choose_spec valid)) (Classical.choose_spec (Classical.choose_spec valid)).2) current before
  · simp only [dispatch,dite_eq_right valid,raw_cast]
    exact refused_physical coins setup checks representation created view sourcePrevious physicalPrevious generator views credential parsing
      keyId identityKey mlKey current before (invalid identityKey mlKey valid)


include sourcePrevious ml signing prekey kemContract in
theorem normal (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (keyId : U64) (identityKey mlKey : Slice U8) (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (result : RustM (Option Nat × Store n KemSK R P) × (Backend n KemSK × P))
    (supported : result∈support (run coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey (erase before.base.objects))) :
    ∃reply next,result=(.ok (reply,next),next.backend) := by
  rw [←query coins setup checks representation created view sourcePrevious physicalPrevious generator kem ml signing prekey kemContract views credential parsing keyId identityKey mlKey current before,
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw] at supported
  erw [support_map] at supported
  obtain ⟨packet,_possible,same⟩ := supported
  let call := dispatch coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential parsing keyId identityKey mlKey current before
  exact ⟨call.observe (returned call packet),erase (store call packet).base.objects,same.symm⟩


end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.active_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.active_stored
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.active_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.active_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.active_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.active_physical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.refused_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.refused_physical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical.normal
