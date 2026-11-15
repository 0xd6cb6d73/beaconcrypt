-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
import BeaconcryptCore.Refinement.AdapterPublicBundleMaterial
/-! Direct source Bundle primitive dictionaries use the actual opaque identity and signing request on the physical backend. They keep real primitive randomness/cache/platform effects and contain no owner history or private hash-cut journal. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
local notation "M"=>StateT (Backend n KemSK) (StateT P ProbComp)

noncomputable def edSign (failure : ed.Error) (message : Slice U8) (key : beaconcrypt_crypto.crypto_sign.SecretKey) :
    M (core.result.Result (alloc.vec.Vec U8) ed.Error) :=
  let bytes:=TranscriptAuthParts.absSlice message
  let signature:=setup.joint.sign (view.edSecret key) bytes
  pure (AdapterPublicBundlePrimitives.result failure (RegistrationAuthenticationShared.openedBytes (some (signature.toList++bytes))))

@[instance_reducible] noncomputable def locals
    (_coins : QueryImpl unifSpec (StateT P ProbComp))
    (_setup : PqxdhServerAuthExperiment.Setup base KemSK) (_checks : PqxdhServerAuthExperiment.Checks)
    (_representation : RegistrationServerRoleBackend.ConvertedIdentity _setup)
    (_created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (_view : AdapterPublicWrapperState.MaterialView source KemSK)
    (previous : LocalOperations (RustT M)) : LocalOperations (RustT M) := previous

@[instance_reducible] noncomputable def crypto
    (previous : CryptoOperations (RustT M)) (failure : ed.Error) : CryptoOperations (RustT M) :=
  {previous with
    edPublicBytes:=fun key=>pure (view.edPublic key)
    kxPublicBytes:=fun key=>pure (view.kxPublic key)
    kemPublicBytes:=fun key=>pure (RegistrationNativeBeaconFrontend.pqArray (view.kemPublic key))
    edSign:=fun message key=>⟨RustM.ok <$>edSign (n:=n) (P:=P) setup view failure message key⟩}

@[instance_reducible] noncomputable def children
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (previous : ChildOperations (RustT M)) : ChildOperations (RustT M) :=
  {previous with
    executeHash:=fun request=>⟨(fun digest=>RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
      (fun before=>simulateQ coins ((RegistrationNativePlatformPublicAdapterAuthentication.hash setup checks representation created (RegistrationInputs.hashBytes request)).run before))⟩
    encodeInit:=fun packet=>⟨StateT.lift (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeInit
      (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E) packet).run)⟩
    encodeResponse:=fun packet=>⟨StateT.lift (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeResponse
      (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E) packet).run)⟩}

variable (previousLocal : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (previousCrypto : CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (failure : ed.Error)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (previousChildren : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))

theorem getters :
    let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
    let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
    AdapterPublicBundleMaterial.Getters (m:=M) view := by
  let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
  let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
  exact {ed:=fun _=>rfl,kx:=fun _=>rfl,kem:=fun _=>rfl}

noncomputable def leaves (self : beaconcrypt_public_wrapper.beacon.Beacon) :
    let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
    let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
    let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
    AdapterPublicBundleMaterial.PublicationLeaves (m:=M) (self:=self) := by
  let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
  let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
  let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
  exact {
  edSign:=fun message=>edSign setup view failure message self.identity_key.secret_key
  hash:=fun request before=>simulateQ coins ((RegistrationNativePlatformPublicAdapterAuthentication.hash setup checks representation created (RegistrationInputs.hashBytes request)).run before)
  edLaw:=fun _=>rfl
  hashLaw:=fun _=>rfl}

omit material platform ed in
private theorem array_equal {length : Usize} (left right : Std.Array U8 length) (same : left.val=right.val) : left=right := by
  cases left
  cases right
  cases same
  rfl

theorem outgoing_source (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (secret : view.edSecret self.identity_key.secret_key=owner.identitySeed) :
    let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
    let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
    let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
    AdapterPublicInitPublication.outgoing
      (AdapterPublicBundleMaterial.PublicationLeaves.hash (self:=self) (leaves coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren self))
      (AdapterPublicInitPublication.edMethod (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
        (AdapterPublicBundleMaterial.PublicationLeaves.edSign (self:=self) (leaves coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren self)))=
      RegistrationNativePlatformPublicAdapterBundleSigning.outgoing coins setup checks representation created owner.identitySeed := by
  let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
  let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
  let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
  dsimp only
  funext query
  cases query with
  | inl query=>cases query with
    | hash request=>rfl
    | sign request payload digest=>rfl
  | inr request=>
    classical
    simp only [AdapterPublicInitPublication.outgoing,leaves,AdapterPublicInitPublication.edMethod,edSign,secret]
    by_cases owns:request.public_key=PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519
    · have views:=congrArg (fun bytes : Std.Array U8 32#usize=>bytes.val) owns.symm
      simp only [owns,views,decide_true,ite_true,map_pure,AdapterPublicBundlePrimitives.result_borrowed]
      apply StateT.ext
      intro current
      change pure (_,current)=simulateQ coins ((RegistrationNativePlatformPublicAdapterBundleSigning.rawOutgoing setup checks representation created owner.identitySeed (.inr request)).run current)
      simp only [RegistrationNativePlatformPublicAdapterBundleSigning.rawOutgoing,owns,ite_true,StateT.run_pure,simulateQ_pure]
    · have views : (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519).val≠request.public_key.val:=by
        intro same
        exact owns (array_equal _ _ same).symm
      simp only [views,decide_false,Bool.false_eq_true,ite_false]
      apply StateT.ext
      intro current
      change pure (_,current)=simulateQ coins ((RegistrationNativePlatformPublicAdapterBundleSigning.rawOutgoing setup checks representation created owner.identitySeed (.inr request)).run current)
      simp only [RegistrationNativePlatformPublicAdapterBundleSigning.rawOutgoing,owns,ite_false,StateT.run_pure,simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries.getters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries.getters

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries.leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries.leaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries.outgoing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries.outgoing_source
