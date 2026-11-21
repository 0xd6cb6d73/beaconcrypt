-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
/-! The raw acceptance driver allocates a handle only from the actual returned source token and commits the actual source Self/RNG and observed backend. Enclosing Rust failure/divergence has no replacement object. Private agreement instrumentation is erased back to the actual extracted public call. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend persistent)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R P : Type} {mlSource : RegistrationNativeMldsa.Source}

def handle (count : Nat) (word : AdapterPublicServerAgreementReceipt.Word R) : Option Nat :=
  match word.1 with | .None=>none | .Some _=>some count

noncomputable def finish (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (before : Store n KemSK R P)
    (result : RustM (RegistrationNativePlatformSdkAcceptInstrumentedSource.Word R)×(Backend n KemSK×P)) :
    RustM (Option Nat×Store n KemSK R P)×(Backend n KemSK×P) :=
  match result.1 with
  | .fail error=>(.fail error,result.2)
  | .div=>(.div,result.2)
  | .ok returned=>
    let after:=RegistrationNativePlatformPublicAdapterAccept.committed view views returned result.2
    (.ok (handle before.nextSession returned.2,RegistrationNativePlatformPublicAdapterStore.accept before returned.2 after),after)

noncomputable def observed (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (before : Store n KemSK R P)
    (result : RustM (RegistrationNativePlatformSdkAcceptInstrumentedSource.Word R)×(RegistrationNativeExperiment.State n KemSK mlSource×P)) :=
  finish view views before (result.1,persistent result.2)

theorem erase_reply (receipt : AdapterPublicServerReservationReceipt.Receipt R)
    (word : RustM (AdapterPublicServerAgreementReceipt.Word R)) :
    RegistrationNativePlatformSdkAcceptInstrumentedSource.erase
      (RegistrationNativePlatformSdkAcceptInstrumentedSource.reply receipt word)=word :=by
  cases word <;>rfl

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable {I Reader Response : Type} {base : OracleSpec I}
variable (containers : ContainerOperations (RustT (StateT P ProbComp)))
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

noncomputable def run {Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (input : Slice U8) (before : Store n KemSK R P) :=
  (fun result=>finish view views before
    (RegistrationNativePlatformSdkAcceptInstrumentedSource.reply result.1.1.1 result.1.1.2,(result.1.2,result.2))) <$>
      ((RegistrationNativePlatformPublicAdapterAccept.program containers coins setup checks verify representation created generator view
        before.server input before.rng).run before.backend.1).run before.backend.2

variable (locals : LocalOperations (RustT (StateT P ProbComp)))

theorem source {E Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×P) (before : Store n KemSK R P)
    (related : AdapterPublicWrapperState.Server view views created credential before.server current.1.server)
    (basis : before.backend=persistent current) (input : Slice U8)
    (edGetter : ∀key,(@CryptoOperations.edPublicBytes material ed
      (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run=pure (.ok (view.edPublic key)))
    (mlGetter : ∀identity,(locals.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey)) :
    let : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
      RegistrationNativePlatformPublicAdapterLeaves.localOperations locals
    let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
      RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
    observed view views before <$>
      RegistrationNativePlatformSdkAcceptInstrumentedSource.source coins setup codec route verify edLaws recording writer generator
        before.server input before.rng current.1 current.2=
      run containers coins setup checks verify representation created generator view views input before :=by
  let : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterLeaves.localOperations locals
  let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  have same:=RegistrationNativePlatformPublicAdapterAccept.instrumented_source locals containers coins setup codec checks route verify representation created
    generator edLaws recording writer view views credential before.server input before.rng current.1 current.2 related edGetter mlGetter
  have lifted:=congrArg (fun computation=>finish view views before <$>computation) same
  simp only [run,Functor.map_map] at lifted ⊢
  rw [basis]
  exact lifted

noncomputable def actual {E Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×P) :
    ProbComp (RustM (AdapterPublicServerAgreementReceipt.Word R)×(RegistrationNativeExperiment.State n KemSK mlSource×P)) :=
  let : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterLeaves.localOperations locals
  let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  let : CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  let : ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    AdapterPublicWrapperChildren.children (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  let : Codecs (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    AdapterPublicConcreteCodecs.codecs
  (fun result=>(result.1.1,(result.1.2,result.2))) <$>
    (((AdapterPublicServerAcceptDispatch.entry input
      ((beaconcrypt_public_request.server.Server.get_shared_secret_with_rng
        (m:=RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
        generator self input rng).run)).run current.1).run current.2)


theorem actual_source {E Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : RegistrationNativeExperiment.State n KemSK mlSource×P) (before : Store n KemSK R P)
    (related : AdapterPublicWrapperState.Server view views created credential before.server current.1.server)
    (basis : before.backend=persistent current) (input : Slice U8)
    (edGetter : ∀key,(@CryptoOperations.edPublicBytes material ed
      (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run=pure (.ok (view.edPublic key)))
    (mlGetter : ∀identity,(locals.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey)) :
    Prod.map id persistent <$>actual containers coins setup verify locals generator codec route edLaws recording writer
      before.server input before.rng current=
      (fun result=>(result.1.1.2,(result.1.2,result.2))) <$>
        ((RegistrationNativePlatformPublicAdapterAccept.program containers coins setup checks verify representation created generator view
          before.server input before.rng).run before.backend.1).run before.backend.2 :=by
  let : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterLeaves.localOperations locals
  let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterLeaves.containerOperations containers
  have erased:=RegistrationNativePlatformSdkAcceptInstrumentedSource.erasure coins setup codec route verify edLaws recording writer generator
    before.server input before.rng current.1 current.2
  have first:=congrArg (fun computation=>Prod.map id persistent <$>computation) erased
  have physical:=RegistrationNativePlatformPublicAdapterAccept.instrumented_source locals containers coins setup codec checks route verify representation created
    generator edLaws recording writer view views credential before.server input before.rng current.1 current.2 related edGetter mlGetter
  have second:=congrArg (fun computation=>Prod.map RegistrationNativePlatformSdkAcceptInstrumentedSource.erase id <$>computation) physical
  simp only [Functor.map_map,Prod.map,id_eq] at first second
  simp only [erase_reply] at second
  unfold actual
  rw [basis]
  simpa only [Functor.map_map,Prod.map,id_eq,persistent] using first.symm.trans second

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore.erase_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore.erase_reply
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore.actual_source
