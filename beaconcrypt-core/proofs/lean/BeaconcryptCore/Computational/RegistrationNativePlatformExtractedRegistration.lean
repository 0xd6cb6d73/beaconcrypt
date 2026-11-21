-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication
/-! Current registration dispatch closes the actual publication/writer, authentication and seal request trees. Complete callbacks retain their persistent primitive/platform state and every Rust result. Ordinary record routes are composed separately with the extracted stateful World dictionary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedRegistration
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK E Value : Type} {base : OracleSpec I}
variable {m : Type →Type} [Monad m] [LawfulMonad m]
variable [primitive : AdapterSealPrimitive.Operations] [ed : AdapterInitEdPrimitive.Operations]
variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (reserveRegistration reservePeer : m Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)

noncomputable def handler : QueryImpl RegistrationNativeRawAdapter.TypedSpec (RegistrationNativePlatformExperiment.M n KemSK source m)
  | .inr (.bundle owner)=>RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source writer owner
  | .inr (.accept packet)=>do
      modify fun before=>{before with parsedAccepts:=before.parsedAccepts+1}
      RegistrationNativePlatformExperiment.server (RegistrationNativePlatformExtractedAuthentication.accept coins setup
        (RegistrationNativeWire.ledgerCodec wire) route source.verify checks representation created reserveRegistration packet)
  | .inr (.build handle application)=>do
      let result←RegistrationNativePlatformExperiment.server (RegistrationNativePlatformExtractedSourceSeal.build coins setup
        (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer
        (RegistrationNativeMldsa.owned source credential) helper writer handle application)
      pure (do let optional←result; .ok (optional.map fun value=>(value.1,TranscriptAuthParts.absSlice value.2)))
  | .inr (.finish index packet)=>RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformExtractedFinish.finish setup source wire index packet))
  | query=>RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer query

/-- Current registration callbacks execute the checked source request bodies; only narrow Ed primitive functionality is needed for Init authentication. -/
theorem handler_source (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    handler (n:=n) coins setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer=
      RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer := by
  funext query
  cases query with
  | inl coin=>rfl
  | inr query=>cases query <;>
      simp only [handler,RegistrationNativePlatformExperiment.handler,
        RegistrationNativePlatformExtractedBundle.bundle_source,
        RegistrationNativePlatformExtractedAuthentication.accept_source coins setup (RegistrationNativeWire.ledgerCodec wire) route source.verify checks representation created functional,
        RegistrationNativePlatformExtractedSourceSeal.build_source,
        RegistrationNativePlatformExtractedFinish.finish_source]

/-- Any adaptive typed program retains its exact complete native and persistent platform execution, with no whole-program law supplied by the caller. -/
theorem program_source (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : RegistrationNativeExperiment.State n KemSK source) :
    (simulateQ (handler coins setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run before=
      (simulateQ (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run before := by
  rw [handler_source coins setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer functional]
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedRegistration
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedRegistration.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedRegistration.handler_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedRegistration.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedRegistration.program_source
