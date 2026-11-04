-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerSigningOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildIssuance
import BeaconcryptCore.Computational.RegistrationNativeServerIssuance
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment

/-! Every actual source build that appends a response signing receipt retains its own moved token, source completion gate and first-record hash stage. The exact receipt includes failed signatures and all later failed writers/installations. This proves staged issuance and does not infer completed peer installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerIssuance
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeServerIssuance (history Stage)
open RegistrationSigningShared (SignReply)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {E Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : AdapterSealPrimitive.Operations]

/-- All-outcome actual complete source build issuance retains the actual consumed token and record stage rather than assuming publication success. -/
theorem source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before : State n) (previous : Platform)
    (result : RustM (Option (U64 × alloc.vec.Vec U8)) × State n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer sign helper writer handle application).run before).run previous))
    (changed : history result.2 ≠ history before) :
    ∃ token current pin plaintext,
      RegistrationServerSdkSource.take handle before = (some token, current) ∧ application = some plaintext ∧
      Stage token current.control pin plaintext (history before) (history result.2) := by
  obtain ⟨cut, hashed, current, platform, recordCalled, path, _extension, continued⟩ :=
    RegistrationNativePlatformBuildIssuance.source coins setup codec view failure allocation erased reservePeer sign helper writer
      handle application before previous result next supported changed
  obtain ⟨digest, signature, appended⟩ := RegistrationNativePlatformServerSigningOrigin.afterRecord_receipt coins sign writer
    cut.current.control hashed current platform ((cut.reply, cut.completed), next) continued
  have frame := RegistrationNativePlatformSourceFrames.record_frame coins setup codec view failure allocation erased helper cut.initial
    cut.reserved.world cut.reservePlatform (.ok (.Ok hashed), current) platform recordCalled
  change cut.completed.world.2 = current.world.2 ++ _ at appended
  rw [frame.2, cut.historyBefore, cut.historyAfter] at appended
  obtain ⟨controlEq, pinEq, tokenEq, applicationEq⟩ := RegistrationNativeServerBindingReceipt.lookup_fields
    cut.current.control cut.pinned cut.token cut.plaintext cut.lookup cut.lookupStarted
  have admitted := cut.occupancyResumed
  rw [PeerOwnership.completion_lookup_resume] at admitted
  simp only [controlEq, pinEq, tokenEq, applicationEq] at admitted
  exact ⟨cut.token, cut.current, cut.pinned, cut.plaintext, cut.tokenTaken, cut.applicationSome,
    (if cut.occupied then .Occupied else .Available), cut.initial, hashed, digest, signature, admitted, path, appended⟩

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The original corrected typed callback retains that exact staged issuance on every returned build outcome. -/
theorem typed {mlSource : RegistrationNativeMldsa.Source}
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8))
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (previous next : Platform)
    (reply : RustM (Option (U64 × Pqxdh.Bytes)))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created mlSource credential view failure allocation
        reserveRegistration reservePeer erased helper writer (.inr (.build handle application))).run before).run previous))
    (changed : after.server.world.world.2 ≠ before.server.world.world.2) :
    ∃ token current pin plaintext,
      RegistrationServerSdkSource.take handle before.server = (some token, current) ∧ application = some plaintext ∧
      Stage token current.control pin plaintext (history before.server) (history after.server) := by
  simp only [RegistrationNativePlatformExperiment.handler, StateT.run, bind_pure_comp, map_apply, support_map] at supported
  obtain ⟨⟨⟨raw, current⟩, platform⟩, called, same⟩ := supported
  have currentEq : current = after := congrArg (fun result => result.1.2) same
  cases currentEq
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at called
  obtain ⟨⟨⟨result, completed⟩, finalPlatform⟩, reached, closed⟩ := called
  have serverEq : completed = after.server := congrArg (fun result => result.1.2.server) closed
  have actual := source coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer
    (RegistrationNativeMldsa.owned mlSource credential) helper writer handle application before.server previous (result, completed) finalPlatform reached
    (by simpa only [serverEq] using changed)
  simpa only [serverEq] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformServerIssuance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerIssuance.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerIssuance.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerIssuance.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerIssuance.typed
