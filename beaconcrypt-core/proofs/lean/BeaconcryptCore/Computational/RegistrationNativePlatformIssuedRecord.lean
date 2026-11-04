-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildIssuance
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFinishContents
import BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt

/-! New chronological signing receipts in an actual complete source build supply the exact moved token, source-selected first initializer and concrete successful source first-record cut. The cache anchor is the actual whole-build final cache, including later failed publication and installation. A staged record is not a premise that a completed Server peer exists. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIssuedRecord
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι}
variable [primitive : AdapterSealPrimitive.Operations]

/-- A changed actual build signing log derives the moved agreement, source admission and actual allocator/AEAD/hash/raw-writer record receipt at its final shared-cache anchor. -/
theorem source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : RustM (Option (U64 × alloc.vec.Vec U8)) × RegistrationServerFrontendCompiler.State n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformSourceSeal.build coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer sign
        (AdapterRecordRawBytes.helper rawAllocation serializer) writer handle application).run before).run previous))
    (changed : result.2.world.world.2 ≠ before.world.world.2) :
    ∃ (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
        (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability) (plaintext : Slice U8)
        (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash),
      RegistrationServerSdkSource.take handle before = (some token, current) ∧ application = some plaintext ∧
      registration.begin_server_completion current.control pin availability token.agreement plaintext = .ok (.Ok initial) ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧
      RegistrationNativePlatformSourceFinishContents.RecordCut (n := n) coins setup wire view failure allocation erased
        rawAllocation serializer initial hashed result.2.world.world.1.primitive.2 := by
  obtain ⟨cut, hashed, current, platform, called, path, extension, _continued⟩ :=
    RegistrationNativePlatformBuildIssuance.source coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer
      sign (AdapterRecordRawBytes.helper rawAllocation serializer) writer handle application before previous result next supported changed
  obtain ⟨controlEq, pinEq, tokenEq, applicationEq⟩ := RegistrationNativeServerBindingReceipt.lookup_fields
    cut.current.control cut.pinned cut.token cut.plaintext cut.lookup cut.lookupStarted
  have admitted := cut.occupancyResumed
  rw [PeerOwnership.completion_lookup_resume] at admitted
  simp only [controlEq, pinEq, tokenEq, applicationEq] at admitted
  refine ⟨cut.token, cut.current, cut.pinned, (if cut.occupied then .Occupied else .Available), cut.plaintext,
    cut.initial, hashed, cut.tokenTaken, cut.applicationSome, admitted, path, ?_⟩
  refine ⟨(cut.reserved.world, cut.reservePlatform), (current, platform), ?_, extension⟩
  exact (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mpr called


omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The literal corrected public typed build retains the same source first-record and moved-token receipt whenever its signing history grows, including failed final replies. -/
theorem typed {mlSource : RegistrationNativeMldsa.Source}
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8))
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (previous next : Platform)
    (reply : RustM (Option (U64 × Pqxdh.Bytes)))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created mlSource credential view failure allocation
        reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer
        (.inr (.build handle application))).run before).run previous))
    (changed : after.server.world.world.2 ≠ before.server.world.world.2) :
    ∃ (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
        (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability) (plaintext : Slice U8)
        (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash),
      RegistrationServerSdkSource.take handle before.server = (some token, current) ∧ application = some plaintext ∧
      registration.begin_server_completion current.control pin availability token.agreement plaintext = .ok (.Ok initial) ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧
      RegistrationNativePlatformSourceFinishContents.RecordCut (n := n) coins setup wire view failure allocation erased
        rawAllocation serializer initial hashed (RegistrationNativeWorldCache.cache after) := by
  simp only [RegistrationNativePlatformExperiment.handler, StateT.run, bind_pure_comp, map_apply, support_map] at supported
  obtain ⟨⟨⟨raw, current⟩, platform⟩, called, same⟩ := supported
  have currentEq : current = after := congrArg (fun value => value.1.2) same
  cases currentEq
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at called
  obtain ⟨⟨⟨result, completed⟩, finalPlatform⟩, reached, closed⟩ := called
  have serverEq : completed = after.server := congrArg (fun value => value.1.2.server) closed
  have actual := source coins setup wire view failure allocation erased reservePeer (RegistrationNativeMldsa.owned mlSource credential)
    rawAllocation serializer writer handle application before.server previous (result, completed) finalPlatform reached
    (by simpa only [serverEq] using changed)
  simpa only [serverEq, RegistrationNativeWorldCache.cache] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformIssuedRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIssuedRecord.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIssuedRecord.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIssuedRecord.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIssuedRecord.typed
