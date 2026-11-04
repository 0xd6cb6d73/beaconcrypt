-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerIssuance
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace

/-! One actual source response issuance retains the exact first-record support witness and the very same signed hash capability. This joint receipt avoids selecting separate primitive paths that merely share projected public fields. Full native record state, allocator state, actual moved token and final cache anchor remain together through later failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordStage
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerFrontendCompiler (State)
open RegistrationNativeServerIssuance (history)
open RegistrationSigningShared (Receipt SignReply)
open RegistrationSigningTrace (Command replyBytes)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι}
variable [primitive : AdapterSealPrimitive.Operations]

structure Stage (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before after : State n) (receipt : Receipt) where
  token : peer.ConsumedRegistration
  current : State n
  pin : session.ServerAuthenticationPin
  plaintext : Slice U8
  availability : pqxdh.KeyIdAvailability
  initial : registration.ServerInitialKdf
  hashed : registration.ServerResponseHash
  digest : CtxRomAuth.CtxDigest
  signature : SignReply
  recordBefore : RegistrationServerRootCompiler.Local n
  recordAfter : RegistrationServerRootCompiler.Local n
  recordPlatform : Platform
  afterRecordPlatform : Platform
  taken : RegistrationServerSdkSource.take handle before = (some token, current)
  supplied : application = some plaintext
  admitted : registration.begin_server_completion current.control pin availability token.agreement plaintext = .ok (.Ok initial)
  path : RegistrationServerRecordExecutor.Path initial hashed
  recordCalled : ((.ok (.Ok hashed), recordAfter), afterRecordPlatform) ∈ support
    (((RegistrationNativePlatformSourceSealTrace.record coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased helper initial).run recordBefore).run recordPlatform)
  priorHistory : recordBefore.world.2 = history before
  cacheExtension : recordAfter.world.1.primitive.2 ≤ after.world.world.1.primitive.2
  appended : history after = history before ++ [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)]
  selected : receipt = ⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩

/-- Every newly retained actual source issuance selects a single coupled first-record/hash/sign witness, including failed final replies. -/
theorem source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before : State n) (previous : Platform)
    (result : RustM (Option (U64 × alloc.vec.Vec U8)) × State n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformSourceSeal.build coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer sign helper writer handle application).run before).run previous))
    (receipt : Receipt) (member : receipt ∈ history result.2) (prior : receipt ∉ history before) :
    Nonempty (Stage coins setup wire view failure allocation erased helper handle application before result.2 receipt) := by
  have changed : history result.2 ≠ history before := fun same => prior (same ▸ member)
  obtain ⟨cut, hashed, current, platform, called, path, extension, continued⟩ := RegistrationNativePlatformBuildIssuance.source coins setup
    (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer sign helper writer handle application before previous result next supported changed
  obtain ⟨digest, signature, appended⟩ := RegistrationNativePlatformServerSigningOrigin.afterRecord_receipt coins sign writer
    cut.current.control hashed current platform ((cut.reply, cut.completed), next) continued
  have frame := RegistrationNativePlatformSourceFrames.record_frame coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased helper cut.initial
    cut.reserved.world cut.reservePlatform (.ok (.Ok hashed), current) platform called
  change cut.completed.world.2 = current.world.2 ++ _ at appended
  rw [frame.2, cut.historyBefore, cut.historyAfter] at appended
  have selected : receipt = (⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt) := by
    have actualMember : receipt ∈ history before ++ [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)] := appended ▸ member
    rcases List.mem_append.mp actualMember with old | single
    · exact False.elim (prior old)
    · exact List.mem_singleton.mp single
  obtain ⟨controlEq, pinEq, tokenEq, applicationEq⟩ := RegistrationNativeServerBindingReceipt.lookup_fields
    cut.current.control cut.pinned cut.token cut.plaintext cut.lookup cut.lookupStarted
  have admitted := cut.occupancyResumed
  rw [PeerOwnership.completion_lookup_resume] at admitted
  simp only [controlEq, pinEq, tokenEq, applicationEq] at admitted
  exact ⟨⟨cut.token, cut.current, cut.pinned, cut.plaintext, (if cut.occupied then .Occupied else .Available), cut.initial,
    hashed, digest, signature, cut.reserved.world, current, cut.reservePlatform, platform, cut.tokenTaken, cut.applicationSome,
    admitted, path, called, cut.historyBefore, extension, appended, selected⟩⟩

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual corrected typed build supplies that same joint source record/issuance witness. -/
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
    (receipt : Receipt) (member : receipt ∈ history after.server) (prior : receipt ∉ history before.server) :
    Nonempty (Stage coins setup wire view failure allocation erased helper handle application before.server after.server receipt) := by
  simp only [RegistrationNativePlatformExperiment.handler, StateT.run, bind_pure_comp, map_apply, support_map] at supported
  obtain ⟨⟨⟨raw, current⟩, platform⟩, called, same⟩ := supported
  have currentEq : current = after := congrArg (fun result => result.1.2) same
  cases currentEq
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at called
  obtain ⟨⟨⟨result, completed⟩, finalPlatform⟩, reached, closed⟩ := called
  have serverEq : completed = after.server := congrArg (fun result => result.1.2.server) closed
  have actual := source coins setup wire view failure allocation erased reservePeer (RegistrationNativeMldsa.owned mlSource credential)
    helper writer handle application before.server previous (result, completed) finalPlatform reached receipt
      (by simpa only [serverEq] using member) prior
  simpa only [serverEq] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordStage.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordStage.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordStage.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordStage.typed
