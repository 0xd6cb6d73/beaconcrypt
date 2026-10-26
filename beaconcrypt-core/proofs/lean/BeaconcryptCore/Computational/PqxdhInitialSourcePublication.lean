import BeaconcryptCore.Computational.PqxdhInitialOriginPostPath
import BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath

/-!
The actual supplied initial64 constructor and complete first Server builder establish the publication/path invariant before the full adaptive post client. The trace begins empty, so no prior publication or installed-session origin is assumed. Successful matching Beacon finishes acquire their own source-derived origin during that same client. Every recorded selected-origin publication is already present in the private cache before a final checker is evaluated.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialSourcePublication
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialOriginPostPath PqxdhInitialOriginFinishPath RawCtxCursorLineage
variable {ι M P I D K X Response A N Result : Type} {extra : OracleSpec ι} {S B : Nat}

def empty : PqxdhInitialOriginPost.Trace Bool S B := ⟨fun _ => none, []⟩

/-- An uninstrumented original family starts with no asserted selected installation or publication. -/
theorem empty_invariant (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (before : Front M P I D K S B) (state : State A N) : Invariant root selected (before, empty) state := by
  constructor
  · intro installed
    cases installed
  · intro number recorded
    exact False.elim (List.not_mem_nil recorded)

/-- The complete actual first builder supplies the installed-session and already executed publication paths from the same initial64 constructor. -/
theorem builder_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (entry : ConcreteRatchetKernel) (initialized : PqxdhInitialReplyErasure.kernelOf false response64 = ok entry)
    (selected : RawCtxProtocolReveals.Owner S B) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before after : Front M P I D K S B)
    (state afterState : State A N) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (supported : ((reply, after), afterState) ∈ support
      ((simulateQ (PqxdhInitialNativeLog.handler source writer stage
        (withInitial source selectedMessage previousRoot response64 other))
        ((PqxdhInitialPendingBuilder.build source
          (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64)
          sender index metadata ready).run before)).run state)) :
    Invariant (rootFor (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain) previousRoot response64 selected)
      selected (after, PqxdhInitialOriginPost.afterBuilder empty after index true reply) afterState := by
  cases reply with
  | fail error => exact empty_invariant _ selected after afterState
  | div => exact empty_invariant _ selected after afterState
  | ok reply =>
    cases reply with
    | none => exact empty_invariant _ selected after afterState
    | some response =>
      cases found : (after.roles.1.1 index).server.peers response.keyId with
      | none =>
        simpa only [PqxdhInitialOriginPost.afterBuilder, found] using empty_invariant
          (rootFor (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain) previousRoot response64 selected) selected after afterState
      | some peer =>
        obtain ⟨actualPeer, actualPresent, path⟩ := PqxdhInitialOriginBuilderPath.supplied_build source writer stage
          (withInitial source selectedMessage previousRoot response64 other) response64 entry initialized sender index metadata ready
          before after state afterState response supported
        have samePeer : actualPeer = peer := Option.some.inj (actualPresent.symm.trans found)
        subst actualPeer
        constructor
        · intro installed kernel present
          by_cases same : selected = .server index response.keyId
          · subst selected
            simp only [RawCtxGenericRoleFamily.selectedKernel, found, Option.map_some, Option.some.injEq] at present
            subst kernel
            exact path
          · simp only [PqxdhInitialOriginPost.afterBuilder, found, Function.update_of_ne same, empty] at installed
            cases installed
        · intro number recorded
          obtain ⟨actualResponse, actualPeer, sameReply, present, publication, origin⟩ :=
            PqxdhInitialOriginPost.builder_recorded empty after index true (.ok (some response)) (selected, number) true recorded
              (by simp [empty])
          have sameResponse : actualResponse = response := by cases sameReply; rfl
          subst actualResponse
          have samePeer : actualPeer = peer := Option.some.inj (present.symm.trans found)
          subst actualPeer
          have owner := congrArg Prod.fst publication
          have numberEq := congrArg Prod.snd publication
          simp only at owner numberEq
          subst selected
          subst number
          obtain ⟨earlier, walked⟩ := path
          exact ⟨earlier, RawCtxSelectedQueryTrace.rootVector peer.kernel.send_chain, walked⟩


noncomputable def sequence (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front M P I D K S B) : StateT (State A N) ProbComp (Result × Snapshot M P I D K S B) :=
  simulateQ (PqxdhInitialNativeLog.handler source writer stage
    (withInitial source selectedMessage previousRoot response64 other))
    ((PqxdhInitialOriginPost.sequence source
      (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64)
      (PqxdhInitialSelectedOrigin.mark source selectedMessage) true sender route decode index metadata ready post).run (before, empty))

/-- The actual constructor, complete first builder and original adaptive post establish the source publication invariant from an empty trace, with no initialized-path premise. -/
theorem sequence_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (entry : ConcreteRatchetKernel) (initialized : PqxdhInitialReplyErasure.kernelOf false response64 = ok entry)
    (selected : RawCtxProtocolReveals.Owner S B) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front M P I D K S B) (state : State A N)
    (result : (Result × Snapshot M P I D K S B) × State A N)
    (supported : result ∈ support ((sequence source writer stage selectedMessage previousRoot response64 other
      sender route decode index metadata ready post before).run state)) :
    Invariant (rootFor (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain) previousRoot response64 selected)
      selected result.1.2 result.2 := by
  change result ∈ support ((simulateQ
    (PqxdhInitialNativeLog.handler source writer stage (withInitial source selectedMessage previousRoot response64 other)) (do
      let built ← (PqxdhInitialPendingBuilder.build source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64) sender index metadata ready).run before
      (simulateQ (PqxdhInitialOriginPost.compiler (PqxdhInitialSelectedOrigin.mark source selectedMessage)
        sender route decode) (post built.1)).run
        (built.2, PqxdhInitialOriginPost.afterBuilder empty built.2 index true built.1))).run state) at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨built, reached, rest⟩ := supported
  exact program_invariant source writer stage selectedMessage previousRoot response64 other
    (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain) selected sender route decode (post built.1.1) _ built.2
    (builder_invariant source writer stage selectedMessage previousRoot response64 other entry initialized selected
      sender index metadata ready before built.1.2 state built.2 built.1.1 reached) result rest

/-- Every successful selected-session publication of the full actual source has its directional path already cached before any final lineage checker. -/
theorem publication_cached (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (entry : ConcreteRatchetKernel) (initialized : PqxdhInitialReplyErasure.kernelOf false response64 = ok entry)
    (selected : RawCtxProtocolReveals.Owner S B) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front M P I D K S B) (state : State A N)
    (result : (Result × Snapshot M P I D K S B) × State A N)
    (supported : result ∈ support ((sequence source writer stage selectedMessage previousRoot response64 other
      sender route decode index metadata ready post before).run state))
    (number : Std.U64) (published : ((selected, number), true) ∈ result.1.2.2.published) :
    RawCtxSourcePublishedPath.Cached
      (rootFor (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain) previousRoot response64 selected)
      number result.2.1.1.2.1 :=
  (sequence_invariant source writer stage selectedMessage previousRoot response64 other entry initialized selected
    sender route decode index metadata ready post before state result supported).2 number published

end BeaconcryptCore.Computational.PqxdhInitialSourcePublication

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePublication.empty_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePublication.empty_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePublication.builder_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePublication.builder_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePublication.sequence_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePublication.sequence_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePublication.publication_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePublication.publication_cached
