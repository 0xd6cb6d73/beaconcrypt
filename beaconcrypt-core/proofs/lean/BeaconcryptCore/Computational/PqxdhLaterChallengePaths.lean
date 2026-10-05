import BeaconcryptCore.Computational.PqxdhLaterSendAddress
import BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace
import BeaconcryptCore.Computational.RawCtxNativeSendSequence

/-! Request-time source paths for the literal later challenge wrapper. The private occurrence annotation follows the existing source compiler; it is never reconstructed from the final installed marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePaths

section Prefix
variable {ι A Result : Type} {spec : OracleSpec ι}

private theorem program_preserves (impl : QueryImpl spec (StateT A ProbComp)) (valid : A → Prop)
    (step : ∀ query before result, valid before → result ∈ support ((impl query).run before) → valid result.2)
    (client : OracleComp spec Result) (before : A) (initial : valid before) (result : Result × A)
    (supported : result ∈ support ((simulateQ impl client).run before)) : valid result.2 := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simpa only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using supported ▸ initial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    exact supported.elim fun reply evidence => ih reply.1 reply.2 (step query before reply initial evidence.1) result evidence.2

variable {extra : OracleSpec ι} {S B : Nat}
open PqxdhFirstRecordConfidentiality (ConfPostSpec AdvSpec)
open PqxdhRecordConfidentialityChallenge PqxdhRecordConfidentialityTrace

/-- An invariant of the actual source callbacks holds at every reached challenge request, before its send. This transports the complete source state along the literal adaptive prefix. -/
theorem reaches_preserves (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (valid : A → Prop)
    (step : ∀ query before result, valid before → result ∈ support ((impl query).run before) → valid result.2)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result) (before current : State) (ambient source : A)
    (initial : valid ambient)
    (reached : Reaches impl owner number bit client before ambient rest current source) : valid source := by
  induction reached with
  | here => exact initial
  | later query next before ambient reply rest current source actual tail ih =>
    exact ih (program_preserves impl valid step ((handler owner number bit query).run before) ambient initial reply actual)

/-- The exact reached prefix retains the write-once challenge and the sticky competing-publication flag. -/
theorem reaches_kept (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result) (before current : State) (ambient source : A)
    (reached : Reaches impl owner number bit client before ambient rest current source) : Kept before current := by
  induction reached with
  | here => exact ⟨fun _ => ⟨rfl, rfl⟩, id⟩
  | later query next before ambient reply rest current source actual tail ih =>
    exact (interpreted_kept impl owner number bit query before ambient reply actual).trans ih

end Prefix
section Source
open PqxdhInitialReceiptConstruction PqxdhInitialPendingPost
variable {ι A N M P I D K X Response AD PT CT : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev SourceState (A N M P I D K Response : Type) (S B : Nat) :=
  PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response
    PqxdhPhase2DecapsulationRouting.Shared Bool S B × InitialState A N

/-- The existing occurrence compiler and concrete retained callback interpreter, reassociated into one complete state. All native state, original markers, receipts and backend state remain present. -/
noncomputable def sourceHandler
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior)
    (selected : PqxdhCorrelatedExtractFamily.Message) (root : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (InitialState A N) ProbComp))
    (application : Response → StateT (InitialState A N) ProbComp (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (InitialState A N) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (InitialState A N) ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B) (StateT (SourceState A N M P I D K Response S B) ProbComp) :=
  fun query before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((simulateQ (PqxdhInitialOccurrencePaths.handler source writer prior selected root response pre application selector aux)
      ((PqxdhInitialInstallOccurrence.compiler (PqxdhInitialSelectedOrigin.mark source selected) sender route decode query).run
        before.1)).run before.2)

/-- Both pieces of operational provenance concern the same current state. Prior unlabelled owners remain unrestricted. -/
def Valid (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (prior : RawCtxSelectedParentTable.Prior)
    (serverInitial : RustM (KernelOf RatchetChain)) (beaconInitial : KernelOf RatchetChain)
    (state : SourceState A N M P I D K Response S B) : Prop :=
  PqxdhRetainedSelectedOrigins.Selected serverInitial beaconInitial state.1.1.2 state.1.2 ∧
    PqxdhInitialOccurrencePaths.Holds cr prior state.1.1.1 state.1.2

variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior)
    (selected : PqxdhCorrelatedExtractFamily.Message) (root : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (InitialState A N) ProbComp))
    (application : Response → StateT (InitialState A N) ProbComp (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (InitialState A N) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (InitialState A N) ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "impl" => sourceHandler source writer prior selected root response pre application selector aux sender route decode

/-- The source's interpreted owner callbacks are exactly the retained native callbacks in the same full backend state. -/
theorem source_calls :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (PqxdhInitialOccurrencePaths.handler (S := S) (B := B) source writer prior selected root response pre application selector aux) calls =
      RawCtxGenericNativeCalls.calls (PqxdhInitialOccurrencePaths.native source writer prior) := by
  have forwarding : PqxdhInitialOccurrencePaths.handler (S := S) (B := B) source writer prior selected root response pre application selector aux ∘ₛ
      primitiveForward = RawCtxPendingNativeCalls.pending (PqxdhInitialOccurrencePaths.native source writer prior)
        (PqxdhInitialOccurrencePaths.publicCalls source writer prior) := by
    funext query
    simp [QueryImpl.compose, primitiveForward, PqxdhInitialOccurrencePaths.handler, PqxdhInitialPendingPost.handler,
      OracleSpec.query, RawCtxPendingFamilyLiveQueries.handler]
  simpa only [calls, RawCtxGenericOwnerInterpretation.interpretedCalls, ← QueryImpl.simulateQ_compose, forwarding] using
    (RawCtxPendingNativeCalls.calls_interpretation
      (PqxdhInitialOccurrencePaths.native (A := A) (N := N) source writer prior)
      (PqxdhInitialOccurrencePaths.publicCalls source writer prior))

/-- The record branch is the original full native LIVE frontend in the same retained backend state. -/
theorem source_records (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxGenericFamilyLive.State (KernelOf RatchetChain) M P I D K S B) :
    simulateQ (PqxdhInitialOccurrencePaths.handler source writer prior selected root response pre application selector aux)
      (simulateQ liveForward ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run entry)) =
    (RawCtxGenericFamilyLive.impl
      (RawCtxGenericNativeCalls.calls (PqxdhInitialOccurrencePaths.native source writer prior))
      (PqxdhInitialOccurrencePaths.publicCalls source writer prior)
      (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) sender route decode query).run entry := by
  have forwarding : PqxdhInitialOccurrencePaths.handler (S := S) (B := B) source writer prior selected root response pre application selector aux ∘ₛ
      liveForward = RawCtxPendingFamilyLiveQueries.handler
        (RawCtxPendingNativeCalls.pending (PqxdhInitialOccurrencePaths.native source writer prior)
          (PqxdhInitialOccurrencePaths.publicCalls source writer prior))
        (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) := by
    funext request
    simp [QueryImpl.compose, liveForward, PqxdhInitialOccurrencePaths.handler, PqxdhInitialPendingPost.handler, OracleSpec.query]
  rw [← QueryImpl.simulateQ_compose, forwarding, RawCtxPendingFamilyLiveQueries.step_interpretation,
    RawCtxPendingNativeCalls.calls_interpretation, RawCtxPendingNativeCalls.public_interpretation]

/-- The literal source operation supplies both invariant-preservation laws, including every failed or replacing finish and every record/reveal/selector request. -/
theorem source_step (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (serverInitial : RustM (KernelOf RatchetChain))
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : SourceState A N M P I D K Response S B)
    (result : (PqxdhInitialGenericPost.Spec extra S B).Range query × SourceState A N M P I D K Response S B)
    (valid : Valid cr prior serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined before)
    (supported : result ∈ support ((impl query).run before)) :
    Valid cr prior serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined result.2 := by
  simp only [sourceHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨actual, supported, rfl⟩ := supported
  exact ⟨PqxdhRetainedSelectedOrigins.step_selected source writer prior selected root response pre application
    selector aux serverInitial sender route decode query before.1 before.2 valid.1 actual supported,
    PqxdhInitialOccurrencePaths.step_holds source writer prior selected root response pre application
      selector aux cr (PqxdhInitialSelectedOrigin.mark source selected) sender route decode query before.1 before.2
      valid.2 actual supported⟩

/-- The flattened interpreter is exactly the existing complete occurrence program, including its full backend poststate. This is a program equality, not merely a supported-state projection. -/
theorem source_program {Result : Type}
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : SourceState A N M P I D K Response S B) :
    (simulateQ impl client).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((simulateQ (PqxdhInitialOccurrencePaths.handler source writer prior selected root response pre application selector aux)
          ((simulateQ (PqxdhInitialInstallOccurrence.compiler
            (PqxdhInitialSelectedOrigin.mark source selected) sender route decode) client).run before.1)).run before.2) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [sourceHandler, StateT.run, map_bind, bind_map_left]
    exact bind_congr fun reply => ih reply.1.1 (reply.1.2, reply.2)

/-- The actual retained source supplies the callback laws required by prefix transport; there is no caller callback-preservation premise. Both provenance facts hold at the request state, before challenge encryption. -/
theorem source_reaches {Result : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (serverInitial : RustM (KernelOf RatchetChain))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Result)
    (before current : PqxdhRecordConfidentialityChallenge.State)
    (ambient reached : SourceState A N M P I D K Response S B)
    (initial : Valid cr prior serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined ambient)
    (traced : PqxdhRecordConfidentialityTrace.Reaches impl owner number bit client before ambient rest current reached) :
    Valid cr prior serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined reached := by
  exact reaches_preserves impl _
    (source_step source writer prior selected root response pre application selector aux sender route decode cr serverInitial)
    owner number bit client rest before current ambient reached initial traced

/-- The initial Builder's only possible publication is its literal first send. It cannot supply a later-position target before the challenge Post begins. -/
theorem builder_absent
    (serverResponse : pqxdh.concrete.InitialRatchetKdfResponse) (origin : Bool)
    (index : Fin S) (metadata : P) (input : PqxdhPrivateAcceptedRoot.Ready)
    (entry : Front RatchetChain M P I D K S B) (before : InitialState A N)
    (result : ((RustM (Option PqxdhServerRegistrationPublication.Response) ×
      Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf RatchetChain))) × Front RatchetChain M P I D K S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (PqxdhInitialOccurrencePaths.handler source writer prior selected root response pre application selector aux)
      ((PqxdhInitialBuilderReceipt.build source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
        sender index metadata input).run entry)).run before))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (later : 2 ≤ number.val) :
    ((owner, number), true) ∉ (PqxdhInitialOriginPost.afterBuilder
      PqxdhInitialSourcePublication.empty result.1.2 index origin result.1.1.1).published := by
  intro recorded
  obtain ⟨published, peer, replied, present, position, _⟩ := PqxdhInitialOriginPost.builder_recorded
    PqxdhInitialSourcePublication.empty result.1.2 index origin result.1.1.1 (owner, number) true recorded
      (by simp [PqxdhInitialSourcePublication.empty])
  obtain ⟨receipt, _, initialized, _, advanced, encrypted, atSend, atSent, installed, sent⟩ :=
    PqxdhInitialReceiptPublication.build_published
      (PqxdhInitialOccurrencePaths.handler source writer prior selected root response pre application selector aux)
      source _ sender index metadata input entry before result supported published replied
  rw [source_calls] at sent
  have increment := (RawCtxNativeSendSequence.native (PqxdhInitialOccurrencePaths.native source writer prior)
    receipt.initial _ atSend ((advanced, some encrypted), atSent) sent encrypted rfl).2
  obtain ⟨_, _, _, initialKernel, _, created, _, _, _, initialFields⟩ :=
    PqxdhInitialSuppliedPositions.pair_refines source.crypto serverResponse
  have zero : receipt.initial.control.send_sequence.val = 0 := by
    rw [created, RawCtxMaterialInterpretation.rust_map_ok] at initialized
    exact (RustM.ok.inj initialized) ▸ initialFields.sendSequence
  have peerEq := Option.some.inj (present.symm.trans installed)
  have numberEq := congrArg (fun publication => publication.2.val) position
  simp only [peerEq] at numberEq
  simp only [zero, Nat.zero_add] at increment
  omega

/-- A true literal challenge Post after the actual first Builder has a reached challenge origin whose starting annotation is constructed by that Builder. No initial path certificate is requested for arbitrary preexisting owners. -/
theorem sequence_origin {Selection : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (serverResponse : pqxdh.concrete.InitialRatchetKdfResponse) (origin : Bool)
    (index : Fin S) (metadata : P) (input : PqxdhPrivateAcceptedRoot.Ready)
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) (selection : Selection)
    (entry : Front RatchetChain M P I D K S B) (before : InitialState A N)
    (result : (Bool × PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response
      PqxdhPhase2DecapsulationRouting.Shared Bool S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (PqxdhInitialOccurrencePaths.handler source writer prior selected root response pre application selector aux)
      ((PqxdhInitialInstallOccurrence.sequence source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
        (PqxdhInitialSelectedOrigin.mark source selected) origin sender route decode index metadata input
        (PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection)).run
        ((entry, PqxdhInitialSourcePublication.empty), PqxdhInitialInstallOccurrence.empty))).run before))
    (accepted : result.1.1 = true) :
    ∃ reply ambient current,
      Valid cr prior (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
        (PqxdhInitialRootAudit.kernel (root, response)).refined ambient ∧
      PqxdhRecordConfidentialityTrace.Origin impl owner number bit (adversary selection reply)
        PqxdhRecordConfidentialityChallenge.initial ambient ((true, current), (result.1.2, result.2)) ∧
      PqxdhRecordConfidentialityChallenge.Target number current ∧
      (2 ≤ number.val → ((owner, number), true) ∉ ambient.1.1.2.published) := by
  simp only [PqxdhInitialInstallOccurrence.sequence, StateT.run, simulateQ_bind] at supported
  change result ∈ support (StateT.run _ before) at supported
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨built, builtSupported, rest⟩ := supported
  let ambient : SourceState A N M P I D K Response S B :=
    (((built.1.2, PqxdhInitialOriginPost.afterBuilder PqxdhInitialSourcePublication.empty built.1.2 index origin built.1.1.1),
      PqxdhInitialInstallOccurrence.built (PqxdhInitialInstallOccurrence.begin PqxdhInitialInstallOccurrence.empty)
        0 input index built.1.2 built.1.1.1 built.1.1.2), built.2)
  have actual : (result.1.1, (result.1.2, result.2)) ∈ support
      ((simulateQ impl (PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection built.1.1.1)).run ambient) := by
    rw [source_program, support_map]
    exact ⟨result, rest, rfl⟩
  obtain ⟨current, traced, target⟩ := PqxdhRecordConfidentialityTrace.post_origin impl adversary owner number bit selection
    built.1.1.1 ambient _ actual accepted
  refine ⟨built.1.1.1, ambient, current, ?_, traced, target, fun later =>
    builder_absent source writer prior selected root response pre application selector aux sender
      serverResponse origin index metadata input entry before built builtSupported owner number later⟩
  refine ⟨PqxdhRetainedSelectedOrigins.builder_selected source writer prior selected root response pre application selector aux
    _ _ origin sender index metadata input entry before PqxdhInitialSourcePublication.empty
    PqxdhInitialInstallOccurrence.empty ?_ built builtSupported,
    PqxdhInitialOccurrencePaths.builder_holds source writer prior selected root response pre application selector aux
      cr serverResponse sender index metadata input entry before built builtSupported⟩
  exact fun _ impossible => nomatch impossible

end Source
end BeaconcryptCore.Computational.PqxdhLaterChallengePaths

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.reaches_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.reaches_preserves
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.reaches_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.reaches_kept
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_calls
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_records
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_program
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.source_reaches
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.builder_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.builder_absent
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePaths.sequence_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePaths.sequence_origin
