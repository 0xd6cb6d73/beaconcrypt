import BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths

/-! The original Boolean marker selects the actual initializer coordinate. Its concrete receipt retains the corresponding supplied directional initial kernel; it does not identify sessions by equal key bytes. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins
open PqxdhInitialReceiptConstruction PqxdhInitialPendingPost
variable {A N I D K X Response : Type}

/-- The concrete retained optional initializer returns the exact selected supplied kernel on the original Boolean marker, with every ambient/cache field unchanged. -/
theorem initial_selected (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (root : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (marked : PqxdhInitialSelectedOrigin.mark source selected secrets = true) :
    initial (A := A) (N := N) source selected root response secrets =
      pure (some (PqxdhInitialRootAudit.kernel (root, response)).refined) := by
  have matching := (PqxdhInitialSelectedOrigin.selectedRequest_iff selected
    (PqxdhInitialRootLabelBridge.request source secrets)).mp marked
  funext state
  simp only [initial, PqxdhInitialNativeInitializer.selected_initial source selected root response secrets matching]
  rfl

/-- A marked source finish receipt contains the literal selected initializer kernel, before its first receive advances either direction. The marker is the original coordinate test, not a comparison of secret bytes. -/
theorem receipt_selected (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (root : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (InitialState A N) ProbComp))
    (calls : RawCtxChainOwner.Calls (KernelOf RatchetChain) (StateT (InitialState A N) ProbComp))
    (application : Response → StateT (InitialState A N) ProbComp (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K) (before : InitialState A N)
    (result : PqxdhInitialFinishReceipt.Result (KernelOf RatchetChain) Bool I D K Response
      PqxdhPhase2DecapsulationRouting.Shared × InitialState A N)
    (supported : result ∈ support ((PqxdhInitialFinishReceipt.owner
      (PqxdhInitialSelectedOrigin.mark source selected) pre calls application
      (initial source selected root response) decode raw entry).run before))
    (receipt : PqxdhInitialFinishReceipt.Receipt (KernelOf RatchetChain) Response PqxdhPhase2DecapsulationRouting.Shared)
    (recorded : result.1.2 = some receipt) (marked : result.1.1.2 = some true) :
    receipt.initial = (PqxdhInitialRootAudit.kernel (root, response)).refined := by
  obtain ⟨control, prekey, oneTime, kem, atPrepared, atInitial, staged, phase, prepared,
    initialized, finished, tagged⟩ := PqxdhInitialFinishReceipt.owner_origin
      (PqxdhInitialSelectedOrigin.mark source selected) pre calls application
      (initial source selected root response) decode raw entry before result supported receipt recorded
  rw [tagged] at marked
  obtain ⟨payload, _, same⟩ := Option.map_eq_some_iff.mp marked
  rw [initial_selected source selected root response receipt.prepared.root same] at initialized
  simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at initialized
  exact initialized.1

section Interpretation
variable {κ Kernel Shared Origin : Type} {spec : OracleSpec κ} {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem prepared_interpretation (impl : QueryImpl spec m)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (application : Response → OracleComp spec (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → OracleComp spec (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) :
    simulateQ impl (PqxdhInitialFinishReceipt.prepared mark calls application initial decode control entry pending) =
      PqxdhInitialFinishReceipt.prepared mark
        (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls)
        (fun reply => simulateQ impl (application reply))
        (fun secrets => simulateQ impl (initial secrets)) decode control entry pending := by
  simp only [PqxdhInitialFinishReceipt.prepared, simulateQ_bind]
  refine bind_congr fun kernel => ?_
  cases kernel <;> simp only [simulateQ_bind, simulateQ_pure, PqxdhInitialPendingPost.after_interpretation]

private theorem owner_interpretation (impl : QueryImpl spec m)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (OracleComp spec))
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (application : Response → OracleComp spec (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → OracleComp spec (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) :
    simulateQ impl (PqxdhInitialFinishReceipt.owner mark pre calls application initial decode raw entry) =
      PqxdhInitialFinishReceipt.owner mark (impl ∘ₛ pre)
        (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls)
        (fun reply => simulateQ impl (application reply))
        (fun secrets => simulateQ impl (initial secrets)) decode raw entry := by
  unfold PqxdhInitialFinishReceipt.owner
  cases phase : entry.beacon.phase <;> simp only [simulateQ_pure]
  simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose]
  refine bind_congr fun pending => ?_
  cases pending <;> simp only [simulateQ_pure, prepared_interpretation]

private theorem receipt_presence {State : Type}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → StateT State ProbComp (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (before : State)
    (result : PqxdhInitialFinishReceipt.Result Kernel Origin I D K Response Shared × State)
    (supported : result ∈ support ((PqxdhInitialFinishReceipt.owner mark pre calls application initial decode raw entry).run before)) :
    result.1.1.2.isSome = result.1.1.1.1.isSome ∧
      (result.1.1.1.1.isSome = true → result.1.2.isSome = true) := by
  have erased := PqxdhInitialFinishReceipt.owner_erase mark pre calls application initial decode raw entry
  have projected : (result.1.1, result.2) ∈ support
      ((PqxdhInitialFinishOrigin.owner mark pre calls application initial decode raw entry).run before) := by
    rw [← erased, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  refine ⟨PqxdhInitialFinishOrigin.published mark pre calls application initial decode raw entry before _ projected, ?_⟩
  intro accepted
  simpa only [PqxdhInitialFinishReceipt.successful, accepted, ite_true] using
    PqxdhInitialFinishReceipt.published mark pre calls application initial decode raw entry before result supported

end Interpretation

section Traces
open PqxdhInitialInstallOccurrence RawCtxProtocolReveals
variable {S B : Nat} {Shared : Type}

/-- Every owner labelled by the original selected-coordinate marker has a literal installation receipt with the corresponding directional initializer. Unlabelled preexisting owners carry no assertion. -/
def Selected (serverInitial : RustM (KernelOf RatchetChain)) (beaconInitial : KernelOf RatchetChain)
    (origins : PqxdhInitialOriginPost.Trace Bool S B)
    (receipts : Trace RatchetChain Response Shared S B) : Prop :=
  ∀ owner, origins.installed owner = some true →
    ∃ occurrence, receipts.installed owner = some occurrence ∧
      match owner with
      | .server _ _ => serverInitial = .ok (initialKernel occurrence.evidence)
      | .beacon _ => initialKernel occurrence.evidence = beaconInitial

private theorem finish_selected
    (serverInitial : RustM (KernelOf RatchetChain)) (beaconInitial : KernelOf RatchetChain)
    (origins : PqxdhInitialOriginPost.Trace Bool S B) (receipts : Trace RatchetChain Response Shared S B)
    (valid : Selected serverInitial beaconInitial origins receipts)
    (index : Fin B) (raw : Pqxdh.Bytes)
    (result : PqxdhInitialFinishReceipt.Result (KernelOf RatchetChain) Bool I D K Response Shared)
    (presence : result.1.2.isSome = result.1.1.1.isSome)
    (recorded : result.1.1.1.isSome = true → result.2.isSome = true)
    (selected : ∀ receipt, result.2 = some receipt → result.1.2 = some true → receipt.initial = beaconInitial) :
    Selected serverInitial beaconInitial (PqxdhInitialOriginPost.finish origins index result.1.2)
      (finished (begin receipts) receipts.nextAttempt index raw result.2 result.1.1.1.isSome) := by
  cases tag : result.1.2 with
  | none =>
    have failed : result.1.1.1.isSome = false := by simpa only [tag, Option.isSome_none] using presence.symm
    cases result.2 <;> simpa only [Selected, PqxdhInitialOriginPost.finish, finished, failed,
      PqxdhInitialInstallOccurrence.note, Bool.false_eq_true, ite_false, begin] using valid
  | some flag =>
    have accepted : result.1.1.1.isSome = true := by simpa only [tag, Option.isSome_some] using presence.symm
    obtain ⟨receipt, receiptEq⟩ := Option.isSome_iff_exists.mp (recorded accepted)
    intro owner labelled
    by_cases same : owner = .beacon index
    · subst owner
      simp only [PqxdhInitialOriginPost.finish, Function.update_self, Option.some.injEq] at labelled
      refine ⟨⟨⟨.beacon index, receipts.nextAttempt⟩, .beacon raw receipt⟩, ?_, selected receipt receiptEq (tag.trans (congrArg some labelled))⟩
      simp only [finished, receiptEq, accepted, PqxdhInitialInstallOccurrence.note, ite_true, Function.update_self]
    · simp only [PqxdhInitialOriginPost.finish, Function.update_of_ne same] at labelled
      simpa only [finished, receiptEq, accepted, PqxdhInitialInstallOccurrence.note, ite_true,
        Function.update_of_ne same, begin] using valid owner labelled

/-- Combining actual receipt provenance with the existing retained path invariant gives both directional paths from the selected supplied initializer for the current marked owner. -/
theorem selected_path {M P I D K AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (prior : RawCtxSelectedParentTable.Prior)
    (serverInitial : RustM (KernelOf RatchetChain)) (beaconInitial : KernelOf RatchetChain)
    (front : Front RatchetChain M P I D K S B) (origins : PqxdhInitialOriginPost.Trace Bool S B)
    (receipts : Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B)
    (selected : Selected serverInitial beaconInitial origins receipts)
    (paths : PqxdhInitialOccurrencePaths.Holds cr prior front receipts)
    (owner : Owner S B) (marked : origins.installed owner = some true)
    (kernel : KernelOf RatchetChain)
    (found : RawCtxGenericRoleFamily.selectedKernel owner front.roles.1 = some kernel) :
    ∃ initial : KernelOf RatchetChain,
      (match owner with
      | .server _ _ => serverInitial = .ok initial
      | .beacon _ => initial = beaconInitial) ∧
      RoleReachable
        (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
        initial.send_chain initial.receive_chain ⟨kernel⟩ := by
  obtain ⟨occurrence, installed, exactInitial⟩ := selected owner marked
  cases owner <;> exact ⟨initialKernel occurrence.evidence, exactInitial, paths _ occurrence installed kernel found⟩

end Traces

section Source
variable {ι M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior)
    (selected : PqxdhCorrelatedExtractFamily.Message) (root : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (InitialState A N) ProbComp))
    (application : Response → StateT (InitialState A N) ProbComp (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (InitialState A N) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (InitialState A N) ProbComp))
local notation "sourceHandler" => PqxdhInitialOccurrencePaths.handler (S := S) (B := B)
  source writer prior selected root response pre application selector aux
local notation "mark" => PqxdhInitialSelectedOrigin.mark source selected

/-- The actual occurrence interpreter supplies the selected initializer law inside the complete finish program. No independent initializer callback premise is needed. -/
theorem handler_receipt_selected (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K) (before : InitialState A N)
    (result : PqxdhInitialFinishReceipt.Result (KernelOf RatchetChain) Bool I D K Response
      PqxdhPhase2DecapsulationRouting.Shared × InitialState A N)
    (supported : result ∈ support ((simulateQ sourceHandler
      (PqxdhInitialFinishReceipt.owner mark preForward calls applicationForward initialForward decode raw entry)).run before))
    (receipt : PqxdhInitialFinishReceipt.Receipt (KernelOf RatchetChain) Response PqxdhPhase2DecapsulationRouting.Shared)
    (recorded : result.1.2 = some receipt) (marked : result.1.1.2 = some true) :
    receipt.initial = (PqxdhInitialRootAudit.kernel (root, response)).refined := by
  rw [owner_interpretation] at supported
  apply receipt_selected source selected root response (sourceHandler ∘ₛ preForward)
    (RawCtxGenericOwnerInterpretation.interpretedCalls sourceHandler calls)
    (fun reply => simulateQ sourceHandler (applicationForward reply)) decode raw entry before result
    ?_ receipt recorded marked
  simpa only [initialForward, simulateQ_spec_query, PqxdhInitialOccurrencePaths.handler,
    PqxdhInitialPendingPost.handler] using supported

/-- Every complete original Post operation preserves the link from the Boolean coordinate marker to the actual supplied directional initializer. Original optional replies and all backend effects remain in the same source interpreter. -/
theorem step_selected (serverInitial : RustM (KernelOf RatchetChain))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (entry : PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Bool S B)
    (before : InitialState A N)
    (valid : Selected serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined entry.1.2 entry.2)
    (result : ((PqxdhInitialGenericPost.Spec extra S B).Range query ×
      PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Bool S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ sourceHandler
      ((PqxdhInitialInstallOccurrence.compiler mark sender route decode query).run entry)).run before)) :
    Selected serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined result.1.2.1.2 result.1.2.2 := by
  rcases query with (query | query) | ⟨index, raw⟩
  · simp only [PqxdhInitialInstallOccurrence.compiler, PqxdhInitialOriginPost.compiler, StateT.run,
      bind_pure_comp, Functor.map_map, simulateQ_map] at supported
    change result ∈ support (StateT.run _ before) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    exact valid
  · simp only [PqxdhInitialInstallOccurrence.compiler, PqxdhInitialOriginPost.compiler, StateT.run,
      bind_pure_comp, Functor.map_map, simulateQ_map] at supported
    change result ∈ support (StateT.run _ before) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    exact valid
  · simp only [PqxdhInitialInstallOccurrence.compiler, StateT.run, bind_pure_comp,
      simulateQ_map] at supported
    change result ∈ support (StateT.run _ before) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    have interpreted := reached
    rw [owner_interpretation] at interpreted
    have presence := receipt_presence mark (sourceHandler ∘ₛ preForward)
      (RawCtxGenericOwnerInterpretation.interpretedCalls sourceHandler calls)
      (fun reply => simulateQ sourceHandler (applicationForward reply))
      (fun secrets => simulateQ sourceHandler (initialForward secrets)) decode raw _ before completed interpreted
    exact finish_selected serverInitial _ entry.1.2 entry.2 valid index raw completed.1 presence.1 presence.2
      (fun receipt recorded marked => handler_receipt_selected source writer prior selected root response
        pre application selector aux decode raw _ before completed reached receipt recorded marked)

/-- The same selected-installation provenance survives every supported complete adaptive Post, including rejected finishes, disclosures and repeated record requests. -/
theorem program_selected {Result : Type} (serverInitial : RustM (KernelOf RatchetChain))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (entry : PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Bool S B)
    (before : InitialState A N)
    (valid : Selected serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined entry.1.2 entry.2)
    (result : (Result × PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Bool S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ sourceHandler
      ((simulateQ (PqxdhInitialInstallOccurrence.compiler mark sender route decode) client).run entry)).run before)) :
    Selected serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined result.1.2.1.2 result.1.2.2 := by
  induction client using OracleComp.inductionOn generalizing entry before result with
  | pure value =>
    simpa only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using supported ▸ valid
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
    change result ∈ support
      (((simulateQ sourceHandler
          ((PqxdhInitialInstallOccurrence.compiler mark sender route decode query).run entry)).run before) >>= fun reply =>
        ((simulateQ sourceHandler
          ((simulateQ (PqxdhInitialInstallOccurrence.compiler mark sender route decode) (next reply.1.1)).run reply.1.2)).run reply.2)) at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    exact ih reply.1.1 reply.1.2 reply.2
      (step_selected source writer prior selected root response pre application selector aux serverInitial
        sender route decode query entry before valid reply head) result tail

/-- The actual initial Server builder links its assigned-key Boolean marker to the same successful receipt and literal caller initializer. Failed and unpublished attempts preserve all prior installed labels. -/
theorem builder_selected (serverInitial : RustM (KernelOf RatchetChain))
    (beaconInitial : KernelOf RatchetChain) (origin : Bool)
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (entry : Front RatchetChain M P I D K S B) (before : InitialState A N)
    (origins : PqxdhInitialOriginPost.Trace Bool S B)
    (receipts : PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B)
    (valid : Selected serverInitial beaconInitial origins receipts)
    (result : ((RustM (Option PqxdhServerRegistrationPublication.Response) ×
      Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf RatchetChain))) × Front RatchetChain M P I D K S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ sourceHandler
      ((PqxdhInitialBuilderReceipt.build source serverInitial sender index metadata ready).run entry)).run before)) :
    Selected serverInitial beaconInitial
      (PqxdhInitialOriginPost.afterBuilder origins result.1.2 index origin result.1.1.1)
      (PqxdhInitialInstallOccurrence.built (PqxdhInitialInstallOccurrence.begin receipts) receipts.nextAttempt
        ready index result.1.2 result.1.1.1 result.1.1.2) := by
  cases answer : result.1.1.1 with
  | fail error =>
    cases result.1.1.2 <;> simpa only [Selected, PqxdhInitialOriginPost.afterBuilder,
      PqxdhInitialInstallOccurrence.built, PqxdhInitialInstallOccurrence.note, Bool.false_eq_true,
      ite_false, PqxdhInitialInstallOccurrence.begin] using valid
  | div =>
    cases result.1.1.2 <;> simpa only [Selected, PqxdhInitialOriginPost.afterBuilder,
      PqxdhInitialInstallOccurrence.built, PqxdhInitialInstallOccurrence.note, Bool.false_eq_true,
      ite_false, PqxdhInitialInstallOccurrence.begin] using valid
  | ok optional =>
    cases optional with
    | none =>
      cases result.1.1.2 <;> simpa only [Selected, PqxdhInitialOriginPost.afterBuilder,
        PqxdhInitialInstallOccurrence.built, PqxdhInitialInstallOccurrence.note, Bool.false_eq_true,
        ite_false, PqxdhInitialInstallOccurrence.begin] using valid
    | some reply =>
      obtain ⟨receipt, recorded, initialized, keyEq, advanced, encrypted, atSend, atSent, peer, sent⟩ :=
        PqxdhInitialReceiptPublication.build_published sourceHandler source serverInitial sender index metadata
          ready entry before result supported reply answer
      rw [keyEq] at peer
      simp only [Selected, PqxdhInitialOriginPost.afterBuilder, peer, PqxdhInitialInstallOccurrence.built,
        recorded, keyEq, decide_true, Option.isSome_some, Bool.and_self, PqxdhInitialInstallOccurrence.note,
        ite_true, PqxdhInitialInstallOccurrence.begin]
      intro owner labelled
      by_cases same : owner = .server index receipt.candidate.key_id
      · subst owner
        exact ⟨_, Function.update_self _ _ _, initialized⟩
      · simpa only [Function.update_of_ne same] using valid owner
          (by simpa only [Function.update_of_ne same] using labelled)

/-- The actual first Builder and arbitrary complete Post construct selected directional provenance from empty analysis labels. Arbitrary preexisting roles are never assigned a selected initializer by assumption. -/
theorem sequence_selected {Result : Type} (serverInitial : RustM (KernelOf RatchetChain))
    (origin : Bool) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (entry : Front RatchetChain M P I D K S B) (before : InitialState A N)
    (result : (Result × PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Bool S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ sourceHandler
      ((PqxdhInitialInstallOccurrence.sequence source serverInitial mark origin sender route decode index metadata ready post).run
        ((entry, PqxdhInitialSourcePublication.empty), PqxdhInitialInstallOccurrence.empty))).run before)) :
    Selected serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined result.1.2.1.2 result.1.2.2 := by
  simp only [PqxdhInitialInstallOccurrence.sequence, StateT.run, simulateQ_bind] at supported
  change result ∈ support (StateT.run _ before) at supported
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨builtResult, builtSupported, rest⟩ := supported
  apply program_selected source writer prior selected root response pre application selector aux serverInitial
    sender route decode (post builtResult.1.1.1) _ builtResult.2 _ result rest
  apply builder_selected source writer prior selected root response pre application selector aux serverInitial
    _ origin sender index metadata ready entry before PqxdhInitialSourcePublication.empty
    PqxdhInitialInstallOccurrence.empty _ builtResult builtSupported
  intro owner impossible
  cases impossible

end Source
end BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins

/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.initial_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.initial_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.receipt_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.receipt_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.selected_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.selected_path
/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.handler_receipt_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.handler_receipt_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.step_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.step_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.program_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.program_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.builder_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.builder_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.sequence_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedSelectedOrigins.sequence_selected
