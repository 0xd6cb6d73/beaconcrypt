import BeaconcryptCore.Computational.PqxdhLaterChallengePaths

/-! Chronological attribution of the original marked publication to the actual later challenge request. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin
open PqxdhInitialReceiptConstruction PqxdhInitialPendingPost PqxdhLaterChallengePaths
variable {ι A N M P I D K X Response : Type} {extra : OracleSpec ι} {S B : Nat}

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

/-- Every marked publication added by a source query records the marker installed before that exact query. Failed and successful finish operations can change the current marker, but cannot add a record publication. -/
theorem source_publication (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : SourceState A N M P I D K Response S B)
    (result : (PqxdhInitialGenericPost.Spec extra S B).Range query × SourceState A N M P I D K Response S B)
    (supported : result ∈ support ((impl query).run before))
    (publication : RawCtxPublishedRecords.Publication S B) :
    (publication, true) ∈ result.2.1.1.2.published ↔
      (publication, true) ∈ before.1.1.2.published ∨
      publication ∈ PqxdhRecordConfidentialityChallenge.publications query result.1 ∧
        before.1.1.2.installed publication.1 = some true := by
  simp only [sourceHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨actual, supported, rfl⟩ := supported
  rcases query with (query | query) | ⟨index, raw⟩
  · simp only [PqxdhInitialInstallOccurrence.compiler, PqxdhInitialOriginPost.compiler, StateT.run,
      bind_pure_comp, Functor.map_map, simulateQ_map] at supported
    change actual ∈ support (StateT.run _ before.2) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨completed, _, rfl⟩ := supported
    exact PqxdhInitialOriginPost.record_member before.1.1.2 query completed.1.1 publication true
  · simp only [PqxdhInitialInstallOccurrence.compiler, PqxdhInitialOriginPost.compiler, StateT.run,
      bind_pure_comp, Functor.map_map, simulateQ_map] at supported
    change actual ∈ support (StateT.run _ before.2) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    simp only [PqxdhRecordConfidentialityChallenge.publications, List.not_mem_nil, false_and, or_false]
  · simp only [PqxdhInitialInstallOccurrence.compiler, bind_pure_comp, simulateQ_map] at supported
    change actual ∈ support (StateT.run _ before.2) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨completed, _, rfl⟩ := supported
    cases tag : completed.1.1.2 <;> simp only [PqxdhInitialOriginPost.finish, tag,
      PqxdhRecordConfidentialityChallenge.publications, List.not_mem_nil, false_and, or_false]

set_option backward.isDefEq.respectTransparency false in
/-- A successful publication in the actual source record branch identifies the installed kernel before that query and its exact old counter. -/
theorem source_record_kernel (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : SourceState A N M P I D K Response S B)
    (result : (RawCtxProtocolReveals.SourceSpec S B).Range query × SourceState A N M P I D K Response S B)
    (supported : result ∈ support ((impl (.inl (.inl query))).run before))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (recorded : (owner, number) ∈ RawCtxPublishedRecords.record query result.1) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.1.roles.1 = some kernel ∧
      number.val = kernel.control.send_sequence.val + 1 := by
  simp only [sourceHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨actual, supported, rfl⟩ := supported
  simp only [PqxdhInitialInstallOccurrence.compiler, PqxdhInitialOriginPost.compiler, StateT.run,
    bind_pure_comp, Functor.map_map, simulateQ_map] at supported
  change actual ∈ support (StateT.run _ before.2) at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨completed, reached, rfl⟩ := supported
  have interpreted := source_records source writer prior selected root response pre application selector aux sender route decode query before.1.1.1.roles
  simp only [StateT.run] at interpreted
  rw [interpreted] at reached
  exact RawCtxNativeSendSequence.live _ (fun kernel => kernel.control.send_sequence.val)
    (fun entry context state result supported sent published =>
      (RawCtxNativeSendSequence.native _ entry context state result supported sent published).1)
    _ _ sender route decode query before.1.1.1.roles before.2 completed reached owner number recorded

open PqxdhFirstRecordConfidentiality (AdvSpec)
open PqxdhRecordConfidentialityChallenge PqxdhRecordConfidentialityTrace

/-- After the chosen challenge, its unchanged wrapper excludes every other target publication. The complete source suffix therefore preserves exactly whether the marked target publication was already present. -/
theorem used_publication {Result : Type}
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result) (before : State)
    (ambient : SourceState A N M P I D K Response S B)
    (result : (Result × State) × SourceState A N M P I D K Response S B)
    (traced : Trace impl owner number bit client before ambient result)
    (used : before.pair.isSome) (target : Target number result.1.2) :
    ((owner, number), true) ∈ result.2.1.1.2.published ↔
      ((owner, number), true) ∈ ambient.1.1.2.published := by
  induction traced with
  | pure => rfl
  | query query next before ambient step result actual tail ih =>
    rcases query with query | ⟨left, right⟩
    · obtain ⟨reply, returned, projected, excluded⟩ :=
        forwarded_excluded impl owner number bit query next before ambient step result actual tail target
      exact (ih (by simpa only [projected, observe] using used) target).trans
        (by simpa only [excluded, false_and, or_false] using
          (source_publication source writer prior selected root response pre application selector aux sender route decode
            query ambient (reply, step.2) returned (owner, number)))
    · simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run, used, true_or, ite_true,
        simulateQ_pure] at actual
      change step ∈ support (pure ((none, before), ambient)) at actual
      simp only [mem_support_pure_iff] at actual
      subst step
      exact ih used target

/-- Before the accepted challenge, the sticky wrapper flag excludes every competing target send. Rejected challenge attempts are retained and cannot create a marked target publication. -/
theorem unused_publication {Result : Type}
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result) (before current : State)
    (ambient reached : SourceState A N M P I D K Response S B)
    (traced : Reaches impl owner number bit client before ambient rest current reached)
    (unused : current.pair = none) (clear : current.otherTarget = false) :
    ((owner, number), true) ∈ reached.1.1.2.published ↔
      ((owner, number), true) ∈ ambient.1.1.2.published := by
  induction traced with
  | here => rfl
  | later query next before ambient step rest current reached actual tail ih =>
    have kept := reaches_kept impl owner number bit (next step.1.1) rest step.1.2 current step.2 reached tail
    rcases query with query | ⟨left, right⟩
    · have forwarded : (PqxdhRecordConfidentialityChallenge.handler (extra := extra) owner number bit (.inl query)).run before =
          (fun reply => (screen before query reply, observe owner number before query reply)) <$>
            ((PqxdhFirstRecordConfidentiality.ConfPostSpec extra S B).query query :
              OracleComp (PqxdhFirstRecordConfidentiality.ConfPostSpec extra S B) _) := by
        simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run, bind_pure_comp]
      rw [forwarded, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at actual
      obtain ⟨reply, returned, rfl⟩ := actual
      have excluded := ((observe_target owner number before query reply.1).mp (kept.2 clear)).2
      exact (ih unused clear).trans (by
        simpa only [excluded, false_and, or_false] using
          (source_publication source writer prior selected root response pre application selector aux sender route decode
            query ambient reply returned (owner, number)))
    · simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run] at actual
      split at actual
      · simp only [simulateQ_pure] at actual
        change step ∈ support (pure ((none, before), ambient)) at actual
        simp only [mem_support_pure_iff] at actual
        subst step
        exact ih unused clear
      · simp only [bind_pure_comp, simulateQ_map] at actual
        change step ∈ support (StateT.run _ ambient) at actual
        rw [StateT.run_map, support_map] at actual
        obtain ⟨reply, _, rfl⟩ := actual
        have impossible := (kept.1 (by rfl)).1
        simp only [unused, reduceCtorEq] at impossible

set_option backward.isDefEq.respectTransparency false in
/-- A successful literal challenge send appends its actual returned owner/sequence with the marker read before that send. -/
theorem send_publication (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (before after : SourceState A N M P I D K Response S B) (record : RawCtxSourceSend.Encrypted)
    (supported : (some record, after) ∈ support ((simulateQ impl (send owner plaintext)).run before)) :
    ((owner, record.sequence), true) ∈ after.1.1.2.published ↔
      ((owner, record.sequence), true) ∈ before.1.1.2.published ∨ before.1.1.2.installed owner = some true := by
  cases owner with
  | server index peer =>
    have actual := source_publication source writer prior selected root response pre application selector aux sender route decode
      (sendRequest (extra := extra) (.server index peer) plaintext) before (some record, after)
      (by simpa only [send, simulateQ_spec_query] using supported) (.server index peer, record.sequence)
    simpa only [publications, sendRequest, RawCtxPublishedRecords.record, List.mem_singleton, true_and] using actual
  | beacon index =>
    have actual := source_publication source writer prior selected root response pre application selector aux sender route decode
      (sendRequest (extra := extra) (.beacon index) plaintext) before (some record, after)
      (by simpa only [send, simulateQ_spec_query] using supported) (.beacon index, record.sequence)
    simpa only [publications, sendRequest, RawCtxPublishedRecords.record, List.mem_singleton, true_and] using actual

set_option backward.isDefEq.respectTransparency false in
/-- The actual challenge send exposes the pre-send installed kernel and the increment relating its counter to the returned record, for either role. -/
theorem send_kernel (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (before after : SourceState A N M P I D K Response S B) (record : RawCtxSourceSend.Encrypted)
    (supported : (some record, after) ∈ support ((simulateQ impl (send owner plaintext)).run before)) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.1.roles.1 = some kernel ∧
      record.sequence.val = kernel.control.send_sequence.val + 1 := by
  cases owner with
  | server index peer =>
    exact source_record_kernel source writer prior selected root response pre application selector aux sender route decode
      (.inl (.inl ⟨index, .inl (plaintext, peer)⟩)) before (some record, after)
      (by simpa only [send, sendRequest, simulateQ_spec_query] using supported) (.server index peer) record.sequence
      (by simp only [RawCtxPublishedRecords.record, List.mem_singleton])
  | beacon index =>
    exact source_record_kernel source writer prior selected root response pre application selector aux sender route decode
      (.inl (.inr (.inl ⟨index, .inl plaintext⟩))) before (some record, after)
      (by simpa only [send, sendRequest, simulateQ_spec_query] using supported) (.beacon index) record.sequence
      (by simp only [RawCtxPublishedRecords.record, List.mem_singleton])

/-- The unchanged final marked-publication event and the wrapper's competing-publication exclusion identify the marker at the actual challenge request. Later reinstallation cannot supply this witness. -/
theorem marked_request {Result : Type}
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result)
    (left right : Pqxdh.Bytes)
    (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
    (before current : State) (ambient reached after : SourceState A N M P I D K Response S B)
    (record : RawCtxSourceSend.Encrypted)
    (result : (Result × State) × SourceState A N M P I D K Response S B)
    (traced : Reaches impl owner number bit client before ambient
      ((AdvSpec extra S B).query (.inr (left, right)) >>= next) current reached)
    (unused : current.pair = none) (clear : current.otherTarget = false)
    (sent : (some record, after) ∈ support ((simulateQ impl (send owner (if bit then right else left))).run reached))
    (tail : Trace impl owner number bit (next (some record))
      { current with pair := some (left, right), reply := some (some record) } after result)
    (sequence : record.sequence = number) (target : Target number result.1.2)
    (absent : ((owner, number), true) ∉ ambient.1.1.2.published)
    (recorded : ((owner, number), true) ∈ result.2.1.1.2.published) :
    reached.1.1.2.installed owner = some true := by
  have atSend := (used_publication source writer prior selected root response pre application selector aux sender route decode
    owner number bit (next (some record)) _ after result tail (by rfl) target).mp recorded
  have atRequest := send_publication source writer prior selected root response pre application selector aux sender route decode
    owner (if bit then right else left) reached after record sent
  rw [sequence] at atRequest
  exact (atRequest.mp atSend).resolve_left (fun earlier => absent
    ((unused_publication source writer prior selected root response pre application selector aux sender route decode
      owner number bit client _ before current ambient reached traced unused clear).mp earlier))

/-- The same actual challenge request simultaneously has a source-established selected path, a marked owner and the exact pre-send counter. The complete request and suffix witnesses are retained. -/
theorem request_facts {Result AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (serverInitial : RustM (KernelOf RatchetChain))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result)
    (left right : Pqxdh.Bytes)
    (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
    (before current : State) (ambient reached after : SourceState A N M P I D K Response S B)
    (record : RawCtxSourceSend.Encrypted)
    (result : (Result × State) × SourceState A N M P I D K Response S B)
    (initial : Valid cr prior serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined ambient)
    (traced : Reaches impl owner number bit client before ambient
      ((AdvSpec extra S B).query (.inr (left, right)) >>= next) current reached)
    (unused : current.pair = none) (clear : current.otherTarget = false)
    (sent : (some record, after) ∈ support ((simulateQ impl (send owner (if bit then right else left))).run reached))
    (tail : Trace impl owner number bit (next (some record))
      { current with pair := some (left, right), reply := some (some record) } after result)
    (sequence : record.sequence = number) (target : Target number result.1.2)
    (absent : ((owner, number), true) ∉ ambient.1.1.2.published)
    (recorded : ((owner, number), true) ∈ result.2.1.1.2.published) :
    Valid cr prior serverInitial (PqxdhInitialRootAudit.kernel (root, response)).refined reached ∧
      reached.1.1.2.installed owner = some true ∧
      ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner reached.1.1.1.roles.1 = some kernel ∧
        number.val = kernel.control.send_sequence.val + 1 := by
  refine ⟨source_reaches source writer prior selected root response pre application selector aux sender route decode
    cr serverInitial owner number bit client _ before current ambient reached initial traced,
    marked_request source writer prior selected root response pre application selector aux sender route decode
      owner number bit client left right next before current ambient reached after record result traced unused clear sent tail
      sequence target absent recorded, ?_⟩
  simpa only [sequence] using send_kernel source writer prior selected root response pre application selector aux sender route decode
    owner (if bit then right else left) reached after record sent

/-- The literal first Builder and complete challenge Post supply the request-time marker, kernel and counter from the original final publication event; there is no incoming source-path or old-publication premise. -/
theorem sequence_request {Selection AD PT CT : Type}
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
    (accepted : result.1.1 = true)
    (later : 2 ≤ number.val)
    (published : ((owner, number), true) ∈ result.1.2.1.2.published) :
    ∃ reply ambient final left right,
      ∃ (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Bool),
      ∃ current reached after record,
      Reaches impl owner number bit (adversary selection reply) initial ambient
        ((AdvSpec extra S B).query (.inr (left, right)) >>= next) current reached ∧
      current.pair = none ∧ left.length = right.length ∧ current.otherTarget = false ∧
      (some record, after) ∈ support ((simulateQ impl (send owner (if bit then right else left))).run reached) ∧
      Trace impl owner number bit (next (some record))
        { current with pair := some (left, right), reply := some (some record) } after
        ((true, final), (result.1.2, result.2)) ∧
      record.sequence = number ∧ Target number final ∧
      Valid cr prior (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
        (PqxdhInitialRootAudit.kernel (root, response)).refined reached ∧
      reached.1.1.2.installed owner = some true ∧
      ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner reached.1.1.1.roles.1 = some kernel ∧
        number.val = kernel.control.send_sequence.val + 1 := by
  obtain ⟨reply, ambient, final, valid, origin, target, absent⟩ := sequence_origin source writer prior selected root response
    pre application selector aux sender route decode cr serverResponse origin index metadata input adversary owner number bit
      selection entry before result supported accepted
  obtain ⟨left, right, next, current, reached, after, record, traced, unused, length, clear, sent, tail, sequence⟩ := origin
  exact ⟨reply, ambient, final, left, right, next, current, reached, after, record, traced, unused, length, clear,
    sent, tail, sequence, target, request_facts source writer prior selected root response pre application selector aux
      sender route decode cr _ owner number bit (adversary selection reply) left right next initial current ambient reached
        after record ((true, final), (result.1.2, result.2)) valid traced unused clear sent tail sequence target (absent later) published⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.source_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.source_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.source_record_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.source_record_kernel
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.used_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.used_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.unused_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.unused_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.send_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.send_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.send_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.send_kernel
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.marked_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.marked_request
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.request_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.request_facts
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.sequence_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeOrigin.sequence_request
