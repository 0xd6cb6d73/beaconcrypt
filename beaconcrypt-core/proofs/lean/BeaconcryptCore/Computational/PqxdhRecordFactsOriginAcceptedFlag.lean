-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive

/-! Actual accepted source operations raise their exact selected replay marker. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Private Service ServiceSpec)
open PqxdhRecordFactsOriginMuteUntilBad (openingBad serviceBad rawBad)
variable {n : Nat}

/-- An actual successful erased opening identifies its real selected material and raises that coordinate's replay marker through the same source parser and argument gates. -/
theorem opening_result_bad (read : RawCtxReceive.FrameDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (opened : RawCtxWholeOwner.Decrypted)
    (accepted : (PqxdhRecordFactsHashLocal.openingResult read pending state).1 = .Some opened) :
    ∃ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) ∧
      RawCtxInterpretedOpening.sequence pending = .ok opened.sequence ∧
      serviceBad label (RawCtxUniversalDecoder.decoder read) (.opening pending) state = true := by
  unfold PqxdhRecordFactsHashLocal.openingResult at accepted
  split at accepted
  · cases accepted
  · rename_i slices payload
    split at accepted
    · cases accepted
    · rename_i input arguments
      split at accepted
      · rename_i width
        refine ⟨input.material, ?_, ?_, ?_⟩
        · simpa only [RawCtxChainInterpretation.opening_material_chains] using
            PqxdhRecordLiftCtxAvailability.openArguments_material _ input arguments
        · have actual := (PqxdhRecordLiftCtxHybrid.openArguments_facts _ input arguments).1
          cases reply : (PqxdhRecordFactsHashLocal.keyedRawResult (RawCtxUniversalDecoder.decoder read)
            input.material (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
              (PqxdhRecordLiftIdeal.materialAt state.base.chain input.material).2 input.context width)) state).1 with
          | none => simp only [reply, RawCtxSharedOpeningConsumer.apiReply, reduceCtorEq] at accepted
          | some plaintext =>
              simp only [reply, RawCtxSharedOpeningConsumer.apiReply] at accepted
              cases accepted
              simpa only [RawCtxChainInterpretation.opening_sequence_chains] using actual
        · simp only [serviceBad, openingBad, payload, arguments, width, dite_true, rawBad, ite_true]
          cases reply : (PqxdhRecordFactsHashLocal.keyedRawResult (RawCtxUniversalDecoder.decoder read)
            input.material (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
              (PqxdhRecordLiftIdeal.materialAt state.base.chain input.material).2 input.context width)) state).1 <;>
            simp_all only [RawCtxSharedOpeningConsumer.apiReply, Option.isSome_some,
              reduceCtorEq]
      · cases accepted

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A literal successful source opening callback raises the marker for its actual material coordinate, retaining its complete poststate and plaintext. -/
theorem opening_accepted_bad (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n) (before after : CtxPrivate n)
    (opened : RawCtxWholeOwner.Decrypted)
    (supported : (.Some opened, after) ∈ support
      ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.opening pending)).run before)) :
    ∃ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) ∧
      RawCtxInterpretedOpening.sequence pending = .ok opened.sequence ∧
      serviceBad label (RawCtxUniversalDecoder.decoder codec.frameRead) (.opening pending) before = true := by
  rw [PqxdhRecordFactsHashLocal.opening_source, support_pure, Set.mem_singleton_iff] at supported
  exact opening_result_bad codec.frameRead pending before opened (congrArg Prod.fst supported.symm)

/-- A successful opening at the selected coordinate forces the actual marker to true, for either initial marker and every complete source poststate. -/
theorem marked_opening_accepted (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n)
    (material : RawCtxInterpretedOpening.material pending = .ok (.Some target))
    (before after : CtxPrivate n) (flag nextFlag : Bool) (opened : RawCtxWholeOwner.Decrypted)
    (supported : (.Some opened, (after, nextFlag)) ∈ support
      ((PqxdhRecordFactsOriginMuteAdaptive.marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (.opening pending)).run (before, flag))) :
    nextFlag = true := by
  simp only [PqxdhRecordFactsOriginMuteAdaptive.marked, StateT.run,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reply, reached, same⟩ := supported
  have accepted : reply.1 = .Some opened := (congrArg Prod.fst same).symm
  obtain ⟨label, selected, _, hit⟩ := opening_accepted_bad modes replace setup codec pending before reply.2 opened
    (by simpa only [← accepted, Prod.mk.eta, StateT.run] using reached)
  have labelEq : label = target := by cases selected.symm.trans material; rfl
  simpa only [← labelEq, hit, Bool.or_true] using congrArg (fun value => value.2.2) same

/-- Once the selected replay marker is raised, every actual adaptive continuation retains it while preserving the full source result and state. -/
theorem marked_program_sticky {X : Type} (target : Label n) (decode : RawDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (before : CtxPrivate n × Bool) (initial : before.2 = true)
    (result : X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordFactsOriginMuteAdaptive.marked target decode impl) work).run before)) :
    result.2.2 = true := by
  exact PqxdhRecordLiftFlat.support_keep_oracle
    (PqxdhRecordFactsOriginMuteAdaptive.marked target decode impl) (fun state => state.2 = true)
    (fun query state raised reply reached =>
      PqxdhRecordFactsOriginMuteAdaptive.marked_sticky target decode impl query state raised reply reached)
    work before initial result supported

/-- Source coordinate attribution and the returned sequence identify the exact marker, rather than merely an equal final dictionary entry. -/
theorem marked_opening_attributed (target anchor : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n)
    (attributed : PqxdhRecordLiftMaterialTable.EffectAttributed anchor (.openRequested pending))
    (slot : target.slot = anchor.slot) (direction : target.direction = anchor.direction)
    (before after : CtxPrivate n) (flag nextFlag : Bool) (opened : RawCtxWholeOwner.Decrypted)
    (position : target.position + 1 = opened.sequence.val)
    (supported : (.Some opened, (after, nextFlag)) ∈ support
      ((PqxdhRecordFactsOriginMuteAdaptive.marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (.opening pending)).run (before, flag))) :
    nextFlag = true := by
  have original : (.Some opened, after) ∈ support
      ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.opening pending)).run before) := by
    rw [← PqxdhRecordFactsOriginMuteAdaptive.marked_erase target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (.opening pending) (before, flag)]
    rw [support_map]
    exact ⟨(.Some opened, (after, nextFlag)), supported, rfl⟩
  obtain ⟨label, material, sequence, _⟩ := opening_accepted_bad modes replace setup codec pending before after opened original
  obtain ⟨actualSeq, selectedSeq, origin⟩ := PqxdhRecordLiftMaterialTable.opening_attributed anchor pending attributed label material
  have seqEq : actualSeq = opened.sequence := Aeneas.Std.RustM.ok.inj (selectedSeq.symm.trans sequence)
  have posEq : label.position = target.position := by
    have sourcePosition := origin.2.2
    rw [seqEq] at sourcePosition
    change opened.sequence.val = label.position + 1 at sourcePosition
    omega
  have labelEq : label = target := by
    have slotEq : label.slot = target.slot := origin.1.trans slot.symm
    have directionEq : label.direction = target.direction := origin.2.1.trans direction.symm
    cases label
    cases target
    simp_all
  exact marked_opening_accepted target modes replace setup codec pending (labelEq ▸ material) before after flag nextFlag opened supported

/-- Interpret the original recursive receive with only the selected replay marker added to the private state. -/
noncomputable def markedReceiveRun (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext)
    (state : CtxPrivate n × Bool) : ProbComp
      ((PqxdhRecordLiftWorldCompiler.LabeledKernel n × CoreModels.core.option.Option RawCtxWholeOwner.Decrypted) × (CtxPrivate n × Bool)) :=
  (simulateQ (PqxdhRecordFactsOriginMuteAdaptive.marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec))
    (simulateQ PqxdhRecordLiftProtocol.localLift (PqxdhRecordLiftOpaqueDrivers.receiveProgram effect))).run state

/-- A successful source receive raises the marker at its actual slot, direction, and returned sequence, through every skipped-key callback. -/
theorem receive_accepted_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (entry : PqxdhRecordLiftWorldCompiler.LabeledKernel n) (context : RawCtxWholeOwner.OpenContext)
    (sequence : Aeneas.Std.U64) (aligned : PqxdhRecordLiftChainState.Aligned entry)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext)
    (tracked : PqxdhRecordLiftChainState.Tracked entry context effect)
    (admitted : PqxdhFirstRecordReplay.Admitted entry sequence effect)
    (attributed : PqxdhRecordLiftMaterialTable.EffectAttributed entry.receive_chain effect)
    (slot : target.slot = entry.receive_chain.slot) (direction : target.direction = entry.receive_chain.direction)
    (before : CtxPrivate n × Bool)
    (result : (PqxdhRecordLiftWorldCompiler.LabeledKernel n × CoreModels.core.option.Option RawCtxWholeOwner.Decrypted) × (CtxPrivate n × Bool))
    (supported : result ∈ support (markedReceiveRun target modes replace setup codec effect before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2 = true := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect before result with
  | h depth ih =>
      cases effect with
      | rejected original prior =>
          simp only [markedReceiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          simp only [supported, reduceCtorEq] at accepted
      | openRequested pending =>
          simp only [markedReceiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, bind_pure_comp,
            simulateQ_map, simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift,
            StateT.run_map, support_map] at supported
          obtain ⟨reply, reached, rfl⟩ := supported
          have serviceAccepted : reply.1 = .Some opened := (PqxdhRecordFactsOriginReceive.finish_reply pending reply.1).symm.trans accepted
          exact marked_opening_attributed target entry.receive_chain modes replace setup codec pending attributed slot direction
            before.1 reply.2.1 before.2 reply.2.2 opened position
            (by simpa only [← serviceAccepted, Prod.mk.eta] using reached)
      | kdfRequested pending =>
          simp only [markedReceiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind,
            simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift, StateT.run_bind,
            mem_support_bind_iff] at supported
          obtain ⟨looked, reached, continued⟩ := supported
          exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending
            (PqxdhRecordLiftChainState.advance pending.request 1, pending.request)) _
            (PqxdhRecordLiftChainState.resume_tracked entry context pending pending.request tracked)
            (PqxdhFirstRecordReplay.resume_admitted entry sequence pending
              (PqxdhRecordLiftChainState.advance pending.request 1, pending.request) admitted)
            (PqxdhRecordLiftMaterialTable.resume_source_attributed entry context sequence pending aligned tracked admitted
              attributed.1 attributed.2) looked.2 result continued accepted rfl

/-- The actual admitted source kernel supplies every recursive attribution premise from its existing certificate. -/
theorem admitted_accepted_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (entry : PqxdhRecordLiftWorldCompiler.LabeledKernel n) (context : RawCtxWholeOwner.OpenContext)
    (sequence : Aeneas.Std.U64) (certified : PqxdhRecordLiftChainCoordinates.Certified entry)
    (slot : target.slot = entry.receive_chain.slot) (direction : target.direction = entry.receive_chain.direction)
    (before : CtxPrivate n × Bool)
    (result : (PqxdhRecordLiftWorldCompiler.LabeledKernel n × CoreModels.core.option.Option RawCtxWholeOwner.Decrypted) × (CtxPrivate n × Bool))
    (supported : result ∈ support (markedReceiveRun target modes replace setup codec
      (RawCtxChainReceive.normalBegin entry sequence context) before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2 = true := by
  exact receive_accepted_flag target modes replace setup codec entry context sequence certified.2.1 _
    (PqxdhRecordLiftChainState.begin_tracked entry context sequence)
    (PqxdhFirstRecordReplay.begin_admitted entry sequence context certified.1.capacity)
    (PqxdhRecordLiftMaterialTable.begin_attributed entry.receive_chain entry certified.2.2 sequence context)
    slot direction before result supported opened accepted position

/-- Every successful actual hidden kernel receive raises the selected opposite-direction coordinate's marker at the returned sequence. -/
theorem kernel_accepted_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (role : PqxdhRecordLiftInterface.Role)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : PqxdhRecordLiftWorldCompiler.LabeledKernel n)
    (oriented : PqxdhRecordLiftWorldProvenance.Oriented role (.hidden slot entry))
    (targetSlot : target.slot = slot)
    (direction : target.direction = !PqxdhRecordLiftWorldProvenance.sendDirection role)
    (sequence : Aeneas.Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (before : CtxPrivate n × Bool)
    (result : (PqxdhRecordLiftWorldCompiler.StoredKernel n × CoreModels.core.option.Option RawCtxWholeOwner.Decrypted) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordFactsOriginMuteAdaptive.marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec))
      (PqxdhRecordLiftProtocol.kernelReceive (.hidden slot entry) sequence context)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2 = true := by
  simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
    StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact admitted_accepted_flag target modes replace setup codec entry context sequence oriented.1
    (targetSlot.trans oriented.2.1.2.symm) (direction.trans oriented.2.2.2.symm)
    before inner reached opened accepted position

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.opening_result_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.opening_result_bad

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.opening_accepted_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.opening_accepted_bad

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.marked_opening_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.marked_opening_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.marked_program_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.marked_program_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.marked_opening_attributed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.marked_opening_attributed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.receive_accepted_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.receive_accepted_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.admitted_accepted_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.admitted_accepted_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.kernel_accepted_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag.kernel_accepted_flag
