import BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement
import BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening

/-! The initial Beacon receive erases its selected material interpretation only after the actual optional reply and sequence-one gate. All component calls and rejected-receive effects are retained. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls

/-- The source normalizer preserves the exact optional opening reply. -/
theorem finish_reply {Send Receive Material Context Plaintext : Type}
    (pending : RawCtxInterpretedOpening.Opening Send Receive Material Context)
    (reply : core.option.Option Plaintext) :
    (RawCtxChainReceive.normalFinish pending reply).2 = reply := by
  have same := RawCtxChainReceive.normalFinish_native
    (fun _ : Send => RawCtxSelectedChain.unusedChain)
    (fun _ : Receive => RawCtxSelectedChain.unusedChain) pending reply
  exact (congrArg Prod.snd same).symm

/-- The actual opening wrapper returns its prepared sequence. A wrong registration sequence discards only the result after executing the unchanged opening service. -/
theorem opening_wrong (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (candidate : pqxdh.BeaconRegistrationCandidate) (native : Kernel → ConcreteRatchetKernel)
    (pending : RawCtxInterpretedOpening.Opening Chain Chain Material RawCtxWholeOwner.OpenContext)
    (target : Std.U64) (sequence : RawCtxInterpretedOpening.sequence pending = ok target)
    (wrong : target ≠ 1#u64) :
    (fun reply => PqxdhBeaconPhase2Publication.afterOpening candidate
      (native (RawCtxChainReceive.normalFinish pending reply).1)
      (RawCtxChainReceive.normalFinish pending reply).2) <$>
        receive source rest read expected (.inr pending) =
      (fun _ => none) <$> receive source rest read expected (.inr pending) := by
  simp only [receive, RawCtxSelectedOpenConsumer.service]
  cases found : RawCtxInterpretedArguments.openArguments (opening pending) with
  | none => simp only [map_pure, finish_reply, PqxdhBeaconPhase2Publication.afterOpening]
  | some input =>
    have fields := RawCtxSelectedOpenConsumer.arguments_some (opening pending) input found
    have targetEq : input.sequence = target := RustM.ok.inj
      (fields.2.1.symm.trans ((RawCtxChainInterpretation.opening_sequence_chains _ _ pending).trans sequence))
    simp only [Functor.map_map]
    congr 1
    funext reply
    cases reply <;> simp only [finish_reply,
      RawCtxSharedOpeningConsumer.apiReply, PqxdhBeaconPhase2Publication.afterOpening, targetEq,
      wrong, ne_eq, not_false_eq_true, ite_true]

/-- Every actual skipped-key continuation retains its target; a wrong-sequence final observation is empty without removing any oracle effect. -/
theorem program_wrong (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (candidate : pqxdh.BeaconRegistrationCandidate) (native : Kernel → ConcreteRatchetKernel)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (effect : RawCtxChainReceive.Effect Chain Chain Material RawCtxWholeOwner.OpenContext)
    (scope : Scope target context effect) (wrong : target ≠ 1#u64) :
    (fun result => PqxdhBeaconPhase2Publication.afterOpening candidate (native result.1) result.2) <$>
        simulateQ (receive source rest read expected) (RawCtxChainReceive.program effect) =
      (fun _ => none) <$> simulateQ (receive source rest read expected) (RawCtxChainReceive.program effect) := by
  generalize depth : RawCtxChainReceive.effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected entry actual =>
      simp only [RawCtxChainReceive.program, simulateQ_pure, map_pure,
        PqxdhBeaconPhase2Publication.afterOpening]
    | openRequested pending =>
      simp only [RawCtxChainReceive.program, simulateQ_spec_query, simulateQ_map,
        bind_pure_comp, Functor.map_map]
      exact opening_wrong source rest read expected candidate native pending target scope.1 wrong
    | kdfRequested pending =>
      simp only [RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query, receive, pure_bind]
      exact ih _ (depth ▸ RawCtxChainReceive.normalResume_rank pending (step source rest pending.request))
        _ (by simpa only [scope.1, scope.2] using resume_scope pending (step source rest pending.request)) rfl

/-- At the actual empty initial kernel, the post-opening registration observation is independent of every material map. Target one leaves no stored material; all other targets retain their actual receive effects before the original gate rejects them. -/
theorem execute_material (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (candidate : pqxdh.BeaconRegistrationCandidate) (first second : Material → RatchetMaterial)
    (send receiving : Chain) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (fun result => PqxdhBeaconPhase2Publication.afterOpening candidate
      (PqxdhServerAuthSendFactor.resolve (RawCtxMaterialInterpretation.mapRefined first result.1)) result.2) <$>
        simulateQ (receive source rest read expected)
          (RawCtxChainReceive.execute (PqxdhServerAuthBeaconFirstOpening.initial send receiving) target context) =
    (fun result => PqxdhBeaconPhase2Publication.afterOpening candidate
      (PqxdhServerAuthSendFactor.resolve (RawCtxMaterialInterpretation.mapRefined second result.1)) result.2) <$>
        simulateQ (receive source rest read expected)
          (RawCtxChainReceive.execute (PqxdhServerAuthBeaconFirstOpening.initial send receiving) target context) := by
  by_cases one : target = 1#u64
  · subst target
    have same := PqxdhServerAuthBeaconFirstOpening.execute_one_material
      (receive source rest read expected) first second send receiving context
    simpa only [Functor.map_map, Prod.map_def, id_eq] using congrArg
      (fun work => (fun result => PqxdhBeaconPhase2Publication.afterOpening candidate
        (PqxdhServerAuthSendFactor.resolve result.1) result.2) <$> work) same
  · exact (program_wrong source rest read expected candidate
      (fun entry => PqxdhServerAuthSendFactor.resolve (RawCtxMaterialInterpretation.mapRefined first entry))
      target context _ (begin_scope _ target context) one).trans
        (program_wrong source rest read expected candidate
          (fun entry => PqxdhServerAuthSendFactor.resolve (RawCtxMaterialInterpretation.mapRefined second entry))
          target context _ (begin_scope _ target context) one).symm

/-- The literal empty Beacon kernel with its first receive chain and material represented privately. -/
def initial (other : RootOutput) : Kernel :=
  PqxdhServerAuthBeaconFirstOpening.initial (.known (RawCtxFreshChainCut.concreteChain other)) .hidden

def localState (candidate : pqxdh.BeaconRegistrationCandidate) (other : RootOutput) :
    RawCtxChainOwner.State Kernel Unit :=
  ⟨initial other, candidate.server_binding.identity_key_id, absBytes candidate.associated_data, (), 0⟩

/-- Arbitrary raw bytes retain their parser/validation path and complete receive effects. Only the final registration observation forgets the material interpretation. -/
theorem raw_material (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (first second : Material → RatchetMaterial) :
    (fun result => PqxdhBeaconPhase2Publication.afterOpening candidate
      (PqxdhServerAuthSendFactor.resolve (RawCtxMaterialInterpretation.mapRefined first result.2.kernel)) result.1) <$>
        raw source rest read bytes (localState candidate rest.2.2) =
    (fun result => PqxdhBeaconPhase2Publication.afterOpening candidate
      (PqxdhServerAuthSendFactor.resolve (RawCtxMaterialInterpretation.mapRefined second result.2.kernel)) result.1) <$>
        raw source rest read bytes (localState candidate rest.2.2) := by
  unfold raw RawCtxChainOwner.rawReceive
  simp only [StateT.run]
  by_cases empty : bytes.isEmpty = true
  · simp only [empty, ite_true, map_pure, RawCtxChainOwner.publish,
      PqxdhBeaconPhase2Publication.afterOpening]
  · simp only [empty, Bool.false_eq_true, ite_false]
    cases decoded : read bytes with
    | none => simp only [map_pure, RawCtxChainOwner.publish, PqxdhBeaconPhase2Publication.afterOpening]
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame (localState candidate rest.2.2).expectedSender
          (localState candidate rest.2.2).associatedData frame
      · simp only [valid, ite_true, bind_pure_comp, Functor.map_map, RawCtxChainOwner.publish, calls]
        exact execute_material source rest read frame.sender candidate first second _ _ frame.sequence _
      · simp only [valid, ite_false, map_pure, RawCtxChainOwner.publish,
          PqxdhBeaconPhase2Publication.afterOpening]

/-- The final observation uses a fixed material resolver only after the checked gate; it does not add that resolver to any primitive query. -/
noncomputable def observe (candidate : pqxdh.BeaconRegistrationCandidate)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State Kernel Unit) :
    Option PqxdhBeaconPhase2Publication.Staged :=
  PqxdhBeaconPhase2Publication.afterOpening candidate
    (PqxdhServerAuthCtxBuildSettlement.resolve result.2.kernel) result.1

noncomputable def rawProgram (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (candidate : pqxdh.BeaconRegistrationCandidate) :=
  observe candidate <$> raw source rest read bytes (localState candidate rest.2.2)

/-- The actual factor-side raw owner and key-free final observation have the same staged result and entire shared cache after erasing component bookkeeping. All arbitrary-byte failure paths and returned challenger plaintext are retained. -/
theorem raw_observation {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (state : RawCtxSelectedReceiveCompiler.State A) :
    ((fun result => PqxdhBeaconPhase2Publication.afterOpening candidate
      (PqxdhServerAuthSendFactor.resolve result.2.kernel) result.1) <$>
        (RawCtxChainOwner.rawReceive (valueCalls source key rest) read bytes).run
          (mapOwner key (localState candidate rest.2.2))).run (RawCtxSelectedReceiveCompiler.project state) =
      Prod.map id RawCtxSelectedReceiveCompiler.project <$>
        (RawCtxSelectedReceiveCompiler.evaluated source key read
          (rawProgram source rest read bytes candidate)).run state := by
  have equal := raw_material source rest read bytes candidate (RawCtxSelectedMessageKey.interpret key)
    (RawCtxSelectedMessageKey.interpret ⟨List.replicate 32 0, by simp⟩)
  have interpreted := congrArg (fun work =>
    (RawCtxSelectedReceiveCompiler.evaluated source key read work).run state) equal
  simp only [RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map] at interpreted
  rw [StateT.run_map, PqxdhServerAuthCtxCalls.raw_source]
  simp only [Functor.map_map, mapOwner, interpret]
  rw [rawProgram, RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map]
  simp only [Functor.map_map, Prod.map_def, id_eq]
  simpa only [Functor.map_map, Prod.map_def, id_eq, observe, PqxdhServerAuthCtxBuildSettlement.resolve,
    PqxdhServerAuthCtxBuildSettlement.native, interpret] using
      congrArg (fun work => Prod.map id RawCtxSelectedReceiveCompiler.project <$> work) interpreted

open PqxdhServerAuthExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The material-value receive callback is the literal native primitive callback used by the source Beacon factor. -/
theorem native_labels (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (key : RootOutput) (rest : Residual) :
    PqxdhServerAuthBeaconFactor.primLabels (PqxdhServerAuthBeaconFactor.nativePrim setup codec) setup.source
      (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)).1 =
      valueReceive (A := Unit) setup.source key rest := by
  funext query
  cases query with
  | inl chain => rfl
  | inr pending =>
    simp only [PqxdhServerAuthBeaconFactor.primLabels, PqxdhServerAuthBeaconFactor.nativePrim,
      QueryImpl.apply_compose, valueReceive, RawCtxSourceOpen.ownerAdapter, QueryImpl.simulateQ_compose]

/-- The executable selected Beacon tail uses the real application getter and the complete raw service. It has no selected-message-key argument and returns the original optional staged result. -/
noncomputable def program (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option PqxdhBeaconPhase2Publication.Staged) :=
  let prepared := PqxdhPhase2DhRootConsumer.cleared pending
  let candidate := PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate
  match codec.application prepared.response with
  | none => pure none
  | some bytes => rawProgram source rest codec.frameRead bytes candidate

/-- The concrete source factor callback, including its original getter and staged state, is exactly the executable selected Beacon tail after full cache projection. No success, sequence or material-settlement premise remains. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (key : RootOutput) (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (state : RawCtxSelectedReceiveCompiler.State Unit) :
    (PqxdhServerAuthBeaconFactor.factored (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
      (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response))
      codec.frameRead (PqxdhPhase2DhRootConsumer.cleared pending)
      (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest))).run
        (RawCtxSelectedReceiveCompiler.project state) =
      Prod.map id RawCtxSelectedReceiveCompiler.project <$>
        (RawCtxSelectedReceiveCompiler.evaluated setup.source key codec.frameRead
          (program setup.source codec rest pending)).run state := by
  simp only [PqxdhServerAuthBeaconFactor.factored, program, pure_bind]
  cases obtained : codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response with
  | none =>
    rfl
  | some bytes =>
    simp only [PqxdhServerAuthBeaconFactor.primCalls, native_labels, bind_pure_comp]
    exact raw_observation setup.source key rest codec.frameRead bytes
      (PqxdhBeaconPhase2Publication.clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate) state

/-- The complete selected Beacon callback attempts at most one component call, including rejected parser, validation and opening paths. The source's local chain derivations remain in the program. -/
theorem program_bound (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    (program source codec rest pending).IsTotalQueryBound 1 := by
  unfold program
  dsimp only
  split
  · trivial
  · simpa only [rawProgram, IsTotalQueryBound, isQueryBound_map_iff] using
      raw_bound source rest codec.frameRead _ _

/-- The concrete callback issues neither selected seals nor uniform requests. Parser and getter rejection do not omit any attempted opening. -/
theorem program_other (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    (program source codec rest pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (program source codec rest pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  unfold program
  dsimp only
  split
  · exact ⟨by trivial, by trivial⟩
  · simpa only [rawProgram, isQueryBoundP_map_iff] using
      PqxdhServerAuthCtxSend.raw_other source rest codec.frameRead _ _

/-- Explicit attempted-call bills for the complete selected Beacon callback. The total cap is one; local real-HKDF derivations and interpreter sampling have their separate source bills. -/
theorem program_bills (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    (program source codec rest pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (program source codec rest pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 1 ∧
      (program source codec rest pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 ∧
      (program source codec rest pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  have total := (isQueryBoundP_true_iff _ _).2 (program_bound source codec rest pending)
  exact ⟨(program_other source codec rest pending).1,
    IsQueryBoundP.of_imp (fun _ _ => True.intro) total,
    IsQueryBoundP.of_imp (fun _ _ => True.intro) total,
    (program_other source codec rest pending).2⟩

end BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.finish_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.finish_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.opening_wrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.opening_wrong

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_wrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_wrong

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.execute_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.execute_material

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.raw_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.raw_material

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.raw_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.raw_observation

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.native_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.native_labels

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_other

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial.program_bills
