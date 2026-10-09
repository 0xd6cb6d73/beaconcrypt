-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld
import BeaconcryptCore.Computational.RawCtxSelectedOpenScope
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid
import BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive

/-! Actual receive results retain their decoded source sequence and sender metadata. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata
open PqxdhRecordLiftWorldCompiler (Label StoredKernel)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
variable {n : Nat}

/-- The target and immutable context of every labelled receive capability. -/
def Scope {Send Receive Material Context : Type} (target : Std.U64) (context : Context) :
    RawCtxChainReceive.Effect Send Receive Material Context → Prop
  | .rejected _ actual => actual = context
  | .kdfRequested pending => pending.target = target ∧ pending.context = context
  | .openRequested pending => RawCtxInterpretedOpening.sequence pending = .ok target ∧ pending.context = context

/-- Arbitrary chain interpretations retain precisely the source target and immutable context. -/
theorem scope_native {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (target : Std.U64) (context : Context) (effect : RawCtxChainReceive.Effect Send Receive Material Context) :
    RawCtxSelectedOpenScope.Scope target context (RawCtxChainReceive.nativeEffect send receive effect) ↔
      Scope target context effect := by
  cases effect with
  | rejected => rfl
  | kdfRequested => rfl
  | openRequested pending =>
    simp only [RawCtxChainReceive.nativeEffect, RawCtxSelectedOpenScope.Scope, Scope,
      RawCtxChainInterpretation.opening_sequence_chains]
    rfl

/-- Literal labelled admission retains the decoded target and context through cached, future and rejected paths. -/
theorem begin_scope {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (entry : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    Scope target context (RawCtxChainReceive.normalBegin entry target context) := by
  apply (scope_native send receive target context _).mp
  rw [← RawCtxChainReceive.normalBegin_native]
  exact RawCtxSelectedOpenScope.begin_scope _ target context

/-- Every typed labelled derivation response retains the same requested target and context. -/
theorem resume_scope {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : RawCtxChainReceive.Kdf Send Receive Material Context) (reply : Receive × Material) :
    Scope pending.target pending.context (RawCtxChainReceive.normalResume pending reply) := by
  apply (scope_native send receive pending.target pending.context _).mp
  rw [← RawCtxChainReceive.normalResume_native]
  exact RawCtxSelectedOpenScope.resume_scope _ _


/-- Literal accepted hidden openings retain their selected sequence and immutable source context. -/
theorem opening_metadata (read : RawCtxReceive.FrameDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (opened : RawCtxWholeOwner.Decrypted)
    (accepted : (PqxdhRecordFactsHashLocal.openingResult read pending state).1 = .Some opened) :
    RawCtxInterpretedOpening.sequence pending = .ok opened.sequence ∧
      opened.keyId = pending.context.frame.sender := by
  unfold PqxdhRecordFactsHashLocal.openingResult at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · rename_i input arguments
      split at accepted
      · simp only [RawCtxSharedOpeningConsumer.apiReply] at accepted
        split at accepted
        · cases accepted
        · cases accepted
          have facts := PqxdhRecordLiftCtxHybrid.openArguments_facts _ _ arguments
          constructor
          · simpa only [RawCtxChainInterpretation.opening_sequence_chains] using facts.1
          · have context := congrArg (fun context => context.frame.sender) facts.2
            cases pending; exact context
      · cases accepted


open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftChainState (advance)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every supported complete erased opening reply has its own source sequence and sender. -/
theorem erased_opening_metadata (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
      (.opening pending)).run state))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1 = .Some opened) :
    RawCtxInterpretedOpening.sequence pending = .ok opened.sequence ∧
      opened.keyId = pending.context.frame.sender := by
  rw [PqxdhRecordFactsHashLocal.opening_source, support_pure, Set.mem_singleton_iff] at supported
  subst result
  exact opening_metadata codec.frameRead pending state opened accepted

noncomputable def receiveRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext)
    (state : CtxPrivate n) :=
  (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (simulateQ PqxdhRecordLiftProtocol.localLift
      (PqxdhRecordLiftOpaqueDrivers.receiveProgram effect))).run state

/-- Skipped derivations and commitment retain metadata from the same original decoded target and context. -/
theorem receive_metadata (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (send receive : Label n → RatchetChain) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext)
    (scope : Scope target context effect) (state : CtxPrivate n)
    (result : (PqxdhRecordLiftWorldCompiler.LabeledKernel n ×
      core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support (receiveRun modes replace setup codec effect state))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    opened.sequence = target ∧ opened.keyId = context.frame.sender := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
    cases effect with
    | rejected entry prior =>
      simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at accepted
    | openRequested pending =>
      simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift,
        StateT.run_map, support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      have serviceAccepted := (PqxdhRecordFactsOriginReceive.finish_reply pending reply.1).symm.trans accepted
      have metadata := erased_opening_metadata modes replace setup codec pending state reply reached opened serviceAccepted
      exact ⟨RustM.ok.inj (metadata.1.symm.trans scope.1), metadata.2.trans (congrArg (fun c => c.frame.sender) scope.2)⟩
    | kdfRequested pending =>
      simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind,
        simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨looked, _, continued⟩ := supported
      apply ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ _ looked.2 result continued accepted rfl
      simpa only [scope.1, scope.2] using resume_scope send receive pending (advance pending.request 1, pending.request)


/-- The actual hidden kernel admission supplies target scope for every cached, future, and rejection path. -/
theorem hidden_kernel_metadata (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : PqxdhRecordLiftWorldCompiler.LabeledKernel n)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) (state : CtxPrivate n)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelReceive (.hidden slot entry) target context)).run state))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    opened.sequence = target ∧ opened.keyId = context.frame.sender := by
  simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
    StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  let interpret := PqxdhRecordLiftChainTable.chain (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain
  exact receive_metadata modes replace setup codec interpret interpret target context _
    (begin_scope interpret interpret entry target context) state inner reached opened accepted

/-- A successful hidden owner receive returns the sequence and sender of the exact decoded raw frame. -/
theorem owner_receive_metadata (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : PqxdhRecordLiftWorldCompiler.LabeledKernel n)
    (hidden : owner.kernel = .hidden slot entry) (state : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive read raw owner)).run state))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.1 = .Some opened) :
    ∃ frame, read raw = some frame ∧ opened.sequence = frame.sequence ∧ opened.keyId = frame.sender := by
  unfold PqxdhRecordLiftProtocol.ownerReceive at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at accepted
  · split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at accepted
    · rename_i frame decoded
      split at supported
      · simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        rw [hidden] at reached
        exact ⟨frame, decoded, hidden_kernel_metadata modes replace setup codec slot entry frame.sequence
          ⟨raw, frame, owner.associatedData⟩ state inner reached opened accepted⟩
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        simp only [supported, reduceCtorEq] at accepted


/-- The literal publication callback preserves the accepted hidden owner's decoded metadata. -/
theorem owner_run_metadata (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : PqxdhRecordLiftWorldCompiler.LabeledKernel n)
    (hidden : owner.kernel = .hidden slot entry) (state : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender read (.inr raw) owner)).run state))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.1 = .Some opened) :
    ∃ frame, read raw = some frame ∧ opened.sequence = frame.sequence ∧ opened.keyId = frame.sender := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep, simulateQ_bind,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨inner, reached, continued⟩ := supported
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
  obtain ⟨published, _, equal⟩ := continued
  subst result
  exact owner_receive_metadata modes replace setup codec read raw owner slot entry hidden state
    inner reached opened accepted

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.scope_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.scope_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.begin_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.begin_scope

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.resume_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.resume_scope

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.opening_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.opening_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.erased_opening_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.erased_opening_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.receive_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.receive_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.hidden_kernel_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.hidden_kernel_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.owner_receive_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.owner_receive_metadata

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.owner_run_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceiveMetadata.owner_run_metadata
