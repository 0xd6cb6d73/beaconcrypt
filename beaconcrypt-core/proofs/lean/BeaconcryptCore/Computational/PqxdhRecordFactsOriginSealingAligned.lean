-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory

/-! Source-derived correspondence between each hidden sealing coordinate and its actual wire sequence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocolHistory
open PqxdhRecordLiftWorldCompiler (StoredKernel Owner Label)
open PqxdhRecordLiftWorldProvenance
variable {n : Nat}

/-- Only the actual hidden sealing request carries this local sequence obligation. -/
def SealingAligned : PqxdhRecordLiftProtocol.Service n → Prop
  | .sealing pending => pending.sequence.val = pending.material.position + 1
  | _ => True

/-- Certified source sends supply their actual sequence/coordinate equality before the optional writer responds. -/
theorem kernel_send (role : Role) (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (oriented : Oriented role stored) :
    (PqxdhRecordLiftProtocol.kernelSend stored context).AllQueriesSatisfy SealingAligned := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelSend, allQueriesSatisfy_query_bind_iff,
        allQueriesSatisfy_pure, SealingAligned]
      exact ⟨trivial, fun _ => trivial⟩
  | hidden slot entry =>
      have attributed := PqxdhRecordLiftMaterialTable.send_begin_attributed entry context oriented.1.2.1
      cases admitted : RawCtxChainSend.normalBegin entry context with
      | exhausted original prior =>
          simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
            admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure, pure_bind,
            allQueriesSatisfy_pure]
      | requested pending =>
          simp only [admitted] at attributed
          simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
            admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_spec_query,
            simulateQ_pure, PqxdhRecordLiftProtocol.localLift, bind_assoc, pure_bind,
            allQueriesSatisfy_query_bind_iff, allQueriesSatisfy_pure, SealingAligned,
            RawCtxChainSend.ready]
          exact ⟨trivial, fun _ => ⟨attributed.2.2, fun _ => trivial⟩⟩

/-- A complete hidden receive makes only lookup and opening requests, regardless of its recursive path. -/
theorem receive_program (effect : PqxdhRecordLiftChainCompiler.Effect (Slot n) RawCtxWholeOwner.OpenContext) :
    (simulateQ PqxdhRecordLiftProtocol.localLift
      (PqxdhRecordLiftOpaqueDrivers.receiveProgram effect)).AllQueriesSatisfy SealingAligned := by
  generalize depthEq : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
        simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure, allQueriesSatisfy_pure]
    | openRequested pending =>
        simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind, simulateQ_spec_query,
          simulateQ_pure, PqxdhRecordLiftProtocol.localLift, allQueriesSatisfy_query_bind_iff,
          allQueriesSatisfy_pure, SealingAligned]
        exact ⟨trivial, fun _ => trivial⟩
    | kdfRequested pending =>
        simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind, simulateQ_spec_query,
          PqxdhRecordLiftProtocol.localLift, allQueriesSatisfy_query_bind_iff, SealingAligned]
        exact ⟨trivial, fun _ => ih _ (depthEq ▸ RawCtxChainReceive.normalResume_rank pending
          (PqxdhRecordLiftChainState.advance pending.request 1, pending.request)) _ rfl⟩

/-- Known and hidden receive interfaces make no hidden sealing request. -/
theorem kernel_receive (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (PqxdhRecordLiftProtocol.kernelReceive stored target context).AllQueriesSatisfy SealingAligned := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive, allQueriesSatisfy_query_bind_iff,
        allQueriesSatisfy_pure, SealingAligned]
      exact ⟨trivial, fun _ => trivial⟩
  | hidden slot entry =>
      apply allQueriesSatisfy_bind (receive_program _)
      intro result
      exact allQueriesSatisfy_pure _ _

/-- The actual empty-input, parsing and validity gates preserve source sealing alignment for either selected-owner command. -/
theorem owner_step (role : Role) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (oriented : Oriented role owner.kernel) :
    (PqxdhRecordLiftProtocol.ownerStep sender decode query owner).AllQueriesSatisfy SealingAligned := by
  cases query with
  | inl plaintext =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerSend]
      split_ifs
      · exact allQueriesSatisfy_pure _ _
      · exact allQueriesSatisfy_bind (kernel_send role owner.kernel _ oriented) (fun _ => allQueriesSatisfy_pure _ _)
  | inr raw =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerReceive]
      repeat' split
      case h_2.isTrue =>
        exact allQueriesSatisfy_bind (kernel_receive owner.kernel _ _) (fun _ => allQueriesSatisfy_pure _ _)
      all_goals exact allQueriesSatisfy_pure _ _

/-- Publication follows the actual command without changing its sealing alignment obligation. -/
theorem owner_run (role : Role) (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (owner : Owner n) (oriented : Oriented role owner.kernel) :
    (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner).AllQueriesSatisfy SealingAligned := by
  apply allQueriesSatisfy_bind (owner_step role sender decode query owner oriented)
  intro result
  rw [allQueriesSatisfy_query_bind_iff]
  exact ⟨trivial, fun _ => allQueriesSatisfy_pure _ _⟩

/-- Actual Server routing derives the selected sender's certificate from the complete safe source control. -/
theorem server_step (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) :
    (PqxdhRecordLiftProtocol.serverStep decode route query control).AllQueriesSatisfy SealingAligned := by
  cases existing : control.server with
  | none =>
      cases query <;> simp only [PqxdhRecordLiftProtocol.serverStep, existing, allQueriesSatisfy_pure]
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected, allQueriesSatisfy_pure]
          | some peer =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected]
              exact allQueriesSatisfy_bind (owner_run .server _ server.sender decode (.inl plaintext) _
                (safe.1.1 server existing keyId peer selected)) (fun _ => allQueriesSatisfy_pure _ _)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, allQueriesSatisfy_pure]
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected, allQueriesSatisfy_pure]
              | some peer =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected]
                  exact allQueriesSatisfy_bind (owner_run .server _ server.sender decode (.inr raw) _
                    (safe.1.1 server existing keyId peer selected)) (fun _ => allQueriesSatisfy_pure _ _)

/-- Actual Beacon routing derives the established owner's certificate from the same safe source control. -/
theorem beacon_step (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) :
    (PqxdhRecordLiftProtocol.beaconStep decode owner query control).AllQueriesSatisfy SealingAligned := by
  cases selected : control.owners[owner]? with
  | none =>
      simp only [PqxdhRecordLiftProtocol.beaconStep, selected, allQueriesSatisfy_pure]
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;> simp only [PqxdhRecordLiftProtocol.beaconStep, selected, allQueriesSatisfy_pure]
      | established shell kernel =>
          simp only [PqxdhRecordLiftProtocol.beaconStep, selected]
          exact allQueriesSatisfy_bind (owner_run .beacon _ shell.identityKeyId decode query _
            (safe.1.2 _ (List.mem_of_getElem? selected))) (fun _ => allQueriesSatisfy_pure _ _)

/-- Resolving a newly admitted kernel allocates only its existing private slot. -/
theorem resolve (role : Role) (ref : KernelRef n) :
    (PqxdhRecordLiftProtocol.resolve role ref).AllQueriesSatisfy SealingAligned := by
  cases ref <;> simp only [PqxdhRecordLiftProtocol.resolve, allQueriesSatisfy_pure,
    allQueriesSatisfy_query_bind_iff, SealingAligned]
  exact ⟨trivial, fun _ => trivial⟩

/-- Administrative capabilities, including either installation path, never issue a hidden sealing request. -/
theorem capability (query : (CapabilitySpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    (PqxdhRecordLiftProtocol.capability query control).AllQueriesSatisfy SealingAligned := by
  cases query with
  | installServer keyId identity ref =>
      simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installServer]
      repeat' split
      all_goals first
        | exact allQueriesSatisfy_pure _ _
        | exact allQueriesSatisfy_bind (resolve .server ref) (fun _ => allQueriesSatisfy_pure _ _)
  | installBeacon owner shell ref =>
      simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installBeacon]
      split_ifs
      · exact allQueriesSatisfy_bind (resolve .beacon ref) (fun _ => allQueriesSatisfy_pure _ _)
      · exact allQueriesSatisfy_pure _ _
  | hash bytes =>
      change ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query (.hash bytes)) : OracleComp _ _) >>= fun reply =>
        pure (reply, control)).AllQueriesSatisfy SealingAligned
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, fun _ => allQueriesSatisfy_pure _ _⟩
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftProtocol.capability]
      repeat' split
      all_goals exact allQueriesSatisfy_pure _ _
  | peerPresent keyId => exact allQueriesSatisfy_pure _ _
  | ownerPresent owner => exact allQueriesSatisfy_pure _ _
  | appendOwner sender pin phase => exact allQueriesSatisfy_pure _ _

/-- Literal environment charges and coins preserve sealing alignment without interpreting their replies. -/
theorem effects (query : (EnvEffects n).Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    ((PqxdhRecordLiftProtocol.effects query).run control).AllQueriesSatisfy SealingAligned := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  change ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query (.charge (effectKind query))) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) >>= _).AllQueriesSatisfy SealingAligned
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun _ => ?_⟩
  cases query with
  | inl coin =>
      change ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query (.coin coin)) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) >>= _).AllQueriesSatisfy SealingAligned
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, fun _ => allQueriesSatisfy_pure _ _⟩
  | inr request => exact capability request control

/-- Every actual WorldSpec command derives sealing alignment from the source certificate. -/
theorem handler (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control) :
    ((PqxdhRecordLiftProtocol.handler decode route query).run control).AllQueriesSatisfy SealingAligned := by
  rcases query with created | (effect | (server | ⟨owner, record⟩))
  · change (PqxdhRecordLiftProtocol.initializeServer created control).AllQueriesSatisfy _
    unfold PqxdhRecordLiftProtocol.initializeServer
    split <;> exact allQueriesSatisfy_pure _ _
  · exact effects effect control
  · cases server with
    | inl input => exact server_step decode route (.inl input) control safe
    | inr raw => exact server_step decode route (.inr raw) control safe
  · cases record with
    | inl plaintext => exact beacon_step decode owner (.inl plaintext) control safe
    | inr raw => exact beacon_step decode owner (.inr raw) control safe

private theorem bind_supported {A B : Type} (first : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) A)
    (next : A → OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) B)
    (front : first.AllQueriesSatisfy SealingAligned)
    (tail : ∀ result ∈ support first, (next result).AllQueriesSatisfy SealingAligned) :
    (first >>= next).AllQueriesSatisfy SealingAligned := by
  classical
  apply (isQueryBoundP_zero_iff _ SealingAligned).mp
  simpa only [Nat.zero_add] using isQueryBoundP_bind
    ((isQueryBoundP_zero_iff _ SealingAligned).mpr front)
    (fun result supported => (isQueryBoundP_zero_iff _ SealingAligned).mpr (tail result supported))

/-- Every adaptive schedule maintains source safety before each actual command; all of its hidden sealing requests have their real sequence. -/
theorem schedule {Result : Type} (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) :
    (PqxdhRecordLiftProtocol.schedule decode route client control).AllQueriesSatisfy SealingAligned := by
  induction client using OracleComp.inductionOn generalizing control with
  | pure value =>
      simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_pure, StateT.run_pure, allQueriesSatisfy_pure]
  | query_bind query next ih =>
      simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply bind_supported _ _ (handler decode route query control safe)
      intro result supported
      exact ih result.1 result.2 (PqxdhRecordLiftProtocolHistory.handler decode route query control safe result supported).1

/-- The initialized actual environment/adversary program derives sealing sequence alignment for every typed reply path, without a target-honesty or cryptographic premise. -/
theorem program {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary).AllQueriesSatisfy SealingAligned :=
  schedule codec.frameRead route _ _ initial_safe

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.kernel_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.kernel_send

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.receive_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.receive_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.kernel_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.kernel_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.owner_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.owner_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.owner_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.owner_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.server_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.server_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.beacon_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.beacon_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.resolve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.resolve

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.capability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.handler

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned.program
