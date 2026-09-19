import BeaconcryptCore.Computational.PqxdhInitialNativePath
import BeaconcryptCore.Computational.PqxdhInitialOriginPost
import BeaconcryptCore.Computational.PqxdhInitialNativeInitializer
import BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin

/-!
The actual first receive preserves the selected installed session's send path. Successful finish metadata is tied to the original prepared initializer coordinate and the returned source kernel. Failure and inactive branches retain their original publication behavior; an owner index alone does not identify the selected session.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialPendingPost PqxdhInitialNativeLog
variable {ι Chain M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

def beaconKernel (state : RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K) : Option (KernelOf Chain) :=
  match state.beacon.phase with | .established _ _ kernel => some kernel | _ => none

private theorem opening_kernel (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : KernelOf Chain)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : PqxdhInitialGenericBeacon.Staged (KernelOf Chain))
    (found : PqxdhInitialGenericBeacon.afterOpening candidate kernel reply = some staged) : staged.kernel = kernel := by
  cases reply with
  | none => cases found
  | some opened =>
    simp only [PqxdhInitialGenericBeacon.afterOpening] at found
    split at found
    · cases found
    · split at found
      · split at found
        · cases found
        · cases found; rfl
      · cases found

/-- Any installed kernel returned by the original terminal finish comes from its actual successful staged first receive. -/
theorem finish_kernel (control : pqxdh.BeaconInitSent)
    (before : RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K)
    (staged : Option (PqxdhInitialGenericBeacon.Staged (KernelOf Chain))) (kernel : KernelOf Chain)
    (found : beaconKernel (PqxdhInitialGenericBeacon.finish control before staged).2 = some kernel) :
    ∃ actual, staged = some actual ∧ actual.kernel = kernel ∧
      (PqxdhInitialGenericBeacon.finish control before staged).1.isSome = true := by
  cases staged with
  | none => cases found
  | some staged =>
    simp only [PqxdhInitialGenericBeacon.finish] at found ⊢
    split at found
    · cases found
    · split at found
      · cases found
      · exact ⟨staged, rfl, Option.some.inj found, by simp_all only [if_false, Option.isSome_some]⟩

private theorem finish_some (control : pqxdh.BeaconInitSent)
    (before : RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K)
    (staged : Option (PqxdhInitialGenericBeacon.Staged (KernelOf Chain))) :
    (beaconKernel (PqxdhInitialGenericBeacon.finish control before staged).2).isSome =
      (PqxdhInitialGenericBeacon.finish control before staged).1.isSome := by
  cases staged with
  | none => rfl
  | some staged =>
    simp only [PqxdhInitialGenericBeacon.finish]
    split
    · rfl
    · split <;> rfl

/-- The complete original first raw receive retains the initialized sender path through its actual application, opening and authentication result. -/
theorem after_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (root : RootOutput) (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) (kernel : KernelOf RatchetChain)
    (state : State A N C) (valid : RawCtxSourceSendPath.Path root ⟨kernel⟩ state.1.1.2.1)
    (result : Option (PqxdhInitialGenericBeacon.Staged (KernelOf RatchetChain)) × State A N C)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage external)
      (PqxdhInitialGenericBeacon.afterInitial calls applicationForward decode pending kernel)).run state)) :
    ∀ staged, result.1 = some staged → RawCtxSourceSendPath.Path root ⟨staged.kernel⟩ result.2.1.1.2.1 := by
  simp only [PqxdhInitialGenericBeacon.afterInitial, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨application, first, rest⟩ := supported
  have extension := PqxdhInitialNativePath.program_extends source writer stage external (applicationForward pending.response)
    state application first
  have valid' := RawCtxSourceSendPath.path_extends root ⟨kernel⟩ _ _ valid extension
  cases found : application.1 with
  | none =>
    simp only [found, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at rest
    subst result
    intro staged impossible
    cases impossible
  | some raw =>
    simp only [found, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
    obtain ⟨received, actual, finished⟩ := rest
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at finished
    subst result
    have preserved := PqxdhInitialNativePath.raw_path source writer stage external root decode raw
      (PqxdhInitialGenericBeacon.localOwner (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata) kernel)
      application.2 valid' received actual
    intro staged produced
    rw [opening_kernel _ _ _ staged produced]
    exact preserved.2

/-- An unmarked finish cannot install a replacement kernel: any remaining installed kernel is the same original inactive-session kernel. -/
theorem unmarked_kernel {AuxState Origin : Type}
    (impl : QueryImpl (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B) (StateT AuxState ProbComp))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K) (state : AuxState)
    (result : PqxdhInitialFinishOrigin.Result (KernelOf Chain) Origin I D K × AuxState)
    (supported : result ∈ support ((simulateQ impl
      (PqxdhInitialFinishOrigin.owner mark preForward calls applicationForward initialForward decode raw entry)).run state))
    (unmarked : result.1.2 = none) (kernel : KernelOf Chain) (found : beaconKernel result.1.1.2 = some kernel) :
    beaconKernel entry = some kernel := by
  rw [PqxdhInitialOriginPost.owner_interpretation] at supported
  have published := PqxdhInitialFinishOrigin.published mark _ _ _ _ decode raw entry state result supported
  have noReply : result.1.1.1.isSome = false := by
    rw [unmarked] at published
    exact published.symm
  unfold PqxdhInitialFinishOrigin.owner at supported
  cases phase : entry.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨prepared, preparation, rest⟩ := supported
    cases ready : prepared.1 with
    | none =>
      simp only [ready, StateT.run_pure, mem_support_pure_iff] at rest
      subst result
      cases found
    | some prepared =>
      simp only [ready, StateT.run_bind, mem_support_bind_iff] at rest
      obtain ⟨staged, tail, done⟩ := rest
      simp only [StateT.run_pure, mem_support_pure_iff] at done
      subst result
      change beaconKernel (PqxdhInitialGenericBeacon.finish control entry staged.1).2 = some kernel at found
      change (PqxdhInitialGenericBeacon.finish control entry staged.1).1.isSome = false at noReply
      have same := finish_some control entry staged.1
      rw [found, noReply] at same
      cases same
  all_goals
    simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact found


section Current
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpandHybrid

noncomputable def withInitial (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache)) :
    QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache)
  | .inl query => other (.inl query)
  | .inr (.inl reply) => other (.inr (.inl reply))
  | .inr (.inr (.inl secrets)) =>
      (Prod.snd <$> PqxdhInitialNativeInitializer.initial fixed selected previousRoot response secrets :
        PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache (Option (KernelOf RatchetChain)))
  | .inr (.inr (.inr query)) => other (.inr (.inr (.inr query)))

noncomputable def sendRoot (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response) : RootOutput :=
  RawCtxSelectedQueryTrace.rootVector (PqxdhInitialRootAudit.kernel (previousRoot, response)).refined.send_chain

/-- Matching the complete actual initializer coordinate returns the same original supplied-response kernel and retains every source interpreter field. -/
theorem initial_selected (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (chosen : PqxdhInitialSelectedOrigin.mark source selected secrets = true)
    (state : State A N RootOracle.QueryCache) :
    (simulateQ (handler (S := S) (B := B) source writer stage (withInitial source selected previousRoot response other))
      (initialForward secrets)).run state =
      pure (some (PqxdhInitialRootAudit.kernel (previousRoot, response)).refined, state) := by
  have matching := (PqxdhInitialSelectedOrigin.selectedRequest_iff selected
    (PqxdhInitialRootLabelBridge.request source secrets)).mp chosen
  simp only [initialForward, simulateQ_spec_query]
  rw [PqxdhInitialNativeLog.external_handler]
  simp only [withInitial, PqxdhInitialNativeInitializer.selected_initial source selected previousRoot response secrets matching]
  rfl

/-- The actual selected initial kernel starts its executed cache path at send counter zero under any already retained private cache. -/
theorem initial_path (source : FixedHkdfSha512NoSaltSource) (previousRoot : RootOutput)
    (response : PqxdhInitialRootLabelService.Response) (table : RawCtxKdfRequestTable.Table) :
    RawCtxSourceSendPath.Path (sendRoot previousRoot response)
      (PqxdhInitialRootAudit.kernel (previousRoot, response)) table := by
  refine ⟨[], ?_⟩
  rw [PqxdhInitialNativeInitializer.kernel_send_zero source (previousRoot, response)]
  rfl

/-- The complete first-receive tail from a matching actual initializer preserves that session's original directional path, with no target-chain or callback law supplied. -/
theorem selected_tail_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response PqxdhPhase2DecapsulationRouting.Shared)
    (chosen : PqxdhInitialSelectedOrigin.mark source selected pending.root = true)
    (state : State A N RootOracle.QueryCache)
    (result : Option (PqxdhInitialGenericBeacon.Staged (KernelOf RatchetChain)) × State A N RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage
      (withInitial source selected previousRoot response other))
      (PqxdhInitialGenericBeacon.tail calls applicationForward initialForward decode pending)).run state)) :
    ∀ staged, result.1 = some staged →
      RawCtxSourceSendPath.Path (sendRoot previousRoot response) ⟨staged.kernel⟩ result.2.1.1.2.1 := by
  simp only [PqxdhInitialGenericBeacon.tail, simulateQ_bind, StateT.run_bind] at supported
  rw [initial_selected source writer stage selected previousRoot response other pending.root chosen state] at supported
  simp only [pure_bind] at supported
  exact after_path source writer stage (withInitial source selected previousRoot response other)
    (sendRoot previousRoot response) decode pending _ state (initial_path source previousRoot response _) result supported

/-- A true origin on an actual successful finish identifies the installed selected-session kernel and its already initialized source path. -/
theorem marked_finish_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K)
    (state : State A N RootOracle.QueryCache)
    (result : PqxdhInitialFinishOrigin.Result (KernelOf RatchetChain) Bool I D K × State A N RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage
      (withInitial source selected previousRoot response other))
      (PqxdhInitialFinishOrigin.owner (PqxdhInitialSelectedOrigin.mark source selected)
        preForward calls applicationForward initialForward decode raw entry)).run state))
    (marked : result.1.2 = some true) :
    ∃ kernel, beaconKernel result.1.1.2 = some kernel ∧
      RawCtxSourceSendPath.Path (sendRoot previousRoot response) ⟨kernel⟩ result.2.1.1.2.1 := by
  rw [PqxdhInitialOriginPost.owner_interpretation] at supported
  obtain ⟨control, prekey, oneTime, kem, prepared, atTail, staged, phase, preparation, tail, finished, success, chosen⟩ :=
    PqxdhInitialFinishOrigin.origin (PqxdhInitialSelectedOrigin.mark source selected) _ _ _ _ decode raw entry state result supported true marked
  have actualTail : (staged, result.2) ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage
      (withInitial source selected previousRoot response other))
      (PqxdhInitialGenericBeacon.tail calls applicationForward initialForward decode prepared)).run atTail) := by
    rw [PqxdhInitialPendingPost.tail_interpretation]
    exact tail
  have paths := selected_tail_path source writer stage selected previousRoot response other decode prepared chosen.symm
    atTail (staged, result.2) actualTail
  have present : (beaconKernel (PqxdhInitialGenericBeacon.finish control entry staged).2).isSome = true := by
    rw [finish_some, ← finished]
    exact success
  cases found : beaconKernel (PqxdhInitialGenericBeacon.finish control entry staged).2 with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
  | some kernel =>
    obtain ⟨actual, produced, same, _⟩ := finish_kernel control entry staged kernel found
    refine ⟨kernel, ?_, ?_⟩
    · rw [finished]
      exact found
    · simpa only [same] using paths actual produced

end Current
end BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.finish_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.finish_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.after_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.after_path

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.unmarked_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.unmarked_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.initial_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.initial_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.initial_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.initial_path

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.selected_tail_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.selected_tail_path

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.marked_finish_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath.marked_finish_path
