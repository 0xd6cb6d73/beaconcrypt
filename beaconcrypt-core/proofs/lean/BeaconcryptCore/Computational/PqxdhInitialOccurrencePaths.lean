import BeaconcryptCore.Computational.PqxdhInitialReceiptPublication

/-!
The actual occurrence trace follows installed kernels across the original outer Post schedule. New installations obtain their paths from literal source initializer receipts; original record operations preserve those paths under the same retained private table. Prior unlabelled owners remain unrestricted.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths
open PqxdhInitialReceiptConstruction PqxdhInitialPendingPost
variable {A N α β ι κ : Type} {spec : OracleSpec ι} {other : OracleSpec κ}

private def lift (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp α) :
    StateT (InitialState A N) ProbComp α := fun state =>
  (fun result => (result.1, ((result.2, state.1.2), state.2))) <$> work.run state.1.1

private theorem lift_pure (value : α) :
    lift (pure value : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp α) =
      (pure value : StateT (InitialState A N) ProbComp α) := rfl

private theorem lift_bind (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp α)
    (next : α → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β) :
    lift (work >>= next) = lift work >>= fun value => lift (N := N) (next value) := by
  funext state
  change (fun result => (result.1, ((result.2, state.1.2), state.2))) <$>
      (work state.1.1 >>= fun first => next first.1 first.2) =
    (((fun result => (result.1, ((result.2, state.1.2), state.2))) <$> work state.1.1) >>= fun first =>
      (fun result => (result.1, ((result.2, first.2.1.2), first.2.2))) <$> next first.1 first.2.1.1)
  simp only [map_bind, bind_map_left]

private theorem simulate_lift
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (client : OracleComp spec α) :
    simulateQ (fun query => lift (N := N) (impl query)) client = lift (simulateQ impl client) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact lift_pure value |>.symm
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lift_bind, ih]

private theorem compose_lift
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (adapter : QueryImpl other (OracleComp spec)) :
    (fun query => lift (N := N) (impl query)) ∘ₛ adapter =
      (fun query => lift ((impl ∘ₛ adapter) query)) := by
  funext query
  exact simulate_lift impl (adapter query)

noncomputable def native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT (InitialState A N) ProbComp) :=
  fun query => lift (RawCtxFunctionalFamily.native source writer prior query)

private theorem native_calls (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior) :
    RawCtxGenericNativeCalls.calls (native (A := A) (N := N) source writer prior) =
      PqxdhInitialReceiptPublication.nativeCalls source writer prior := by
  unfold RawCtxGenericNativeCalls.calls native
  simp only [compose_lift, simulate_lift, PqxdhInitialReceiptPublication.nativeCalls,
    PqxdhInitialBeaconAmbient.liftCalls, PqxdhInitialBeaconAmbient.lift,
    RawCtxGenericNativeCalls.calls, StateT.run, Functor.map_map]
  rfl

section Source
variable {I D K X Response M P Origin Result AD PT CT : Type} {S B : Nat} {extra : OracleSpec ι}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : PqxdhSecretInputKdf.RootOutput)
    (response64 : PqxdhInitialRootLabelService.Response)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (InitialState A N) ProbComp))
    (application : Response → StateT (InitialState A N) ProbComp (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (InitialState A N) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (InitialState A N) ProbComp))

noncomputable def publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT (InitialState A N) ProbComp) :=
  fun query => lift ((RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift) query)

noncomputable def handler :
    QueryImpl (Spec extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B)
      (StateT (InitialState A N) ProbComp) :=
  PqxdhInitialPendingPost.handler
    (RawCtxPendingNativeCalls.pending (native source writer prior) (publicCalls source writer prior))
    (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
    pre application (initial source selected previousRoot response64) selector aux

private theorem handler_calls :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux) calls =
        PqxdhInitialReceiptPublication.nativeCalls source writer prior := by
  have forwarding : handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux ∘ₛ
      primitiveForward = RawCtxPendingNativeCalls.pending (native source writer prior) (publicCalls source writer prior) := by
    funext query
    simp [QueryImpl.compose, primitiveForward, handler, PqxdhInitialPendingPost.handler,
      OracleSpec.query, RawCtxPendingFamilyLiveQueries.handler]
  have pending : RawCtxGenericOwnerInterpretation.interpretedCalls
      (handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux) calls =
        RawCtxGenericOwnerInterpretation.interpretedCalls
          (RawCtxPendingNativeCalls.pending (native source writer prior) (publicCalls source writer prior))
          RawCtxPendingOwnerQueries.calls := by
    simp only [calls, RawCtxGenericOwnerInterpretation.interpretedCalls, ← QueryImpl.simulateQ_compose, forwarding]
  exact pending.trans ((RawCtxPendingNativeCalls.calls_interpretation _ _).trans (native_calls source writer prior))

private theorem prepared_source
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response PqxdhPhase2DecapsulationRouting.Shared) :
    simulateQ (handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux)
      (PqxdhInitialFinishReceipt.prepared mark calls applicationForward initialForward decode control entry pending) =
        PqxdhInitialFinishReceipt.prepared mark (PqxdhInitialReceiptPublication.nativeCalls source writer prior)
          application (initial source selected previousRoot response64) decode control entry pending := by
  simp only [PqxdhInitialFinishReceipt.prepared, simulateQ_bind, initialForward, simulateQ_spec_query,
    handler, PqxdhInitialPendingPost.handler]
  apply bind_congr
  intro kernel
  cases kernel with
  | none => exact simulateQ_pure _ _
  | some kernel =>
    simp only [simulateQ_bind, PqxdhInitialPendingPost.after_interpretation]
    have actual := handler_calls (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux
    simp only [handler] at actual
    rw [actual]
    simp only [applicationForward, simulateQ_spec_query, PqxdhInitialPendingPost.handler, simulateQ_pure]

private theorem finish_source
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K) :
    simulateQ (handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux)
      (PqxdhInitialFinishReceipt.owner mark preForward calls applicationForward initialForward decode raw entry) =
        PqxdhInitialFinishReceipt.owner mark pre (PqxdhInitialReceiptPublication.nativeCalls source writer prior)
          application (initial source selected previousRoot response64) decode raw entry := by
  unfold PqxdhInitialFinishReceipt.owner
  cases phase : entry.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose]
    have forwarding : handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux ∘ₛ
        preForward = pre := by
      funext query
      simp [QueryImpl.compose, preForward, handler, PqxdhInitialPendingPost.handler, OracleSpec.query]
    rw [forwarding]
    apply bind_congr
    intro pending
    cases pending with
    | none => exact simulateQ_pure _ _
    | some pending =>
      exact prepared_source source writer prior selected previousRoot response64 pre application selector aux
        mark decode control entry pending
  all_goals exact simulateQ_pure _ _

private theorem finish_failed_kernel
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K) (before : InitialState A N)
    (result : PqxdhInitialFinishReceipt.Result (KernelOf RatchetChain) Origin I D K Response
      PqxdhPhase2DecapsulationRouting.Shared × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux)
      (PqxdhInitialFinishReceipt.owner mark preForward calls applicationForward initialForward decode raw entry)).run before))
    (failed : result.1.1.1.1.isSome = false) (kernel : KernelOf RatchetChain)
    (found : PqxdhInitialOriginFinishPath.beaconKernel result.1.1.1.2 = some kernel) :
    PqxdhInitialOriginFinishPath.beaconKernel entry = some kernel := by
  have original : (result.1.1, result.2) ∈ support ((simulateQ
      (handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux)
      (PqxdhInitialFinishOrigin.owner mark preForward calls applicationForward initialForward decode raw entry)).run before) := by
    rw [← PqxdhInitialFinishReceipt.owner_erase, simulateQ_map, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  have interpreted := original
  rw [PqxdhInitialOriginPost.owner_interpretation] at interpreted
  have presence := PqxdhInitialFinishOrigin.published mark _ _ _ _ decode raw entry before
    (result.1.1, result.2) interpreted
  have absent : result.1.1.2 = none := by
    cases observed : result.1.1.2 with
    | none => rfl
    | some marker => simp only [observed, Option.isSome_some, failed, Bool.true_eq_false] at presence
  exact PqxdhInitialOriginFinishPath.unmarked_kernel
    (handler source writer prior selected previousRoot response64 pre application selector aux)
      mark decode raw entry before (result.1.1, result.2) original absent kernel found

def AtOccurrence (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (prior : RawCtxSelectedParentTable.Prior)
    (occurrence : PqxdhInitialInstallOccurrence.Occurrence RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B)
    (kernel : KernelOf RatchetChain) : Prop :=
  RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
    (PqxdhInitialInstallOccurrence.initialKernel occurrence.evidence).send_chain
    (PqxdhInitialInstallOccurrence.initialKernel occurrence.evidence).receive_chain ⟨kernel⟩

private theorem finish_selected
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (index : Fin B)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K) (before : InitialState A N)
    (trace : PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B)
    (initialPaths : ∀ occurrence, trace.installed (.beacon index) = some occurrence →
      ∀ kernel, PqxdhInitialOriginFinishPath.beaconKernel entry = some kernel → AtOccurrence cr prior occurrence kernel)
    (result : PqxdhInitialFinishReceipt.Result (KernelOf RatchetChain) Origin I D K Response
      PqxdhPhase2DecapsulationRouting.Shared × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux)
      (PqxdhInitialFinishReceipt.owner mark preForward calls applicationForward initialForward decode raw entry)).run before)) :
    ∀ occurrence,
      (PqxdhInitialInstallOccurrence.finished (PqxdhInitialInstallOccurrence.begin trace)
        trace.nextAttempt index raw result.1.2 result.1.1.1.1.isSome).installed (.beacon index) = some occurrence →
      ∀ kernel, PqxdhInitialOriginFinishPath.beaconKernel result.1.1.1.2 = some kernel →
        AtOccurrence cr prior occurrence kernel := by
  intro occurrence labelled kernel found
  cases success : result.1.1.1.1.isSome
  case true =>
    have actual := supported
    rw [finish_source] at actual
    have presence := PqxdhInitialFinishReceipt.published mark pre
      (PqxdhInitialReceiptPublication.nativeCalls source writer prior) application
      (initial source selected previousRoot response64) decode raw entry before result actual
    cases recorded : result.1.2 with
    | none =>
      simp only [PqxdhInitialFinishReceipt.successful, success, ite_true, recorded,
        Option.isSome_none, Bool.false_eq_true] at presence
    | some receipt =>
      simp only [PqxdhInitialInstallOccurrence.finished, recorded, PqxdhInitialInstallOccurrence.note,
        success, ite_true, Function.update_self, Option.some.injEq] at labelled
      subst occurrence
      exact PqxdhInitialReceiptPublication.beacon_path source writer prior cr selected previousRoot response64
        mark pre application decode raw entry before result actual receipt recorded kernel found
  case false =>
    have oldLabel : trace.installed (.beacon index) = some occurrence := by
      cases recorded : result.1.2 <;>
        simpa only [PqxdhInitialInstallOccurrence.finished, recorded, PqxdhInitialInstallOccurrence.note,
          PqxdhInitialInstallOccurrence.begin, success, Bool.false_eq_true, ite_false] using labelled
    exact initialPaths occurrence oldLabel kernel (finish_failed_kernel source writer prior selected previousRoot response64
      pre application selector aux mark decode raw entry before result supported success kernel found)

def Holds (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (prior : RawCtxSelectedParentTable.Prior) (front : Front RatchetChain M P I D K S B)
    (trace : PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B) : Prop :=
  ∀ owner occurrence, trace.installed owner = some occurrence →
    ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner front.roles.1 = some kernel →
      AtOccurrence cr prior occurrence kernel

private theorem finish_other
    (trace : PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B)
    (index : Fin B) (raw : Pqxdh.Bytes)
    (receipt : Option (PqxdhInitialFinishReceipt.Receipt (KernelOf RatchetChain) Response PqxdhPhase2DecapsulationRouting.Shared))
    (published : Bool) (owner : RawCtxProtocolReveals.Owner S B) (different : owner ≠ .beacon index) :
    (PqxdhInitialInstallOccurrence.finished (PqxdhInitialInstallOccurrence.begin trace)
      trace.nextAttempt index raw receipt published).installed owner = trace.installed owner := by
  cases receipt with
  | none => rfl
  | some receipt =>
    simp only [PqxdhInitialInstallOccurrence.finished, PqxdhInitialInstallOccurrence.note]
    split <;> simp only [PqxdhInitialInstallOccurrence.begin, Function.update_of_ne different]

private theorem install_other
    (front : Front RatchetChain M P I D K S B) (index : Fin B)
    (after : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K)
    (owner : RawCtxProtocolReveals.Owner S B) (different : owner ≠ .beacon index) :
    RawCtxGenericRoleFamily.selectedKernel owner (install index front after).roles.1 =
      RawCtxGenericRoleFamily.selectedKernel owner front.roles.1 := by
  cases owner with
  | server server peer => rfl
  | beacon beacon =>
    have unequal : beacon ≠ index := fun same => different (congrArg RawCtxProtocolReveals.Owner.beacon same)
    simp only [RawCtxGenericRoleFamily.selectedKernel, install, Function.update_of_ne unequal]

private theorem selected_beacon (front : Front RatchetChain M P I D K S B) (index : Fin B) :
    RawCtxGenericRoleFamily.selectedKernel (.beacon index) front.roles.1 =
      PqxdhInitialOriginFinishPath.beaconKernel (front.roles.1.2 index) := by
  cases phase : (front.roles.1.2 index).beacon.phase <;>
    simp only [RawCtxGenericRoleFamily.selectedKernel, PqxdhInitialOriginFinishPath.beaconKernel, phase]

private theorem finish_holds
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (index : Fin B)
    (front : Front RatchetChain M P I D K S B) (before : InitialState A N)
    (trace : PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B)
    (valid : Holds cr prior front trace)
    (result : PqxdhInitialFinishReceipt.Result (KernelOf RatchetChain) Origin I D K Response
      PqxdhPhase2DecapsulationRouting.Shared × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux)
      (PqxdhInitialFinishReceipt.owner mark preForward calls applicationForward initialForward decode raw (front.roles.1.2 index))).run before)) :
    Holds cr prior (install index front result.1.1.1.2)
      (PqxdhInitialInstallOccurrence.finished (PqxdhInitialInstallOccurrence.begin trace)
        trace.nextAttempt index raw result.1.2 result.1.1.1.1.isSome) := by
  intro owner occurrence labelled kernel found
  by_cases same : owner = .beacon index
  · subst owner
    have previous : ∀ occurrence, trace.installed (.beacon index) = some occurrence →
        ∀ kernel, PqxdhInitialOriginFinishPath.beaconKernel (front.roles.1.2 index) = some kernel →
          AtOccurrence cr prior occurrence kernel := by
      have previous := valid (.beacon index)
      rw [selected_beacon] at previous
      exact previous
    have paths := finish_selected source writer prior selected previousRoot response64 pre application selector aux
      cr mark decode raw index (front.roles.1.2 index) before trace previous result supported occurrence labelled kernel
    apply paths
    rw [selected_beacon] at found
    simpa only [install, Function.update_self] using found
  · rw [finish_other trace index raw result.1.2 result.1.1.1.1.isSome owner same] at labelled
    rw [install_other front index result.1.1.1.2 owner same] at found
    exact valid owner occurrence labelled kernel found

private theorem path_rules
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (occurrence : PqxdhInitialInstallOccurrence.Occurrence RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B) :
    RawCtxFamilyStateInvariant.Rules (PqxdhInitialReceiptPublication.nativeCalls (A := A) (N := N) source writer prior)
      (fun _ _ => True) (fun kernel _ => AtOccurrence cr prior occurrence kernel) where
  refl := fun _ => trivial
  trans := fun _ _ _ _ _ => trivial
  mono := fun _ _ _ _ valid => valid
  receive := by
    intro entry target context state result supported
    simp only [PqxdhInitialReceiptPublication.nativeCalls, PqxdhInitialBeaconAmbient.liftCalls,
      PqxdhInitialBeaconAmbient.lift, StateT.run, Functor.map_map, support_map] at supported
    obtain ⟨actual, reached, rfl⟩ := supported
    exact ⟨trivial, fun valid => RawCtxRetainedNativeCycles.receive_valid source writer prior cr
      _ _ entry valid target context state.1.1 actual reached⟩
  send := by
    intro entry context state result supported
    simp only [PqxdhInitialReceiptPublication.nativeCalls, PqxdhInitialBeaconAmbient.liftCalls,
      PqxdhInitialBeaconAmbient.lift, StateT.run, Functor.map_map, support_map] at supported
    obtain ⟨actual, reached, rfl⟩ := supported
    exact ⟨trivial, fun valid => RawCtxRetainedNativeCycles.send_valid source writer prior cr
      _ _ entry valid context state.1.1 actual reached⟩

private theorem record_reachable
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (occurrence : PqxdhInitialInstallOccurrence.Occurrence RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B)
    (owner : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxGenericFamilyLive.State (KernelOf RatchetChain) M P I D K S B) (before : InitialState A N)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query ×
      RawCtxGenericFamilyLive.State (KernelOf RatchetChain) M P I D K S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (handler source writer prior selected previousRoot response64 pre application selector aux)
      (simulateQ liveForward ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run entry))).run before))
    (valid : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner entry.1 = some kernel → AtOccurrence cr prior occurrence kernel) :
    ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner result.1.2.1 = some kernel → AtOccurrence cr prior occurrence kernel := by
  have forwarding : handler (S := S) (B := B) source writer prior selected previousRoot response64 pre application selector aux ∘ₛ
      liveForward = RawCtxPendingFamilyLiveQueries.handler
        (RawCtxPendingNativeCalls.pending (native source writer prior) (publicCalls source writer prior))
        (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) := by
    funext query
    simp [QueryImpl.compose, liveForward, handler, PqxdhInitialPendingPost.handler, OracleSpec.query]
  rw [← QueryImpl.simulateQ_compose, forwarding, RawCtxPendingFamilyLiveQueries.step_interpretation,
    RawCtxPendingNativeCalls.calls_interpretation, native_calls, RawCtxPendingNativeCalls.public_interpretation] at supported
  exact (RawCtxFamilyStateInvariant.live _ _ _ (path_rules source writer prior cr occurrence)
    _ (fun _ _ _ _ => trivial) _ (fun _ _ _ _ => trivial) sender route decode query entry before result supported owner).2 valid

/-- One complete original Post query preserves the installed occurrence paths, including records, disclosures, selector effects and successful or failed Beacon replacement attempts. -/
theorem step_holds
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (entry : PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Origin S B)
    (before : InitialState A N) (valid : Holds cr prior entry.1.1 entry.2)
    (result : ((PqxdhInitialGenericPost.Spec extra S B).Range query ×
      PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Origin S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (handler source writer prior selected previousRoot response64 pre application selector aux)
      ((PqxdhInitialInstallOccurrence.compiler mark sender route decode query).run entry)).run before)) :
    Holds cr prior result.1.2.1.1 result.1.2.2 := by
  rcases query with (query | query) | ⟨index, raw⟩
  · simp only [PqxdhInitialInstallOccurrence.compiler, PqxdhInitialOriginPost.compiler, StateT.run,
      bind_pure_comp, Functor.map_map, simulateQ_map] at supported
    change result ∈ support (StateT.run _ before) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    intro owner occurrence labelled kernel found
    exact record_reachable source writer prior selected previousRoot response64 pre application selector aux
      cr occurrence owner sender route decode query entry.1.1.roles before completed reached
      (valid owner occurrence labelled) kernel found
  · simp only [PqxdhInitialInstallOccurrence.compiler, PqxdhInitialOriginPost.compiler, StateT.run,
      bind_pure_comp, Functor.map_map, simulateQ_map] at supported
    change result ∈ support (StateT.run _ before) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact valid
  · simp only [PqxdhInitialInstallOccurrence.compiler, StateT.run, bind_pure_comp,
      simulateQ_map] at supported
    change result ∈ support (StateT.run _ before) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    exact finish_holds source writer prior selected previousRoot response64 pre application selector aux
      cr mark decode raw index entry.1.1 before entry.2 valid completed reached

/-- Every supported complete adaptive Post execution preserves the actual installed occurrence paths from its admitted input state. All replies, stops, private state and original history are retained in this same source interpreter. -/
theorem program_holds
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (entry : PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Origin S B)
    (before : InitialState A N) (valid : Holds cr prior entry.1.1 entry.2)
    (result : (Result × PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response PqxdhPhase2DecapsulationRouting.Shared Origin S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (handler source writer prior selected previousRoot response64 pre application selector aux)
      ((simulateQ (PqxdhInitialInstallOccurrence.compiler mark sender route decode) client).run entry)).run before)) :
    Holds cr prior result.1.2.1.1 result.1.2.2 := by
  induction client using OracleComp.inductionOn generalizing entry before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact valid
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
    change result ∈ support
      (((simulateQ (handler source writer prior selected previousRoot response64 pre application selector aux)
          ((PqxdhInitialInstallOccurrence.compiler mark sender route decode query).run entry)).run before) >>= fun reply =>
        ((simulateQ (handler source writer prior selected previousRoot response64 pre application selector aux)
          ((simulateQ (PqxdhInitialInstallOccurrence.compiler mark sender route decode) (next reply.1.1)).run reply.1.2)).run reply.2)) at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    have advanced := step_holds source writer prior selected previousRoot response64 pre application selector aux
      cr mark sender route decode query entry before valid reply head
    exact ih reply.1.1 reply.1.2 reply.2 advanced result tail

/-- An empty occurrence annotation imposes no path condition on arbitrary preexisting roles. Only actual later installations receive a new certificate. -/
theorem empty_holds (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (front : Front RatchetChain M P I D K S B) :
    Holds (Response := Response) cr prior front PqxdhInitialInstallOccurrence.empty := by
  intro owner occurrence impossible
  cases impossible

/-- The actual first Builder supplies the source path certificate for every occurrence it installs from an empty annotation. Existing unlabelled roles remain unrestricted, and unsuccessful builders install no occurrence. -/
theorem builder_holds
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (serverResponse : pqxdh.concrete.InitialRatchetKdfResponse)
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (input : PqxdhPrivateAcceptedRoot.Ready)
    (front : Front RatchetChain M P I D K S B) (before : InitialState A N)
    (result : ((RustM (Option PqxdhServerRegistrationPublication.Response) ×
      Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf RatchetChain))) × Front RatchetChain M P I D K S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (handler source writer prior selected previousRoot response64 pre application selector aux)
      ((PqxdhInitialBuilderReceipt.build source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
        sender index metadata input).run front)).run before)) :
    Holds (Response := Response) cr prior result.1.2
      (PqxdhInitialInstallOccurrence.built (PqxdhInitialInstallOccurrence.begin PqxdhInitialInstallOccurrence.empty)
        0 input index result.1.2 result.1.1.1 result.1.1.2) := by
  cases returned : result.1.1.1
  case ok optional =>
    cases optional
    case none =>
      intro owner occurrence labelled kernel found
      cases recorded : result.1.1.2 <;>
        simp only [PqxdhInitialInstallOccurrence.built, recorded, PqxdhInitialInstallOccurrence.note,
          PqxdhInitialInstallOccurrence.begin, PqxdhInitialInstallOccurrence.empty, Bool.false_eq_true, ite_false] at labelled <;>
        cases labelled
    case some response =>
      obtain ⟨receipt, recorded, _, keyEq, advanced, encrypted, atSend, atSent, peer, sent⟩ :=
        PqxdhInitialReceiptPublication.build_published
          (handler source writer prior selected previousRoot response64 pre application selector aux)
          source _ sender index metadata input front before result supported response returned
      have initialPath := (PqxdhInitialReceiptConstruction.server
        (handler source writer prior selected previousRoot response64 pre application selector aux)
        source serverResponse sender index metadata input front before result supported receipt recorded
        (withInterpreter cr (RawCtxFunctionalFamily.execute prior))).2
      rw [handler_calls] at sent
      let actual : PqxdhInitialInstallOccurrence.Occurrence RatchetChain Response
          PqxdhPhase2DecapsulationRouting.Shared S B :=
        ⟨⟨.server index receipt.candidate.key_id, 0⟩, .server input receipt⟩
      have advancedPath : AtOccurrence cr prior actual advanced :=
        ((path_rules source writer prior cr actual).send receipt.initial _ atSend
          ((advanced, some encrypted), atSent) sent).2 initialPath
      rw [keyEq] at peer
      intro owner occurrence labelled kernel found
      simp only [PqxdhInitialInstallOccurrence.built, recorded, keyEq, peer,
        decide_true, Option.isSome_some, Bool.and_true, PqxdhInitialInstallOccurrence.note,
        ite_true, PqxdhInitialInstallOccurrence.begin, PqxdhInitialInstallOccurrence.empty] at labelled
      by_cases same : owner = .server index receipt.candidate.key_id
      · subst owner
        simp only [Function.update_self, Option.some.injEq] at labelled
        subst occurrence
        simp only [RawCtxGenericRoleFamily.selectedKernel, peer, Option.map_some,
          Option.some.injEq] at found
        subst kernel
        exact advancedPath
      · rw [Function.update_of_ne same] at labelled
        cases labelled
  all_goals
    intro owner occurrence labelled kernel found
    cases recorded : result.1.1.2 <;>
      simp only [PqxdhInitialInstallOccurrence.built, recorded, PqxdhInitialInstallOccurrence.note,
        PqxdhInitialInstallOccurrence.begin, PqxdhInitialInstallOccurrence.empty, Bool.false_eq_true, ite_false] at labelled <;>
      cases labelled

/-- The actual first Builder and complete adaptive Post construct and preserve all new installed occurrence paths from an empty annotation. No certificate is assumed for preexisting roles or for an arbitrary initializer. -/
theorem sequence_holds
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (serverResponse : pqxdh.concrete.InitialRatchetKdfResponse)
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (input : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (entry : Front RatchetChain M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)
    (before : InitialState A N)
    (result : (Result × PqxdhInitialInstallOccurrence.State RatchetChain M P I D K Response
      PqxdhPhase2DecapsulationRouting.Shared Origin S B) × InitialState A N)
    (supported : result ∈ support ((simulateQ
      (handler source writer prior selected previousRoot response64 pre application selector aux)
      ((PqxdhInitialInstallOccurrence.sequence source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
        mark origin sender route decode index metadata input post).run
          (entry, PqxdhInitialInstallOccurrence.empty))).run before)) :
    Holds cr prior result.1.2.1.1 result.1.2.2 := by
  simp only [PqxdhInitialInstallOccurrence.sequence, StateT.run, simulateQ_bind] at supported
  change result ∈ support
    (((simulateQ (handler source writer prior selected previousRoot response64 pre application selector aux)
        ((PqxdhInitialBuilderReceipt.build source
          (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
          sender index metadata input).run entry.1)).run before) >>= fun built =>
      ((simulateQ (handler source writer prior selected previousRoot response64 pre application selector aux)
        ((simulateQ (PqxdhInitialInstallOccurrence.compiler mark sender route decode)
          (post built.1.1.1)).run
            ((built.1.2, PqxdhInitialOriginPost.afterBuilder entry.2 built.1.2 index origin built.1.1.1),
              PqxdhInitialInstallOccurrence.built
                (PqxdhInitialInstallOccurrence.begin PqxdhInitialInstallOccurrence.empty)
                0 input index built.1.2 built.1.1.1 built.1.1.2))).run built.2)) at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨built, reached, rest⟩ := supported
  have installed := builder_holds source writer prior selected previousRoot response64 pre application selector aux
    cr serverResponse sender index metadata input entry.1 before built reached
  exact program_holds source writer prior selected previousRoot response64 pre application selector aux
    cr mark sender route decode (post built.1.1.1) _ built.2 installed result rest

end Source
end BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.step_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.step_holds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.program_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.program_holds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.empty_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.empty_holds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.builder_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.builder_holds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.sequence_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOccurrencePaths.sequence_holds
