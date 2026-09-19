import BeaconcryptCore.Computational.PqxdhInitialNativeCarried
import BeaconcryptCore.Computational.PqxdhInitialNativeInitializer
import BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets
import BeaconcryptCore.Computational.RawCtxPendingNonKdfStore

/-!
Uniform-query costs for the actual full pending source are derived from its original private, primitive and external callback programs. The complete first builder and adaptive post schedule retain a conservative explicit bound; the executable carried prefix is charged by literal scan-and-finish equality. No marginal distribution equality transports resource costs.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeBudgets
open PqxdhJointKdfGame RawCtxSelectiveChainGame
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The actual mutable native backend pays76 per private derivation and64 per commitment query, with no additional native caller coins. -/
theorem native_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp RawCtxMixedOwner.NativeSpec Result) (qKdf qHash : Nat)
    (kdfs : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .kdf) qKdf)
    (hashes : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) qHash)
    (state : RawCtxPendingSelectiveFamily.State A) :
    ((simulateQ (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      client).run state).IsTotalQueryBound (76 * qKdf + 64 * qHash) := by
  simpa only [RawCtxPendingSelectiveFamily.backend, QueryImpl.simulateQ_compose, Nat.zero_add] using
    RawCtxSelectiveChainBudgets.backend_uniform source writer stage
      (simulateQ RawCtxServerServices.nativeLift client) 0 qKdf qHash
      (RawCtxSelectiveChainBudgets.native_coins client)
      (RawCtxServerServiceBounds.nativeLift_bound .kdf client qKdf kdfs)
      (RawCtxServerServiceBounds.nativeLift_bound .hash client qHash hashes) state

/-- The original inner opening executes at most one commitment query under every primitive reply. -/
theorem open_hash (input : RawCtxWholeOwner.OpenInput) :
    (RawCtxMixedOwner.receiveAdapter (.inr input)).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .hash) 1 := by
  change (simulateQ RawCtxMixedOwner.receiveLift
    (simulateQ RawCtxSourceOpen.openLift (RawCtxSourceOpen.openInput input))).IsQueryBoundP _ 1
  apply RawCtxMixedOwner.receiveLift_bound .hash
  apply RawCtxSourceOpen.simulate_bound RawCtxSourceOpen.openLift (fun query => query.isLeft = true)
    _ _ 1 (RawCtxSourceOpen.openInput_bounds input).1
  intro query
  cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [RawCtxMixedOwner.receiveKind])

/-- The original inner seal executes at most one commitment query, including AEAD and writer rejection. -/
theorem seal_hash (input : RawCtxSourceSend.SealInput) :
    (RawCtxMixedOwner.sendAdapter (.inr input)).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .hash) 1 := by
  change (simulateQ RawCtxMixedOwner.sendLift
    (simulateQ RawCtxSourceSeal.sealLift (RawCtxSourceSeal.sealInput input))).IsQueryBoundP _ 1
  apply RawCtxMixedOwner.sendLift_bound .hash
  apply RawCtxSourceOpen.simulate_bound RawCtxSourceSeal.sealLift
    (fun query => RawCtxSourceSeal.callKind query = .hash) _ _ 1
    (RawCtxSourceSeal.sealInput_bound input .hash)
  intro query
  rcases query with aead | (hash | writer)
  all_goals exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [RawCtxMixedOwner.sendKind, RawCtxSourceSeal.callKind])

/-- Complete source opening has at most64 uniform calls from its original commitment cache, with no private derivation inside. -/
theorem open_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (input : RawCtxWholeOwner.OpenInput) (state : RawCtxPendingSelectiveFamily.State A) :
    ((simulateQ (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      (RawCtxMixedOwner.receiveAdapter (.inr input))).run state).IsTotalQueryBound 64 := by
  have kdfs : (RawCtxMixedOwner.receiveAdapter (.inr input)).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .kdf) 0 := by
    apply IsQueryBoundP.of_imp (p' := fun query => query.isLeft = true) _
      (RawCtxPendingNonKdfStore.open_zero input)
    intro query selected
    rcases query with request | (sealing | (opening | (hash | publish))) <;>
      simp_all only [RawCtxMixedOwner.callKind, reduceCtorEq, Sum.isLeft]
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] using
    native_program source writer stage _ 0 1 kdfs (open_hash input) state

/-- Complete source sealing has at most64 uniform calls from its original commitment cache, with no private derivation inside. -/
theorem seal_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (input : RawCtxSourceSend.SealInput) (state : RawCtxPendingSelectiveFamily.State A) :
    ((simulateQ (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      (RawCtxMixedOwner.sendAdapter (.inr input))).run state).IsTotalQueryBound 64 := by
  have kdfs : (RawCtxMixedOwner.sendAdapter (.inr input)).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .kdf) 0 := by
    apply IsQueryBoundP.of_imp (p' := fun query => query.isLeft = true) _
      (RawCtxPendingNonKdfStore.seal_zero input)
    intro query selected
    rcases query with request | (sealing | (opening | (hash | publish))) <;>
      simp_all only [RawCtxMixedOwner.callKind, reduceCtorEq, Sum.isLeft]
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] using
    native_program source writer stage _ 0 1 kdfs (seal_hash input) state

/-- The enriched opening callback retains missing-material and failed-opening branches within the actual64-call cap. -/
theorem receive_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (opening : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : RawCtxPendingSelectiveFamily.State A) :
    ((RawCtxPendingNativeCalls.receive
      (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      (.inr opening)).run state).IsTotalQueryBound 64 := by
  simp only [RawCtxPendingNativeCalls.receive, QueryImpl.apply_compose, RawCtxInterpretedReceive.nativeAdapter,
    _root_.simulateQ_spec_query, QueryImpl.simulateQ_compose, RawCtxWholeOwner.adapter]
  split
  · simp only [simulateQ_pure, StateT.run_pure]
    trivial
  · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      IsTotalQueryBound, isQueryBound_map_iff]
    simpa only [QueryImpl.simulateQ_compose, IsTotalQueryBound] using open_uniform source writer stage _ state

/-- The enriched sealing callback pays its one possible64-byte commitment draw while retaining all original AEAD and writer outcomes. -/
theorem send_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sealing : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext)
    (state : RawCtxPendingSelectiveFamily.State A) :
    ((RawCtxPendingNativeCalls.send
      (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      (.inr sealing)).run state).IsTotalQueryBound 64 := by
  simp only [RawCtxPendingNativeCalls.send, QueryImpl.apply_compose, RawCtxInterpretedSend.nativeAdapter,
    _root_.simulateQ_spec_query, QueryImpl.simulateQ_compose, RawCtxSourceSend.adapter,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
  simpa only [QueryImpl.simulateQ_compose, IsTotalQueryBound] using seal_uniform source writer stage _ state

def publicCost : RawCtxServerServices.PublicSpec.Domain → Nat
  | .inl _ => 1
  | .inr (.inl _) => 64
  | .inr (.inr _) => 0

/-- Actual public services retain caller-coin1, commitment64 and fixed real-HKDF0 uniform costs. -/
theorem public_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : RawCtxServerServices.PublicSpec.Domain) (state : RawCtxPendingSelectiveFamily.State A) :
    (((RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift) query).run state).IsTotalQueryBound
      (publicCost query) := by
  rcases query with coin | (bytes | request)
  all_goals simp only [QueryImpl.apply_compose, RawCtxServerServices.publicLift, simulateQ_spec_query, publicCost]
  · simpa [RawCtxPendingSelectiveFamily.backend, QueryImpl.apply_compose, RawCtxServerServiceBounds.nativePredicate] using
      RawCtxSelectiveChainBudgets.compiled_uniform source writer stage (.inl coin) state
  · simpa [RawCtxPendingSelectiveFamily.backend, QueryImpl.apply_compose, RawCtxServerServiceBounds.nativePredicate, RawCtxMixedOwner.callKind] using
      RawCtxSelectiveChainBudgets.compiled_uniform source writer stage (.inr (.inl (.inr (.inr (.inr (.inl bytes)))))) state
  · simpa [RawCtxPendingSelectiveFamily.backend, QueryImpl.apply_compose, RawCtxServerServiceBounds.nativePredicate] using
      RawCtxSelectiveChainBudgets.compiled_uniform source writer stage (.inr (.inr request)) state

def liveCost : (RawCtxPendingSelectiveFamily.Spec S B).Domain → Nat
  | .inl (.inl (.inl _)) | .inl (.inr (.inl (.inl _))) => 76
  | .inl (.inl (.inr _)) | .inl (.inr (.inl (.inr _))) => 64
  | .inl (.inr (.inr query)) => publicCost query
  | .inr _ => 0

/-- Every actual enriched callback retains its concrete private76, open/seal64, public1/64/0 or read0 uniform bill. -/
theorem live_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) (state : RawCtxPendingSelectiveFamily.State A) :
    ((RawCtxPendingSelectiveFamily.handler source writer stage query).run state).IsTotalQueryBound (liveCost query) := by
  rcases query with ((request | opening) | ((request | sealing) | publicQuery)) | read
  · rw [RawCtxPendingParentCallbacks.receive_step]
    simpa only [liveCost, IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxSelectiveChainGame.private_uniform source stage _ state.2
  · simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose,
      RawCtxPendingOwnerQueries.erase, simulateQ_spec_query, RawCtxPendingNativeCalls.original, liveCost]
    exact receive_uniform source writer stage _ state
  · rw [RawCtxPendingParentCallbacks.send_step]
    simpa only [liveCost, IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxSelectiveChainGame.private_uniform source stage _ state.2
  · simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose,
      RawCtxPendingOwnerQueries.erase, simulateQ_spec_query, RawCtxPendingNativeCalls.original, liveCost]
    exact send_uniform source writer stage _ state
  · simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose,
      RawCtxPendingOwnerQueries.erase, simulateQ_spec_query, RawCtxPendingNativeCalls.original, liveCost]
    exact public_uniform source writer stage publicQuery state
  · simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxGenericFamilyRead.nativeReader, StateT.run_pure, liveCost]
    trivial

/-- Native logging and the outer identity/root-cache state add no uniform calls to any actual live callback. -/
theorem logged_live_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) (state : PqxdhInitialNativeLog.State A N C) :
    ((PqxdhInitialNativeLog.handler source writer stage external (.inl query)).run state).IsTotalQueryBound (liveCost query) := by
  rw [PqxdhInitialNativeLog.live_handler]
  simpa only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp,
    IsTotalQueryBound, isQueryBound_map_iff] using live_uniform source writer stage query state.1.1

structure ExternalBudget where
  preparation : Nat
  application : Nat
  initializer : Nat
  selector : Nat
  auxiliary : Nat

def externalCost (budget : ExternalBudget) :
    (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared).Domain → Nat
  | .inl _ => budget.preparation
  | .inr (.inl _) => budget.application
  | .inr (.inr (.inl _)) => budget.initializer
  | .inr (.inr (.inr (.inl _))) => budget.selector
  | .inr (.inr (.inr (.inr _))) => budget.auxiliary

def LocalBounds
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C)) (budget : ExternalBudget) : Prop :=
  ∀ query state cache, ((external query state).run cache).IsTotalQueryBound (externalCost budget query)

/-- An original external callback pays its own preparation/application/initializer/selector/auxiliary cap, with all ambient effects retained. -/
theorem external_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (budget : ExternalBudget) (bounded : LocalBounds external budget)
    (query : (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared).Domain)
    (state : PqxdhInitialNativeLog.State A N C) :
    ((PqxdhInitialNativeLog.handler (S := S) (B := B) source writer stage external (.inr query)).run state).IsTotalQueryBound
      (externalCost budget query) := by
  rw [PqxdhInitialNativeLog.external_handler]
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bounded query (state.1.1.1, state.2.1) state.2.2

def callbackCap (budget : ExternalBudget) : Nat :=
  max 76 (max budget.preparation (max budget.application (max budget.initializer (max budget.selector budget.auxiliary))))

/-- Every complete actual pending callback fits the explicit maximum of its native and separate external caps. -/
theorem step_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (budget : ExternalBudget) (bounded : LocalBounds external budget)
    (query : (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeLog.State A N C) :
    ((PqxdhInitialNativeLog.handler source writer stage external query).run state).IsTotalQueryBound (callbackCap budget) := by
  cases query with
  | inl query =>
      apply (logged_live_uniform source writer stage external query state).mono
      rcases query with ((request | opening) | ((request | sealing) | (coin | (hash | hkdf)))) | read
      all_goals simp only [liveCost, publicCost, callbackCap]
      all_goals omega
  | inr query =>
      apply (external_uniform source writer stage external budget bounded query state).mono
      rcases query with preparation | (application | (initializer | (selector | auxiliary)))
      all_goals simp only [externalCost, callbackCap]
      all_goals omega

/-- Every original adaptive pending client pays the actual uniform cap at each of its syntactically bounded callbacks. -/
theorem program_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (budget : ExternalBudget) (bounded : LocalBounds external budget)
    (client : OracleComp (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B) Result)
    (queries : Nat) (sourceBound : client.IsTotalQueryBound queries) (state : PqxdhInitialNativeLog.State A N C) :
    ((simulateQ (PqxdhInitialNativeLog.handler source writer stage external) client).run state).IsTotalQueryBound
      (queries * callbackCap budget) := by
  apply (isQueryBoundP_true_iff _ _).mp
  exact PqxdhBeaconPhase2Bounds.interpreted_total_bound _ (fun _ => True) (callbackCap budget) queries
    (fun query reached => (step_uniform source writer stage external budget bounded query reached).isQueryBoundP)
    client sourceBound state

/-- The actual first builder and whole original post schedule supply the complete source uniform bill; only individual external callback caps remain parameters. -/
theorem source_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (budget : ExternalBudget) (bounded : LocalBounds external budget)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
    (qPost : Nat) (sourceBound : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : PqxdhInitialNativeLog.State A N C) :
    ((simulateQ (PqxdhInitialNativeLog.handler source writer stage external)
      (PqxdhInitialNativeCarried.original (X := X) (Response := Response) source mark sender route decode execution)).run state).IsTotalQueryBound
      ((7 + qPost * 67) * callbackCap budget) := by
  apply program_uniform source writer stage external budget bounded _ (7 + qPost * 67) _ state
  exact PqxdhInitialOriginPost.sequence_total source execution.initial mark execution.origin sender route decode
    execution.index execution.metadata execution.ready execution.outside qPost sourceBound (execution.before, execution.trace)

/-- The actual executable carried predecessor sampler pays no more than its literal complete original source execution, including every retained external callback. -/
theorem carried_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (budget : ExternalBudget) (bounded : LocalBounds external budget)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
    (qPost : Nat) (sourceBound : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : PqxdhInitialNativeLog.State A N C) :
    (PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state).IsTotalQueryBound
      ((7 + qPost * 67) * callbackCap budget) := by
  apply IsTotalQueryBound.of_bind_left (ob := fun cut =>
    RawCtxPendingMixedPrefix.finish (PqxdhInitialNativeLog.handler source writer stage external)
      (RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) cut))
  rw [PqxdhInitialNativeCarried.carried_finish]
  exact source_uniform source writer stage external budget bounded mark sender route decode execution qPost sourceBound state

noncomputable def initializer (source : FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : PqxdhSecretInputKdf.RootOutput)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    PqxdhInitialBeaconAmbient.Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache
      (Option (RawCtxPendingOwnerQueries.Kernel RatchetChain)) :=
  Prod.snd <$> PqxdhInitialNativeInitializer.initial source selected previousRoot response secrets

/-- The actual retained initializer's source OptionKernel callback costs at most32, including repeated selected and other root-cache requests; erasing its private audit adds no work. -/
theorem initializer_uniform (source : FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : PqxdhSecretInputKdf.RootOutput)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : RawCtxSharedPrimitive.SharedState A × N)
    (cache : PqxdhCorrelatedExpand.RootOracle.QueryCache) :
    ((initializer source selected previousRoot response secrets state).run cache).IsTotalQueryBound 32 := by
  change (((Prod.snd <$> PqxdhInitialNativeInitializer.initial source selected previousRoot response secrets).run state).run cache).IsTotalQueryBound 32
  simp only [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
  change ((PqxdhInitialNativeInitializer.initial source selected previousRoot response secrets state).run cache).IsTotalQueryBound 32
  exact PqxdhInitialNativeInitializer.initial_uniform source selected previousRoot response secrets state cache

end BeaconcryptCore.Computational.PqxdhInitialNativeBudgets

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.native_program
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.open_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.open_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.seal_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.seal_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.open_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.open_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.seal_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.seal_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.receive_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.receive_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.send_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.send_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.public_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.public_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.live_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.live_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.logged_live_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.logged_live_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.external_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.external_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.step_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.program_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.source_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.carried_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.carried_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.initializer_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeBudgets.initializer_uniform
