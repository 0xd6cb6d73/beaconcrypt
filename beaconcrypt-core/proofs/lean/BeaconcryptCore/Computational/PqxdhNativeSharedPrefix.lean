import BeaconcryptCore.Computational.RawCtxSharedPrefixScan
import BeaconcryptCore.Computational.PqxdhInitialNativeInitializer

/-!
The literal audited native prefix executes through the shared hash interface. All source-local preparation, selector, application and allocation callbacks carry their full non-ROM state. The initializer is its original retained root-cache computation. The hash cache is exclusively executed by the forwarded native record/public backend; no callback is supplied an independently writable hash cache.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhNativeSharedPrefix
open CtxRomAuth AdaptiveCtxSharedHash PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev ExternalState (A N C : Type) := (A × N) × C
abbrev LocalCallback (A N C Value : Type) := StateT (ExternalState A N C) ProbComp Value

/-- Source-local effects cannot inspect or replace the ROM cache through this interface. -/
def localLift {Value : Type} (work : LocalCallback A N C Value) : Ambient A N C Value :=
  fun state cache => (fun result => ((result.1, ((result.2.1.1, state.1.2), result.2.1.2)), result.2.2)) <$>
    work ((state.1.1, state.2), cache)

structure Local (A N C : Type) where
  shared : A
  store : RawCtxSelectiveChainGame.Store
  inputs : List PqxdhJointKdf.JointKdfAddress
  privateState : N
  roots : C
  audit : List RootOutput

def attach (state : Local A N C) (cache : CtxRO.QueryCache) : PqxdhInitialNativeAudit.State A N C :=
  (((((state.shared, cache), state.store), state.inputs), (state.privateState, state.roots)), state.audit)

def externalState (state : Local A N C) : ExternalState A N C := ((state.shared, state.privateState), state.roots)

def afterExternal (state : Local A N C) (after : ExternalState A N C) : Local A N C :=
  { state with shared := after.1.1, privateState := after.1.2, roots := after.2 }

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

noncomputable def external : QueryImpl
    (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
    (StateT (ExternalState A N C) ProbComp)
  | .inl query => pre query
  | .inr (.inl reply) => application reply
  | .inr (.inr (.inl secrets)) => Prod.snd <$> initial secrets
  | .inr (.inr (.inr (.inl query))) => selector query
  | .inr (.inr (.inr (.inr query))) => aux query

noncomputable def live (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) :
    StateT (Local A N C) (OracleComp HashSpec) ((RawCtxPendingSelectiveFamily.Spec S B).Range query) := fun state =>
  (fun result => (result.1, { state with
    shared := result.2.1
    store := result.2.2
    inputs := RawCtxSelectiveFamilyLog.inputs query state.inputs
    audit := state.audit ++ PqxdhInitialNativeAudit.liveInputs query })) <$>
      (RawCtxSelectiveSharedRom.pending source writer stage query).run (state.shared, state.store)

noncomputable def localCall {Value : Type} (work : LocalCallback A N C Value) :
    StateT (Local A N C) (OracleComp HashSpec) Value := fun state =>
  (fun result => (result.1, afterExternal state result.2)) <$>
    simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState state))

noncomputable def initialCall (work : LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) :
    StateT (Local A N C) (OracleComp HashSpec) (Option (PqxdhInitialPendingPost.KernelOf RatchetChain)) := fun state =>
  (fun result => (result.1.2, { afterExternal state result.2 with
    audit := state.audit ++ PqxdhInitialParentObserverCompiler.candidates result.1 })) <$>
      simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState state))

noncomputable def compiler : QueryImpl
    (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B)
    (StateT (Local A N C) (OracleComp HashSpec))
  | .inl query => live source writer stage query
  | .inr (.inr (.inr (.inl secrets))) => initialCall (initial secrets)
  | .inr query => localCall (external pre application initial selector aux query)

/-- All local callback effects, including failed optional operations, retain the exact source state while the ROM cache is threaded unchanged. -/
theorem external_step {Value : Type} (work : LocalCallback A N C Value)
    (state : Local A N C) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach (afterExternal state result.1.2) result.2)) <$>
      (simulateQ hashImpl (simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState state)))).run cache =
      (fun result => (result.1.1, (((result.1.2.1, state.store), state.inputs), (result.1.2.2, result.2)), state.audit)) <$>
        ((localLift work ((state.shared, cache), state.privateState)).run state.roots) := by
  rw [RawCtxSelectiveSharedRom.coins_complete]
  simp only [localLift, StateT.run, Functor.map_map, attach, afterExternal, externalState]

/-- The native live callback updates the exact private history and audit after its actual reply, preserving all other state. -/
theorem live_step (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain)
    (state : Local A N C) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((live source writer stage query).run state)).run cache =
      (fun result => (result.1, (((result.2, RawCtxSelectiveFamilyLog.inputs query state.inputs),
        (state.privateState, state.roots)), state.audit ++ PqxdhInitialNativeAudit.liveInputs query))) <$>
        (RawCtxPendingSelectiveFamily.handler source writer stage query).run ((state.shared, cache), state.store) := by
  let pack := fun result : (RawCtxPendingSelectiveFamily.Spec S B).Range query × RawCtxPendingSelectiveFamily.State A =>
    (result.1, (((result.2, RawCtxSelectiveFamilyLog.inputs query state.inputs),
      (state.privateState, state.roots)), state.audit ++ PqxdhInitialNativeAudit.liveInputs query))
  have linked := congrArg (fun work => pack <$> work)
    (RawCtxSelectiveSharedRom.pending_step source writer stage query (state.shared, state.store) cache)
  change (fun result => (result.1.1, attach result.1.2 result.2)) <$>
    (simulateQ hashImpl ((fun result => (result.1, { state with
      shared := result.2.1
      store := result.2.2
      inputs := RawCtxSelectiveFamilyLog.inputs query state.inputs
      audit := state.audit ++ PqxdhInitialNativeAudit.liveInputs query })) <$>
        (RawCtxSelectiveSharedRom.pending source writer stage query).run (state.shared, state.store))).run cache = _
  rw [simulateQ_map, StateT.run_map]
  simpa only [Functor.map_map, pack, attach, RawCtxSelectiveSharedRom.attach] using linked

/-- Local source work has its complete probability computation and original optional reply, with no capability to initialize a separate ROM cache. -/
theorem local_step {Value : Type} (work : LocalCallback A N C Value)
    (state : Local A N C) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((localCall work).run state)).run cache =
      (fun result => (result.1.1, (((result.1.2.1, state.store), state.inputs), (result.1.2.2, result.2)), state.audit)) <$>
        ((localLift work ((state.shared, cache), state.privateState)).run state.roots) := by
  change (fun result => (result.1.1, attach result.1.2 result.2)) <$>
    (simulateQ hashImpl ((fun result => (result.1, afterExternal state result.2)) <$>
      simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState state)))).run cache = _
  rw [simulateQ_map, StateT.run_map]
  simpa only [Functor.map_map] using external_step work state cache

/-- Every actual retained initializer updates its original root cache and appends its actual root/two-chain audit, including repeated matching initializers. -/
theorem initial_step (work : LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (state : Local A N C) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((initialCall work).run state)).run cache =
      (fun result => (result.1.1.2, (((result.1.2.1, state.store), state.inputs), (result.1.2.2, result.2)),
        state.audit ++ PqxdhInitialParentObserverCompiler.candidates result.1.1)) <$>
        ((localLift work ((state.shared, cache), state.privateState)).run state.roots) := by
  change (fun result => (result.1.1, attach result.1.2 result.2)) <$>
    (simulateQ hashImpl ((fun result => (result.1.2, { afterExternal state result.2 with
      audit := state.audit ++ PqxdhInitialParentObserverCompiler.candidates result.1 })) <$>
        simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState state)))).run cache = _
  rw [simulateQ_map, StateT.run_map, RawCtxSelectiveSharedRom.coins_complete]
  simp only [localLift, StateT.run, Functor.map_map, attach, afterExternal, externalState]

set_option backward.isDefEq.respectTransparency false in
/-- The actual full audited source callback is simulated with the complete native state, not merely the marginal returned value. -/
theorem step (query : (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : Local A N C) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((compiler source writer stage pre application initial selector aux query).run state)).run cache =
      (PqxdhInitialNativeAudit.handler source writer stage (fun request => localLift (pre request))
        (fun reply => localLift (application reply)) (fun secrets => localLift (initial secrets))
        (fun request => localLift (selector request)) (fun request => localLift (aux request)) query).run (attach state cache) := by
  rcases query with query | (query | (reply | (secrets | (query | query))))
  · have linked := live_step source writer stage query state cache
    simp only [compiler, PqxdhInitialNativeAudit.handler, PqxdhInitialNativeLog.handler,
      PqxdhInitialNativeLog.bare, PqxdhInitialNativeLog.erase, PqxdhInitialNativeLog.inputs,
      StateT.run, bind_pure_comp, Functor.map_map, attach] at linked ⊢
    exact linked
  · have linked := local_step (pre query) state cache
    simp only [compiler, external, PqxdhInitialNativeAudit.handler, PqxdhInitialNativeLog.handler,
      PqxdhInitialNativeLog.bare, PqxdhInitialNativeLog.erase, PqxdhInitialNativeLog.inputs,
      PqxdhInitialNativeLog.liftExternal, PqxdhInitialNativeAudit.external,
      StateT.run, bind_pure_comp, Functor.map_map, attach] at linked ⊢
    exact linked
  · have linked := local_step (application reply) state cache
    simp only [compiler, external, PqxdhInitialNativeAudit.handler, PqxdhInitialNativeLog.handler,
      PqxdhInitialNativeLog.bare, PqxdhInitialNativeLog.erase, PqxdhInitialNativeLog.inputs,
      PqxdhInitialNativeLog.liftExternal, PqxdhInitialNativeAudit.external,
      StateT.run, bind_pure_comp, Functor.map_map, attach] at linked ⊢
    exact linked
  · have linked := initial_step (initial secrets) state cache
    simp only [compiler, PqxdhInitialNativeAudit.handler, StateT.run, bind_pure_comp, attach] at linked ⊢
    exact linked
  · have linked := local_step (selector query) state cache
    simp only [compiler, external, PqxdhInitialNativeAudit.handler, PqxdhInitialNativeLog.handler,
      PqxdhInitialNativeLog.bare, PqxdhInitialNativeLog.erase, PqxdhInitialNativeLog.inputs,
      PqxdhInitialNativeLog.liftExternal, PqxdhInitialNativeAudit.external,
      StateT.run, bind_pure_comp, Functor.map_map, attach] at linked ⊢
    exact linked
  · have linked := local_step (aux query) state cache
    simp only [compiler, external, PqxdhInitialNativeAudit.handler, PqxdhInitialNativeLog.handler,
      PqxdhInitialNativeLog.bare, PqxdhInitialNativeLog.erase, PqxdhInitialNativeLog.inputs,
      PqxdhInitialNativeLog.liftExternal, PqxdhInitialNativeAudit.external,
      StateT.run, bind_pure_comp, Functor.map_map, attach] at linked ⊢
    exact linked
def selected (depth : Nat)
    (query : (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : Local A N C) : Bool :=
  PqxdhInitialNativeAuditCarried.selected depth query (attach state ∅)

/-- The original predecessor/first-hit selector depends on the private KDF table and cursor, and cannot branch on the CTX ROM cache. -/
theorem selection_cache (depth : Nat)
    (query : (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : Local A N C) (cache : CtxRO.QueryCache) :
    PqxdhInitialNativeAuditCarried.selected depth query (attach state cache) = selected depth query state := by
  cases query <;> rfl

/-- The original selected cut is always an actual private source callback, under the same static coverage proof. -/
theorem native_selection (depth : Nat)
    (query : (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeAudit.State A N C)
    (chosen : PqxdhInitialNativeAuditCarried.selected depth query state = true) :
    PqxdhInitialForwardPost.selected query = true := by
  cases query with
  | inl query => exact RawCtxFirstParentPrefix.selected_private depth query state.1.1 chosen
  | inr query => cases chosen

variable {M P Result Origin : Type}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeAuditCarried.Execution extra M P I D K Result Origin S B)

noncomputable def carried (depth : Nat) (state : Local A N C) :=
  RawCtxSharedPrefixScan.scan PqxdhInitialForwardPost.selected (selected depth)
    (fun query state chosen => native_selection depth query (attach state ∅) chosen)
    (compiler source writer stage pre application initial selector aux)
    (PqxdhInitialNativeCarried.code source mark sender route decode execution)
    (PqxdhInitialOriginForwardBuilder.program_covered source mark execution.origin sender route decode
      execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace) state

/-- The complete literal source first-builder and adaptive post prefix execute through the shared ROM, retaining the actual saved descriptor, all private state, logs, caches, candidates and source order. -/
theorem carried_source (depth : Nat) (state : Local A N C) (cache : CtxRO.QueryCache) :
    RawCtxSharedPrefixScan.restore attach <$>
      (simulateQ hashImpl (carried source writer stage pre application initial selector aux mark sender route decode execution depth state)).run cache =
      PqxdhInitialNativeAuditCarried.carried source writer (fun request => localLift (pre request))
        (fun reply => localLift (application reply)) (fun secrets => localLift (initial secrets))
        (fun request => localLift (selector request)) (fun request => localLift (aux request))
        mark sender route decode execution depth stage (attach state cache) := by
  exact RawCtxSharedPrefixScan.source PqxdhInitialForwardPost.selected (selected depth)
    (fun query state chosen => native_selection depth query (attach state ∅) chosen)
    (compiler source writer stage pre application initial selector aux)
    (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth)
    (PqxdhInitialNativeAudit.handler source writer stage (fun request => localLift (pre request))
      (fun reply => localLift (application reply)) (fun secrets => localLift (initial secrets))
      (fun request => localLift (selector request)) (fun request => localLift (aux request)))
    attach (selection_cache depth) (step source writer stage pre application initial selector aux)
    _ _ state cache

open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialRootLabelService

noncomputable def initialLocal {A N : Type} (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : Message)
    (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply := fun state =>
  (fun result => ((result.1.1, some (PqxdhInitialRootAudit.kernel result.1).refined), (state.1, result.2))) <$>
    (PqxdhInitialRootAudit.retained fixed selectedMessage previousRoot response
      (PqxdhInitialRootLabelBridge.request fixed secrets)).run state.2

/-- The actual retained initializer is the source-local callback, retaining its exact root-cache response and source kernel without inspecting the commitment cache. -/
theorem initial_source {A N : Type} (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : Message)
    (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    localLift (initialLocal (A := A) (N := N) fixed selectedMessage previousRoot response secrets) =
      PqxdhInitialNativeInitializer.initial fixed selectedMessage previousRoot response secrets := by
  funext state cache
  simp only [localLift, initialLocal, PqxdhInitialNativeInitializer.initial, Functor.map_map]
  rfl

/-- Initializer cache misses retain the original at-most32 uniform draws; repeated hits do not draw a replacement response. -/
theorem initial_local_uniform {A N : Type} (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : Message)
    (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : ExternalState A N RootOracle.QueryCache) :
    ((initialLocal fixed selectedMessage previousRoot response secrets).run state).IsTotalQueryBound 32 := by
  simpa only [initialLocal, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhInitialRootAudit.retained_uniform fixed selectedMessage previousRoot response
      (PqxdhInitialRootLabelBridge.request fixed secrets) state.2

end BeaconcryptCore.Computational.PqxdhNativeSharedPrefix


/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.external_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.external_step

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.live_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.live_step

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.local_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.local_step

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.initial_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.initial_step

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.step

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.selection_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.selection_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.native_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.native_selection

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.carried_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.carried_source

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.initial_source

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.initial_local_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.initial_local_uniform
