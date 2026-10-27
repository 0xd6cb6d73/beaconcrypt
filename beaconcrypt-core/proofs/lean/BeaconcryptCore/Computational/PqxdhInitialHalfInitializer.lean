import BeaconcryptCore.Computational.PqxdhInitialHalfObserverCompiler
import BeaconcryptCore.Computational.PqxdhInitialNativeInitializer
import BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon

/-!
After the initial64 comparison, the first-half observer may retain the earlier private root. The audited selected/known initializer service preserves that actual root input and returns the unchanged target-free optional Slot kernel. Matching source coordinates reuse the same hidden initial half in either orientation; nonselected coordinates retain the exact cached root and real64 response. No extra random draw is introduced.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfInitializer
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialRootLabelService PqxdhInitialSelectedBeacon PqxdhInitialBeaconAmbient
variable {A N : Type}

noncomputable def value (source : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (second : Bool) (other : RootOutput) :
    Request → StateT RootOracle.QueryCache ProbComp (RootOutput × InitialValue)
  | .known root => pure (root, PqxdhInitialSelectedService.known source root)
  | .family message => if message = selected then pure (previousRoot, .inr (second, other)) else do
      let root ← PqxdhCorrelatedExpandHybrid.uniformImpl (.inr message)
      pure (root, PqxdhInitialSelectedService.known source root)

/-- Erasing only the private initializer input gives the exact original target-free known/selected reply service. -/
theorem value_erase (source : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (second : Bool) (other : RootOutput) (query : Request) :
    Prod.snd <$> value source selected previousRoot second other query =
      PqxdhInitialSelectedService.value source selected second other query := by
  cases query with
  | known root => rfl
  | family message =>
      simp only [value, PqxdhInitialSelectedService.value]
      split <;> simp only [map_pure, map_bind]

/-- Native reconstruction retains the actual root input, original selected64 response and the complete root-cache computation. -/
theorem value_native (source : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (second : Bool) (other target : RootOutput) (query : Request) :
    Prod.map id (response target) <$> value source selected previousRoot second other query =
      PqxdhInitialRootAudit.retained source selected previousRoot
        (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)) query := by
  cases query with
  | known root => simp only [value, map_pure, Prod.map_apply, id_eq,
      PqxdhInitialSelectedService.known_response, PqxdhInitialRootAudit.retained, PqxdhInitialRootAudit.native]
  | family message =>
      simp only [value, PqxdhInitialRootAudit.retained]
      split
      · rfl
      · simp only [map_bind, map_pure, Prod.map_apply, id_eq,
          PqxdhInitialSelectedService.known_response, PqxdhInitialRootAudit.native]

noncomputable def initial (source : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (second : Bool) (other : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    Ambient A N RootOracle.QueryCache PqxdhInitialHalfObserverCompiler.InitialReply := fun state =>
  (fun reply => ((reply.1, labelKernel reply.2), state)) <$>
    value source selected previousRoot second other (PqxdhInitialRootLabelBridge.request source secrets)

/-- The selected source request returns the same hidden-half kernel before its first receive, retaining the earlier input for the alias audit. -/
theorem selected_initial (source : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (second : Bool) (other : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (matching : PqxdhInitialRootLabelBridge.request source secrets = .family selected) :
    initial (A := A) (N := N) source selected previousRoot second other secrets =
      pure (previousRoot, labelKernel (.inr (second, other))) := by
  funext state cache
  simp only [initial, matching, value]
  rfl

/-- Removing the private audit field recovers the exact original current Beacon initializer, including all repeated matching requests and cache effects. -/
theorem initial_erase (count : Nat) (source : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (second : Bool) (other : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    Functor.map (f := Ambient A (PqxdhPhase1AcceptanceOracle.BareState count) RootOracle.QueryCache) Prod.snd
      (initial source selected previousRoot second other secrets) =
      PqxdhInitialCurrentBeacon.initialization count source selected second other secrets := by
  funext state cache
  have erased := congrArg (fun work => work.run cache)
    (value_erase source selected previousRoot second other (PqxdhInitialRootLabelBridge.request source secrets))
  simp only [StateT.run_map] at erased
  change ((Prod.snd <$> initial source selected previousRoot second other secrets :
    Ambient A (PqxdhPhase1AcceptanceOracle.BareState count) RootOracle.QueryCache _).run state).run cache = _
  simp only [StateT.run_map]
  unfold initial PqxdhInitialCurrentBeacon.initialization
  change (fun result => ((result.1.1.2, result.1.2), result.2)) <$>
      (((fun reply => ((reply.1, labelKernel reply.2), state)) <$>
        value source selected previousRoot second other (PqxdhInitialRootLabelBridge.request source secrets)).run cache) =
    ((fun reply => (reply.bind labelKernel, state)) <$>
      PqxdhInitialSelectedService.service source selected second other secrets).run cache
  simp only [PqxdhInitialSelectedService.service, StateT.run_map, Functor.map_map]
  rw [← erased]
  simp only [Functor.map_map]
  rfl

private theorem kernel_native (target root : RootOutput) (reply : InitialValue) :
    (labelKernel reply).map (RawCtxSelectedParentCalls.nativeKernel target) =
      some (PqxdhInitialRootAudit.kernel (root, response target reply)).refined := by
  have mapped := congrArg (Option.map ConcreteRatchetKernel.refined) (response_map target reply)
  rw [Option.map_some, Option.map_map] at mapped
  rw [PqxdhInitialNativeInitializer.kernel_input_unused root (List.Vector.replicate 32 0)]
  exact mapped.symm

/-- The complete labelled audit reconstructs the original native initializer and exact ambient/root-cache state; the target appears only in this source interpretation. -/
theorem initial_native (source : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (second : Bool) (other target : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    Functor.map (f := Ambient A N RootOracle.QueryCache)
      (Prod.map id (Option.map (RawCtxSelectedParentCalls.nativeKernel target)))
      (initial source selected previousRoot second other secrets) =
      PqxdhInitialNativeInitializer.initial source selected previousRoot
        (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)) secrets := by
  funext state cache
  have native := congrArg (fun work => work.run cache)
    (value_native source selected previousRoot second other target (PqxdhInitialRootLabelBridge.request source secrets))
  simp only [StateT.run_map] at native
  change ((Prod.map id (Option.map (RawCtxSelectedParentCalls.nativeKernel target)) <$>
    initial source selected previousRoot second other secrets : Ambient A N RootOracle.QueryCache _).run state).run cache = _
  simp only [StateT.run_map]
  unfold initial PqxdhInitialNativeInitializer.initial
  change (fun result => ((Prod.map id (Option.map (RawCtxSelectedParentCalls.nativeKernel target)) result.1.1, result.1.2), result.2)) <$>
      (((fun reply => ((reply.1, labelKernel reply.2), state)) <$>
        value source selected previousRoot second other (PqxdhInitialRootLabelBridge.request source secrets)).run cache) =
    ((fun reply => ((reply.1, some (PqxdhInitialRootAudit.kernel reply).refined), state)) <$>
      PqxdhInitialRootAudit.retained source selected previousRoot
        (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target))
        (PqxdhInitialRootLabelBridge.request source secrets)).run cache
  simp only [StateT.run_map, Functor.map_map]
  rw [← native]
  simp only [Functor.map_map]
  congr 1
  funext reply
  exact congrArg (fun kernel => (((reply.1.1, kernel), state), reply.2))
    (kernel_native target reply.1.1 reply.1.2)

/-- The literal audited service pays the same at-most32-byte root-cache bill, with no extra draw for its input or label bookkeeping. -/
theorem initial_uniform (source : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (second : Bool) (other : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : RawCtxSharedPrimitive.SharedState A × N) (cache : RootOracle.QueryCache) :
    ((initial source selected previousRoot second other secrets state).run cache).IsTotalQueryBound 32 := by
  have bound := PqxdhInitialSelectedService.value_uniform source selected second other
    (PqxdhInitialRootLabelBridge.request source secrets) cache
  rw [← value_erase source selected previousRoot second other] at bound
  simpa only [initial, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff] using bound

end BeaconcryptCore.Computational.PqxdhInitialHalfInitializer

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.value_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.value_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.value_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.value_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.selected_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.selected_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.initial_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.initial_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.initial_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.initial_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.initial_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfInitializer.initial_uniform
