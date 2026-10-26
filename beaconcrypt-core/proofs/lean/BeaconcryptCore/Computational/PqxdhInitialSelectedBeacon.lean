import BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative
import BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend
import BeaconcryptCore.Computational.RawCtxInitialSentinelSampler

/-!
The Beacon initializer and first receive use concrete retained-parent calls and a private selected-half representation. Known initializer responses retain their actual64 bytes; a selected response retains only its orientation and opposite32 bytes. The original optional initializer, application, raw receive and publication are preserved. Constructor conversion is executable pattern matching on RustM, and no inverse or arbitrary representation witness is used.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon
open RawCtxGenericRoleStorage PqxdhBeaconPhase2Shared
open PqxdhJointKdfGame PqxdhSecretInputKdf
open RawCtxSelectedParentEntry RawCtxSelectedParentTable
variable {A I D K X Response Shared : Type}

def optionRust {α : Type} : RustM α → Option α
  | .ok value => some value
  | .fail _ => none
  | .div => none

/-- Converting the complete RustM constructor result to an optional kernel commutes with its representation map. -/
theorem option_map {α β : Type} (f : α → β) (result : RustM α) :
    optionRust (f <$> result) = (optionRust result).map f := by
  cases result <;> rfl

def knownKernel (kernel : ConcreteRatchetKernel) : RawCtxSelectedChain.Kernel :=
  RawCtxChainInterpretation.mapChains RawCtxSelectedChain.Slot.known RawCtxSelectedChain.Slot.known kernel.refined

/-- A known initializer response keeps both actual directional chains and every control/material field. -/
theorem known_native (target : RootOutput) (kernel : ConcreteRatchetKernel) :
    RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) (knownKernel kernel) = kernel := by
  cases kernel
  rfl

noncomputable def normalize (output : PqxdhSecretInputKdf.HmacBlock) : ConcreteRatchetKernel :=
  PqxdhBeaconPhase2Publication.normalInitial
    (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)))
    (RawCtxSelectedInitialConstructor.response64 output)

/-- Either selected initial half reconstructs the exact original normalized nonce-free Beacon kernel. -/
theorem selected_initial (second : Bool) (other target : RootOutput) :
    some (normalize (RawCtxInitialSentinelSampler.join second other target)) =
      (optionRust (RawCtxInitialSentinelSampler.labelInitial second true other)).map
        (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) := by
  have exactInitial := PqxdhBeaconPhase2Publication.normalInitial_exact
    (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)))
    (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target))
  have constructor := RawCtxInitialSentinelSampler.constructor
    (true, PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)) second other target
  change _ = ok (normalize (RawCtxInitialSentinelSampler.join second other target)) at exactInitial
  change _ = _ at constructor
  have combined := exactInitial.symm.trans constructor
  exact (congrArg optionRust combined).trans (option_map _ _)

noncomputable def raw (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    QueryImpl RawCtxSourceOpen.NativeSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  RawCtxSelectedParentNativeBackend.backend source writer prior entry target ∘ₛ RawCtxMixedOwner.receiveLift

/-- The original retained-parent receive adapter realizes the selected Slot kernel with unchanged full shared primitive effects. -/
theorem selected_receive (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (kernel : RawCtxSelectedChain.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (PqxdhInitialGenericBeaconNative.calls (raw (A := A) source writer prior entry target)).receive
      (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) kernel) sequence context =
      Prod.map (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) id <$>
        (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)).receive kernel sequence context := by
  have adapter : raw (A := A) source writer prior entry target ∘ₛ RawCtxSourceOpen.nativeAdapter =
      RawCtxSelectedParentNativeBackend.backend source writer prior entry target ∘ₛ RawCtxMixedOwner.receiveAdapter := by
    funext query
    simp only [raw, RawCtxMixedOwner.receiveAdapter, QueryImpl.compose, QueryImpl.simulateQ_compose]
  simp only [PqxdhInitialGenericBeaconNative.calls, adapter]
  rw [RawCtxSelectedParentNativeBackend.receive_realized]
  change (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$>
      (RawCtxSelectedParentCalls.nativeCalls source writer prior entry target).receive
        (RawCtxSelectedParentCalls.nativeKernel target kernel) sequence context = _
  rw [RawCtxSelectedParentCalls.receive_map, Functor.map_map]
  rfl

/-- A private service reply keeps actual known64 bytes or only the selected orientation and opposite32 bytes. -/
abbrev InitialValue := Sum PqxdhSecretInputKdf.HmacBlock (Bool × RootOutput)

def response (target : RootOutput) : InitialValue → pqxdh.concrete.InitialRatchetKdfResponse
  | .inl output => RawCtxSelectedInitialConstructor.response64 output
  | .inr selected => RawCtxSelectedInitialConstructor.response64
      (RawCtxInitialSentinelSampler.join selected.1 selected.2 target)

noncomputable def labelKernel : InitialValue → Option RawCtxSelectedChain.Kernel
  | .inl output => some (knownKernel (normalize output))
  | .inr selected => optionRust (RawCtxInitialSentinelSampler.labelInitial selected.1 true selected.2)

/-- Every selected or known initializer reply has the exact same original concrete kernel, including complete constructor failure behavior. -/
theorem response_map (target : RootOutput) (value : InitialValue) :
    some (PqxdhBeaconPhase2Publication.normalInitial
      (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)))
      (response target value)) =
      (labelKernel value).map (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) := by
  cases value with
  | inl output => exact congrArg some (known_native target (normalize output)).symm
  | inr selected => exact selected_initial selected.1 selected.2 target

noncomputable def labelInitial
    (service : Secrets Shared → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option InitialValue))
    (secrets : Secrets Shared) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option RawCtxSelectedChain.Kernel) :=
  (fun value => value.bind labelKernel) <$> service secrets

noncomputable def handler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (application : Response → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option Pqxdh.Bytes))
    (service : Secrets Shared → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option InitialValue)) :
    QueryImpl (PqxdhInitialFusedOwner.Spec I D K X Response Shared)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl query => pre query
  | .inr (.inl (.inl query)) => raw source writer prior entry target query
  | .inr (.inl (.inr reply)) => application reply
  | .inr (.inr secrets) => Option.map (response target) <$> service secrets

set_option backward.isDefEq.respectTransparency false in
/-- The optional private initializer keeps every service effect and reuses exactly its selected or known response; it makes no fresh replacement draw. -/
theorem initializer_map (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (application : Response → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option Pqxdh.Bytes))
    (service : Secrets Shared → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option InitialValue))
    (secrets : Secrets Shared) :
    PqxdhInitialGenericBeaconNative.initial
      (fun q => handler source writer prior entry target pre application service (.inr q)) secrets =
      Option.map (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) <$>
        labelInitial service secrets := by
  simp only [PqxdhInitialGenericBeaconNative.initial, handler, labelInitial, Functor.map_map]
  apply congrArg (fun f => f <$> service secrets)
  funext value
  cases value with
  | none => rfl
  | some value => exact response_map target value

/-- Concrete retained-parent calls and exact optional initializer replies discharge the complete original Beacon owner without a caller-supplied callback correspondence premise. -/
theorem owner_selected (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (application : Response → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option Pqxdh.Bytes))
    (service : Secrets Shared → StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option InitialValue))
    (decode : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (state : BeaconState RawCtxSelectedChain.Kernel I D K) :
    simulateQ (handler source writer prior entry target pre application service)
      (PqxdhInitialFusedOwner.owner decode bytes
        (nativeBeacon (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state)) =
      Prod.map id (nativeBeacon (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        PqxdhInitialGenericBeacon.owner pre
          (RawCtxSelectedParentCalls.labelCalls source writer prior entry
            (RawCtxSelectedParentCalls.childResponse prior entry target))
          application (labelInitial service) decode bytes state := by
  exact PqxdhInitialGenericBeaconNative.owner_mapped _ _ _
    (selected_receive source writer prior entry target) _
    (initializer_map source writer prior entry target pre application service) decode bytes state

end BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.option_map' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.option_map
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.known_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.known_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.selected_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.selected_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.selected_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.selected_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.response_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.response_map
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.initializer_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.initializer_map
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.owner_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon.owner_selected
