import BeaconcryptCore.Computational.RawCtxSourceChainHandles

/-!
The source opening getters read material, sequence and original context, independently of both chain fields. Their chosen-value normalizers preserve absent and mistagged slots. The full optional opening program and complete shared primitive state are equal for arbitrary chain interpretations, allowing an interpreter to fill unread chain fields without obtaining secret bytes. This does not erase material, alter source state, or prove a security property.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxChainOpeningArguments
open RawCtxChainInterpretation RawCtxInterpretedOpening

/-- Actual selected opening arguments do not inspect either chain field; arbitrary chain maps preserve material, sequence and context. -/
theorem arguments_chains {Send Receive : Type}
    (send send' : Send → RatchetChain) (receive receive' : Receive → RatchetChain)
    (pending : Opening Send Receive RatchetMaterial RawCtxWholeOwner.OpenContext) :
    RawCtxWholeOwner.arguments (toNative (mapOpeningChains send receive pending)) =
      RawCtxWholeOwner.arguments (toNative (mapOpeningChains send' receive' pending)) := by
  have materialEq : (toNative (mapOpeningChains send receive pending)).material =
      (toNative (mapOpeningChains send' receive' pending)).material := by
    rw [native_material, native_material, opening_material_chains, opening_material_chains]
  have sequenceEq : (toNative (mapOpeningChains send receive pending)).sequence =
      (toNative (mapOpeningChains send' receive' pending)).sequence := by
    rw [native_sequence, native_sequence, opening_sequence_chains, opening_sequence_chains]
  have hm : (toNative (mapOpeningChains send receive pending)).material_total.choose =
      (toNative (mapOpeningChains send' receive' pending)).material_total.choose := by
    apply RustM.ok.inj
    exact (toNative (mapOpeningChains send receive pending)).material_total.choose_spec.symm.trans
      (materialEq.trans (toNative (mapOpeningChains send' receive' pending)).material_total.choose_spec)
  have hs : (toNative (mapOpeningChains send receive pending)).sequence_total.choose =
      (toNative (mapOpeningChains send' receive' pending)).sequence_total.choose := by
    apply RustM.ok.inj
    exact (toNative (mapOpeningChains send receive pending)).sequence_total.choose_spec.symm.trans
      (sequenceEq.trans (toNative (mapOpeningChains send' receive' pending)).sequence_total.choose_spec)
  simp only [RawCtxWholeOwner.arguments, hm, hs]
  rfl

/-- The complete source opening adapter issues the same optional primitive call for any two interpretations of its chain fields. -/
theorem adapter_chains {Send Receive : Type}
    (send send' : Send → RatchetChain) (receive receive' : Receive → RatchetChain)
    (pending : Opening Send Receive RatchetMaterial RawCtxWholeOwner.OpenContext) :
    RawCtxWholeOwner.adapter (.inr (toNative (mapOpeningChains send receive pending))) =
      RawCtxWholeOwner.adapter (.inr (toNative (mapOpeningChains send' receive' pending))) := by
  simp only [RawCtxWholeOwner.adapter, arguments_chains send send' receive receive' pending]
  rfl

/-- The actual shared source opening callback is chain-independent as a complete stateful computation, so a constant chain interpretation can be used privately. -/
theorem native_chains {Send Receive Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (send send' : Send → RatchetChain) (receive receive' : Receive → RatchetChain)
    (pending : Opening Send Receive RatchetMaterial RawCtxWholeOwner.OpenContext) :
    RawCtxSourceChainHandles.receiveNative (Auxiliary := Auxiliary) source writer
      (.inr (toNative (mapOpeningChains send receive pending))) =
    RawCtxSourceChainHandles.receiveNative source writer
      (.inr (toNative (mapOpeningChains send' receive' pending))) := by
  exact congrArg (simulateQ (RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ RawCtxMixedOwner.receiveAdapter))
    (adapter_chains send send' receive receive' pending)

end BeaconcryptCore.Computational.RawCtxChainOpeningArguments

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOpeningArguments.arguments_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOpeningArguments.arguments_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOpeningArguments.adapter_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOpeningArguments.adapter_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOpeningArguments.native_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOpeningArguments.native_chains
