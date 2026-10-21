import BeaconcryptCore.Computational.PqxdhAdaptiveFinalMaterial
import BeaconcryptCore.Computational.PqxdhAdaptiveFirstMaterial
import BeaconcryptCore.Computational.RawCtxSelectedMessageKey

/-! The source's final complete76 draw can supply an ordinary uniform message key after the exact source prefix, nonce and next chain. Every continuation sees the same reconstructed full output. This distribution identity does not itself simulate secret-key use or reveal checks. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhFinalMaterialKeySplit
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

/-- Reconstructing one source reply from its three actual projections preserves every byte. -/
theorem reconstruct (output : FullOutput) :
    materialChainEquiv.symm (((material output).1, (material output).2), nextChain output) = output := by
  exact materialChainEquiv.symm_apply_apply output

/-- The exact source continuation, including final private-state checks, is preserved after the selected message-key draw is placed last. -/
theorem complete {Result : Type} (continuation : FullOutput → ProbComp Result) :
    𝒮[($ᵗ FullOutput) >>= continuation] =
      𝒮[(do let nonce ← $ᵗ NonceOutput
             let chain ← $ᵗ RootOutput
             let key ← $ᵗ RootOutput
             continuation (materialChainEquiv.symm ((key, nonce), chain)))] := by
  have same := RawCtxSelectedMessageKey.key_observed_vcvioLegacy
    (fun key nonce chain => continuation (materialChainEquiv.symm ((key, nonce), chain)))
  simpa only [reconstruct] using same

end BeaconcryptCore.Computational.PqxdhFinalMaterialKeySplit

/-- info: 'BeaconcryptCore.Computational.PqxdhFinalMaterialKeySplit.reconstruct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFinalMaterialKeySplit.reconstruct

/-- info: 'BeaconcryptCore.Computational.PqxdhFinalMaterialKeySplit.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFinalMaterialKeySplit.complete
