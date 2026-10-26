import BeaconcryptCore.Computational.PqxdhErasedParentSample
import BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource

/-! The exact later-record endpoint erases only support proofs and an unused earlier cache field. Its full predecessor, nonce, next-chain, selected message key, retained continuation and final source event remain coupled exactly as before. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhErasedParentMaterial
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhInitialBeaconAmbient PqxdhInitialSourceInitialSecrecy
open RawCtxSelectedParentEntry PqxdhErasedParentSample
open PqxdhOrderedChainHybrids
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (depth : Nat)

local notation "LocalPacket" => Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
abbrev MaterialContext := ((LocalPacket × Entry) × RootOutput) × NonceOutput × RootOutput

noncomputable def prepare (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    ProbComp (MaterialContext (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) := do
  let packet ← PqxdhErasedParentSample.sample source writer sender route decode depth prior
  let parent ← $ᵗ FullOutput
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  pure (((normalize packet, fromOutput (address packet) parent), nextChain parent), nonce, chain)

/-- Erasing unused earlier cache metadata commutes through the full material sampler. -/
theorem prepare_normalized (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    prepare source writer sender route decode depth prior = (do
      let packet ← PqxdhErasedParentSample.normalize <$>
        PqxdhErasedParentSample.sample source writer sender route decode depth prior
      let parent ← $ᵗ FullOutput
      let nonce ← $ᵗ NonceOutput
      let chain ← $ᵗ RootOutput
      pure (((packet, fromOutput (address packet) parent), nextChain parent), nonce, chain)) := by
  simp only [prepare, bind_map_left, address_normalize]

noncomputable def observe
    (context : MaterialContext (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) (key : RootOutput) : ProbComp Bool :=
  PqxdhErasedParentSample.native source writer sender route decode 0 context.1.1 context.1.2
    (materialChainEquiv.symm ((key, context.2.1), context.2.2))

noncomputable def ideal (prior : ProbComp (Context extra M P I D K X Response A N S B)) : ProbComp Bool := do
  let context ← prepare source writer sender route decode depth prior
  let key ← $ᵗ RootOutput
  observe source writer sender route decode context key

/-- The final source observer and all parent/material draws keep exactly the same probability computation after runtime erasure. -/
theorem ideal_source (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    (do
      let pair ← RawCtxSelectedParentCandidates.sample
        (PqxdhInitialSampledParent.sample source writer sender route decode depth prior)
        (PqxdhInitialSampledParent.address source writer sender route decode depth)
      let nonce ← $ᵗ NonceOutput
      let chain ← $ᵗ RootOutput
      let key ← $ᵗ RootOutput
      PqxdhInitialSampledParent.native source writer sender route decode depth 0 pair.1 pair.2
        (materialChainEquiv.symm ((key, nonce), chain))) =
      ideal source writer sender route decode depth prior := by
  unfold ideal prepare RawCtxSelectedParentCandidates.sample
  simp only [bind_assoc, pure_bind]
  rw [← sample_erase source writer sender route decode depth]
  simp only [bind_map_left]
  apply bind_congr
  intro packet
  apply bind_congr
  intro parent
  apply bind_congr
  intro nonce
  apply bind_congr
  intro chain
  apply bind_congr
  intro key
  simp only [observe, address_erase, native_erase]
  exact (native_normalize source writer sender route decode 0
    (erase source writer sender route decode depth packet,
      fromOutput (PqxdhInitialSampledParent.address source writer sender route decode depth packet) parent)
    (nextChain parent) (materialChainEquiv.symm ((key, nonce), chain))).symm

end BeaconcryptCore.Computational.PqxdhErasedParentMaterial


/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentMaterial.prepare_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentMaterial.prepare_normalized

/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentMaterial.ideal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentMaterial.ideal_source
