import BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap
import BeaconcryptCore.Computational.RawCtxSelectedInitialSecond
import BeaconcryptCore.Computational.RawCtxInitialChildSecrecy

/-!
The first directional child can reuse the selected-chain interpreter without inventing a predecessor derivation. Its analysis-only entry uses the root domain, which every actual private ratchet callback rejects by domain inequality. Its material retains the opposite initial half and twelve independent reduction-only bytes; the selected initial half occurs only in the unavailable coordinate. No source initialization nonce, source cache binding or public HKDF override is introduced. The actual initializer remains a single64-byte response; the reduction's unused twelve bytes are separately counted.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInitialSentinel
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain

/-- A private interpreter marker, never a source initializer or derivation address. -/
def sentinel : JointKdfAddress := rootAddress []

/-- Every actual typed private ratchet request has the ratchet domain regardless of its chain bytes. -/
theorem private_address (chain : RatchetChain) :
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) =
      ratchetAddress (PqxdhRefinement.absBytes chain.bytes) := by
  change (⟨PqxdhRefinement.absBytes ratchet.SYM_RATCHET_INFO, PqxdhRefinement.absBytes chain.bytes⟩ : JointKdfAddress) = _
  have info : PqxdhRefinement.absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO
  exact congrArg (fun domain => (⟨domain, PqxdhRefinement.absBytes chain.bytes⟩ : JointKdfAddress)) info

/-- No actual private ratchet query can access the analysis marker; this uses only distinct literal domain labels. -/
theorem private_ne (chain : RatchetChain) :
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) ≠ sentinel := by
  rw [private_address]
  exact Ne.symm (rootAddress_ne_ratchetAddress [] (PqxdhRefinement.absBytes chain.bytes))

/-- The analysis entry stores the opposite initial half, never the selected half; its final coordinate is reduction-only randomness. -/
def entry (other : RootOutput) (extra : NonceOutput) : Entry := ⟨sentinel, other, extra⟩

/-- Every actual private response is the original retained lookup, independent of both the marker and the reduction-only twelve bytes. -/
theorem lookup_private (prior : Prior) (other target : RootOutput) (extra : NonceOutput) (chain : RatchetChain) :
    lookup prior (entry other extra) target (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain)) =
      prior (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain)) := by
  simp only [lookup, entry, private_ne, if_false]

/-- The first-child observer reuses one supplied complete child for hidden requests and the original retained lookup for every known request. -/
noncomputable def firstStep (prior : Prior) (challenge : RatchetKdfResponse) : Slot → Slot × RatchetMaterial
  | .hidden => let reply := RawCtxInterpretedReceive.decodeResponse challenge
      (.known reply.1, reply.2)
  | .known chain =>
      let reply := RawCtxInterpretedReceive.decodeResponse
        (RawCtxKdfRequestTable.fullResponse (prior (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain))))
      (.known reply.1, reply.2)

/-- The retained-parent interpreter specializes exactly to a first-child observer that has no target input or artificial source predecessor. -/
theorem first_step (prior : Prior) (other : RootOutput) (extra : NonceOutput)
    (challenge : RatchetKdfResponse) (slot : Slot) :
    RawCtxSelectedParentTable.step prior (entry other extra) challenge slot = firstStep prior challenge slot := by
  cases slot <;> simp only [RawCtxSelectedParentTable.step, firstStep, entry, private_ne, if_false]


end BeaconcryptCore.Computational.RawCtxInitialSentinel

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinel.private_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinel.private_address

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinel.private_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinel.private_ne

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinel.lookup_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinel.lookup_private

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinel.first_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinel.first_step
