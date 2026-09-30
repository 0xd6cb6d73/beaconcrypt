import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule
import BeaconcryptCore.Computational.PqxdhServerAuthSendFactor
import BeaconcryptCore.Computational.PqxdhFinalMaterialKeySplit

/-!
The selected authentication entry uses the literal 108-byte source factor. Its uniform game can put the 32-byte message key first, while the executable continuation draws only the nonce, next chain and opposite initial chain. These are complete-continuation distribution equalities, not a claim that an arbitrary source context is independent of its selected key.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhJointKdfGame PqxdhRefinement

/-- Convert the same complete 76-byte reply and the same opposite initial chain. -/
def factor (output : PqxdhServerAuthKeySchedule.Output) : PqxdhServerAuthSendFactor.Factor :=
  (RawCtxKdfRequestTable.fullResponse output.1, output.2)

/-- No byte of the selected ratchet response changes at the source interface. -/
theorem factor_decoded (output : PqxdhServerAuthKeySchedule.Output) :
    RawCtxInterpretedReceive.decodeResponse (factor output).1 =
      (RawCtxFreshChainCut.concreteChain (nextChain output.1),
        RawCtxSelectedMessageKey.interpret (material output.1).1
          (.hidden (material output.1).2)) :=
  RawCtxSelectedMessageKey.decoded_selected output.1

/-- The initializer and the stream used by the source factor have the same prefix. -/
theorem initializer_prefix (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    PqxdhServerAuthKeySchedule.initializer source root =
      initialPrefix (PqxdhJointKdf.productionStream source.crypto
        (PqxdhServerAuthSendFactor.address root)) := by
  have info : absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using absBytes_SYM_RATCHET_INFO
  simp only [absBytes] at info
  apply List.Vector.toList_injective
  simp only [PqxdhServerAuthKeySchedule.initializer, initialPrefix,
    PqxdhJointKdf.productionStream, PqxdhServerAuthSendFactor.address,
    RawCtxKdfRequestTable.address, PqxdhRootTableInitialization.rootArray,
    absBytes, List.map_map, Function.comp_def]
  simpa [List.Vector.toList, List.Vector.take, info] using
    source.prefixConsistent.ratchetPrefix root.toList

/-- Both native initial directions come from the same actual initializer prefix. -/
theorem initial_chains (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    PqxdhSecretInputKdf.first32 (PqxdhServerAuthKeySchedule.initializer source root) =
        PqxdhServerAuthSendFactor.target source root ∧
      RawCtxSelectedInitialSecond.secondChain (PqxdhServerAuthKeySchedule.initializer source root) =
        PqxdhServerAuthSendFactor.other source root := by
  rw [initializer_prefix]
  exact ⟨(RawCtxSelectedInitialSampler.shared_prefix_parts _).2,
    (RawCtxSelectedInitialSampler.shared_prefix_parts _).1⟩

/-- The key-schedule factor is the exact one consumed by the source Server build. -/
theorem factor_source (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    factor (PqxdhServerAuthKeySchedule.fromRoot source root) =
      PqxdhServerAuthSendFactor.factor source root := by
  have info : absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using absBytes_SYM_RATCHET_INFO
  simp only [absBytes] at info
  simp only [factor, PqxdhServerAuthKeySchedule.fromRoot,
    PqxdhServerAuthKeySchedule.fromInitializer, (initial_chains source root).1,
    (initial_chains source root).2, PqxdhServerAuthSendFactor.factor]
  congr 1
  rw [← RawCtxKdfRequestTable.fullResponse_source]
  congr 2
  simp [PqxdhServerAuthKeySchedule.step, RawCtxKdfRequestTable.address,
    RawCtxChainSend.nativeRequest, RawCtxFreshChainCut.concreteChain,
    absBytes, List.map_map, Function.comp_def, PqxdhJointKdf.ratchetAddress, info]

/-- The executable context contains nonce12, next-chain32 and opposite-chain32. -/
abbrev Residual := NonceOutput × RootOutput × RootOutput

/-- Only the mathematical interpretation reconstructs the complete factor with the key. -/
noncomputable def output (key : RootOutput) (rest : Residual) :
    PqxdhServerAuthKeySchedule.Output :=
  (materialChainEquiv.symm ((key, rest.1), rest.2.1), rest.2.2)

/-- The hidden slot and known next chain are the exact decoded source coordinates. -/
theorem output_decoded (key : RootOutput) (rest : Residual) :
    RawCtxInterpretedReceive.decodeResponse (factor (output key rest)).1 =
      (RawCtxFreshChainCut.concreteChain rest.2.1,
        RawCtxSelectedMessageKey.interpret key (.hidden rest.1)) := by
  rw [factor_decoded]
  have parts : (material (output key rest).1, nextChain (output key rest).1) =
      ((key, rest.1), rest.2.1) := materialChainEquiv.apply_symm_apply _
  rw [show material (output key rest).1 = (key, rest.1) from congrArg Prod.fst parts,
    show nextChain (output key rest).1 = rest.2.1 from congrArg Prod.snd parts]

set_option linter.deprecated false in
/-- A uniform factor has exactly the ordinary challenger-key-first distribution, through every complete continuation. No context or outcome is conditioned on success. -/
theorem key_first {Result : Type}
    (continuation : PqxdhServerAuthKeySchedule.Output → ProbComp Result) :
    𝒮[(($ᵗ PqxdhServerAuthKeySchedule.Output) >>= continuation)] =
      𝒮[(do let key ← $ᵗ RootOutput
             let rest ← $ᵗ Residual
             continuation (output key rest))] := by
  have split := PqxdhFinalMaterialKeySplit.complete
    (fun full => do let other ← $ᵗ RootOutput; continuation (full, other))
  have reorder := evalSPMF_bind_bind_swap ($ᵗ (NonceOutput × RootOutput))
    ($ᵗ RootOutput) (fun pair key => do
      let other ← $ᵗ RootOutput
      continuation (output key (pair.1, pair.2, other)))
  simp only [← pairSample, bind_assoc, pure_bind, output] at split reorder ⊢
  exact split.trans reorder

set_option linter.deprecated false in
/-- A separately sampled complete source context can also be placed after the challenger key. Its full state and adaptive continuation are retained. -/
theorem key_first_context {Context Result : Type} (sample : ProbComp Context)
    (continuation : Context → PqxdhServerAuthKeySchedule.Output → ProbComp Result) :
    𝒮[(do let context ← sample
           let full ← $ᵗ PqxdhServerAuthKeySchedule.Output
           continuation context full)] =
      𝒮[(do let key ← $ᵗ RootOutput
             let context ← sample
             let rest ← $ᵗ Residual
             continuation context (output key rest))] := by
  exact (evalSPMF_bind_congr' sample (fun context => key_first (continuation context))).trans
    (evalSPMF_bind_bind_swap sample ($ᵗ RootOutput) (fun context key => do
      let rest ← $ᵗ Residual
      continuation context (output key rest)))

/-- The executable's remaining random material costs exactly the 76-byte allowance; the ordinary challenger supplies the separate 32-byte key. -/
theorem residual_bound : ($ᵗ Residual : ProbComp Residual).IsTotalQueryBound 76 := by
  simp only [← pairSample, bind_assoc, pure_bind]
  exact isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 12) (fun nonce =>
      isTotalQueryBound_bind
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun chain =>
          isTotalQueryBound_bind
            (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
            (fun other => show (pure (nonce, chain, other) : ProbComp Residual).IsTotalQueryBound 0 from by trivial)))

end BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.factor_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.factor_decoded

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.initializer_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.initializer_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.initial_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.initial_chains

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.factor_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.factor_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.output_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.output_decoded

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.key_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.key_first

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.key_first_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.key_first_context

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.residual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial.residual_bound
