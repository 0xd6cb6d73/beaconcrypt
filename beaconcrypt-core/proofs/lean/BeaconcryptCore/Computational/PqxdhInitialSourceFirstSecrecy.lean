import BeaconcryptCore.Computational.PqxdhInitialSourceHalf

/-!
The first evolving-chain comparison is instantiated to the same sampled source experiment as every later stage. One shared uniform64 response supplies both directions. The ordinary full76 sampler uses a root-domain marker and retains only the other half plus an unused12-byte analysis coordinate. The complete source observation, including failed preparation branches, original publication and final byte freshness, is preserved through the evaluated sampling law.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhInitialSourceFirstSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialSourceInitialSecrecy (Input Context)
open PqxdhInitialSourceHalf RawCtxInitialSentinelSampler
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

def address (_ : Context extra M P I D K X Response A N S B) : JointKdfAddress :=
  rootAddress []

private theorem target_source (target : RootOutput) :
    RawCtxSelectedParentPrivatePatch.targetAddress target = FixedHkdfDomain.ratchet.address target.toList :=
  PqxdhInitialNativeLineageCheck.request_concrete target

noncomputable def observer := PqxdhInitialHalfSecrecy.observer source writer (mark (extra := extra)
  (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source)
  sender route decode (view source)
noncomputable def aliasTester := PqxdhInitialHalfSecrecy.aliasTester source writer (mark (extra := extra)
  (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source)
  sender route decode (view source)

/-- The actual initial64 experiment and the constructed ordinary full76 reduction have the same complete source observation, in either adaptively selected direction and on completed branches. -/
theorem actual_source (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    𝒟[PqxdhInitialSourceSampled.game source writer sender route decode prior 0] =
    𝒟[PqxdhInitialHalfSecrecy.actual source writer (mark source) sender route decode (view source) prior address] := by
  simp only [PqxdhInitialSourceSampled.game, PqxdhInitialHalfSecrecy.actual,
    RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro context
  cases context with
  | inl decision =>
      simp only [PqxdhInitialSourceSampled.observe, PqxdhInitialHalfSecrecy.native]
      exact ((OracleComp.EvalDistEq.bind_const ($ᵗ HmacBlock) (pure decision)).trans
        (OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) (pure decision)).symm).evalDist_eq
  | inr input =>
      have sampled := initial_observed (second input.selected) (fun other target =>
        PqxdhInitialSourceInitialSecrecy.sourceGame source writer sender route decode input zeroRoot
          (RawCtxSelectedInitialConstructor.response64 (join (second input.selected) other target)) 0)
      simp only [join_parts] at sampled
      refine sampled.evalDist_eq.trans ?_
      apply evalDist_bind_congr
      intro output
      simpa only [address, RawCtxSelectedParentEntry.fromOutput, RawCtxInitialSentinel.entry, RawCtxInitialSentinel.sentinel,
        target_source] using congrArg evalDist (real_native source writer sender route decode input
        (PqxdhOrderedChainHybrids.material output).1 (PqxdhOrderedChainHybrids.nextChain output)
        (PqxdhOrderedChainHybrids.material output).2)

/-- The adjacent stage uses the identical full initializer distribution and draws only the first selected full76 child; every original source effect and the complete publication/freshness event remain inside the equality. -/
theorem random_source (prior : ProbComp (Context extra M P I D K X Response A N S B))
    (positive : ∀ input, Sum.inr input ∈ support prior → 0 < input.number.val) :
    𝒟[PqxdhInitialSourceSampled.game source writer sender route decode prior 1] =
    𝒟[PqxdhInitialHalfSecrecy.random source writer (mark source) sender route decode (view source) prior address] := by
  simp only [PqxdhInitialSourceSampled.game, PqxdhInitialHalfSecrecy.random,
    RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  apply evalDist_bind_congr_of_support
  intro context supported
  cases context with
  | inl decision =>
      simp only [PqxdhInitialSourceSampled.observe, PqxdhInitialHalfSecrecy.native]
      exact ((OracleComp.EvalDistEq.bind_const ($ᵗ HmacBlock) (pure decision)).trans
        ((OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) (($ᵗ FullOutput) >>= fun _ => pure decision)).trans
          (OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) (pure decision))).symm).evalDist_eq
  | inr input =>
      have sampled := initial_observed (second input.selected) (fun other target =>
        PqxdhInitialSourceInitialSecrecy.sourceGame source writer sender route decode input zeroRoot
          (RawCtxSelectedInitialConstructor.response64 (join (second input.selected) other target)) 1)
      simp only [join_parts] at sampled
      refine sampled.evalDist_eq.trans ?_
      apply evalDist_bind_congr
      intro output
      exact random_native source writer sender route decode input (positive input supported)
        (PqxdhOrderedChainHybrids.material output).1 (PqxdhOrderedChainHybrids.nextChain output)
        (PqxdhOrderedChainHybrids.material output).2

end BeaconcryptCore.Computational.PqxdhInitialSourceFirstSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstSecrecy.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstSecrecy.actual_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstSecrecy.random_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstSecrecy.random_source
