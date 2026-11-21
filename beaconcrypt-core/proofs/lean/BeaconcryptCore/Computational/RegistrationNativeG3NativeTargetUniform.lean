-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetStartup
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformSecurity

/-! The complete actual known108 good target probability is averaged over the genuine shared seed/scalar/KEM-family/challenge/candidate prior. The reserved selected-key receipt is derived from that prior, preserving the original single canonical target product. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniform
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open PqxdhKemIndCca
open RegistrationNativeSelectiveRecordTraceUniformSecurity (Context prior provider)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem profile_selected (setup : Setup base KemSK) (count : Nat) (selected : Fin (count + 1))
    (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK)
    (supported : profile ∈ support (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem count selected)) :
    count ≤ profile.pairs.length ∧ ∃ chosen, profile.pairs[selected.val]? = some chosen ∧ chosen.1 = profile.publicKey := by
  simp only [RegistrationNativeG3NativeRepeatUniformBound.prior, mem_support_bind_iff] at supported
  obtain ⟨chosen, _chosen, others, _others, pair, _pair, returned⟩ := supported
  simp only [mem_support_pure_iff] at returned
  cases returned
  refine ⟨by simp only [List.length_ofFn]; omega, chosen, ?_, rfl⟩
  simpa only [List.nil_append, List.length_nil, Nat.zero_add] using PqxdhLiveKemSelection.selected_index [] selected chosen others

/-- The actual sampled context contains its genuine reserved selected public key and sufficient actual family length. -/
theorem prior_selected (setup : Setup base KemSK) (budget : Budget) (selected : Fin (budget.create + 1))
    (context : Context KemSK) (supported : context ∈ support (prior setup budget selected)) :
    budget.create ≤ context.profile.pairs.length ∧ ∃ chosen,
      context.profile.pairs[selected.val]? = some chosen ∧ chosen.1 = context.profile.publicKey := by
  simp only [prior, mem_support_bind_iff] at supported
  obtain ⟨seed, _seed, scalar, _scalar, profile, sampled, candidate, _candidate, returned⟩ := supported
  simp only [mem_support_pure_iff] at returned
  cases returned
  exact profile_selected setup budget.create selected profile sampled

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))

noncomputable def full : ProbComp Bool := do
  let context ← prior setup budget target.2
  (fun outcome => @decide (RegistrationNativeG3NativeTargetStartup.Good setup wire serverKeyId budget target claim outcome) (Classical.propDecidable _)) <$>
    RegistrationNativeG3MaterializedTracedStartup.fullGame (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
      context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds .P adversary

/-- The actual entire uniform-prior good target has the same selected physical-handle ordinal required by the concrete record bound. -/
theorem probability (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire) :
    Pr{let won ← (full setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)}[won = true] ≤
      Pr{let won ← (RegistrationNativeSelectiveRecordTraceUniformSecurity.full (n := budget.cap 4 + budget.cap 5)
        setup checks wire route source ensureInit identityIndex serverKeyId target.1.val bounds adversary budget target.2 claim)}[won = true] := by
  unfold full RegistrationNativeSelectiveRecordTraceUniformSecurity.full
  apply prEvent_bind_mono_of_forall_le_of_support
  intro context sampled
  obtain ⟨reserved, chosen, chosenAt, publicKey⟩ := prior_selected setup budget target.2 context sampled
  simp only [RegistrationNativeSelectiveRecordTraceUniformSecurity.fixedFull, prEvent_map,
    RegistrationNativeSelectiveRecordTraceTarget.event, decide_eq_true_eq]
  have compared := RegistrationNativeG3NativeTargetStartup.probability setup checks wire source route ensureInit identityIndex serverKeyId bounds .P adversary budget target
    context.seed context.scalar context.profile.pairs chosen context.profile.challenge context.candidate claim bounded reserved chosenAt readback responseReadback
  rw [publicKey] at compared
  simpa only [provider] using compared

end BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniform.prior_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniform.prior_selected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniform.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniform.probability
