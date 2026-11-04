-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame
import BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeReduction

/-! The selected-attempt ordinary EUF comparison is instantiated with the actual complete initialized native stopping program. Candidate validity and same-cut freshness are derived from that source execution. The remaining bound premise is purely syntactic finite generation count, not a security or history assertion. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEuf
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaEuf (PublicKey Forgery)
open RegistrationNativeMldsaStoppedGame (program)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)

noncomputable def game {count : Nat} (target : Fin (count + 1)) : ProbComp Bool := do
  match ← RegistrationNativeMldsa.generate source with
  | none => pure false
  | some challenge => do
      let others ← RegistrationNativeMldsaEager.family source count
      let result ← (simulateQ (RegistrationNativeMldsaEager.handler source
        (List.ofFn (target.insertNth (some challenge) others)))
          (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId challenge.publicKey)).run {}
      pure result.1.isSome

private theorem sampled_good {count : Nat} (target : Fin (count + 1))
    (bounded : ∀ publicKey, (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey).IsQueryBoundP
      (RegistrationNativeMldsaEager.IsGenerate source) (count + 1))
    (challenge : Credential source) (generated : some challenge ∈ support (RegistrationNativeMldsa.generate source))
    (others : Fin count → Option (Credential source)) (reserved : others ∈ support (RegistrationNativeMldsaEager.family source count))
    (result : Option Forgery × Pool source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaEager.handler source
      (List.ofFn (target.insertNth (some challenge) others)))
        (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId challenge.publicKey)).run {})) :
    result.1.isSome = true ↔ RegistrationNativeMldsaEufTapeReduction.RawWin source challenge.publicKey result := by
  have lazy_possible : result ∈ support (RegistrationNativeMldsaZeroSource.evaluate source
      (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId challenge.publicKey) {}) := by
    have same := RegistrationNativeMldsaEager.complete_target_first source _ count (bounded challenge.publicKey) target
    rw [support_eq_of_evalDistEq same]
    apply (mem_support_bind_iff _ _ _).mpr
    refine ⟨some challenge, generated, ?_⟩
    apply (mem_support_bind_iff _ _ _).mpr
    exact ⟨others, reserved, supported⟩
  constructor
  · intro selected
    cases candidate : result.1 with
    | none => simp only [candidate, Option.isSome_none, Bool.false_eq_true] at selected
    | some forgery =>
        obtain ⟨valid, fresh⟩ := RegistrationNativeMldsaStoppedGame.zero_good source setup checks wire route representation adversary
          ensureInit identityIndex serverKeyId challenge.publicKey result lazy_possible forgery candidate
        exact ⟨forgery, candidate, valid, fresh⟩
  · rintro ⟨forgery, selected, _valid, _fresh⟩
    simp only [selected, Option.isSome_some]

private theorem bind_probability {Answer : Type} (first : ProbComp Answer)
    (left right : Answer → ProbComp Bool)
    (same : ∀ answer ∈ support first, Pr{let won ← left answer}[won = true] = Pr{let won ← right answer}[won = true]) :
    Pr{let won ← first >>= left}[won = true] = Pr{let won ← first >>= right}[won = true] :=
  le_antisymm
    (prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun answer member => (same answer member).le)
    (prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun answer member => (same answer member).ge)

/-- The executable actual native first-candidate experiment is bounded by an ordinary generated-key primitive EUF adversary for each reserved generation attempt. -/
theorem bound {count : Nat} (target : Fin (count + 1))
    (bounded : ∀ publicKey, (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey).IsQueryBoundP
      (RegistrationNativeMldsaEager.IsGenerate source) (count + 1)) :
    Pr{let won ← game (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId target}[won = true] ≤
      RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId)) := by
  have same : Pr{let won ← game (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId target}[won = true] =
      Pr{let won ← (RegistrationNativeMldsaEufTapeReduction.sourceGame source target
        (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId))}[won = true] := by
    unfold game RegistrationNativeMldsaEufTapeReduction.sourceGame
    apply bind_probability
    intro generated possible
    cases generated with
    | none => rfl
    | some challenge =>
        apply bind_probability
        intro others reserved
        rw [bind_pure_comp, bind_pure_comp, prEvent_map, prEvent_map]
        apply prEvent_congr_of_support
        intro result supported
        simpa only [decide_eq_true_eq] using
          sampled_good source setup checks wire route representation adversary ensureInit identityIndex serverKeyId target bounded
            challenge possible others reserved result supported
  rw [same]
  exact RegistrationNativeMldsaEufTapeReduction.bound source target _
end BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEuf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEuf.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEuf.bound
