-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame

/-! A public bundle guess that has passed without selecting a target cannot later arm. The complete remaining actual adaptive source computation therefore agrees in both private interpretations, including all failed callbacks and writers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveUnselected
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (selected position : Nat) (placeholder : Ed25519Signature)
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve)
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "MainState" => RegistrationNativeIdentityMain.State n KemSK mlSource × Platform
local notation "view" => RegistrationNativeIdentityCensorOutgoingView.view placeholder

local notation "current" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder

local notation "entered(" query "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.entered position query before
local notation "called(" masked "," query "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked query before
local notation "run(" masked "," accept "," work "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.visit setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked accept work before

def Passed (position : Nat) (before : FullState) : Prop :=
  position < before.1.2.bundles ∧ before.1.2.target = none

omit primitive in
private theorem entry_unarmed (query : TypedSpec.Domain) (before : FullState) (prior : Passed position before) :
    RegistrationNativeIdentityCensorPrefix.Unarmed (entered(query, before)).1.2 := by
  apply RegistrationNativeIdentityCensorUnarmedMain.enter position query before.1.2 prior.2
  intro index _same
  exact Nat.ne_of_gt prior.1

private theorem call_equal (query : TypedSpec.Domain) (before : FullState) (prior : Passed position before) :
    called(false, query, before) = called(true, query, before) := by
  unfold RegistrationNativeIdentityCensorAdaptivePostselection.call
  exact RegistrationNativeIdentityCensorUnarmedMain.paired setup.joint selected placeholder (current query)
    (entered(query, before)) (entry_unarmed position query before prior)

omit primitive in
private theorem entered_count (query : TypedSpec.Domain) (before : FullState) :
    before.1.2.bundles ≤ (entered(query, before)).1.2.bundles := by
  rcases query with query | command
  · exact Nat.le_refl _
  · cases command <;> try exact Nat.le_refl _
    exact Nat.le_add_right _ _

private theorem call_passed (masked : Bool) (query : TypedSpec.Domain) (before : FullState) (prior : Passed position before)
    (result : TypedSpec.Range query × FullState) (reached : result ∈ support called(masked, query, before)) :
    Passed position result.2 := by
  have frame := RegistrationNativeIdentityCensorUnarmedFrame.main setup.joint selected placeholder masked (current query)
    (entered(query, before)) (entry_unarmed position query before prior) result reached
  have bundles := congrArg (fun value => value.1.bundles) frame.1
  refine ⟨?_, frame.2.2.1⟩
  exact (prior.1.trans_le (entered_count position query before)).trans_le (Nat.le_of_eq bundles.symm)

private theorem visit_query (masked : Bool) (accept : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : FullState × Nat) :
    run(masked, accept, (TypedSpec.query query >>= next), before) =
      (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query before.2 with
      | some packet => pure (before.1.1.2.target.map fun message => (message, packet))
      | none => do
          let selectedCut ← RegistrationNativeIdentityCensorAdaptivePostselection.cut query <$> called(masked, query, before.1)
          match selectedCut with
          | none => pure none
          | some kept => run(masked, accept, (next kept.1), (kept.2, before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0))) := rfl

/-- No later callback can revive an unused public bundle guess; the original adaptive packet observation remains identical. -/
theorem paired (accept : Nat) (work : OracleComp TypedSpec A) (before : FullState × Nat) (prior : Passed position before.1) :
    run(false, accept, work, before) = run(true, accept, work, before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [visit_query, visit_query]
    cases attempted : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query before.2 with
    | some packet => rfl
    | none =>
      dsimp only
      rw [call_equal setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
        erased helper reserve selected position placeholder query before.1 prior]
      simp only [bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro result reached
      have later := call_passed setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
        erased helper reserve selected position placeholder true query before.1 prior result reached
      unfold RegistrationNativeIdentityCensorAdaptivePostselection.cut
      cases published : RegistrationNativeIdentityCensorAdaptivePostselection.published query result.1 result.2 with
      | true => simp only [ite_true]
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact ih result.1 (result.2, before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0) later

/-- The unused public guess has identical executable packet-client source observations, including all later adaptive replies. -/
theorem client (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : FullState × Nat) (prior : Passed position before.1) :
    (simulateQ (RegistrationNativeIdentityCensorAdaptiveSource.sourceBackend setup.joint selected placeholder false)
      (RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current defaults work (before.1.1, before.2))).run' before.1.2 =
    (simulateQ (RegistrationNativeIdentityCensorAdaptiveSource.sourceBackend setup.joint selected placeholder true)
      (RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current defaults work (before.1.1, before.2))).run' before.1.2 := by
  rw [RegistrationNativeIdentityCensorAdaptiveSource.source, RegistrationNativeIdentityCensorAdaptiveSource.source]
  exact paired setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
    erased helper reserve selected position placeholder accept work before prior

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveUnselected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveUnselected.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveUnselected.paired

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveUnselected.client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveUnselected.client
