-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenService
import BeaconcryptCore.Computational.RegistrationNativeMldsa
import BeaconcryptCore.Computational.PqxdhLiveServerConstruction
import BeaconcryptCore.Computational.RawCtxSourceOpen

/-! Literal native startup and primitive-source costs. Initialization, ML generation, signing and indexed KEM are explicit primitive programs; their supplied costs constrain only those bodies. Constructor failure retains its actual draws, and successful unsupplied identity construction adds exactly the existing32-byte sampling allowance. No callback frame or protocol security conclusion is assumed. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
variable {n : Nat} {Value : Type}

def coinCost (count : Nat) : EffectKind → Nat
  | .coin => count
  | .hash | .administrative => 0

/-- A primitive probability program uses only the original World coin route. -/
theorem coins_bound (work : ProbComp Value) (count : Nat) (bounded : work.IsTotalQueryBound count)
    (kind : EffectKind) :
    (simulateQ (RegistrationNativeHiddenService.coins (n := n)) work).IsQueryBoundP
      (fun query => effectKind query = kind) (coinCost count kind) := by
  cases kind with
  | coin =>
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ _ count
        ((isQueryBoundP_true_iff _ _).mpr bounded)
      intro query
      simp [RegistrationNativeHiddenService.coins, effectKind, isQueryBoundP_query_iff]
  | hash =>
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      intro query
      simp [RegistrationNativeHiddenService.coins, effectKind, isQueryBoundP_query_iff]
  | administrative =>
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      intro query
      simp [RegistrationNativeHiddenService.coins, effectKind, isQueryBoundP_query_iff]

/-- ML generation forwards its actual source draws without an extra native coin. -/
theorem generation_bound (source : RegistrationNativeMldsa.Source) (qGenerate : Nat)
    (generation : source.generate.IsTotalQueryBound qGenerate) :
    (RegistrationNativeMldsa.generate source).IsTotalQueryBound qGenerate :=
  RegistrationNativeMldsa.generation_bound source qGenerate generation

/-- A matching owned signing attempt retains the source signer cost, including failed signatures; a key mismatch costs zero. -/
theorem signing_bound (source : RegistrationNativeMldsa.Source) (qSign : Nat)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (credential : RegistrationNativeMldsa.Credential source) (request : registration.MldsaSigningRequest) :
    (RegistrationNativeMldsa.owned source credential request).IsTotalQueryBound qSign := by
  classical
  unfold RegistrationNativeMldsa.owned
  split
  · exact signing _ _
  · trivial

/-- Source initialization is charged even when it fails, before the optional32-byte Server identity draw. -/
theorem constructor_bound (primitives : PqxdhJointIdentity.Primitives) (ensureInit : StateT Unit ProbComp Bool)
    (qInit : Nat) (initialization : (ensureInit.run ()).IsTotalQueryBound qInit)
    (identityIndex : Nat) (serverKeyId : U64) :
    ((PqxdhLiveServerConstruction.construct (P := Unit) primitives ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound
      (qInit + 32) := by
  simpa only [Option.isNone_none, ite_true] using
    PqxdhLiveServerConstruction.construct_uniform (P := Unit) primitives ensureInit qInit
      (fun state => by cases state; exact initialization) identityIndex serverKeyId none ()

end BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts.coins_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts.coins_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts.generation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts.generation_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts.signing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts.signing_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts.constructor_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts.constructor_bound
