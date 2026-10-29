-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSampledMonad

/-! The generated Server constructor's seed is an independent private challenge draw. Its actual runtime initialization and original counted dummy seed draw stay at their original positions, including failure branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedConstruct
open PqxdhRecordLiftWorld (sampled)
open PqxdhJointIdentity (IdentitySeed Primitives)
open PqxdhLiveServerConstruction (Created initialized)
variable {n : Nat} {Value : Type}

def replace (joint : Primitives) (identityIndex : Nat) (serverKeyId : U64) (seed : IdentitySeed)
    (constructed : Option (Created Unit) × Unit) : Option (Created Unit) × Unit :=
  (constructed.1.map (fun _ => initialized joint identityIndex serverKeyId .generated seed), constructed.2)

/-- The literal constructor's initialization and optional generated-seed branch use the actual native counted sampler. -/
theorem construct (joint : Primitives) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (before : PqxdhRecordLiftWorld.State n) :
    (sampled ((PqxdhLiveServerConstruction.construct (P := Unit) joint ensureInit identityIndex serverKeyId none).run ())).run before = (do
      let ready ← (sampled (ensureInit.run ())).run before
      if ready.1.1 then do
        let generated ← (sampled PqxdhJointIdentity.sampleSeed).run ready.2
        pure ((some (initialized joint identityIndex serverKeyId .generated generated.1), ready.1.2), generated.2)
      else pure ((none, ready.1.2), ready.2)) := by
  change (sampled (do
    let ready ← ensureInit.run ()
    if ready.1 then (fun seed => (some (initialized joint identityIndex serverKeyId .generated seed), ready.2)) <$> PqxdhJointIdentity.sampleSeed
    else pure (none, ready.2))).run before = _
  rw [RegistrationNativeSampledMonad.bind]
  apply bind_congr
  intro ready
  split
  · rw [map_eq_bind_pure_comp, RegistrationNativeSampledMonad.bind]
    simp only [Function.comp_def, RegistrationNativeSampledMonad.pure]
  · exact RegistrationNativeSampledMonad.pure _ _

/-- Replacing the source seed by an early independent private seed retains the complete constructor outcome and World law for every continuation. -/
theorem eager (joint : Primitives) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (before : PqxdhRecordLiftWorld.State n)
    (next : (Option (Created Unit) × Unit) → PqxdhRecordLiftWorld.State n → ProbComp Value) :
    (do let constructed ← (sampled ((PqxdhLiveServerConstruction.construct (P := Unit) joint ensureInit identityIndex serverKeyId none).run ())).run before
        next constructed.1 constructed.2) =ᵈ
      (do let seed ← PqxdhJointIdentity.sampleSeed
          let constructed ← (sampled ((PqxdhLiveServerConstruction.construct (P := Unit) joint ensureInit identityIndex serverKeyId none).run ())).run before
          next (replace joint identityIndex serverKeyId seed constructed.1) constructed.2) := by
  simp only [construct, bind_assoc]
  refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointIdentity.sampleSeed
    ((sampled (ensureInit.run ())).run before)
    (fun seed ready => do
      let constructed ← (if ready.1.1 then do
        let generated ← (sampled PqxdhJointIdentity.sampleSeed).run ready.2
        pure ((some (initialized joint identityIndex serverKeyId .generated generated.1), ready.1.2), generated.2)
      else pure ((none, ready.1.2), ready.2))
      next (replace joint identityIndex serverKeyId seed constructed.1) constructed.2)).symm
  apply _root_.EvalDistEq.bind_right
  intro ready
  split
  · simp only [bind_assoc, pure_bind, replace, Option.map_some]
    exact RegistrationNativeSampling.scalar_eager ready.2 (fun seed world => next
      (some (initialized joint identityIndex serverKeyId .generated seed), ready.1.2) world)
  · simp only [pure_bind, replace, Option.map_none]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm

end BeaconcryptCore.Computational.RegistrationNativeSeedConstruct

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedConstruct.construct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedConstruct.construct
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedConstruct.eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedConstruct.eager
