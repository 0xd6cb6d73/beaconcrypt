-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicGame
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerErasure

/-! On a reached selected-first eager table, the actual dynamic native stopping continuation is bounded by the actual fixed challenge-key continuation. Shared callbacks, full-monitor comparison, early stopping and tracking erasure are all checked source operations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerContinuation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaEuf (Forgery)
open RegistrationNativeMldsaStop (freeze monitor)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)

/-- Dynamic learned-key first-candidate probability is bounded by the actual fixed challenge-key source continuation at the same eager startup cut. -/
theorem bound (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source))
    (ghost : RegistrationNativeMldsaGenerationGhost.State) (pool : Pool source)
    (safe : RegistrationNativeMldsaGhostEager.Fixed source challenge.publicKey (ghost, pool)) :
    Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativeMldsaDynamicGame.continued source setup checks wire route representation adversary selected (some initial, ghost))).run pool}[
      result.1.isSome = true] ≤
    Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativeMldsaStoppedGame.continued source setup checks wire route representation adversary challenge.publicKey (some initial))).run pool}[
      result.1.isSome = true] := by
  let native := RegistrationNativeMldsaProfile.handler (n := n) setup checks wire route representation initial.created initial.credential
  let observer := RegistrationNativeMldsaTrialObserver.observe (n := n) (KemSK := KemSK) (source := handleSource source) source.verify
  let client := adversary initial.public
  let before := (initial.state, (ghost, pool))
  let callback := fun query => RegistrationNativeMldsaGhostEagerExecution.execute source selected tape (native query)
  let dynamic := RegistrationNativeMldsaGhostEagerExecution.dynamic source observer
  let constant := RegistrationNativeMldsaGhostEagerExecution.constant source observer challenge.publicKey
  have dynamic_coupled := RegistrationNativeMldsaGhostEagerStop.program source selected tape native observer
    RegistrationNativeMldsaTableStop.defaultReply client (initial.state, ghost) none pool
  have dynamic_probability :
      Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
        (RegistrationNativeMldsaDynamicGame.continued source setup checks wire route representation adversary selected (some initial, ghost))).run pool}[
        result.1.isSome = true] =
      Pr{let result ← (simulateQ (freeze callback dynamic RegistrationNativeMldsaTableStop.defaultReply) client).run (before, none)}[
        result.2.2.isSome = true] := by
    rw [← dynamic_coupled, prEvent_map]
    simp only [RegistrationNativeMldsaDynamicGame.continued,
      RegistrationNativeMldsaSharedStop.runState, simulateQ_map, StateT.run_map, prEvent_map]
    rfl
  have dynamic_selected := (RegistrationNativeMldsaStop.selected callback dynamic
    RegistrationNativeMldsaTableStop.defaultReply client before none).prEvent_eq (fun candidate => candidate.isSome = true)
  have fixed_selected := (RegistrationNativeMldsaStop.selected callback constant
    RegistrationNativeMldsaTableStop.defaultReply client before none).prEvent_eq (fun candidate => candidate.isSome = true)
  simp only [prEvent_map] at dynamic_selected fixed_selected
  have erased := RegistrationNativeMldsaGhostEagerErasure.program source selected tape native observer challenge.publicKey
    RegistrationNativeMldsaTableStop.defaultReply client before none
  have fixed_plain :
      Pr{let result ← (simulateQ (freeze callback constant RegistrationNativeMldsaTableStop.defaultReply) client).run (before, none)}[
        result.2.2.isSome = true] =
      Pr{let result ← (simulateQ (freeze (fun query => RegistrationNativeMldsaGhostEagerErasure.plain source tape (native query))
        (RegistrationNativeMldsaGhostEagerErasure.observe source observer challenge.publicKey) RegistrationNativeMldsaTableStop.defaultReply) client).run
          ((initial.state, pool), none)}[result.2.2.isSome = true] := by
    have probability := congrArg (fun computation : ProbComp (V × ((RegistrationNativeExperiment.State n KemSK (handleSource source) × Pool source) × Option Forgery)) =>
      Pr{let result ← computation}[result.2.2.isSome = true]) erased
    simpa only [prEvent_map, RegistrationNativeMldsaGhostEagerErasure.arrange,
      RegistrationNativeMldsaGhostEagerErasure.view, before] using probability
  have plain_coupled := RegistrationNativeMldsaSharedStop.program (handleSource source)
    (RegistrationNativeMldsaEager.handler source tape) native (observer challenge.publicKey)
    RegistrationNativeMldsaTableStop.defaultReply client initial.state none pool
  have plain_probability :
      Pr{let result ← (simulateQ (freeze (fun query => RegistrationNativeMldsaGhostEagerErasure.plain source tape (native query))
        (RegistrationNativeMldsaGhostEagerErasure.observe source observer challenge.publicKey) RegistrationNativeMldsaTableStop.defaultReply) client).run
          ((initial.state, pool), none)}[result.2.2.isSome = true] =
      Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
        (RegistrationNativeMldsaStoppedGame.continued source setup checks wire route representation adversary challenge.publicKey (some initial))).run pool}[
        result.1.isSome = true] := by
    have probability := congrArg (fun computation : ProbComp (V × ((RegistrationNativeExperiment.State n KemSK (handleSource source) × Pool source) × Option Forgery)) =>
      Pr{let result ← computation}[result.2.2.isSome = true]) plain_coupled
    have callback_equal : RegistrationNativeMldsaSharedStop.callback (handleSource source)
        (RegistrationNativeMldsaEager.handler source tape) native =
        (fun query => RegistrationNativeMldsaGhostEagerErasure.plain source tape (native query)) := rfl
    have observer_equal : RegistrationNativeMldsaSharedStop.observer (observer challenge.publicKey) =
        RegistrationNativeMldsaGhostEagerErasure.observe source observer challenge.publicKey := rfl
    rw [callback_equal, observer_equal] at probability
    simpa only [prEvent_map, RegistrationNativeMldsaSharedStop.arrange,
      RegistrationNativeMldsaSharedStop.runState, RegistrationNativeMldsaStoppedGame.continued,
      simulateQ_map, StateT.run_map] using probability.symm
  calc
    _ = _ := dynamic_probability
    _ = _ := dynamic_selected.symm
    _ ≤ _ := RegistrationNativeMldsaGhostEagerExecution.monitor_bound source selected tape challenge chosen native observer client before safe
    _ = _ := fixed_selected
    _ = _ := fixed_plain
    _ = _ := plain_probability
end BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerContinuation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerContinuation.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerContinuation.bound
