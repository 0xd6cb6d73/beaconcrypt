-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicGame
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostSharedStop
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostNative

/-! The complete actual initialized true-count dynamic full monitor has the same candidate distribution as the ordinal-only free stopping program. Every callback uses the original native source and one shared actual private table. The full execution may continue after capture; freezing retains the exact same first candidate and its source prefix. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaEuf (Forgery)
open RegistrationNativeMldsaStop (freeze monitor)
variable {n : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)

noncomputable def continued (previous : Platform) (stopped : Bool) (selected : Nat)
    (initial : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State)
    (pool : Pool source) : ProbComp (Option Forgery) :=
  match initial.1 with
  | none => pure none
  | some initialValue =>
      let callback := RegistrationNativePlatformMldsaGhostNative.callback source selected setup checks wire route representation initialValue.created initialValue.credential view failure allocation reserveRegistration reservePeer erased helper writer
      let handler := if stopped then freeze callback (RegistrationNativePlatformMldsaGhostNative.observe source) RegistrationNativeMldsaTableStop.defaultReply
        else monitor callback (RegistrationNativePlatformMldsaGhostNative.observe source)
      (fun result => result.2.2) <$> (simulateQ handler (adversary initialValue.public)).run
        (((initialValue.state, previous), (initial.2, pool)), none)

noncomputable def game (previous : Platform) (stopped : Bool) (selected : Nat) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64) : ProbComp (Option Forgery) := do
  let started ← RegistrationNativeMldsaTableProgram.evaluate source
    (RegistrationNativeMldsaGenerationGhost.run source selected
      (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {}) {}
  continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous stopped selected started.1 started.2

private theorem continued_free (previous : Platform) (selected : Nat)
    (initial : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State)
    (pool : Pool source) :
    Prod.fst <$> RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativePlatformMldsaDynamicGame.continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary selected previous initial) pool =
      continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous true selected initial pool := by
  cases initialized : initial.1 with
  | none =>
      simp only [RegistrationNativePlatformMldsaDynamicGame.continued, continued, initialized,
        RegistrationNativeMldsaTableProgram.evaluate, simulateQ_pure, StateT.run_pure, map_pure]
  | some initialValue =>
      let native := RegistrationNativePlatformMldsaCountStop.handler (n := n) setup checks wire route representation initialValue.created initialValue.credential view failure allocation reserveRegistration reservePeer erased helper writer
      let observer := RegistrationNativePlatformMldsaCountStop.observe (n := n) (KemSK := KemSK) (Platform := Platform) (source := handleSource source)
      have same := RegistrationNativeMldsaGhostSharedStop.program source
        (RegistrationNativeMldsaTableProgram.handler source) selected native observer RegistrationNativeMldsaTableStop.defaultReply
        (adversary initialValue.public) ((initialValue.state, previous), initial.2) none pool
      have callback_equal : (fun query => RegistrationNativeMldsaGhostSharedStop.execute source
          (RegistrationNativeMldsaTableProgram.handler source) selected (native query)) =
          RegistrationNativePlatformMldsaGhostNative.callback source selected setup checks wire route representation initialValue.created initialValue.credential view failure allocation reserveRegistration reservePeer erased helper writer := rfl
      have observer_equal : RegistrationNativeMldsaGhostSharedStop.dynamic observer =
          RegistrationNativePlatformMldsaGhostNative.observe source := rfl
      rw [callback_equal, observer_equal] at same
      have free_observer_equal : RegistrationNativeMldsaGhostSharedStop.observe observer =
          RegistrationNativePlatformMldsaDynamicGame.observe source := rfl
      rw [free_observer_equal] at same
      have projected := congrArg (fun computation => (fun result => result.2.2) <$> computation) same
      simpa only [RegistrationNativePlatformMldsaDynamicGame.continued, continued, initialized,
        ite_true, RegistrationNativeMldsaTableProgram.evaluate,
        RegistrationNativeMldsaSharedStop.runState, simulateQ_map, StateT.run_map,
        Functor.map_map, RegistrationNativeMldsaGhostSharedStop.arrange] using projected

/-- Interpreting the entire ordinal-only free stopping program recovers the actual initialized frozen native source game. -/
theorem frozen (previous : Platform) (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Prod.fst <$> RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativePlatformMldsaDynamicGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous selected ensureInit identityIndex serverKeyId) {} =
      game (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous true selected ensureInit identityIndex serverKeyId := by
  simp only [RegistrationNativePlatformMldsaDynamicGame.program, game, RegistrationNativeMldsaTableProgram.evaluate,
    simulateQ_bind, StateT.run_bind, map_bind]
  apply bind_congr
  intro started
  exact continued_free source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous selected started.1 started.2

/-- Continuing the actual native source after selection has exactly the first-candidate distribution of freezing at its literal cut. -/
theorem selected (previous : Platform) (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    EvalDistEq (game (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous false selected ensureInit identityIndex serverKeyId)
      (game (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous true selected ensureInit identityIndex serverKeyId) := by
  unfold game
  apply EvalDistEq.bind_right
  intro started
  cases initialized : started.1.1 with
  | none => simp only [continued, initialized]; rfl
  | some initialValue =>
      simp only [continued, initialized, Bool.false_eq_true, ite_false, ite_true]
      exact RegistrationNativeMldsaStop.selected _ _ RegistrationNativeMldsaTableStop.defaultReply
        (adversary initialValue.public) ((initialValue.state, previous), (started.1.2, started.2)) none

/-- The actual complete dynamic source monitor's candidate mass is the candidate mass of the checked free stopping program, retaining actual source histories throughout the transport. -/
theorem probability (previous : Platform) (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let candidate ← game (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous false selected ensureInit identityIndex serverKeyId}[
      candidate.isSome = true] =
    Pr{let result ← (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativePlatformMldsaDynamicGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous selected ensureInit identityIndex serverKeyId) {})}[
        result.1.isSome = true] := by
  have same := (RegistrationNativePlatformMldsaDynamicSource.selected (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous selected ensureInit identityIndex serverKeyId).prEvent_eq
    (fun candidate => candidate.isSome = true)
  rw [← frozen, prEvent_map] at same
  exact same
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicSource


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicSource.frozen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicSource.frozen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicSource.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicSource.selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicSource.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicSource.probability
