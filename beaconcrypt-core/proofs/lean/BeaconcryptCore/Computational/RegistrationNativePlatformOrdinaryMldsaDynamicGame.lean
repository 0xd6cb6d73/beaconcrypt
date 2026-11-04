-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource

/-! The dynamic first-candidate source game learns its target public key from the actual selected generation reply. Its source code receives only an attempt ordinal, never a future key. Effectful startup, all typed native callbacks and first-candidate stopping remain literal; accounting normalization retains the exact public generation ghost. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicGame
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaEuf (Forgery)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaCountMap (transform)
open RegistrationNativeMldsaCountStart (initialProject)
open RegistrationNativeMldsaGhostState (track)
variable {n : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)

abbrev State := RegistrationNativePlatformOrdinaryMldsaCountStop.State n KemSK Platform (handleSource source) × RegistrationNativeMldsaGenerationGhost.State

def observe : RegistrationNativeMldsaStop.Observer (spec := RegistrationNativeRawAdapter.TypedSpec)
    (State := State (n := n) (KemSK := KemSK) (Platform := Platform) source) (Candidate := Forgery) :=
  fun query before reply after => after.2.publicKey.bind
    (fun publicKey => RegistrationNativeMldsaTrialObserver.observe source.verify publicKey query before.1.1 reply after.1.1)

omit primitive in
private theorem observe_view (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : State (n := n) (KemSK := KemSK) (Platform := Platform) source) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    observe source query (RegistrationNativeMldsaGhostCount.view RegistrationNativePlatformOrdinaryMldsaCountStop.projection before) reply
      (RegistrationNativeMldsaGhostCount.view RegistrationNativePlatformOrdinaryMldsaCountStop.projection after) = observe source query before reply after := by
  cases learned : after.2.publicKey with
  | none => simp only [observe, RegistrationNativeMldsaGhostCount.view, learned, Option.bind_none]
  | some key =>
      simp only [observe, RegistrationNativeMldsaGhostCount.view, learned, Option.bind_some]
      exact RegistrationNativeMldsaTrialObserverView.observe_count source.verify key query before.1.1 after.1.1 reply

omit primitive in
private theorem view_idempotent (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source) :
    RegistrationNativeMldsaGhostCount.view RegistrationNativePlatformOrdinaryMldsaCountStop.projection
      (RegistrationNativeMldsaGhostCount.view RegistrationNativePlatformOrdinaryMldsaCountStop.projection before) =
      RegistrationNativeMldsaGhostCount.view RegistrationNativePlatformOrdinaryMldsaCountStop.projection before := by
  simp only [RegistrationNativeMldsaGhostCount.view, RegistrationNativePlatformOrdinaryMldsaCountStop.idempotent]

private theorem correct (selected : Nat) (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) :
    RegistrationNativeMldsaCountRules.Correct
      (RegistrationNativeMldsaCountStop.view (RegistrationNativeMldsaGhostCount.view (RegistrationNativePlatformOrdinaryMldsaCountStop.projection (n := n) (Platform := Platform))))
      (simulateQ (RegistrationNativeMldsaStop.freeze
        (fun query => track source selected (RegistrationNativePlatformOrdinaryMldsaCountStop.handler (n := n) setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query))
        (observe (n := n) source) RegistrationNativeMldsaTableStop.defaultReply) (adversary initial.public)) :=
  RegistrationNativeMldsaCountStop.program _ (view_idempotent source) (observe (n := n) source)
    (fun query before after reply => observe_view source query before after reply) _ RegistrationNativeMldsaTableStop.defaultReply
    (fun query => RegistrationNativeMldsaGhostCount.correct source _ selected _
      (RegistrationNativePlatformOrdinaryMldsaCountRun.handler setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)) _

noncomputable def continued (selected : Nat) (previous : Platform)
    (initialized : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State) :
    OracleComp (Spec (handleSource source)) (Option Forgery) :=
  match initialized.1 with
  | none => pure none
  | some initial => (fun result => result.2.2) <$>
      (simulateQ (RegistrationNativeMldsaStop.freeze
        (fun query => track source selected (RegistrationNativePlatformOrdinaryMldsaCountStop.handler (n := n) setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query))
        (observe (n := n) source) RegistrationNativeMldsaTableStop.defaultReply) (adversary initial.public)).run
        (((initial.state, previous), initialized.2), none)

def initialView (initialized : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State) :=
  (initialized.1.map initialProject, initialized.2)

private theorem continued_normalized (selected : Nat) (previous : Platform)
    (initialized : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State) :
    transform (continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous initialized) =
      continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous (initialView source initialized) := by
  cases initial_eq : initialized.1 with
  | none => simp only [continued, initialView, initial_eq, Option.map_none, transform, simulateQ_pure]
  | some initial =>
      have public_same := RegistrationNativeMldsaCountStart.initial_public initial
      simp only [initialProject] at public_same
      have same := congrArg (fun work => (fun result => result.2.2) <$> work)
        ((correct source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected initial).2 (((initial.state, previous), initialized.2), none))
      simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaCountStop.view, RegistrationNativeMldsaGhostCount.view] at same
      simpa only [continued, initialView, initial_eq, Option.map_some, initialProject, RegistrationNativePlatformOrdinaryMldsaCountStop.projection, public_same,
        transform, simulateQ_map] using same

private theorem continued_original (selected : Nat) (previous : Platform)
    (initialized : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State) :
    continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous (initialView source initialized) =
      continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous initialized := by
  cases initial_eq : initialized.1 with
  | none => simp only [continued, initialView, initial_eq, Option.map_none]
  | some initial =>
      have public_same := RegistrationNativeMldsaCountStart.initial_public initial
      simp only [initialProject] at public_same
      have same := congrArg (fun work => (fun result => result.2.2) <$> work)
        ((correct source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected initial).1 (((initial.state, previous), initialized.2), none))
      simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaCountStop.view, RegistrationNativeMldsaGhostCount.view] at same
      simpa only [continued, initialView, initial_eq, Option.map_some, initialProject, RegistrationNativePlatformOrdinaryMldsaCountStop.projection, public_same] using same.symm

omit primitive in
private theorem start_normalized (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    initialView (n := n) source <$> transform (RegistrationNativeMldsaGenerationGhost.run source selected
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}) =
      initialView source <$> RegistrationNativeMldsaGenerationGhost.run source selected
        (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {} := by
  have same := congrArg (fun program => RegistrationNativeMldsaGenerationGhost.run source selected program {})
    (RegistrationNativeMldsaCountStart.start (n := n) (source := handleSource source) setup ensureInit identityIndex serverKeyId)
  simp only [RegistrationNativeMldsaGenerationGhost.run, simulateQ_map, StateT.run_map] at same
  have normalized := RegistrationNativeMldsaGenerationGhost.normalized source selected
    (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {}
  simp only [RegistrationNativeMldsaGenerationGhost.run] at normalized
  rw [normalized] at same
  exact same

noncomputable def program (previous : Platform) (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    OracleComp (Spec (handleSource source)) (Option Forgery) := do
  let initialized ← RegistrationNativeMldsaGenerationGhost.run source selected
    (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {}
  continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous initialized

/-- The dynamic actual initialized source program receives no future target key and preserves its first candidate under checked accounting normalization. -/
theorem normalized (previous : Platform) (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    transform (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous selected ensureInit identityIndex serverKeyId) =
      program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous selected ensureInit identityIndex serverKeyId := by
  simp only [program, transform, simulateQ_bind]
  change (transform (RegistrationNativeMldsaGenerationGhost.run source selected
    (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}) >>= fun initial =>
      transform (continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous initial)) = _
  calc
    _ = transform (RegistrationNativeMldsaGenerationGhost.run source selected
        (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}) >>= fun initial =>
        continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous (initialView source initial) := by
      apply bind_congr
      intro initial
      exact continued_normalized source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous initial
    _ = (initialView source <$> transform (RegistrationNativeMldsaGenerationGhost.run source selected
        (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {})) >>=
        continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous := by rw [bind_map_left]
    _ = (initialView source <$> RegistrationNativeMldsaGenerationGhost.run source selected
        (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}) >>=
        continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous := by rw [start_normalized]
    _ = RegistrationNativeMldsaGenerationGhost.run source selected
        (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {} >>= fun initial =>
        continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous (initialView source initial) := by rw [bind_map_left]
    _ = _ := by
      apply bind_congr
      intro initial
      exact continued_original source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous initial

/-- The dynamically selected actual candidate and full private signing prefix have the same true-count and count-free source semantics. -/
theorem zero (previous : Platform) (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    RegistrationNativeMldsaZeroSource.evaluate source
      (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous selected ensureInit identityIndex serverKeyId) {} =
      RegistrationNativeMldsaTableProgram.evaluate source
        (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous selected ensureInit identityIndex serverKeyId) {} := by
  rw [← RegistrationNativeMldsaZeroSource.source_program, normalized]
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicGame


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicGame.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicGame.normalized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicGame.zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicGame.zero
