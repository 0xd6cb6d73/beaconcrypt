-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource
import BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource

/-! The executable complete native first-candidate game includes actual effectful startup and every original typed callback. Its selected candidate and full private signing prefix are invariant under ML count normalization. Ordinary validity and same-cut message freshness are derived from the actual initialized source, without an authentication or history premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaEuf (PublicKey Forgery Valid Fresh)
open RegistrationNativeMldsaCountStart (initialProject)
open RegistrationNativeMldsaCountMap (transform)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)

noncomputable def continued (publicKey : PublicKey)
    (initial : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source))) :
    OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery) :=
  match initial with
  | none => pure none
  | some initial => (fun result => result.2.2) <$>
      (simulateQ (RegistrationNativeMldsaStop.freeze
        (RegistrationNativeMldsaProfile.handler setup checks wire route representation initial.created initial.credential)
        (RegistrationNativeMldsaTrialObserver.observe source.verify publicKey) RegistrationNativeMldsaTableStop.defaultReply)
        (adversary initial.public)).run (initial.state, none)

private theorem continued_normalized (publicKey : PublicKey)
    (initial : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source))) :
    transform (continued source setup checks wire route representation adversary publicKey initial) =
      continued source setup checks wire route representation adversary publicKey (initial.map initialProject) := by
  cases initial with
  | none => simp only [continued, transform, simulateQ_pure, Option.map_none]
  | some initial =>
      have public_same := RegistrationNativeMldsaCountStart.initial_public initial
      simp only [initialProject] at public_same
      have same := congrArg (fun work => (fun result => result.2.2) <$> work)
        ((RegistrationNativeMldsaCountStop.native setup checks wire route representation initial.created initial.credential
          publicKey RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public)).2 (initial.state, none))
      simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaCountStop.view] at same
      simpa only [continued, transform, simulateQ_map, Option.map_some, initialProject,
        public_same] using same

private theorem continued_original (publicKey : PublicKey)
    (initial : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source))) :
    continued source setup checks wire route representation adversary publicKey (initial.map initialProject) =
      continued source setup checks wire route representation adversary publicKey initial := by
  cases initial with
  | none => rfl
  | some initial =>
      have public_same := RegistrationNativeMldsaCountStart.initial_public initial
      simp only [initialProject] at public_same
      have same := congrArg (fun work => (fun result => result.2.2) <$> work)
        ((RegistrationNativeMldsaCountStop.native setup checks wire route representation initial.created initial.credential
          publicKey RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public)).1 (initial.state, none))
      simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaCountStop.view] at same
      simpa only [continued, Option.map_some, initialProject,
        public_same] using same.symm

noncomputable def program (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery) := do
  let initial ← RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId
  continued (n := n) source setup checks wire route representation adversary publicKey initial

/-- Actual startup and stopped complete typed execution preserve their candidate under count normalization as an equality of free programs. -/
theorem normalized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) :
    transform (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey) =
      program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey := by
  simp only [program, transform, simulateQ_bind]
  change (transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
    transform (continued source setup checks wire route representation adversary publicKey initial)) = _
  calc
    _ = transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
        continued source setup checks wire route representation adversary publicKey (initial.map initialProject) := by
      apply bind_congr
      intro initial
      exact continued_normalized source setup checks wire route representation adversary publicKey initial
    _ = (Option.map initialProject <$> transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId)) >>=
        continued source setup checks wire route representation adversary publicKey := by rw [bind_map_left]
    _ = (Option.map initialProject <$> RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>=
        continued source setup checks wire route representation adversary publicKey := by
      rw [RegistrationNativeMldsaCountStart.start]
    _ = RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId >>= fun initial =>
        continued source setup checks wire route representation adversary publicKey (initial.map initialProject) := by rw [bind_map_left]
    _ = _ := by
      apply bind_congr
      intro initial
      exact continued_original source setup checks wire route representation adversary publicKey initial

/-- Count-free source primitives and actual true-count table execution have identical selected candidates and complete private pool histories. -/
theorem zero (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) :
    RegistrationNativeMldsaZeroSource.evaluate source
      (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey) {} =
      RegistrationNativeMldsaTableProgram.evaluate source
        (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey) {} := by
  rw [← RegistrationNativeMldsaZeroSource.source_program, normalized]

/-- Every candidate actually returned by the complete source program is ordinary valid and fresh against its exact final same-key signing prefix. -/
theorem good (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) (result : Option Forgery × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey) {}))
    (forgery : Forgery) (selected : result.1 = some forgery) :
    Valid source publicKey forgery ∧ Fresh (RegistrationNativeMldsaCandidate.requestsFor publicKey result.2.signing) forgery := by
  simp only [program, RegistrationNativeMldsaTableProgram.evaluate, simulateQ_bind, StateT.run_bind] at supported
  change result ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
    (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {} >>= fun started =>
      RegistrationNativeMldsaTableProgram.evaluate source
        (continued source setup checks wire route representation adversary publicKey started.1) started.2) at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨started, startup, continued_support⟩ := supported
  cases initial_eq : started.1 with
  | none =>
      simp only [initial_eq, continued, RegistrationNativeMldsaTableProgram.evaluate,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued_support
      cases continued_support
      cases selected
  | some initial =>
      simp only [initial_eq, continued, RegistrationNativeMldsaTableProgram.evaluate,
        simulateQ_map, StateT.run_map, support_map] at continued_support
      obtain ⟨inner, possible, same⟩ := continued_support
      cases same
      exact RegistrationNativeMldsaStoppedSource.initialized_good source setup checks wire route representation publicKey ensureInit
        identityIndex serverKeyId started startup initial (by rw [initial_eq]; exact Option.mem_some_self _)
        (adversary initial.public) inner possible forgery selected

/-- The same actual validity/freshness receipt holds for the count-free primitive source used by the ordinary EUF reduction. -/
theorem zero_good (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) (result : Option Forgery × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaZeroSource.evaluate source
      (program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey) {}))
    (forgery : Forgery) (selected : result.1 = some forgery) :
    Valid source publicKey forgery ∧ Fresh (RegistrationNativeMldsaCandidate.requestsFor publicKey result.2.signing) forgery := by
  rw [zero] at supported
  exact good source setup checks wire route representation adversary ensureInit identityIndex serverKeyId publicKey result supported forgery selected
end BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame.normalized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame.zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame.zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame.good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame.good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame.zero_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedGame.zero_good
