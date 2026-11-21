-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop

/-! The complete corrected fixed-key first-candidate game retains actual startup and every reached callback with its external state. Its candidate and private signing-prefix interpretation are unchanged by the checked count normalization. Validity and freshness at captured cuts are separate source invariants. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedGame
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaEuf (PublicKey Forgery Valid Fresh)
open RegistrationNativeMldsaCountStart (initialProject)
open RegistrationNativeMldsaCountMap (transform)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}
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
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)

noncomputable def continued (previous : Platform) (publicKey : PublicKey)
    (initial : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source))) :
    OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery) :=
  match initial with
  | none => pure none
  | some initial => (fun result => result.2.2) <$>
      (simulateQ (RegistrationNativeMldsaStop.freeze
        (RegistrationNativePlatformMldsaCountStop.handler setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaCountStop.observe publicKey) RegistrationNativeMldsaTableStop.defaultReply)
        (adversary initial.public)).run ((initial.state, previous), none)

private theorem continued_normalized (previous : Platform) (publicKey : PublicKey)
    (initial : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source))) :
    transform (continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey initial) =
      continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey (initial.map initialProject) := by
  cases initial with
  | none => simp only [continued, transform, simulateQ_pure, Option.map_none]
  | some initial =>
      have public_same := RegistrationNativeMldsaCountStart.initial_public initial
      simp only [initialProject] at public_same
      have same := congrArg (fun work => (fun result => result.2.2) <$> work)
        ((RegistrationNativePlatformMldsaCountStop.program setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer
          publicKey RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public)).2 ((initial.state, previous), none))
      simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaCountStop.view, RegistrationNativePlatformMldsaCountStop.projection] at same
      simpa only [continued, transform, simulateQ_map, Option.map_some, initialProject,
        public_same] using same

private theorem continued_original (previous : Platform) (publicKey : PublicKey)
    (initial : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source))) :
    continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey (initial.map initialProject) =
      continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey initial := by
  cases initial with
  | none => rfl
  | some initial =>
      have public_same := RegistrationNativeMldsaCountStart.initial_public initial
      simp only [initialProject] at public_same
      have same := congrArg (fun work => (fun result => result.2.2) <$> work)
        ((RegistrationNativePlatformMldsaCountStop.program setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer
          publicKey RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public)).1 ((initial.state, previous), none))
      simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaCountStop.view, RegistrationNativePlatformMldsaCountStop.projection] at same
      simpa only [continued, Option.map_some, initialProject,
        public_same] using same.symm

noncomputable def program (previous : Platform) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) (Option Forgery) := do
  let initial ← RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId
  continued (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey initial

/-- Actual startup and stopped complete corrected typed execution preserve their candidate under count normalization as an equality of free programs. -/
theorem normalized (previous : Platform) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) :
    transform (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId publicKey) =
      program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId publicKey := by
  simp only [program, transform, simulateQ_bind]
  change (transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
    transform (continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey initial)) = _
  calc
    _ = transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>= fun initial =>
        continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey (initial.map initialProject) := by
      apply bind_congr
      intro initial
      exact continued_normalized source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey initial
    _ = (Option.map initialProject <$> transform (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId)) >>=
        continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey := by rw [bind_map_left]
    _ = (Option.map initialProject <$> RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) >>=
        continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey := by
      rw [RegistrationNativeMldsaCountStart.start]
    _ = RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId >>= fun initial =>
        continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey (initial.map initialProject) := by rw [bind_map_left]
    _ = _ := by
      apply bind_congr
      intro initial
      exact continued_original source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous publicKey initial

/-- Count-free source primitives and actual true-count table execution have identical selected candidates and complete private pool histories. -/
theorem zero (previous : Platform) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) :
    RegistrationNativeMldsaZeroSource.evaluate source
      (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId publicKey) {} =
      RegistrationNativeMldsaTableProgram.evaluate source
        (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId publicKey) {} := by
  rw [← RegistrationNativeMldsaZeroSource.source_program, normalized]

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedGame.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedGame.normalized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedGame.zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedGame.zero
